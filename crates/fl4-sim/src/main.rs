//! fl4-sim: deterministic simulation of FL4 on several cores (DESIGN.md
//! §10). The real fl4-core runs against a simulated memory (`SimStore`) and
//! machine (`SimArch`). A seeded scheduler picks which core takes the next
//! kernel entry; user threads issue random, often malformed, syscalls;
//! timers and IPIs are delivered in virtual time. After every entry the
//! oracles check the kernel's invariants. The same seed replays the same
//! run.
//!
//! Until fine-grained locking, kernel entries run one at a time, as under
//! the serial gate; a remote stall runs the target core's stall logic
//! before the initiator continues, which is what the gate protocol does.
//!
//! Usage: fl4-sim [--seeds N] [--first S] [--cores C] [--steps K] [--conc]

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Condvar, Mutex};

use fl4_abi::consts::{bits, object as ot, root_slot as rs};
use fl4_abi::{label, syscall as sc};
use fl4_core::boot::{self, BootParams, Region, MAX_REGIONS};
use fl4_core::capability::Cap;
use fl4_core::layout::{self, irq, ks, node, reg, tcb as tl, PPTR_BASE};
use fl4_core::machine::{Arch, Store};
use fl4_core::obj::{node_get, Slot, Tcb};
use fl4_core::{sched, syscall};
use fl4_store::tx;
use fl4_sync::SerialGate;

/// Simulated physical memory: 0..MEM_BYTES, seen through the kernel window.
const MEM_BYTES: u64 = 96 << 20;
/// Kernel state, idle threads and the extra BootInfo live in "kernel image"
/// memory: the top 8 MiB of simulated memory, not given to user space.
const IMAGE_BYTES: u64 = 8 << 20;

struct Memory {
    words: Vec<AtomicU64>,
}

impl Memory {
    fn index(&self, addr: u64) -> usize {
        let p = addr.wrapping_sub(PPTR_BASE);
        assert!(addr % 8 == 0, "fl4-sim: unaligned kernel access at {addr:#x}");
        assert!(p < MEM_BYTES, "fl4-sim: kernel access outside memory at {addr:#x}");
        (p / 8) as usize
    }
    fn get(&self, addr: u64) -> u64 {
        self.words[self.index(addr)].load(Ordering::Relaxed)
    }
    fn set(&self, addr: u64, v: u64) {
        self.words[self.index(addr)].store(v, Ordering::Relaxed)
    }
}

/// Concurrent mode: one host thread per simulated core, run one at a time
/// in an order the seed decides, switching at memory accesses and spins.
struct Conc {
    baton: Mutex<Baton>,
    cv: Condvar,
    /// Cores asked to service a remote stall.
    call_pending: AtomicU64,
    in_kernel: Vec<AtomicBool>,
    gate_held: Vec<AtomicBool>,
    /// Cores that have run all their steps.
    out_of_steps: AtomicU64,
}

struct Baton {
    turn: u64,
    rng: Rng,
    done: Vec<bool>,
}

impl Conc {
    fn new(n: u64, seed: u64) -> Conc {
        Conc {
            baton: Mutex::new(Baton { turn: 0, rng: Rng(seed ^ 0x5DEE_CE66_D1CE_4E5B | 1), done: vec![false; n as usize] }),
            cv: Condvar::new(),
            call_pending: AtomicU64::new(0),
            in_kernel: (0..n).map(|_| AtomicBool::new(false)).collect(),
            gate_held: (0..n).map(|_| AtomicBool::new(false)).collect(),
            out_of_steps: AtomicU64::new(0),
        }
    }

    fn pass(&self, b: &mut Baton) {
        let live: Vec<u64> = (0..b.done.len() as u64).filter(|&c| !b.done[c as usize]).collect();
        if !live.is_empty() {
            b.turn = live[b.rng.below(live.len() as u64) as usize];
        }
        self.cv.notify_all();
    }

    fn wait_turn(&self, cpu: u64, mut b: std::sync::MutexGuard<'_, Baton>) {
        while b.turn != cpu {
            b = self.cv.wait(b).unwrap();
        }
    }

    /// A scheduling point: maybe let another core run.
    fn pause(&self, cpu: u64) {
        let mut b = self.baton.lock().unwrap();
        if b.rng.below(4) != 0 {
            return;
        }
        self.pass(&mut b);
        self.wait_turn(cpu, b);
    }

    /// A spinning core always lets another core run.
    fn relax(&self, cpu: u64) {
        let mut b = self.baton.lock().unwrap();
        self.pass(&mut b);
        self.wait_turn(cpu, b);
    }

    fn start(&self, cpu: u64) {
        let b = self.baton.lock().unwrap();
        self.wait_turn(cpu, b);
    }

    fn finish(&self, cpu: u64) {
        let mut b = self.baton.lock().unwrap();
        b.done[cpu as usize] = true;
        self.pass(&mut b);
    }
}

#[derive(Clone)]
struct SimStore {
    mem: Arc<Memory>,
    ks_base: u64,
    cpu: u64,
    /// Accesses go through this core's transaction.
    tx: bool,
    conc: Option<Arc<Conc>>,
}

impl SimStore {
    fn pause(&self) {
        if let Some(c) = &self.conc {
            c.pause(self.cpu);
        }
    }
}

impl tx::Mem for SimStore {
    fn load(&self, addr: u64) -> u64 {
        self.pause();
        self.mem.get(addr)
    }
    fn store(&self, addr: u64, v: u64) {
        self.pause();
        self.mem.set(addr, v)
    }
    fn relax(&self) {
        self.pause();
    }
}

impl Store for SimStore {
    fn read(&self, addr: u64) -> u64 {
        if self.tx {
            tx::read(self.cpu, self, addr)
        } else {
            self.pause();
            self.mem.get(addr)
        }
    }
    fn write(&mut self, addr: u64, v: u64) {
        if self.tx {
            self.pause();
            tx::write(self.cpu, addr, v)
        } else {
            self.pause();
            self.mem.set(addr, v)
        }
    }
    fn zero(&mut self, addr: u64, len: u64) {
        assert!(len % 8 == 0);
        if self.tx {
            tx::zero(self.cpu, addr, len);
            return;
        }
        self.pause();
        let mut a = addr;
        while a < addr + len {
            self.mem.set(a, 0);
            a += 8;
        }
    }
    fn ks_base(&self) -> u64 {
        self.ks_base
    }
    fn cur_cpu(&self) -> u64 {
        self.cpu
    }
}

#[derive(Clone, Copy)]
enum Effect {
    Deadline(u64),
    Reschedule(u64),
    Putc(u8),
}

/// Per-core machine state.
#[derive(Default, Clone)]
struct Core {
    deadline: u64,
    /// Pending IRQs (bit = irq number, up to 191).
    pending: [u64; 3],
    /// Inside a transaction: Arch effects are queued.
    tx: bool,
    effects: Vec<Effect>,
    /// An interrupt taken during the current entry.
    held_irq: Option<u64>,
}

struct Machine {
    now: u64,
    cores: Vec<Core>,
    console: Vec<u8>,
    rng: Rng,
    halted: bool,
}

#[derive(Clone)]
struct SimArch {
    m: Arc<Mutex<Machine>>,
    mem: Arc<Memory>,
    ks_base: u64,
    cpu: u64,
    conc: Option<Arc<Conc>>,
}

impl SimArch {
    fn raise(&self, cpu: u64, irq: u64) {
        let mut m = self.m.lock().unwrap();
        m.cores[cpu as usize].pending[(irq / 64) as usize] |= 1 << (irq % 64);
    }

    fn in_tx(&self) -> bool {
        self.m.lock().unwrap().cores[self.cpu as usize].tx
    }

    /// Queue `e` inside a transaction; returns whether it did.
    fn defer(&self, e: Effect) -> bool {
        let mut m = self.m.lock().unwrap();
        let c = &mut m.cores[self.cpu as usize];
        if c.tx {
            c.effects.push(e);
            true
        } else {
            false
        }
    }

    fn apply(&self, e: Effect) {
        match e {
            Effect::Deadline(t) => self.m.lock().unwrap().cores[self.cpu as usize].deadline = t,
            Effect::Reschedule(mask) => {
                let n = self.m.lock().unwrap().cores.len() as u64;
                for c in 0..n {
                    if mask & (1 << c) != 0 && c != self.cpu {
                        self.raise(c, irq::RESCHEDULE_IPI);
                    }
                }
            }
            Effect::Putc(b) => self.m.lock().unwrap().console.push(b),
        }
    }
}

/// 1 tick = 1/100 us: a 100 MHz clock.
const TICKS_PER_US: u64 = 100;

impl Arch for SimArch {
    fn now(&mut self) -> u64 {
        let mut m = self.m.lock().unwrap();
        // Time passes during kernel entries too.
        let d = 1 + m.rng.below(50);
        m.now += d;
        m.now
    }
    fn set_deadline(&mut self, ticks: u64) {
        if !self.defer(Effect::Deadline(ticks)) {
            self.apply(Effect::Deadline(ticks));
        }
    }
    fn us_to_ticks(&self, us: u64) -> u64 {
        us.saturating_mul(TICKS_PER_US)
    }
    fn ticks_to_us(&self, ticks: u64) -> u64 {
        ticks / TICKS_PER_US
    }
    fn max_us(&self) -> u64 {
        u64::MAX / TICKS_PER_US
    }
    fn kernel_wcet_ticks(&self) -> u64 {
        10 * TICKS_PER_US
    }
    fn irq_pending(&mut self) -> bool {
        let m = self.m.lock().unwrap();
        m.cores[self.cpu as usize].pending.iter().any(|w| *w != 0)
    }
    fn take_pending_irq(&mut self) -> u64 {
        let mut m = self.m.lock().unwrap();
        let c = &mut m.cores[self.cpu as usize];
        if let Some(i) = c.held_irq {
            return i;
        }
        for w in 0..3 {
            if c.pending[w] != 0 {
                let b = c.pending[w].trailing_zeros() as u64;
                c.pending[w] &= !(1 << b);
                let i = w as u64 * 64 + b;
                c.held_irq = Some(i);
                return i;
            }
        }
        syscall::NO_IRQ
    }
    fn mask_irq(&mut self, _irq: u64, _mask: bool) {}
    fn ack_irq(&mut self, _irq: u64) {}
    fn set_vspace(&mut self, _root: u64, _asid: u64) {}
    fn invalidate_page(&mut self, _asid: u64, _vaddr: u64) {}
    fn invalidate_asid(&mut self, _asid: u64) {}
    fn invalidate_page_structures(&mut self, _asid: u64) {}
    fn ioapic_map(&mut self, _i: u64, _p: u64, _l: u64, _q: u64, _v: u64) -> bool {
        true
    }
    fn ioapic_map_remapped(&mut self, _i: u64, _p: u64, _l: u64, _q: u64, _v: u64, _h: u64) -> bool {
        true
    }
    fn num_ioapics(&self) -> u64 {
        1
    }
    fn ioapic_pins(&self, _i: u64) -> u64 {
        24
    }
    fn port_in(&mut self, _port: u64, _size: u64) -> u64 {
        0
    }
    fn port_out(&mut self, _port: u64, _size: u64, _v: u64) {}
    fn fpu_flush(&mut self, _tcb: u64) {}
    fn fpu_sanitise(&mut self, _tcb: u64) {}
    fn fpu_reload(&mut self, _tcb: u64) {}
    fn fpu_release(&mut self, _tcb: u64) {}
    fn remote_stall(&mut self, cpu: u64) {
        match &self.conc {
            // Entries run one at a time: the target services the stall at
            // once, on the gate holder's behalf.
            None => {
                let mut s = SimStore { mem: self.mem.clone(), ks_base: self.ks_base, cpu, tx: false, conc: None };
                let mut a = SimArch { cpu, ..self.clone() };
                fl4_core::smp::stall(&mut s, &mut a);
            }
            Some(c) => {
                if self.in_tx() {
                    tx::doom_serial(self.cpu);
                    return;
                }
                // Ask the target and wait until it has serviced the stall.
                c.call_pending.fetch_or(1 << cpu, Ordering::SeqCst);
                while c.call_pending.load(Ordering::SeqCst) & (1 << cpu) != 0 {
                    c.pause(self.cpu);
                }
            }
        }
    }
    fn send_reschedule(&mut self, mask: u64) {
        if !self.defer(Effect::Reschedule(mask)) {
            self.apply(Effect::Reschedule(mask));
        }
    }
    fn putc(&mut self, c: u64) {
        if !self.defer(Effect::Putc(c as u8)) {
            self.apply(Effect::Putc(c as u8));
        }
    }
    fn get_char(&mut self) -> u64 {
        u64::MAX
    }
    fn halt(&mut self) {
        if self.conc.is_some() && self.in_tx() {
            tx::doom_serial(self.cpu);
            return;
        }
        // seL4_DebugHalt (or a debug call that halts on bad arguments)
        // stops the machine: the run ends there.
        self.m.lock().unwrap().halted = true;
    }
}

/// The serial gate of the simulated machine.
static GATE: SerialGate = SerialGate::new();

/// The simulator's side of `fl4_sync::run_entry`.
struct SimEnv {
    s: SimStore,
    a: SimArch,
    conc: Arc<Conc>,
}

impl SimEnv {
    /// Service a remote stall addressed to this core, if any.
    fn service(&self) -> bool {
        let me = 1u64 << self.s.cpu;
        if self.conc.call_pending.load(Ordering::SeqCst) & me == 0 {
            return false;
        }
        let mut s = SimStore { tx: false, ..self.s.clone() };
        let mut a = self.a.clone();
        fl4_core::smp::stall(&mut s, &mut a);
        self.conc.call_pending.fetch_and(!me, Ordering::SeqCst);
        true
    }
}

impl fl4_sync::EntryEnv for SimEnv {
    type S = SimStore;
    type A = SimArch;
    type M = SimStore;
    fn cpu(&self) -> u64 {
        self.s.cpu
    }
    fn multi(&self) -> bool {
        true
    }
    fn store(&self, tx: bool) -> SimStore {
        SimStore { tx, ..self.s.clone() }
    }
    fn arch(&self) -> SimArch {
        self.a.clone()
    }
    fn mem(&self) -> &SimStore {
        &self.s
    }
    fn service_remote(&self) -> bool {
        let r = self.service();
        self.s.pause();
        r
    }
    fn set_tx(&self, on: bool) {
        self.a.m.lock().unwrap().cores[self.s.cpu as usize].tx = on;
        // Send some entries down the serial path, so serial entries overlap
        // transactions often enough to test the gate.
        if on && self.conc.baton.lock().unwrap().rng.below(8) == 0 {
            tx::doom_serial(self.s.cpu);
        }
    }
    fn finish_effects(&self, committed: bool) {
        let effects = std::mem::take(&mut self.a.m.lock().unwrap().cores[self.s.cpu as usize].effects);
        if committed {
            for e in effects {
                self.a.apply(e);
            }
        }
    }
    fn entry_done(&self) {
        self.a.m.lock().unwrap().cores[self.s.cpu as usize].held_irq = None;
    }
    fn holding_gate(&self) {
        self.conc.gate_held[self.s.cpu as usize].store(true, Ordering::SeqCst);
    }
    fn count(&self, what: fl4_sync::Count) {
        let mut st = STATS.lock().unwrap();
        match what {
            fl4_sync::Count::Commit => st.0 += 1,
            fl4_sync::Count::Abort => st.1 += 1,
            fl4_sync::Count::Serial => st.2 += 1,
        }
    }
}

/// Transactions committed, aborted, and entries run serially.
static STATS: Mutex<(u64, u64, u64)> = Mutex::new((0, 0, 0));

/// xorshift64*, seeded.
#[derive(Clone)]
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        if n == 0 {
            0
        } else {
            self.next() % n
        }
    }
}

#[derive(Clone)]
struct Sim {
    s: SimStore,
    a: SimArch,
    ncores: u64,
    /// Root CNode slots holding objects the workload created.
    objs: Vec<u64>,
    next_slot: u64,
    /// Root CNode slots of the workers' fault endpoint and the root task's
    /// reply object: the root task serves the workers' faults.
    fault_ep: u64,
    reply: u64,
}

fn pptr(p: u64) -> u64 {
    p + PPTR_BASE
}

impl Sim {
    fn new(seed: u64, ncores: u64) -> Sim {
        let mem = Arc::new(Memory { words: (0..MEM_BYTES / 8).map(|_| AtomicU64::new(0)).collect() });
        let image = MEM_BYTES - IMAGE_BYTES;
        let ks_base = pptr(image);
        let m = Arc::new(Mutex::new(Machine {
            now: 1_000_000,
            cores: vec![Core::default(); ncores as usize],
            console: Vec::new(),
            halted: false,
            rng: Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1),
        }));
        let s = SimStore { mem: mem.clone(), ks_base, cpu: 0, tx: false, conc: None };
        let a = SimArch { m, mem, ks_base, cpu: 0, conc: None };
        Sim { s, a, ncores, objs: Vec::new(), next_slot: 0, fault_ep: 0, reply: 0 }
    }

    /// Run the kernel part of an entry: directly, or (concurrent mode)
    /// through fl4_sync::run_entry as the kernel does.
    fn enter(&mut self, irq: bool, body: impl FnMut(&mut SimStore, &mut SimArch)) {
        let mut body = body;
        let Some(conc) = self.s.conc.clone() else {
            return body(&mut self.s, &mut self.a);
        };
        let cpu = self.s.cpu as usize;
        conc.in_kernel[cpu].store(true, Ordering::SeqCst);
        let env = SimEnv { s: self.s.clone(), a: self.a.clone(), conc: conc.clone() };
        fl4_sync::run_entry(&env, &GATE, irq, &mut body);
        if conc.gate_held[cpu].swap(false, Ordering::SeqCst) {
            GATE.release();
        }
        conc.in_kernel[cpu].store(false, Ordering::SeqCst);
    }

    /// Oracles may run: no other core is inside the kernel.
    fn quiet(&self) -> bool {
        match &self.s.conc {
            None => true,
            Some(c) => (0..self.ncores).all(|i| i == self.s.cpu || !c.in_kernel[i as usize].load(Ordering::SeqCst)),
        }
    }

    fn on(&mut self, cpu: u64) {
        self.s.cpu = cpu;
        self.a.cpu = cpu;
    }

    fn boot(&mut self) {
        let image = MEM_BYTES - IMAGE_BYTES;
        let idle_base = pptr(image + (1 << 20));
        let extra = pptr(image + (2 << 20));
        // The "root task image": 4 pages at 1 MiB, mapped at 0x400000.
        let ui_p = 1 << 20;
        let mut p = BootParams {
            free: [Region::EMPTY; MAX_REGIONS],
            n_free: 1,
            device: [Region::EMPTY; MAX_REGIONS],
            n_device: 1,
            ui_p_start: ui_p,
            ui_p_end: ui_p + 4 * 4096,
            pv_offset: ui_p.wrapping_sub(0x40_0000),
            v_entry: 0x40_0000,
            extra_bi: extra,
            extra_bi_len: 0,
            num_nodes: self.ncores,
            idle_base,
            idle_stride: 8192,
        };
        p.free[0] = Region { start: pptr(2 << 20), end: pptr(image) };
        p.device[0] = Region { start: MEM_BYTES, end: MEM_BYTES + (1 << 30) };
        self.on(0);
        let ks_base = self.s.ks_base;
        self.s.zero(ks_base, ks::SIZE);
        let root = pptr(image + (3 << 20));
        fl4_core::obj::ks_set(&mut self.s, ks::KERNEL_ROOT, root);
        if boot::create_root_task(&mut self.s, &mut self.a, &mut p).is_err() {
            panic!("create_root_task failed");
        }
        sched::schedule(&mut self.s, &mut self.a);
        sched::activate_thread(&mut self.s, &mut self.a);
        let bi = 0x40_0000 + 4 * 4096 + 4096;
        let _ = bi;
        self.next_slot = self.first_empty();
        self.check("boot");
    }

    /// The first empty slot BootInfo reports (seL4_BootInfo.empty.start).
    fn first_empty(&self) -> u64 {
        let rt = self.root_cnode();
        (rs::NumInitialCaps..(1 << boot::ROOT_CNODE_BITS)).find(|&i| Slot::index(rt, i).cap(&self.s).is_null()).unwrap()
    }

    fn root_cnode(&self) -> u64 {
        match Tcb(self.root_tcb()).slot(tl::SLOT_CTABLE).cap(&self.s) {
            Cap::CNode { ptr, .. } => ptr,
            c => panic!("root CNode cap is {:?}", cap_name(c)),
        }
    }

    fn root_tcb(&self) -> u64 {
        let rt_slot = self.root_cnode_slot(rs::InitThreadTCB);
        match rt_slot {
            Cap::Thread { ptr } => ptr,
            _ => 0,
        }
    }

    fn root_cnode_slot(&self, i: u64) -> Cap {
        // Find the root CNode through any core's debug list: the root
        // server is the TCB named "rootserver".
        let t = self.find_thread(|s, t| name_of(s, t) == "rootserver").expect("root server");
        let rt = match t.slot(tl::SLOT_CTABLE).cap(&self.s) {
            Cap::CNode { ptr, .. } => ptr,
            _ => panic!("no root CNode"),
        };
        Slot::index(rt, i).cap(&self.s)
    }

    fn threads(&self) -> Vec<Tcb> {
        let mut v = Vec::new();
        for c in 0..self.ncores {
            let mut t = node_get(&self.s, c, node::DEBUG_TCBS);
            let mut fuel = 100_000;
            while t != 0 && fuel > 0 {
                v.push(Tcb(t));
                t = Tcb(t).debug_next(&self.s);
                fuel -= 1;
            }
            assert!(fuel > 0, "debug TCB list of core {c} does not end");
        }
        v
    }

    fn find_thread(&self, f: impl Fn(&SimStore, Tcb) -> bool) -> Option<Tcb> {
        self.threads().into_iter().find(|&t| f(&self.s, t))
    }

    // ---- the workload ---------------------------------------------------

    /// Run a syscall as the current thread of `cpu`.
    fn syscall(&mut self, cpu: u64, number: i64, cptr: u64, info: u64, mrs: [u64; 4]) {
        self.on(cpu);
        let t = sched::cur_thread(&self.s);
        if TRACE.load(Ordering::Relaxed) {
            let c = self.objs.iter().position(|&o| o == cptr).map(|_| {
                let cap = Slot::index(self.root_cnode(), cptr).cap(&self.s);
                cap_kind(cap)
            });
            println!(
                "  core {cpu} thread {:#x} ({}) syscall {number} cptr {cptr} {:?} label {} len {} mrs {:x?}",
                t.0,
                name_of(&self.s, t),
                c,
                info >> 12,
                info & 127,
                mrs
            );
        }
        t.set_reg(&mut self.s, reg::CAP, cptr);
        t.set_reg(&mut self.s, reg::MSG_INFO, info);
        t.set_reg(&mut self.s, reg::R10, mrs[0]);
        t.set_reg(&mut self.s, reg::R8, mrs[1]);
        t.set_reg(&mut self.s, reg::R9, mrs[2]);
        t.set_reg(&mut self.s, reg::R15, mrs[3]);
        t.set_reg(&mut self.s, reg::RDX, number as u64);
        let ip = t.reg(&self.s, reg::NEXT_IP);
        t.set_reg(&mut self.s, reg::NEXT_IP, ip.wrapping_add(2));
        self.enter(false, |s, a| syscall::handle_syscall(s, a, number));
    }

    /// Message words beyond the registers go in the IPC buffer.
    fn set_buffer_mr(&mut self, cpu: u64, i: u64, v: u64) {
        self.on(cpu);
        let t = sched::cur_thread(&self.s);
        let buf = fl4_core::msg::lookup_ipc_buffer(&self.s, false, t);
        if buf != 0 {
            fl4_core::msg::buf_set(&mut self.s, buf, i + 1, v);
        }
    }

    fn invoke(&mut self, cpu: u64, cptr: u64, lbl: u64, args: &[u64], extra_caps: &[u64]) {
        let mut mrs = [0u64; 4];
        for (i, &v) in args.iter().enumerate() {
            if i < 4 {
                mrs[i] = v;
            } else {
                self.set_buffer_mr(cpu, i as u64, v);
            }
        }
        for (i, &c) in extra_caps.iter().enumerate() {
            self.set_buffer_mr(cpu, fl4_core::msg::BUF_CAPS - 1 + i as u64, c);
        }
        let info = (lbl << 12) | ((extra_caps.len() as u64) << 7) | args.len() as u64;
        self.syscall(cpu, sc::SysCall, cptr, info, mrs);
    }

    /// Retype objects from the first untyped into free root CNode slots.
    fn setup(&mut self) {
        let ut = self.first_untyped();
        let plan: &[(u64, u64, u64)] = &[
            (ot::Endpoint, 0, 4),
            (ot::Notification, 0, 4),
            (ot::Reply, 0, 4),
            (ot::Tcb, 0, 6),
            (ot::SchedContext, bits::MIN_SCHED_CONTEXT, 6),
            (ot::CapTable, 4, 2),
            (ot::X86Page4K, 0, 4),
        ];
        for &(ty, size, n) in plan {
            let dest = self.next_slot;
            self.invoke(0, ut, label::UntypedRetype, &[ty, size, rs::InitThreadCNode, 0, dest, n], &[rs::InitThreadCNode]);
            self.after("setup retype");
            for i in 0..n {
                if !Slot::index(self.root_cnode(), dest + i).cap(&self.s).is_null() {
                    self.objs.push(dest + i);
                }
            }
            self.next_slot += n;
        }
        // Give each new TCB a CSpace, VSpace, priority, an SC on some core,
        // and start it: these become the threads running random programs.
        let tcbs: Vec<u64> = self.objs_of(|c| matches!(c, Cap::Thread { .. }));
        let scs: Vec<u64> = self.objs_of(|c| matches!(c, Cap::SchedContext { .. }));
        self.fault_ep = self.objs_of(|c| matches!(c, Cap::Endpoint { .. }))[0];
        self.reply = self.objs_of(|c| matches!(c, Cap::Reply { .. }))[0];
        let fault_ep = self.fault_ep;
        for (k, &t) in tcbs.iter().enumerate() {
            self.invoke(0, t, label::TCBSetSpace, &[0, 0], &[fault_ep, rs::InitThreadCNode, rs::InitThreadVSpace]);
            self.after("set space");
            self.invoke(0, t, label::TCBSetPriority, &[100 + k as u64 % 3], &[rs::InitThreadTCB]);
            self.after("sched params");
            if let Some(&scap) = scs.get(k) {
                let core = k as u64 % self.ncores;
                let ctrl = self.sched_control(core);
                self.invoke(0, ctrl, label::SchedControlConfigureFlags, &[1000 * TICKS_PER_US, 1000 * TICKS_PER_US, 0, k as u64, 0], &[scap]);
                self.after("sc configure");
                self.invoke(0, scap, label::SchedContextBind, &[], &[t]);
                self.after("sc bind");
            }
            self.invoke(0, t, label::TCBResume, &[], &[]);
            self.after("resume");
        }
    }

    fn sched_control(&self, core: u64) -> u64 {
        let rt = self.root_cnode();
        (rs::NumInitialCaps..self.next_slot)
            .find(|&i| matches!(Slot::index(rt, i).cap(&self.s), Cap::SchedControl { cpu } if cpu == core))
            .unwrap_or(0)
    }

    fn first_untyped(&self) -> u64 {
        let rt = self.root_cnode();
        let mut best = (0, 0);
        for i in rs::NumInitialCaps..(1 << boot::ROOT_CNODE_BITS) {
            if let Cap::Untyped { size_bits, is_device: false, .. } = Slot::index(rt, i).cap(&self.s) {
                if size_bits > best.1 {
                    best = (i, size_bits);
                }
            }
        }
        best.0
    }

    fn objs_of(&self, f: impl Fn(Cap) -> bool) -> Vec<u64> {
        let rt = self.root_cnode();
        self.objs.iter().copied().filter(|&i| f(Slot::index(rt, i).cap(&self.s))).collect()
    }

    /// The root task's turn: mostly serve the workers' faults (reply with
    /// label 0, which restarts the faulting thread, and wait for the next),
    /// sometimes a random invocation on a valid cap (it has no fault
    /// handler, so it avoids cap faults).
    fn root_turn(&mut self, cpu: u64) {
        // Invoking an endpoint or notification could block the root task
        // for good (nobody would serve faults then): it invokes other objects.
        let targets = self.objs_of(|c| !matches!(c, Cap::Endpoint { .. } | Cap::Notification { .. } | Cap::Reply { .. }));
        let (serve, lbl, len, target, other) = {
            let mut g = self.a.m.lock().unwrap();
            let r = &mut g.rng;
            let n = self.objs.len() as u64;
            let t = if targets.is_empty() { 0 } else { targets[r.below(targets.len() as u64) as usize] };
            (r.below(10) < 7 || targets.is_empty(), r.below(80), r.below(6), t, self.objs[r.below(n) as usize])
        };
        let mode = self.a.m.lock().unwrap().rng.below(10);
        self.on(cpu);
        let t = sched::cur_thread(&self.s);
        t.set_reg(&mut self.s, reg::REPLY, self.reply);
        let _ = serve;
        if mode < 3 {
            // Reply to the last fault (label 0: restart the faulter).
            let r = self.reply;
            self.syscall(cpu, sc::SysSend, r, 0, [0; 4]);
        } else if mode < 6 {
            // Poll for the next fault without blocking.
            let ep = self.fault_ep;
            self.syscall(cpu, sc::SysNBRecv, ep, 0, [0; 4]);
        } else if mode < 7 {
            // Resume a worker (stuck or stopped ones run again).
            let tcbs = self.objs_of(|c| matches!(c, Cap::Thread { .. }));
            let w = tcbs[self.a.m.lock().unwrap().rng.below(tcbs.len() as u64) as usize];
            self.invoke(cpu, w, label::TCBResume, &[], &[]);
        } else {
            let mrs = [other, 1, 0, 4];
            self.invoke(cpu, target, lbl, &mrs[..len.min(4) as usize], &[other]);
        }
    }

    fn is_root(&self, t: Tcb) -> bool {
        name_of(&self.s, t) == "rootserver"
    }

    /// One random user-level action by the current thread of `cpu`.
    fn random_syscall(&mut self, cpu: u64) {
        self.on(cpu);
        if self.is_root(sched::cur_thread(&self.s)) {
            return self.root_turn(cpu);
        }
        let mut guard = self.a.m.lock().unwrap();
        let rng = &mut guard.rng;
        let pick = rng.below(100);
        let n = self.objs.len() as u64;
        let cptr = if n > 0 && rng.below(10) < 8 { self.objs[rng.below(n) as usize] } else { rng.below(64) };
        let other = if n > 0 { self.objs[rng.below(n) as usize] } else { 0 };
        let lbl = rng.below(80);
        let len = rng.below(8);
        let mut mrs = [0u64; 4];
        for m in mrs.iter_mut() {
            *m = match rng.below(4) {
                0 => rng.next(),
                1 => rng.below(16),
                2 => other,
                _ => rng.below(1 << 20),
            };
        }
        let extra = rng.below(3);
        let number = match pick {
            0..=29 => sc::SysCall,
            30..=39 => sc::SysSend,
            40..=49 => sc::SysNBSend,
            50..=59 => sc::SysRecv,
            60..=64 => sc::SysNBRecv,
            65..=69 => sc::SysWait,
            70..=74 => sc::SysReplyRecv,
            75..=79 => sc::SysYield,
            80..=84 => sc::SysNBWait,
            85..=89 => sc::SysNBSendRecv,
            90..=94 => sc::SysDebugPutChar,
            _ => {
                // Any number, except the debug calls that stop the machine.
                let n = -(rng.below(40) as i64);
                if n == sc::SysDebugHalt || n == sc::SysDebugNameThread {
                    sc::SysYield
                } else {
                    n
                }
            }
        };
        drop(guard);
        if extra > 0 {
            self.set_buffer_mr(cpu, fl4_core::msg::BUF_CAPS - 1, other);
        }
        let info = (lbl << 12) | (extra << 7) | len;
        // Reply objects in R12, the NBSendRecv destination in R13.
        self.on(cpu);
        let t = sched::cur_thread(&self.s);
        t.set_reg(&mut self.s, reg::REPLY, other);
        t.set_reg(&mut self.s, reg::NBSEND_RECV_DEST, cptr);
        self.syscall(cpu, number, cptr, info, mrs);
    }

    /// The next thing that happens on core `cpu`.
    fn step(&mut self, cpu: u64) {
        self.on(cpu);
        // At user level a core takes a remote stall's IPI at once.
        if let Some(conc) = self.s.conc.clone() {
            SimEnv { s: self.s.clone(), a: self.a.clone(), conc }.service();
        }
        // A due timer raises its interrupt.
        {
            let mut m = self.a.m.lock().unwrap();
            let now = m.now;
            let core = &mut m.cores[cpu as usize];
            if core.deadline != 0 && core.deadline <= now {
                core.deadline = 0;
                core.pending[(irq::TIMER / 64) as usize] |= 1 << (irq::TIMER % 64);
            }
        }
        // The interrupt the core takes now (not one the kernel polls for,
        // so it is not held for the entry).
        let pending = {
            let mut m = self.a.m.lock().unwrap();
            let c = &mut m.cores[cpu as usize];
            match (0..3).find(|&w| c.pending[w] != 0) {
                Some(w) => {
                    let b = c.pending[w].trailing_zeros() as u64;
                    c.pending[w] &= !(1 << b);
                    w as u64 * 64 + b
                }
                None => syscall::NO_IRQ,
            }
        };
        if pending != syscall::NO_IRQ {
            if TRACE.load(Ordering::Relaxed) {
                println!("  core {cpu} irq {pending}");
            }
            self.enter(true, |s, a| syscall::handle_interrupt_entry(s, a, pending));
            self.after("interrupt");
            return;
        }
        let ct = sched::cur_thread(&self.s);
        if ct == sched::idle_thread(&self.s) {
            // Idle: time passes to this core's next deadline.
            let mut m = self.a.m.lock().unwrap();
            let d = m.cores[cpu as usize].deadline;
            if d > m.now {
                m.now = d.min(m.now + 100 * TICKS_PER_US);
            } else {
                m.now += 10;
            }
            return;
        }
        self.random_syscall(cpu);
        self.after("syscall");
    }

    fn after(&mut self, what: &str) {
        if !self.quiet() {
            return;
        }
        // Check on a copy that does not let other cores run meanwhile.
        let mut q = self.clone();
        q.s.conc = None;
        q.a.conc = None;
        q.check(what);
        q.check_cdt(what);
        q.check_queues(what);
    }

    // ---- oracles ----------------------------------------------------------

    fn check(&self, what: &str) {
        let s = &self.s;
        let threads = self.threads();
        for c in 0..self.ncores {
            let ct = Tcb(node_get(s, c, node::CUR_THREAD));
            let idle = Tcb(node_get(s, c, node::IDLE_THREAD));
            if ct != idle {
                let st = ct.state(s);
                assert!(
                    st == sched::TS_RUNNING || st == sched::TS_RESTART,
                    "{what}: core {c} runs thread {:#x} in state {st}",
                    ct.0
                );
                assert!(ct.sc(s) != 0, "{what}: core {c} runs thread {:#x} without an SC", ct.0);
                assert_eq!(ct.affinity(s), c, "{what}: core {c} runs a thread of core {}", ct.affinity(s));
            }
            // Liveness: an idle core with ready threads has been asked to
            // reschedule (or will choose at its next entry).
            if ct == idle && node_get(s, c, node::SCHED_ACTION) == sched::ACTION_RESUME_CURRENT {
                let ready = (0..layout::NUM_PRIORITIES).any(|p| node_get(s, c, node::READY_QUEUES + p * 16) != 0);
                if ready {
                    let m = self.a.m.lock().unwrap();
                    let pend = m.cores[c as usize].pending;
                    let ipi = pend[(irq::RESCHEDULE_IPI / 64) as usize] & (1 << (irq::RESCHEDULE_IPI % 64)) != 0;
                    let timer = pend[(irq::TIMER / 64) as usize] & (1 << (irq::TIMER % 64)) != 0;
                    assert!(ipi || timer || m.halted, "{what}: core {c} is idle with ready threads and no reschedule pending");
                }
            }
            // Ready queues: well linked, runnable, on this core.
            for prio in 0..layout::NUM_PRIORITIES {
                let off = node::READY_QUEUES + prio * 16;
                let head = node_get(s, c, off);
                let tail = node_get(s, c, off + 8);
                let mut t = head;
                let mut prev = 0;
                let mut n = 0;
                while t != 0 {
                    let tt = Tcb(t);
                    assert_eq!(tt.sched_prev(s), prev, "{what}: ready queue {prio} of core {c} badly linked");
                    assert!(sched::queued(s, tt), "{what}: thread in a ready queue without its flag");
                    assert_eq!(tt.prio(s), prio, "{what}: thread in the wrong ready queue");
                    assert_eq!(tt.affinity(s), c, "{what}: thread in another core's ready queue");
                    assert!(sched::is_runnable(s, tt), "{what}: blocked thread {t:#x} in a ready queue");
                    assert_ne!(t, ct.0, "{what}: the current thread of core {c} is also queued");
                    prev = t;
                    t = tt.sched_next(s);
                    n += 1;
                    assert!(n < 10_000, "{what}: ready queue does not end");
                }
                assert_eq!(tail, prev, "{what}: ready queue {prio} of core {c} has a wrong tail");
            }
        }
        for t in threads {
            if sched::queued(s, t) {
                let off = node::READY_QUEUES + t.prio(s) * 16;
                let mut x = node_get(s, t.affinity(s), off);
                let mut found = false;
                while x != 0 {
                    if x == t.0 {
                        found = true;
                        break;
                    }
                    x = Tcb(x).sched_next(s);
                }
                assert!(found, "{what}: thread {:#x} flagged queued but not in its queue", t.0);
            }
            let st = t.state(s);
            if st == sched::TS_BLOCKED_ON_SEND || st == sched::TS_BLOCKED_ON_RECV {
                let ep = t.block_obj(s);
                let mut x = s.read(ep);
                let mut found = false;
                while x != 0 {
                    if x == t.0 {
                        found = true;
                        break;
                    }
                    x = Tcb(x).ep_next(s);
                }
                assert!(found, "{what}: thread {:#x} blocked on {ep:#x} but not in its queue", t.0);
            }
        }
    }
}

impl Sim {
    /// Every capability slot the workload can reach: the root CNode, the
    /// CNodes it created, and the slots of every TCB.
    fn slots(&self) -> Vec<Slot> {
        let mut v = Vec::new();
        let rt = self.root_cnode();
        for i in 0..(1u64 << boot::ROOT_CNODE_BITS) {
            v.push(Slot::index(rt, i));
        }
        for &o in &self.objs {
            if let Cap::CNode { ptr, radix, .. } = Slot::index(rt, o).cap(&self.s) {
                for i in 0..(1u64 << radix.min(12)) {
                    v.push(Slot::index(ptr, i));
                }
            }
        }
        for t in self.threads() {
            for i in 0..tl::NUM_SLOTS {
                v.push(t.slot(i));
            }
        }
        v
    }

    /// The CDT is a well-formed doubly linked list, and empty slots are
    /// off it.
    fn check_cdt(&self, what: &str) {
        let s = &self.s;
        for sl in self.slots() {
            let c = sl.cap(s);
            let (p, n) = (sl.prev(s), sl.next(s));
            if c.is_null() {
                assert!(p.is_null() && n.is_null(), "{what}: empty slot {:#x} is linked into the CDT", sl.0);
                continue;
            }
            if !n.is_null() {
                assert!(n.prev(s) == sl, "{what}: CDT next of {:#x} does not point back", sl.0);
                assert!(!n.cap(s).is_null(), "{what}: CDT next of {:#x} is empty", sl.0);
            }
            if !p.is_null() {
                assert!(p.next(s) == sl, "{what}: CDT prev of {:#x} does not point back", sl.0);
            }
        }
    }

    /// Endpoint and notification queues hold exactly threads blocked on
    /// them; release queues are in ready-time order.
    fn check_queues(&self, what: &str) {
        let s = &self.s;
        let rt = self.root_cnode();
        for &o in &self.objs {
            let (ptr, want) = match Slot::index(rt, o).cap(s) {
                Cap::Endpoint { ptr, .. } => (ptr, [sched::TS_BLOCKED_ON_SEND, sched::TS_BLOCKED_ON_RECV]),
                Cap::Notification { ptr, .. } => (ptr, [sched::TS_BLOCKED_ON_NTFN, sched::TS_BLOCKED_ON_NTFN]),
                _ => continue,
            };
            let state = s.read(ptr + 8) & 3;
            let mut t = s.read(ptr);
            if state == 0 || (want[0] == sched::TS_BLOCKED_ON_NTFN && state != 1) {
                assert_eq!(t, 0, "{what}: idle object {ptr:#x} has a queue");
            }
            let mut prev = 0;
            let mut n = 0;
            while t != 0 {
                let tt = Tcb(t);
                let st = tt.state(s);
                assert!(want.contains(&st), "{what}: thread {t:#x} queued on {ptr:#x} in state {st}");
                assert_eq!(tt.block_obj(s), ptr, "{what}: thread {t:#x} on {ptr:#x}'s queue blocks on another object");
                assert_eq!(tt.ep_prev(s), prev, "{what}: queue of {ptr:#x} badly linked");
                prev = t;
                t = tt.ep_next(s);
                n += 1;
                assert!(n < 10_000, "{what}: queue of {ptr:#x} does not end");
            }
            assert_eq!(s.read(ptr + 8) & !3, prev, "{what}: queue of {ptr:#x} has a wrong tail");
        }
        for c in 0..self.ncores {
            let mut t = node_get(s, c, node::RELEASE_HEAD);
            let mut last = 0;
            let mut n = 0;
            while t != 0 {
                let tt = Tcb(t);
                assert!(sched::in_release_queue(s, tt), "{what}: thread in core {c}'s release queue without its flag");
                let rtime = fl4_core::sporadic::head(s, fl4_core::obj::Sc(tt.sc(s))).time;
                assert!(rtime >= last, "{what}: release queue of core {c} out of order");
                last = rtime;
                t = tt.sched_next(s);
                n += 1;
                assert!(n < 10_000, "{what}: release queue does not end");
            }
        }
    }
}

/// Print every kernel entry (--trace).
static TRACE: AtomicBool = AtomicBool::new(false);

fn cap_kind(c: Cap) -> &'static str {
    match c {
        Cap::Null => "null",
        Cap::Untyped { .. } => "untyped",
        Cap::Endpoint { .. } => "endpoint",
        Cap::Notification { .. } => "notification",
        Cap::Reply { .. } => "reply",
        Cap::CNode { .. } => "cnode",
        Cap::Thread { .. } => "tcb",
        Cap::SchedContext { .. } => "sc",
        Cap::SchedControl { .. } => "schedcontrol",
        Cap::Frame { .. } => "frame",
        _ => "other",
    }
}

fn name_of(s: &SimStore, t: Tcb) -> String {
    let mut out = Vec::new();
    for w in 0..8 {
        let v = s.read(t.name_addr() + w * 8);
        for k in 0..8 {
            let b = (v >> (k * 8)) as u8;
            if b == 0 {
                return String::from_utf8_lossy(&out).into_owned();
            }
            out.push(b);
        }
    }
    String::from_utf8_lossy(&out).into_owned()
}

fn cap_name(c: Cap) -> &'static str {
    match c {
        Cap::Null => "null",
        Cap::CNode { .. } => "cnode",
        _ => "other",
    }
}

impl Sim {
    fn summary(&self) -> String {
        let mut states = [0u32; 8];
        let threads = self.threads();
        for t in &threads {
            states[(t.state(&self.s) & 7) as usize] += 1;
        }
        let cur: Vec<String> = (0..self.ncores)
            .map(|c| {
                let t = Tcb(node_get(&self.s, c, node::CUR_THREAD));
                name_of(&self.s, t)
            })
            .collect();
        let (console, now) = {
            let m = self.a.m.lock().unwrap();
            (m.console.len(), m.now)
        };
        format!(
            "{} objects, {} threads (inactive/running/restart/recv/send/reply/ntfn/idle {:?}), current {:?}, {} console bytes, time {}",
            self.objs.len(),
            threads.len(),
            states,
            cur,
            console,
            now
        )
    }
}

fn run_one(seed: u64, ncores: u64, steps: u64, verbose: bool, concurrent: bool) {
    let mut sim = Sim::new(seed, ncores);
    sim.boot();
    sim.setup();
    if verbose {
        println!("seed {seed} after setup: {}", sim.summary());
        for c in 0..ncores {
            let m = sim.a.m.lock().unwrap();
            println!("  core {c}: pending {:x?} deadline {} ipi-pending {:#x}", m.cores[c as usize].pending, m.cores[c as usize].deadline, node_get(&sim.s, c, node::IPI_PENDING));
        }
        for t in sim.threads() {
            let sc = fl4_core::obj::Sc(t.sc(&sim.s));
            println!(
                "  thread {:#x} {:?} state {} core {} prio {} sc {:#x} active {} release-queued {} queued {}",
                t.0,
                name_of(&sim.s, t),
                t.state(&sim.s),
                t.affinity(&sim.s),
                t.prio(&sim.s),
                sc.0,
                sc.0 != 0 && fl4_core::sporadic::sc_active(&sim.s, sc),
                sched::in_release_queue(&sim.s, t),
                sched::queued(&sim.s, t)
            );
        }
    }
    if concurrent && ncores > 1 {
        // One host thread per core, interleaved at memory accesses.
        let conc = Arc::new(Conc::new(ncores, seed));
        sim.s.conc = Some(conc.clone());
        sim.a.conc = Some(conc.clone());
        let per_core = steps / ncores;
        let threads: Vec<_> = (0..ncores)
            .map(|cpu| {
                let mut core_sim = sim.clone();
                let conc = conc.clone();
                std::thread::spawn(move || {
                    core_sim.on(cpu);
                    conc.start(cpu);
                    for _ in 0..per_core {
                        if core_sim.a.m.lock().unwrap().halted {
                            break;
                        }
                        core_sim.step(cpu);
                        conc.pause(cpu);
                    }
                    // Out of steps, the core still answers remote stalls, as
                    // an idle core would, until every core is out of steps.
                    conc.out_of_steps.fetch_add(1, Ordering::SeqCst);
                    while conc.out_of_steps.load(Ordering::SeqCst) < ncores {
                        SimEnv { s: core_sim.s.clone(), a: core_sim.a.clone(), conc: conc.clone() }.service();
                        conc.relax(cpu);
                    }
                    conc.finish(cpu);
                })
            })
            .collect();
        for t in threads {
            if t.join().is_err() {
                std::process::exit(101);
            }
        }
        sim.s.conc = None;
        sim.a.conc = None;
        sim.after("end");
        if verbose {
            let st = STATS.lock().unwrap();
            println!("seed {seed}: {} transactions committed, {} aborted, {} serial entries", st.0, st.1, st.2);
        }
    } else {
        for _ in 0..steps {
            if sim.a.m.lock().unwrap().halted {
                break;
            }
            let cpu = sim.a.m.lock().unwrap().rng.below(ncores);
            sim.step(cpu);
        }
    }
    if verbose {
        println!("seed {seed} at the end: {}", sim.summary());
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let opt = |name: &str, def: u64| -> u64 {
        args.iter().position(|a| a == name).and_then(|i| args.get(i + 1)).and_then(|v| v.parse().ok()).unwrap_or(def)
    };
    let cores = opt("--cores", 4);
    let steps = opt("--steps", 2000);
    let verbose = args.iter().any(|a| a == "--verbose");
    // The kernel crates build with panic = abort, so each seed runs in a
    // child process; a failed oracle aborts only that child.
    if let Some(i) = args.iter().position(|a| a == "--one") {
        let seed = args[i + 1].parse().unwrap();
        TRACE.store(args.iter().any(|a| a == "--trace"), Ordering::Relaxed);
        run_one(seed, cores, steps, verbose, args.iter().any(|a| a == "--conc"));
        return;
    }
    let seeds = opt("--seeds", 100);
    let first = opt("--first", 1);
    let timeout = opt("--timeout", 120);
    let me = std::env::current_exe().unwrap();
    let mut failed = 0;
    for seed in first..first + seeds {
        let mut out = std::process::Command::new(&me)
            .args(["--one", &seed.to_string(), "--cores", &cores.to_string(), "--steps", &steps.to_string()])
            .args(if verbose { vec!["--verbose"] } else { vec![] })
            .args(if args.iter().any(|a| a == "--conc") { vec!["--conc"] } else { vec![] })
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        // A run that never ends is a hang (deadlock or livelock) and fails.
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(timeout);
        let hung = loop {
            if out.try_wait().unwrap().is_some() {
                break false;
            }
            if std::time::Instant::now() > deadline {
                let _ = out.kill();
                break true;
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        };
        let out = out.wait_with_output().unwrap();
        if verbose {
            print!("{}", String::from_utf8_lossy(&out.stdout));
        }
        if hung || !out.status.success() {
            failed += 1;
            let err = String::from_utf8_lossy(&out.stderr);
            let why = if hung {
                format!("no progress after {timeout} s")
            } else {
                err.lines().find(|l| !l.is_empty() && !l.starts_with("thread") && !l.starts_with("note:")).unwrap_or("").to_string()
            };
            println!("fl4-sim: seed {seed} ({cores} cores) failed: {why}");
        }
    }
    println!("fl4-sim: {seeds} seeds, {cores} cores, {steps} steps each: {failed} failed");
    if failed > 0 {
        std::process::exit(1);
    }
}
