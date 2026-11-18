//! Kernel entry and exit: entry.S has saved the user registers into the
//! current TCB; dispatch to fl4-core, then run whichever thread is current.
use crate::kprintln;
use fl4_arch_aarch64::arch::{self, PhysArch};
use fl4_arch_aarch64::{fpu, gic, mmu, percpu, smp, timer};
use fl4_core::layout::{irq, node, reg, tcb as tl};
use fl4_core::machine::Store;
use fl4_core::obj::{node_get, Tcb};
use fl4_core::{sched, syscall};
use fl4_store::{Phys, PhysStore};
use fl4_sync::SerialGate;

core::arch::global_asm!(include_str!("entry.S"));

extern "C" {
    fn fl4_restore_user(regs: u64) -> !;
    fn fl4_idle(stack_top: u64) -> !;
}

const KIND_SYNC: u64 = 0;
const KIND_IRQ: u64 = 1;

/// ESR_EL1 exception classes from EL0.
const EC_UNKNOWN: u64 = 0x00;
const EC_FP: u64 = 0x07;
const EC_SVC64: u64 = 0x15;
const EC_IABT_LOW: u64 = 0x20;
const EC_DABT_LOW: u64 = 0x24;

static mut KS_BASE: u64 = 0;

/// The serial gate (DESIGN.md §7).
pub static GATE: SerialGate = SerialGate::new();

pub fn set_ks_base(b: u64) {
    unsafe { KS_BASE = b };
}

pub fn store() -> PhysStore {
    PhysStore { frame_masks: (0, 0), ks_base: unsafe { KS_BASE }, cpu: percpu::cpu_index() as u64, tx: false }
}

fn service_remote() -> bool {
    smp::service(|| {
        let mut s = store();
        let mut a = PhysArch;
        fl4_core::smp::stall(&mut s, &mut a);
    })
}

/// Take the serial gate (on a multi-core system), servicing remote calls
/// while waiting. Returns false when a stall cancelled the entry.
pub fn lock() -> bool {
    let stalled = core::cell::Cell::new(false);
    if smp::multi() {
        GATE.acquire(&Phys, percpu::cpu_index() as u64, || {
            if service_remote() {
                stalled.set(true);
            }
        });
        percpu::get().gate_held = true;
    }
    !stalled.get()
}

fn unlock() {
    let pc = percpu::get();
    if pc.gate_held {
        pc.gate_held = false;
        GATE.release(&Phys);
    }
}

struct KernelEnv;

impl fl4_sync::EntryEnv for KernelEnv {
    type S = PhysStore;
    type A = PhysArch;
    type M = Phys;
    fn cpu(&self) -> u64 {
        percpu::cpu_index() as u64
    }
    fn multi(&self) -> bool {
        smp::multi()
    }
    fn store(&self, tx: bool) -> PhysStore {
        PhysStore { frame_masks: (0, 0), ks_base: unsafe { KS_BASE }, cpu: self.cpu(), tx }
    }
    fn arch(&self) -> PhysArch {
        PhysArch
    }
    fn mem(&self) -> &Phys {
        &Phys
    }
    fn service_remote(&self) -> bool {
        service_remote()
    }
    fn set_tx(&self, on: bool) {
        let pc = percpu::get();
        pc.tx = on;
        if on {
            pc.held_used = false;
        }
    }
    fn finish_effects(&self, committed: bool) {
        if committed {
            arch::apply_effects();
        } else {
            arch::discard_effects();
        }
    }
    fn entry_done(&self) {
        let pc = percpu::get();
        if pc.held_used {
            pc.held_irq = percpu::NO_IRQ;
        }
        pc.held_used = false;
    }
    fn unhandled_irq(&self) -> Option<u64> {
        let pc = percpu::get();
        let v = core::mem::replace(&mut pc.held_irq, percpu::NO_IRQ);
        pc.held_used = false;
        (v != percpu::NO_IRQ).then_some(v)
    }
    fn holding_gate(&self) {
        let pc = percpu::get();
        pc.gate_held = true;
        pc.held_used = false;
    }
    fn count(&self, what: fl4_sync::Count) {
        if !fl4_abi::config::DEBUG_BUILD {
            return;
        }
        use core::sync::atomic::Ordering::Relaxed;
        match what {
            fl4_sync::Count::Commit => {
                let c = smp::TX_COMMITS.fetch_add(1, Relaxed);
                if c & 0x3ffff == 0x3ffff {
                    arch::print_stats();
                }
            }
            fl4_sync::Count::Abort => {
                smp::TX_ABORTS.fetch_add(1, Relaxed);
            }
            fl4_sync::Count::Serial => {
                smp::SERIAL_ENTRIES.fetch_add(1, Relaxed);
            }
        }
    }
}

fn run_entry(irq: bool, body: impl FnMut(&mut PhysStore, &mut PhysArch)) -> bool {
    fl4_sync::run_entry(&KernelEnv, &GATE, irq, body)
}

fn cur_regs() -> u64 {
    let s = store();
    sched::cur_thread(&s).0 + tl::REGS
}

/// Back to the interrupted thread without a kernel entry.
fn resume() -> ! {
    mmu::publish_tables();
    unsafe { fl4_restore_user(cur_regs()) }
}

/// Acknowledge an interrupt; returns its IRQ and whether it needs a
/// kernel entry at all.
fn take_irq() -> Option<u64> {
    let raw = gic::ack();
    let id = raw & 0x3ff;
    if raw == gic::SPURIOUS || id >= 1020 {
        return None;
    }
    percpu::get().iar = raw;
    if id == irq::TIMER_ID {
        // A stale timer interrupt (l4h 0012): the deadline it was for has
        // been replaced by a later one.
        if timer::early() {
            gic::eoi(raw);
            return None;
        }
        timer::quiesce();
    }
    if id == irq::REMOTE_CALL_ID {
        service_remote();
    }
    Some(irq::of(id, percpu::cpu_index() as u64))
}

/// Called by entry.S for every exception from EL0.
#[no_mangle]
extern "C" fn fl4_entry(kind: u64, esr: u64, far: u64) -> ! {
    let s = &mut store();
    let t = sched::cur_thread(s);
    let elr = t.reg(s, reg::ELR_EL1);
    let ec = esr >> 26;
    if kind == KIND_IRQ {
        let irq = match take_irq() {
            Some(i) => i,
            None => resume(),
        };
        t.set_reg(s, reg::FAULT_IP, elr);
        run_entry(true, |s, a| {
            if s.tx {
                syscall::handle_interrupt_entry(&mut s.specialize::<true>(), a, irq)
            } else {
                syscall::handle_interrupt_entry(&mut s.specialize::<false>(), a, irq)
            }
        });
        exit()
    }
    if kind != KIND_SYNC {
        // An SError from user code: asynchronous, so there is no faulting
        // instruction to blame. Report it as a user exception.
        t.set_reg(s, reg::FAULT_IP, elr);
        run_entry(false, |s, a| syscall::handle_user_exception(s, a, esr, 0));
        exit()
    }
    // FP/SIMD trap: lazy switching (fpu.rs). A thread with FP/SIMD
    // disabled gets the fault instead.
    if ec == EC_FP {
        if t.flags(s) & fl4_abi::consts::tcb_flag::FPU_DISABLED == 0 {
            fpu::lazy_load(t.0);
            resume()
        }
    }
    // A syscall restarts at the SVC, for when a remote stall cancels the
    // entry before handle_syscall runs.
    t.set_reg(s, reg::FAULT_IP, if ec == EC_SVC64 { elr.wrapping_sub(4) } else { elr });
    trace(kind, esr, elr, t.0, s);
    let number = t.reg(s, reg::SYSCALL) as i64;
    run_entry(false, |s, a| {
        if s.tx {
            dispatch(&mut s.specialize::<true>(), a, ec, esr, far, elr, number)
        } else {
            dispatch(&mut s.specialize::<false>(), a, ec, esr, far, elr, number)
        }
    });
    exit()
}

#[inline(always)]
fn dispatch<S: Store>(s: &mut S, a: &mut PhysArch, ec: u64, esr: u64, far: u64, elr: u64, number: i64) {
    match ec {
        EC_SVC64 => syscall::handle_syscall(s, a, number),
        EC_DABT_LOW => syscall::handle_vm_fault(s, a, far, esr),
        EC_IABT_LOW => syscall::handle_vm_fault(s, a, elr, esr),
        _ => {
            let _ = EC_UNKNOWN;
            syscall::handle_user_exception(s, a, esr, 0)
        }
    }
}

/// An interrupt while this core idled.
#[no_mangle]
extern "C" fn fl4_kernel_irq() -> ! {
    percpu::get().idle = false;
    if let Some(irq) = take_irq() {
        run_entry(true, |s, a| syscall::handle_interrupt_entry(s, a, irq));
    }
    exit()
}

/// A synchronous exception or SError in the kernel: a bug.
#[no_mangle]
extern "C" fn fl4_kernel_fault(esr: u64, far: u64, elr: u64, sp: u64) -> ! {
    panic!("kernel exception: esr {:#x} far {:#x} elr {:#x} sp {:#x}", esr, far, elr, sp)
}

/// Leave the kernel to the current thread (or the idle loop), giving up
/// the serial gate.
pub fn exit() -> ! {
    let s = &mut store().specialize::<false>();
    let ct = sched::cur_thread(s);
    let core = s.cur_cpu();
    let idle = ct.0 == node_get(s, core, node::IDLE_THREAD);
    // The ASID this core ran was invalidated by another core: if it was
    // deleted, run the current thread on what its VSpace cap now names
    // (the empty table, where it faults), not on the deleted tables.
    let pc = percpu::get();
    if pc.vspace_stale {
        pc.vspace_stale = false;
        let mut a = PhysArch;
        if idle {
            fl4_core::vspace::set_kernel_vm_root(s, &mut a);
        } else {
            fl4_core::vspace::set_vm_root(s, &mut a, ct);
        }
    }
    unlock();
    if idle {
        percpu::get().idle = true;
        unsafe { fl4_idle(percpu::get().stack_top) }
    }
    fpu::switch_to(ct.0, ct.flags(s) & fl4_abi::consts::tcb_flag::FPU_DISABLED != 0);
    mmu::publish_tables();
    unsafe { fl4_restore_user(ct.0 + tl::REGS) }
}

const TRACE_N: usize = 4096;
static mut TRACE: [[u64; 6]; TRACE_N] = [[0; 6]; TRACE_N];
static mut TRACE_I: usize = 0;

fn trace(kind: u64, esr: u64, elr: u64, tcb: u64, s: &PhysStore) {
    if !fl4_abi::config::DEBUG_BUILD {
        return;
    }
    let t = Tcb(tcb);
    let e = [kind, esr, elr, t.reg(s, reg::X7), t.reg(s, reg::X0), tcb];
    unsafe {
        let i = TRACE_I;
        if i >= 2 && (TRACE[(i - 1) % TRACE_N] == e || TRACE[(i - 2) % TRACE_N] == e) {
            return;
        }
        TRACE[i % TRACE_N] = e;
        TRACE_I = i + 1;
    }
}

pub fn dump_trace() {
    unsafe {
        let n = TRACE_I;
        for i in n.saturating_sub(32)..n {
            let t = TRACE[i % TRACE_N];
            kprintln!("  #{} kind {} esr {:#x} pc {:#x} x7 {} x0 {:#x} tcb {:#x}", i, t[0], t[1], t[2], t[3] as i64, t[4], t[5]);
        }
    }
}
