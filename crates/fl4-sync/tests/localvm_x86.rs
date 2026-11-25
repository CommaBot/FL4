//! The x86 local paths of hardware virtualization (`fl4_sync::localvm`):
//! refinement (from the same state, a local path that runs ends where the
//! general path does, word for word, with the same `Arch` effects), decline
//! (one that declines has written only `FAULT_IP` and the clock, and the
//! general path from there ends as from the start), and locks (an object
//! another core holds makes the local path give up having written nothing).
#![cfg(not(feature = "aarch64"))]

use fl4_abi::label;
use fl4_abi::syscall as sc;
use fl4_core::capability::Cap;
use fl4_core::layout::{ks, node, reg, tcb as tl};
use fl4_core::machine::{Arch, Store};
use fl4_core::msginfo::MessageInfo;
use fl4_core::obj::{ks_set, node_get, node_set, Ntfn, Sc, Slot, Tcb, NTFN_ACTIVE, NTFN_IDLE};
use fl4_core::vcpu::vmx::*;
use fl4_core::{interrupt, msg, sched, sporadic, syscall, vcpu};
use fl4_store::lock::{self, Mem};
use std::collections::HashMap;
use std::sync::Mutex;

/// The lock table is the process's: tests run one at a time.
static SERIAL: Mutex<()> = Mutex::new(());

struct Atomics;
impl Mem for Atomics {}

#[derive(Clone, Default)]
struct Memory {
    m: HashMap<u64, u64>,
    cpu: u64,
}
impl Store for Memory {
    fn read(&self, a: u64) -> u64 {
        *self.m.get(&a).unwrap_or(&0)
    }
    fn write(&mut self, a: u64, v: u64) {
        self.m.insert(a, v);
    }
    fn zero(&mut self, a: u64, len: u64) {
        for i in (0..len).step_by(8) {
            self.write(a + i, 0);
        }
    }
    fn clear_free(&mut self, a: u64, len: u64) {
        self.zero(a, len)
    }
    fn ks_base(&self) -> u64 {
        KS_BASE
    }
    fn cur_cpu(&self) -> u64 {
        self.cpu
    }
}
impl Memory {
    /// The nonzero words: a word written 0 equals one never written.
    fn words(&self) -> HashMap<u64, u64> {
        self.m.iter().filter(|(_, v)| **v != 0).map(|(k, v)| (*k, *v)).collect()
    }
    /// The words that differ from `other`'s.
    fn diff(&self, other: &Memory) -> Vec<u64> {
        let (a, b) = (self.words(), other.words());
        let mut d: Vec<u64> = a.keys().chain(b.keys()).filter(|k| a.get(k) != b.get(k)).copied().collect();
        d.sort();
        d.dedup();
        d
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Ev {
    Deadline(u64),
    Ack(u64),
    Mask(u64, bool),
    Vspace(u64, u64),
    Reschedule(u64),
    Stall(u64),
}

#[derive(Clone)]
struct Machine {
    time: u64,
    ev: Vec<Ev>,
}
impl Arch for Machine {
    fn virtualization(&self) -> u64 {
        1
    }
    fn vcpu_capability(&self, f: u64) -> u64 {
        match f {
            0 => 7,
            1 => 48,
            0x486 => 0x20,
            0x488 => 1 << 13,
            0x487 | 0x489 => u32::MAX as u64,
            _ => (u32::MAX as u64) << 32,
        }
    }
    fn now(&mut self) -> u64 {
        self.time
    }
    fn set_deadline(&mut self, t: u64) {
        self.ev.push(Ev::Deadline(t));
    }
    fn us_to_ticks(&self, x: u64) -> u64 {
        x
    }
    fn ticks_to_us(&self, x: u64) -> u64 {
        x
    }
    fn max_us(&self) -> u64 {
        u64::MAX
    }
    fn kernel_wcet_ticks(&self) -> u64 {
        1
    }
    fn irq_pending(&mut self) -> bool {
        false
    }
    fn take_pending_irq(&mut self) -> u64 {
        u64::MAX
    }
    fn mask_irq(&mut self, irq: u64, m: bool) {
        self.ev.push(Ev::Mask(irq, m));
    }
    fn ack_irq(&mut self, irq: u64) {
        self.ev.push(Ev::Ack(irq));
    }
    fn set_vspace(&mut self, r: u64, asid: u64) {
        self.ev.push(Ev::Vspace(r, asid));
    }
    fn invalidate_page(&mut self, _: u64, _: u64) {}
    fn invalidate_asid(&mut self, _: u64) {}
    fn invalidate_page_structures(&mut self, _: u64) {}
    fn ioapic_map(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64) -> bool {
        false
    }
    fn ioapic_map_remapped(&mut self, _: u64, _: u64, _: u64, _: u64, _: u64, _: u64) -> bool {
        false
    }
    fn num_ioapics(&self) -> u64 {
        0
    }
    fn ioapic_pins(&self, _: u64) -> u64 {
        0
    }
    fn port_in(&mut self, _: u64, _: u64) -> u64 {
        0
    }
    fn port_out(&mut self, _: u64, _: u64, _: u64) {}
    fn fpu_flush(&mut self, _: u64) {}
    fn fpu_sanitise(&mut self, _: u64) {}
    fn fpu_reload(&mut self, _: u64) {}
    fn fpu_release(&mut self, _: u64) {}
    fn remote_stall(&mut self, c: u64) {
        self.ev.push(Ev::Stall(c));
    }
    fn send_reschedule(&mut self, m: u64) {
        self.ev.push(Ev::Reschedule(m));
    }
    fn putc(&mut self, _: u64) {}
    fn get_char(&mut self) -> u64 {
        0
    }
    fn halt(&mut self) {}
}

const KS_BASE: u64 = 0x1000_0000;
/// The core the tests run on (not 0, to catch a hard-coded core).
const CPU: u64 = 1;
const IDLE: Tcb = Tcb(0x40_0000);
const IDLE_SC: Sc = Sc(0x41_0000);
const CT: Tcb = Tcb(0x20_0000);
const CSC: Sc = Sc(0x21_0000);
const W: Tcb = Tcb(0x22_0000);
const WSC: Sc = Sc(0x23_0000);
const V: u64 = 0x80_0000;
const N: u64 = 0x90_0000;
const N2: u64 = 0x91_0000;
const ROOT_CNODE: u64 = 0xa0_0000;
const OTHER_V: u64 = 0xb0_0000;
const EPT_ROOT: u64 = 0xc0_0000;
const POOL: u64 = 0xc1_0000;
const ASID: u64 = 0x201;
/// The VCPU's cap in the root CNode, and another thread's VCPU.
const VCPU_CPTR: u64 = 3;
const OTHER_VCPU_CPTR: u64 = 4;
const TIMER_IRQ: u64 = 0x20;
const NOW: u64 = 1_000_000;
const BUDGET: u64 = 5_000;

fn sc_setup(s: &mut Memory, t: Tcb, sc: Sc, budget: u64, period: u64) {
    t.set_sc(s, sc.0);
    sc.set_tcb(s, t.0);
    sc.set_cpu(s, CPU);
    sporadic::refill_new(s, sc, 4, budget, period);
}

/// Core `CPU` at `NOW`, running `CT` (its own SC, budget left, prio 100)
/// with bound VCPU `V` (VMX) and bound notification `N`, idle; a CSpace
/// whose slot 3 holds `V`'s cap and slot 4 another thread's VCPU's.
fn fixture() -> (Memory, Machine) {
    let mut s = Memory { m: HashMap::new(), cpu: CPU };
    let a = Machine { time: NOW, ev: Vec::new() };
    node_set(&mut s, CPU, node::CUR_TIME, NOW - 100);
    ks_set(&mut s, ks::DOMAIN_TIME, 1);
    sc_setup(&mut s, IDLE, IDLE_SC, 1 << 40, 0);
    node_set(&mut s, CPU, node::IDLE_THREAD, IDLE.0);
    node_set(&mut s, CPU, node::IDLE_SC, IDLE_SC.0);
    IDLE.set_affinity(&mut s, CPU);
    for (t, sc) in [(CT, CSC), (W, WSC)] {
        t.set_affinity(&mut s, CPU);
        t.set_prio(&mut s, 100);
        sc_setup(&mut s, t, sc, BUDGET, 10 * BUDGET);
    }
    CT.set_state(&mut s, sched::TS_RUNNING);
    node_set(&mut s, CPU, node::CUR_THREAD, CT.0);
    node_set(&mut s, CPU, node::CUR_SC, CSC.0);
    node_set(&mut s, CPU, node::ARMED, NOW + BUDGET);
    vcpu::init(&mut s, &a, V);
    vcpu::init(&mut s, &a, OTHER_V);
    vcpu::set(&mut s, V, vcpu::TCB, CT.0);
    s.write(CT.0 + tl::VCPU, V);
    vcpu::set(&mut s, OTHER_V, vcpu::TCB, W.0);
    s.write(W.0 + tl::VCPU, OTHER_V);
    CT.set_bound_ntfn(&mut s, N);
    Ntfn(N).set_bound_tcb(&mut s, CT.0);
    Ntfn(N).set_state(&mut s, NTFN_IDLE);
    CT.slot(tl::SLOT_CTABLE).set_cap(&mut s, Cap::CNode { ptr: ROOT_CNODE, radix: 4, guard_size: 60, guard: 0 });
    Slot::index(ROOT_CNODE, VCPU_CPTR).set_cap(&mut s, Cap::Vcpu { ptr: V });
    Slot::index(ROOT_CNODE, OTHER_VCPU_CPTR).set_cap(&mut s, Cap::Vcpu { ptr: OTHER_V });
    CT.set_reg(&mut s, reg::NEXT_IP, 0x4002);
    (s, a)
}

/// `CT` in `TS_RUNNING_VM` after a `SysVMEnter`.
fn running_vm(s: &mut Memory) {
    CT.set_state(s, sched::TS_RUNNING_VM);
}

/// A VMX exit `vm::run` saved: a guest exit (pending) or a host one.
fn exited(s: &mut Memory, pending: bool) {
    running_vm(s);
    vcpu::set(s, V, vcpu::PENDING, pending as u64);
    vcpu::set(s, V, vcpu::VALID, 1);
    for i in 0..30 {
        vcpu::set(s, V, vcpu::EXIT + i * 8, 0x100 + i);
    }
}

fn syscall_regs(s: &mut Memory, lbl: u64, length: u64, cptr: u64, args: &[u64]) {
    CT.set_reg(s, reg::MSG_INFO, MessageInfo::new(lbl, 0, 0, length).to_word());
    CT.set_reg(s, reg::CAP, cptr);
    for (i, &x) in args.iter().enumerate() {
        CT.set_reg(s, msg::msg_register(i as u64), x);
    }
}

/// Run `local` and `general` from the same state; both must end alike.
fn refines(
    s: &Memory,
    a: &Machine,
    local: impl FnOnce(&mut Memory, &mut Machine) -> bool,
    general: impl FnOnce(&mut Memory, &mut Machine),
) -> (Memory, Machine) {
    let (mut ls, mut la) = (s.clone(), a.clone());
    let (mut gs, mut ga) = (s.clone(), a.clone());
    assert!(local(&mut ls, &mut la), "the local path declined");
    general(&mut gs, &mut ga);
    assert_eq!(ls.diff(&gs), Vec::<u64>::new(), "words the local and general paths left differently");
    assert_eq!(la.ev, ga.ev, "Arch effects");
    (ls, la)
}

/// `local` declines: only `allowed` words changed (the restart point and
/// the clock), and the general path from there ends as from `s`.
fn declines(
    s: &Memory,
    a: &Machine,
    local: impl FnOnce(&mut Memory, &mut Machine) -> bool,
    general: impl Fn(&mut Memory, &mut Machine),
) {
    let (mut ls, mut la) = (s.clone(), a.clone());
    assert!(!local(&mut ls, &mut la), "the local path ran");
    let allowed = [
        CT.0 + tl::REGS + reg::FAULT_IP * 8,
        fl4_core::obj::node_base(s, CPU) + node::CUR_TIME,
        fl4_core::obj::node_base(s, CPU) + node::CONSUMED,
    ];
    for w in ls.diff(s) {
        assert!(allowed.contains(&w), "a declined local path wrote {w:#x}");
    }
    assert!(la.ev.is_empty(), "a declined local path made Arch calls: {:?}", la.ev);
    let (mut gs, mut ga) = (s.clone(), a.clone());
    general(&mut gs, &mut ga);
    general(&mut ls, &mut la);
    assert_eq!(ls.diff(&gs), Vec::<u64>::new());
    assert_eq!(la.ev, ga.ev);
}

fn vm_enter_local(s: &mut Memory, a: &mut Machine) -> bool {
    fl4_sync::local_syscall(s, a, &Atomics, sc::SysVMEnter, |_, _| {})
}
fn vm_enter_general(s: &mut Memory, a: &mut Machine) {
    syscall::handle_syscall(s, a, sc::SysVMEnter)
}

#[test]
fn vm_enter_beside_the_gate_refines_handle_syscall() {
    let _g = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let (mut s, a) = fixture();
    CT.set_reg(&mut s, msg::msg_register(0), 0xfff0);
    CT.set_reg(&mut s, msg::msg_register(1), vcpu::PRIMARY_FORCED);
    CT.set_reg(&mut s, msg::msg_register(2), 0);
    let (ls, _) = refines(&s, &a, vm_enter_local, vm_enter_general);
    assert_eq!(CT.state(&ls), sched::TS_RUNNING_VM);
    assert_eq!(vcpu::read_vmcs(&ls, V, GUEST_RIP), 0xfff0);
    // Without a bound notification; with a round-robin SC; with the
    // reprogram flag set.
    let mut s2 = s.clone();
    CT.set_bound_ntfn(&mut s2, 0);
    refines(&s2, &a, vm_enter_local, vm_enter_general);
    let mut s3 = s.clone();
    sporadic::refill_new(&mut s3, CSC, 4, BUDGET, 0);
    node_set(&mut s3, CPU, node::REPROGRAM, 1);
    refines(&s3, &a, vm_enter_local, vm_enter_general);
}

#[test]
fn vm_enter_declines_where_the_general_path_does_more() {
    let _g = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let (s, a) = fixture();
    let cases: Vec<(&str, Box<dyn Fn(&mut Memory)>)> = vec![
        ("an active notification completes the call", Box::new(|s| Ntfn(N).set_state(s, NTFN_ACTIVE))),
        ("the budget is spent", Box::new(|s| node_set(s, CPU, node::CONSUMED, BUDGET))),
        ("a reschedule is pending", Box::new(|s| sched::set_action(s, sched::ACTION_CHOOSE_NEW))),
        ("a reschedule IPI is owed", Box::new(|s| node_set(s, CPU, node::IPI_PENDING, 1))),
        ("a timer is due", Box::new(|s| {
            s.cpu = CPU;
            fl4_core::timer::insert(s, W, NOW - 1, 7)
        })),
        ("a thread is released", Box::new(|s| {
            W.set_state(s, sched::TS_RUNNING);
            sched::release_enqueue(s, W);
        })),
        ("a yield to complete", Box::new(|s| CT.set_yield_to(s, WSC.0))),
    ];
    for (why, change) in cases {
        let mut s2 = s.clone();
        change(&mut s2);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| declines(&s2, &a, vm_enter_local, vm_enter_general)));
        assert!(r.is_ok(), "{why}");
    }
    // Not a VMEnter of a thread with a VCPU, or one that traps syscalls:
    // no local path at all, nothing written.
    for change in [
        Box::new(|s: &mut Memory| s.write(CT.0 + tl::VCPU, 0)) as Box<dyn Fn(&mut Memory)>,
        Box::new(|s: &mut Memory| CT.set_flags(s, fl4_abi::consts::tcb_flag::TRAP_SYSCALLS)),
    ] {
        let mut s2 = s.clone();
        change(&mut s2);
        let mut ls = s2.clone();
        assert!(!vm_enter_local(&mut ls, &mut a.clone()));
        assert!(ls.diff(&s2).is_empty());
    }
}

#[test]
fn a_held_vcpu_or_notification_leaves_vm_enter_to_the_gate_untouched() {
    let _g = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let (s, a) = fixture();
    for held_obj in [V, N] {
        let mut other = lock::Held::new();
        assert!(lock::try_lock_object(&Atomics, held_obj, &mut other));
        let mut ls = s.clone();
        assert!(!vm_enter_local(&mut ls, &mut a.clone()));
        assert!(ls.diff(&s).is_empty(), "wrote with {held_obj:#x} held elsewhere");
        lock::unlock_held(&Atomics, &mut other);
    }
    // Released: it runs, and leaves no lock behind.
    let mut ls = s.clone();
    assert!(vm_enter_local(&mut ls, &mut a.clone()));
    let mut h = lock::Held::new();
    assert!(lock::try_lock_object(&Atomics, V, &mut h) && lock::try_lock_object(&Atomics, N, &mut h));
    lock::unlock_held(&Atomics, &mut h);
}

fn vm_exit_local(irq: u64) -> impl Fn(&mut Memory, &mut Machine) -> bool {
    move |s, a| fl4_sync::local_vm_exit(s, a, &Atomics, irq, |_, _| {})
}
fn vm_exit_general(irq: u64) -> impl Fn(&mut Memory, &mut Machine) {
    move |s, a| syscall::handle_vcpu_exit(s, a, irq, false)
}

#[test]
fn a_guest_exit_beside_the_gate_refines_handle_vcpu_exit() {
    let _g = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let (mut s, a) = fixture();
    exited(&mut s, true);
    let no = syscall::NO_IRQ;
    let (ls, _) = refines(&s, &a, vm_exit_local(no), vm_exit_general(no));
    assert_eq!(CT.state(&ls), sched::TS_RUNNING);
    assert_eq!(CT.reg(&ls, reg::MSG_INFO), 1);
    assert_eq!(vcpu::get(&ls, V, vcpu::PENDING), 0);
    // A pending exit is reported even with a signal on the notification
    // (the exit comes first; the signal waits).
    let mut s2 = s.clone();
    Ntfn(N).set_state(&mut s2, NTFN_ACTIVE);
    refines(&s2, &a, vm_exit_local(no), vm_exit_general(no));
    // A host exit with nothing for the monitor: the guest goes on.
    let mut s3 = s.clone();
    vcpu::set(&mut s3, V, vcpu::PENDING, 0);
    let (ls, _) = refines(&s3, &a, vm_exit_local(no), vm_exit_general(no));
    assert_eq!(CT.state(&ls), sched::TS_RUNNING_VM);
    // ... unless a signal waits: the gate reports it.
    Ntfn(N).set_state(&mut s3, NTFN_ACTIVE);
    declines(&s3, &a, vm_exit_local(no), vm_exit_general(no));
    // Budget spent, a timer due: the gate.
    let mut s4 = s.clone();
    node_set(&mut s4, CPU, node::CONSUMED, BUDGET);
    declines(&s4, &a, vm_exit_local(no), vm_exit_general(no));
    let mut s5 = s.clone();
    fl4_core::timer::insert(&mut s5, W, NOW - 1, 7);
    declines(&s5, &a, vm_exit_local(no), vm_exit_general(no));
}

/// The kernel timer interrupt as a VM exit: nothing due (a timer
/// interrupt for a deadline already dealt with), a round-robin budget
/// expiry that keeps the guest, and a due timer of another thread of this
/// core, which signals its bound notification.
#[test]
fn the_timer_exit_beside_the_gate_refines_handle_vcpu_exit() {
    let _g = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let (mut s, a) = fixture();
    exited(&mut s, false);
    ks_set(&mut s, ks::IRQ_STATE + TIMER_IRQ * 8, interrupt::IRQ_TIMER);
    let (ls, la) = refines(&s, &a, vm_exit_local(TIMER_IRQ), vm_exit_general(TIMER_IRQ));
    assert!(la.ev.contains(&Ev::Ack(TIMER_IRQ)));
    assert_eq!(CT.state(&ls), sched::TS_RUNNING_VM);
    // Round robin, spent: refilled, and the guest goes on.
    let mut rr = s.clone();
    sporadic::refill_new(&mut rr, CSC, 4, BUDGET, 0);
    node_set(&mut rr, CPU, node::CONSUMED, BUDGET);
    let (ls, _) = refines(&rr, &a, vm_exit_local(TIMER_IRQ), vm_exit_general(TIMER_IRQ));
    assert!(sched::cur_thread(&ls) == CT);
    // A sporadic SC spent: the gate (the general path postpones it).
    let mut sp = s.clone();
    node_set(&mut sp, CPU, node::CONSUMED, BUDGET);
    declines(&sp, &a, vm_exit_local(TIMER_IRQ), vm_exit_general(TIMER_IRQ));
    // W's timer is due; its bound notification N2 becomes active.
    let mut due = s.clone();
    W.set_bound_ntfn(&mut due, N2);
    Ntfn(N2).set_bound_tcb(&mut due, W.0);
    Ntfn(N2).set_state(&mut due, NTFN_IDLE);
    fl4_core::timer::insert(&mut due, W, NOW - 1, 7);
    let (ls, _) = refines(&due, &a, vm_exit_local(TIMER_IRQ), vm_exit_general(TIMER_IRQ));
    assert_eq!(Ntfn(N2).state(&ls), NTFN_ACTIVE);
    // A signal for the guest's own notification: the gate.
    let mut sig = s.clone();
    Ntfn(N).set_state(&mut sig, NTFN_ACTIVE);
    declines(&sig, &a, vm_exit_local(TIMER_IRQ), vm_exit_general(TIMER_IRQ));
    // Another core holds N2: nothing written.
    let mut other = lock::Held::new();
    assert!(lock::try_lock_object(&Atomics, N2, &mut other));
    let mut ls = due.clone();
    assert!(!vm_exit_local(TIMER_IRQ)(&mut ls, &mut a.clone()));
    assert!(ls.diff(&due).is_empty());
    lock::unlock_held(&Atomics, &mut other);
}

/// The VCPU state invocations of the VCPU's own thread, `SysCall` and
/// `SysSend`, each against `handle_syscall`, refused ones included.
#[test]
fn vcpu_state_invocations_beside_the_gate_refine_handle_syscall() {
    let _g = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let (s, a) = fixture();
    let regs: Vec<u64> = (0..15).map(|i| 0x1000 + i).collect();
    let cases: Vec<(u64, u64, Vec<u64>)> = vec![
        (label::X86VCPUWriteRegisters, 4, regs[..4].to_vec()),
        (label::X86VCPUFlushTLB, 0, vec![]),
        (label::X86VCPUReadVMCS, 1, vec![GUEST_CR3]),
        (label::X86VCPUReadVMCS, 1, vec![HOST_RIP]),           // Refused.
        (label::X86VCPUWriteVMCS, 2, vec![GUEST_CR3, 0x5000]),
        (label::X86VCPUWriteVMCS, 2, vec![GUEST_ACTIVITY, 7]),  // Refused.
        (label::X86VCPUWriteVMCS, 2, vec![CONTROL_SECONDARY_PROCESSOR_CONTROLS, u64::MAX]),
        (label::X86VCPUReadVMCB, 2, vec![0x400, 2]),            // VMX: illegal.
        (label::X86VCPUWriteVMCB, 2, vec![0x400, 2]),
        (label::X86VCPUReadMSR, 1, vec![0xc000_0082]),
        (label::X86VCPUWriteMSR, 2, vec![0xc000_0082, 0x1234]),
        (label::X86VCPUWriteMSR, 2, vec![0xc000_0082, 1 << 63]), // Not canonical.
        (label::X86VCPUReadMSR, 1, vec![0x485]),
    ];
    for number in [sc::SysCall, sc::SysSend] {
        for (lbl, len, args) in &cases {
            let mut s2 = s.clone();
            vcpu::set(&mut s2, V, vcpu::SVM_CPU, CPU + 1);
            syscall_regs(&mut s2, *lbl, *len, VCPU_CPTR, args);
            let local = |s: &mut Memory, a: &mut Machine| fl4_sync::local_syscall(s, a, &Atomics, number, |_, _| {});
            let general = |s: &mut Memory, a: &mut Machine| syscall::handle_syscall(s, a, number);
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| refines(&s2, &a, local, general)));
            assert!(r.is_ok(), "label {lbl}, args {args:x?}, syscall {number}");
        }
    }
    // A FlushTLB went through: the VPID is revoked.
    let mut s2 = s.clone();
    vcpu::set(&mut s2, V, vcpu::SVM_CPU, CPU + 1);
    syscall_regs(&mut s2, label::X86VCPUFlushTLB, 0, VCPU_CPTR, &[]);
    assert!(fl4_sync::local_syscall(&mut s2, &mut a.clone(), &Atomics, sc::SysCall, |_, _| {}));
    assert_eq!(vcpu::get(&s2, V, vcpu::SVM_CPU), 0);
}

/// Another thread's VCPU (whose invocation stalls that thread), a VCPU
/// invocation with extra caps, a lookup that fails, a held VCPU: no local
/// path, nothing written.
#[test]
fn other_vcpu_invocations_are_left_to_the_gate_untouched() {
    let _g = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let (s, a) = fixture();
    let try_local = |s2: &Memory, number: i64| {
        let mut ls = s2.clone();
        assert!(!fl4_sync::local_syscall(&mut ls, &mut a.clone(), &Atomics, number, |_, _| {}));
        assert!(ls.diff(s2).is_empty());
    };
    let mut s2 = s.clone();
    syscall_regs(&mut s2, label::X86VCPUReadVMCS, 1, OTHER_VCPU_CPTR, &[GUEST_CR3]);
    try_local(&s2, sc::SysCall);
    let mut s3 = s.clone();
    syscall_regs(&mut s3, label::X86VCPUReadVMCS, 1, VCPU_CPTR, &[GUEST_CR3]);
    CT.set_reg(&mut s3, reg::MSG_INFO, MessageInfo::new(label::X86VCPUReadVMCS, 0, 1, 1).to_word());
    try_local(&s3, sc::SysCall);
    let mut s4 = s.clone();
    syscall_regs(&mut s4, label::X86VCPUReadVMCS, 1, 0xe, &[GUEST_CR3]);
    try_local(&s4, sc::SysCall);
    let mut s5 = s.clone();
    syscall_regs(&mut s5, label::X86VCPUReadVMCS, 1, VCPU_CPTR, &[GUEST_CR3]);
    let mut other = lock::Held::new();
    assert!(lock::try_lock_object(&Atomics, V, &mut other));
    try_local(&s5, sc::SysCall);
    lock::unlock_held(&Atomics, &mut other);
    // NBSend or Recv with that label: not a candidate.
    try_local(&s5, sc::SysNBSend);
}

/// The checks before a hardware entry, beside the gate, write nothing, and
/// agree with what `exit` does under it: the root registered for this core
/// (or none), or the gate when `vcpu::check` or `ept::mark_core` would act.
#[test]
fn vm_entry_checks_beside_the_gate_write_nothing() {
    let _g = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let (mut s, mut a) = fixture();
    running_vm(&mut s);
    let ready = |s: &Memory| {
        let before = s.clone();
        let r = fl4_sync::local_vm_entry(s, &Atomics);
        assert!(s.diff(&before).is_empty());
        r
    };
    // No EPT root: the empty one.
    assert_eq!(ready(&s), Some(0));
    // A root this core is not registered for: the gate registers it.
    ks_set(&mut s, ks::ASID_TABLE + (ASID >> 9) * 8, POOL);
    s.write(POOL + (ASID & 511) * 8, EPT_ROOT | 1);
    CT.slot(tl::SLOT_EPT).set_cap(&mut s, Cap::Ept { ptr: EPT_ROOT, level: 0, mapped: true, asid: ASID, vaddr: 0 });
    assert_eq!(ready(&s), None);
    let mut serial = s.clone();
    vcpu::check(&mut serial, &mut a, CT);
    fl4_core::ept::mark_core(&mut serial, EPT_ROOT);
    assert_eq!(serial.diff(&s).len(), 1, "mark_core writes the core bitmap");
    assert_eq!(ready(&serial), Some(EPT_ROOT));
    // Under the gate, with the core registered, nothing changes either.
    let mut again = serial.clone();
    vcpu::check(&mut again, &mut a, CT);
    fl4_core::ept::mark_core(&mut again, EPT_ROOT);
    assert!(again.diff(&serial).is_empty());
    // Another core registered only.
    let mut other_core = serial.clone();
    other_core.cpu = 0;
    node_set(&mut other_core, 0, node::CUR_THREAD, CT.0);
    assert_eq!(ready(&other_core), None);
    // A pending exit, a signal, a thread not in a VM: the gate.
    let mut p = serial.clone();
    vcpu::set(&mut p, V, vcpu::PENDING, 1);
    assert_eq!(ready(&p), None);
    let mut n = serial.clone();
    Ntfn(N).set_state(&mut n, NTFN_ACTIVE);
    assert_eq!(ready(&n), None);
    let mut r = serial.clone();
    CT.set_state(&mut r, sched::TS_RUNNING);
    assert_eq!(ready(&r), None);
    // The notification held by another core: the gate.
    let mut other = lock::Held::new();
    assert!(lock::try_lock_object(&Atomics, N, &mut other));
    assert_eq!(ready(&serial), None);
    lock::unlock_held(&Atomics, &mut other);
    assert_eq!(node_get(&serial, CPU, node::CUR_THREAD), CT.0);
}
