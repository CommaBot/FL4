//! The local paths of hardware virtualization (DESIGN.md §7): what they
//! check and what they run, as `localtimer` is written (checks with reads
//! only, then the general path's own fl4-core functions in its order).
//! `fl4-sync` wraps them in the gate's handshake and the object locks
//! (`local_vm_syscall`, `local_vm_entry`, `local_vm_exit`,
//! `local_vm_timer_irq`, `local_arm_vcpu_run`, `local_arm_vm_entry`,
//! `local_arm_vcpu_run_exit`), as it wraps `localtimer`, locking what
//! `vm_locks` names.
//!
//! x86_64: an l4h vCPU thread `ct` with a bound VCPU `v` enters its guest
//! with `SysVMEnter` and runs it (`TS_RUNNING_VM`) until an exit its
//! monitor must see, which completes the `SysVMEnter`; meanwhile it reads
//! and writes `v` with `X86VCPU*` invocations. Every one of those steps
//! used to take the serial gate. Beside it:
//!
//! * `handle_vm_enter_local`: `SysVMEnter` (`handle_unknown_syscall`'s
//!   VMEnter case: `vcpu::enter` and `finish`);
//! * `vm_entry_ready`: the checks `exit` makes before each hardware entry
//!   (`vcpu::check`, `ept::mark_core`), when they change nothing;
//! * `handle_vcpu_exit_local`: `handle_vcpu_exit` for an exit that carries
//!   no host interrupt (a guest exit, completed with `vcpu::report`, or a
//!   kick) or the kernel timer's (as `localtimer::handle_timer_irq_local`);
//! * `handle_vcpu_invocation_local`: an `X86VCPU*` state invocation of
//!   `ct` on its own bound VCPU (`handle_invocation` through `vcpu::decode`
//!   and `finish`).
//!
//! AArch64: an `ARMVCPURun` caller's run (`handle_arm_vcpu_run_local`),
//! the check before its guest runs (`arm_vm_entry_ready`) and the exits
//! that end it (`handle_arm_vcpu_run_exit_local`), and the kernel timer
//! while its guest runs (`handle_vm_timer_irq_local`).
//!
//! # Proof obligations (P2)
//!
//! * Refinement. As `localtimer`'s: for each `local` path here and its
//!   general entry (`general`: `handle_syscall` for `SysVMEnter` and the
//!   VCPU invocations, `handle_vcpu_exit` for an x86 VM exit,
//!   `handle_interrupt_entry` for an AArch64 guest's timer interrupt, the
//!   AArch64 entry's `handle_vcpu_run_exit` for an `ARMVCPURun` exit), from
//!   the same state, `local s = (true, s')` implies `general s = s'` with
//!   the same `Arch` calls with effects in the same order. Once the checks
//!   pass, each runs the general path's functions in its order, and the
//!   checks show the general path would take no other branch (no fault, no
//!   budget expiry unless a round-robin refill that keeps the thread, no
//!   due timer or release but the one fired, no reschedule pending). The
//!   capability slot of an invocation is given, as `fl4-sync` found it
//!   with the slots of its lookup locked: `general`'s own lookup finds the
//!   same slot. `handle_arm_vcpu_run_local` takes the kernel's word on the
//!   VCPU's hardware state (`hw_ok`) as a premise.
//! * Decline. `local s = (false, s')`: `s'` differs from `s` at most by the
//!   caller's `FAULT_IP` (for a syscall, set to what `general` sets it to
//!   first) and by `sched::update_timestamp`, which `general` begins with.
//!   `vm_entry_ready` and `arm_vm_entry_ready` write nothing.
//! * Frame. Beyond `localtimer`'s footprint (this core's node state,
//!   threads and scheduling contexts of this core with their IPC buffers,
//!   its timer tree, the objects locked): the VCPU, locked. On x86 it is
//!   `ct`'s bound VCPU, which nothing but `ct`'s core touches while `ct` is
//!   current there: hardware runs it only for `ct` (`exit`), and every
//!   invocation on it by another thread runs under the gate after stalling
//!   `ct` (`vcpu::stall`). The bound notification `n` is locked and only
//!   read (a signal to it is the gate's, or another core's local timer
//!   interrupt's under its lock); it must not be active, or `vcpu::check`
//!   would consume it.
use crate::capability::Cap;
#[cfg(not(feature = "aarch64"))]
use crate::ept;
use crate::error::Exc;
#[cfg(feature = "aarch64")]
use crate::layout::tcb as tl;
use crate::layout::{reg, NUM_DOMAINS};
use crate::localtimer::{self, SYSCALL_INSN_LEN};
use crate::machine::{Arch, Store};
use crate::obj::{Ntfn, Sc, Slot, Tcb, NTFN_ACTIVE, NTFN_WAITING};
use crate::{interrupt, ipc, msg, sched, sporadic, vcpu};
use fl4_abi::consts::tcb_flag;
use fl4_abi::label;
use fl4_abi::syscall as sc;

/// Bytes of a VCPU object, as `fl4-sync` reports it locked: on x86 the
/// VMCB, VMCS image, registers and exit frame, and I/O bitmap.
#[cfg(not(feature = "aarch64"))]
pub const VCPU_BYTES: u64 = 0x8000;
/// Bytes of a VCPU object, as `fl4-sync` reports it locked.
#[cfg(feature = "aarch64")]
pub const VCPU_BYTES: u64 = 0x1000;
/// Bytes of a notification, as `fl4-sync` reports it locked.
pub const NTFN_BYTES: u64 = 64;
/// Objects a VM local path locks: the kernel timer's plan, a VCPU and a
/// notification.
pub const MAX_VM_LOCKS: usize = localtimer::MAX_TIMER_LOCKS + 2;
const _: () = assert!(localtimer::MAX_TIMER_LOCKS == 3);

/// What a VM local path of the current thread locks (`vm_locks`).
#[derive(Clone, Copy)]
pub struct VmLocks {
    /// The VCPU (0: none).
    pub vcpu: u64,
    /// The current thread's bound notification, if locked (0: none).
    pub ntfn: u64,
    /// As (address, bytes): a timer plan's objects, `vcpu`, `ntfn`; 0 for
    /// none. `ntfn` may repeat a planned object (a guest thread's own timer
    /// signals it): `fl4-sync` locks each address once and skips 0.
    pub objects: [(u64, u64); MAX_VM_LOCKS],
}

/// The objects a VM local path on VCPU `vc` (0: none) of the current
/// thread locks: `vc` and the thread's bound notification.
pub fn vm_locks<S: Store>(s: &S, vc: u64) -> VmLocks {
    let n = sched::cur_thread(s).bound_ntfn(s);
    VmLocks { vcpu: vc, ntfn: n, objects: [(0, 0), (0, 0), (0, 0), (vc, VCPU_BYTES), (n, NTFN_BYTES)] }
}

/// The objects a VM timer-IRQ local path on VCPU `vc` (0: none) locks:
/// those of timer plan `p`, then `vc` and the thread's bound notification.
pub fn vm_timer_locks<S: Store>(s: &S, vc: u64, p: &localtimer::TimerIrqPlan) -> VmLocks {
    let n = sched::cur_thread(s).bound_ntfn(s);
    VmLocks {
        vcpu: vc,
        ntfn: n,
        objects: [planned(p, 0), planned(p, 1), planned(p, 2), (vc, VCPU_BYTES), (n, NTFN_BYTES)],
    }
}

/// What a VM local path on VCPU `vc` alone locks: `vc`.
pub fn vcpu_locks(vc: u64) -> VmLocks {
    VmLocks { vcpu: vc, ntfn: 0, objects: [(0, 0), (0, 0), (0, 0), (vc, VCPU_BYTES), (0, 0)] }
}

/// Object `i` of timer plan `p`, or (0, 0) for none.
fn planned(p: &localtimer::TimerIrqPlan, i: usize) -> (u64, u64) {
    if i < p.n && i < localtimer::MAX_TIMER_LOCKS {
        p.objects[i]
    } else {
        (0, 0)
    }
}

/// The current thread `ct` and scheduling context `csc` at entry, for a
/// thread that runs or enters a VM: this core's, not the idle thread,
/// running on `csc` (this core's), in the current domain, with no yield to
/// complete (`activate_thread`). Unlike `localtimer::current_ok` it may
/// have a VCPU and be in `TS_RUNNING_VM`: its VCPU state is this core's
/// while it is current (Frame).
fn current_vm_ok<S: Store>(s: &S, cpu: u64, ct: Tcb, csc: Sc) -> bool {
    !ct.is_null()
        && ct != sched::idle_thread(s)
        && ct.affinity(s) == cpu
        && ct.yield_to(s) == 0
        && !csc.is_null()
        && ct.sc(s) == csc.0
        && csc.cpu(s) == cpu
        && ct.domain(s) == sched::cur_domain(s)
}

/// `schedule()`'s `awaken` at `now` has nothing to do on this core: no
/// timer due, no thread of the release queue ready.
fn awaken_quiet<S: Store>(s: &S, cpu: u64, now: u64) -> bool {
    !localtimer::timer_due(s, cpu, now) && !localtimer::release_due(s, cpu)
}

/// Notification `n` (or none) has no signal for `vcpu::check` to consume.
fn ntfn_quiet<S: Store>(s: &S, n: u64) -> bool {
    n == 0 || Ntfn(n).state(s) != NTFN_ACTIVE
}

/// `syscall::finish`.
fn finish<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    sched::schedule(s, a);
    sched::activate_thread(s, a);
    vcpu::check(s, a, sched::cur_thread(s));
}

/// As `syscall` and `budget_ok` begin: the restart point of the syscall
/// instruction, and the clock.
fn syscall_prefix<S: Store, A: Arch>(s: &mut S, a: &mut A, ct: Tcb) {
    let next = ct.reg(s, reg::NEXT_IP);
    ct.set_reg(s, reg::FAULT_IP, next.wrapping_sub(SYSCALL_INSN_LEN));
    sched::update_timestamp(s, a);
}

/// The kernel timer interrupt `irq` while `ct`, in `TS_RUNNING_VM`, runs
/// its guest (x86: a VM exit for it; AArch64: an interrupt from an
/// `ARMVCPURun` guest), holding the locks of `p` (`localtimer::plan_timer_irq`)
/// and of `n`, `ct`'s bound notification, which must not be active:
/// `localtimer::handle_timer_irq_local`'s cases (a round-robin refill that
/// keeps `ct`, one due timer of this core's, or neither), with `vcpu::check`
/// changing nothing before and after. On x86 the general path is
/// `handle_vcpu_exit` (its `vcpu::check` first, with the VCPU's exit not
/// pending), on AArch64 `handle_interrupt_entry`; both then charge the
/// budget, handle the interrupt and `finish`.
pub fn handle_vm_timer_irq_local<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    irq: u64,
    p: &localtimer::TimerIrqPlan,
    n: u64,
) -> bool {
    let cpu = s.cur_cpu();
    if NUM_DOMAINS != 1
        || irq > crate::layout::irq::MAX
        || interrupt::irq_state(s, irq) != interrupt::IRQ_TIMER
        || !localtimer::same_plan(&localtimer::plan_objects(s), p)
    {
        return false;
    }
    let ct = sched::cur_thread(s);
    let csc = sched::cur_sc(s);
    if ct.state(s) != sched::TS_RUNNING_VM
        || ct.bound_ntfn(s) != n
        || !ntfn_quiet(s, n)
        || !vm_running(s, ct)
        || !current_vm_ok(s, cpu, ct, csc)
        || !localtimer::sched_quiet(s, cpu)
    {
        return false;
    }
    sched::update_timestamp(s, a);
    let now = sched::cur_time(s);
    if localtimer::release_due(s, cpu) {
        return false;
    }
    let expired = !sporadic::sufficient(s, a, csc, sched::consumed(s));
    let due = localtimer::timer_due(s, cpu, now);
    // On AArch64 `ct` must stay current without a switch: one back to it
    // (`choose_thread` after a refill, or after a woken thread queued
    // behind it) would set its guest's Stage-2 root, whose VMID may need
    // allocating, which only the gate does (`mmu::hw_vmid_for`). So no
    // refill, and a due timer only where its signal wakes no thread.
    let ok = if expired && due {
        false
    } else if expired {
        !cfg!(feature = "aarch64") && localtimer::round_robin_ok(s, a, cpu, ct, csc, now)
    } else if due {
        localtimer::fire_ok(s, cpu, ct, p, now)
            && (!cfg!(feature = "aarch64")
                || (p.waiter == 0 && (p.ntfn == 0 || Ntfn(p.ntfn).state(s) != NTFN_WAITING)))
    } else {
        true
    };
    if !ok {
        return false;
    }
    if !cfg!(feature = "aarch64") {
        // `handle_vcpu_exit`: the exit is not pending and `n` not active.
        vcpu::check(s, a, ct);
    }
    let _ = sched::check_budget(s, a);
    interrupt::handle_interrupt(s, a, irq);
    finish(s, a);
    true
}

/// The VCPU the current thread runs a guest on (0: none): its bound one.
#[cfg(not(feature = "aarch64"))]
pub fn cur_vcpu<S: Store>(s: &S) -> u64 {
    vcpu::bound(s, sched::cur_thread(s))
}

/// The VCPU the current thread runs a guest on (0: none): its
/// `ARMVCPURun`'s.
#[cfg(feature = "aarch64")]
pub fn cur_vcpu<S: Store>(s: &S) -> u64 {
    run_vcpu(s, sched::cur_thread(s))
}

/// `ct`, in `TS_RUNNING_VM`, runs a guest that `vcpu::check` leaves to run:
/// its bound VCPU, whose exit is not pending.
#[cfg(not(feature = "aarch64"))]
fn vm_running<S: Store>(s: &S, ct: Tcb) -> bool {
    let v = vcpu::bound(s, ct);
    v != 0 && vcpu::get(s, v, vcpu::PENDING) == 0
}

/// `ct`, in `TS_RUNNING_VM`, runs a guest that `vcpu::check` leaves to run:
/// the VCPU of its `ARMVCPURun`.
#[cfg(feature = "aarch64")]
fn vm_running<S: Store>(s: &S, ct: Tcb) -> bool {
    run_vcpu(s, ct) != 0
}

// ---- x86_64 -----------------------------------------------------------------

// `syscall` sends `SysVMEnter` to `handle_unknown_syscall`.
#[cfg(not(feature = "aarch64"))]
const _: () = assert!(sc::SysVMEnter < sc::SYSCALL_MIN || sc::SysVMEnter > sc::SYSCALL_MAX);

/// `SysVMEnter` of the current thread `ct` beside the serial gate,
/// holding the locks of its bound VCPU `v` and bound notification `n`
/// (or 0): `handle_syscall` through `handle_unknown_syscall`'s VMEnter
/// case, `budget_ok`, `vcpu::enter` and `finish`, when the budget is
/// left, `n` has no signal (`vcpu::enter` would complete the call at
/// once with it), and `schedule()` keeps `ct`. Returns false otherwise,
/// having written only `FAULT_IP` and the timestamp (Decline).
#[cfg(not(feature = "aarch64"))]
pub fn handle_vm_enter_local<S: Store, A: Arch>(s: &mut S, a: &mut A, number: i64, v: u64, n: u64) -> bool {
    let ct = sched::cur_thread(s);
    let cpu = s.cur_cpu();
    if NUM_DOMAINS != 1
        || number != sc::SysVMEnter
        || ct.flags(s) & tcb_flag::TRAP_SYSCALLS != 0
        || a.virtualization() == 0
        || v == 0
        || vcpu::bound(s, ct) != v
        || ct.bound_ntfn(s) != n
        || !ntfn_quiet(s, n)
    {
        return false;
    }
    let csc = sched::cur_sc(s);
    if !current_vm_ok(s, cpu, ct, csc)
        || ct.state(s) != sched::TS_RUNNING
        || !sched::is_schedulable(s, ct)
        || !localtimer::sched_quiet(s, cpu)
    {
        return false;
    }
    syscall_prefix(s, a, ct);
    let now = sched::cur_time(s);
    if !sporadic::sufficient(s, a, csc, sched::consumed(s)) || !awaken_quiet(s, cpu, now) {
        return false;
    }
    // `handle_unknown_syscall`: none of the debug or TLS syscalls it
    // tries first is `SysVMEnter`. `budget_ok` writes nothing more.
    let _ = sched::check_budget_restart(s, a);
    vcpu::enter(s, a, ct);
    finish(s, a);
    true
}

/// The checks `exit` makes before a hardware entry of the current
/// thread's guest, beside the serial gate, holding the lock of its bound
/// notification `n`: `vcpu::check` would change nothing (the thread is
/// in `TS_RUNNING_VM` with bound VCPU `v`, whose exit is not pending,
/// and `n` has no signal), and `ept::mark_core` would write nothing (this
/// core is recorded for the EPT root already). The root to enter on (0:
/// the thread's EPT cap names none, and the kernel's empty root is used);
/// None to leave it to the gate. Writes nothing.
///
/// After the gate opens again a serial entry may unmap from the root,
/// delete it, signal `n` or stall the thread, as it may between the
/// general path's release of the gate and the entry instruction: this
/// core is recorded for the root, and every such change interrupts it,
/// which with interrupts off is pending at the entry and exits the
/// guest at once (external-interrupt exiting is forced on).
#[cfg(not(feature = "aarch64"))]
pub fn vm_entry_ready<S: Store>(s: &S, v: u64, n: u64) -> Option<u64> {
    let ct = sched::cur_thread(s);
    if ct.state(s) != sched::TS_RUNNING_VM
        || v == 0
        || vcpu::bound(s, ct) != v
        || vcpu::get(s, v, vcpu::PENDING) != 0
        || ct.bound_ntfn(s) != n
        || !ntfn_quiet(s, n)
    {
        return None;
    }
    match ept::root(s, ct.slot(crate::layout::tcb::SLOT_EPT).cap(s)) {
        Ok((root, _)) => {
            if ept::core_marked(s, root) {
                Some(root)
            } else {
                None
            }
        }
        Err(_) => Some(0),
    }
}

/// `handle_vcpu_exit(irq, false)` beside the serial gate for a VM exit
/// of the current thread `ct` that carries no host interrupt
/// (`irq == NO_IRQ`), holding the locks of its bound VCPU `v` and
/// notification `n`: a guest exit (`PENDING`), which `vcpu::check`
/// completes with `vcpu::report`, or a host exit that leaves the guest
/// to run on (`n` without a signal), when the budget is left, nothing
/// is due and `schedule()` keeps `ct`. Returns false otherwise, having
/// written only the timestamp (Decline). The kernel timer's exit is
/// `handle_vm_timer_irq_local`.
#[cfg(not(feature = "aarch64"))]
pub fn handle_vcpu_exit_local<S: Store, A: Arch>(s: &mut S, a: &mut A, v: u64, n: u64) -> bool {
    let ct = sched::cur_thread(s);
    let cpu = s.cur_cpu();
    let csc = sched::cur_sc(s);
    if NUM_DOMAINS != 1
        || ct.state(s) != sched::TS_RUNNING_VM
        || v == 0
        || vcpu::bound(s, ct) != v
        || ct.bound_ntfn(s) != n
        || (vcpu::get(s, v, vcpu::PENDING) == 0 && !ntfn_quiet(s, n))
        || !current_vm_ok(s, cpu, ct, csc)
        || !sched::is_schedulable(s, ct)
        || !localtimer::sched_quiet(s, cpu)
    {
        return false;
    }
    sched::update_timestamp(s, a);
    let now = sched::cur_time(s);
    // `check_budget` charges nothing; `awaken` does nothing.
    if !sporadic::sufficient(s, a, csc, sched::consumed(s)) || !awaken_quiet(s, cpu, now) {
        return false;
    }
    vcpu::check(s, a, ct);
    let _ = sched::check_budget(s, a);
    finish(s, a);
    true
}

/// A syscall `number` of thread `t` that a VM local path may take:
/// `SysVMEnter` with a bound VCPU, or a VCPU state invocation.
#[cfg(not(feature = "aarch64"))]
pub fn is_vm_syscall<S: Store>(s: &S, t: Tcb, number: i64) -> bool {
    (number == sc::SysVMEnter && vcpu::bound(s, t) != 0)
        || ((number == sc::SysCall || number == sc::SysSend) && is_vcpu_state_label(msg::msg_info(s, t).label))
}

/// The `X86VCPU*` invocations that read or write only the VCPU's own
/// state and the caller (`vcpu::decode`): no extra caps, no other
/// object, no stall when the caller is the VCPU's bound thread.
#[cfg(not(feature = "aarch64"))]
pub fn is_vcpu_state_label(l: u64) -> bool {
    l == label::X86VCPUWriteRegisters
        || l == label::X86VCPUFlushTLB
        || l == label::X86VCPUReadVMCS
        || l == label::X86VCPUWriteVMCS
        || l == label::X86VCPUReadVMCB
        || l == label::X86VCPUWriteVMCB
        || l == label::X86VCPUReadMSR
        || l == label::X86VCPUWriteMSR
}

/// An `X86VCPU*` state invocation (`is_vcpu_state_label`, `SysCall` or
/// `SysSend`) of the current thread `ct` on VCPU `v`, through the cap in
/// `slot` (found by `fl4-sync` with the slots of its lookup locked, so
/// `handle_invocation`'s own lookup finds it too), beside the serial
/// gate holding `v`'s lock: `handle_invocation` through `vcpu::decode`
/// and its reply, and `finish`, when `ct` is `v`'s bound thread (so
/// `vcpu::stall` stalls nothing and no other core runs `v`), budget is
/// left and `schedule()` keeps `ct`. An invocation the decode refuses
/// gets its error reply, as on the general path (its errors come before
/// any write; it has no preemption point). Returns false otherwise,
/// having written only `FAULT_IP` and the timestamp (Decline).
#[cfg(not(feature = "aarch64"))]
pub fn handle_vcpu_invocation_local<S: Store, A: Arch>(s: &mut S, a: &mut A, number: i64, slot: Slot, v: u64) -> bool {
    let ct = sched::cur_thread(s);
    let cpu = s.cur_cpu();
    let info = msg::msg_info(s, ct);
    if NUM_DOMAINS != 1
        || ct.flags(s) & tcb_flag::TRAP_SYSCALLS != 0
        || (number != sc::SysCall && number != sc::SysSend)
        || !is_vcpu_state_label(info.label)
        || info.extra_caps != 0
        || a.virtualization() == 0
        || v == 0
        || slot.cap(s) != (Cap::Vcpu { ptr: v })
        || vcpu::get(s, v, vcpu::TCB) != ct.0
        || vcpu::bound(s, ct) != v
    {
        return false;
    }
    let csc = sched::cur_sc(s);
    if !current_vm_ok(s, cpu, ct, csc)
        || ct.state(s) != sched::TS_RUNNING
        || !sched::is_schedulable(s, ct)
        || !localtimer::sched_quiet(s, cpu)
    {
        return false;
    }
    syscall_prefix(s, a, ct);
    let now = sched::cur_time(s);
    if !sporadic::sufficient(s, a, csc, sched::consumed(s)) || !awaken_quiet(s, cpu, now) {
        return false;
    }
    // `handle_invocation` (`SysCall`: is_call; both blocking): the
    // lookup found `slot`; no extra caps to look up.
    let call = number == sc::SysCall;
    let buf = msg::lookup_ipc_buffer(s, false, ct);
    let extra = match ipc::lookup_extra_caps(s, ct, buf, info) {
        Ok(e) => e,
        Err(_) => return false,
    };
    let mut length = info.length;
    if length > msg::N_MSG_REGISTERS && buf == 0 {
        length = msg::N_MSG_REGISTERS;
    }
    match vcpu::decode(s, a, info.label, length, v, call, buf, &extra) {
        Err(Exc::Sys(e)) => {
            if call {
                crate::syscall::reply_error(s, ct, e);
            }
        }
        Err(_) => {}
        Ok(()) => {
            if ct.state(s) == sched::TS_RESTART {
                if call {
                    msg::reply_success_empty(s, ct);
                }
                sched::set_thread_state(s, ct, sched::TS_RUNNING);
            }
        }
    }
    finish(s, a);
    true
}

// ---- AArch64 ----------------------------------------------------------------

/// A syscall `number` of thread `t` that a VM local path may take: an
/// `ARMVCPURun`.
#[cfg(feature = "aarch64")]
pub fn is_vm_syscall<S: Store>(s: &S, t: Tcb, number: i64) -> bool {
    number == sc::SysCall && msg::msg_info(s, t).label == label::ARMVCPURun
}

/// The VCPU an `ARMVCPURun` caller `t` runs (0 for none).
#[cfg(feature = "aarch64")]
pub fn run_vcpu<S: Store>(s: &S, t: Tcb) -> u64 {
    s.read(t.0.wrapping_add(tl::RUN_VCPU))
}

/// The guest thread VCPU `vc` names (none for `vc` 0).
#[cfg(feature = "aarch64")]
pub fn vcpu_guest<S: Store>(s: &S, vc: u64) -> Tcb {
    if vc == 0 {
        Tcb(0)
    } else {
        Tcb(s.read(vc.wrapping_add(vcpu::TCB)))
    }
}

/// An `ARMVCPURun` (`SysCall`) of the current thread `ct` on VCPU `vc`,
/// through the cap in `slot` (found with the slots of its lookup
/// locked), beside the serial gate, holding the locks of `vc` and of
/// `ct`'s bound notification `n`: `handle_invocation` through
/// `vcpu::decode`'s `decode_run` and `finish`, when nothing of it is
/// another core's. `vc`'s guest thread is inactive (not running, so
/// `remote_tcb_stall` stalls nothing) and bound to `vc`; no run of `vc`
/// is in flight; `vc` last ran here (`OWNER_CPU`: no cross-core flush);
/// `n` has no signal (`vcpu::check` would end the run at once); budget
/// is left and `schedule()` keeps `ct`; and `hw_ok`, the kernel's word
/// (`fl4-sync` `local_arm_vcpu_run` asks it, with these locks held, for
/// `vc` and the guest thread `vc` names) that `vc`'s hardware state is
/// live on no other core and the guest's Stage-2 VMID needs no allocation
/// (both of which only the gate may change elsewhere). A run the decode
/// refuses gets its error reply, as on the general path (its errors come
/// before any write). Returns false otherwise, having written only
/// `FAULT_IP` and the timestamp (Decline).
#[cfg(feature = "aarch64")]
pub fn handle_arm_vcpu_run_local<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    number: i64,
    slot: Slot,
    vc: u64,
    n: u64,
    hw_ok: bool,
) -> bool {
    let ct = sched::cur_thread(s);
    let cpu = s.cur_cpu();
    let info = msg::msg_info(s, ct);
    if NUM_DOMAINS != 1
        || number != sc::SysCall
        || ct.flags(s) & tcb_flag::TRAP_SYSCALLS != 0
        || info.label != label::ARMVCPURun
        || info.extra_caps != 0
        || vc == 0
        || slot.cap(s) != (Cap::Vcpu { ptr: vc })
        || ct.bound_ntfn(s) != n
        || !ntfn_quiet(s, n)
    {
        return false;
    }
    let guest = vcpu_guest(s, vc);
    if guest.is_null()
        || guest == ct
        || guest.state(s) != sched::TS_INACTIVE
        || vcpu::bound(s, guest) != vc
        || s.read(vc.wrapping_add(vcpu::RUN_CALLER)) != 0
        || s.read(vc.wrapping_add(vcpu::OWNER_CPU)) != cpu.wrapping_add(1)
        || !hw_ok
    {
        return false;
    }
    let csc = sched::cur_sc(s);
    // `ct` itself a native thread of this core (no VCPU of its own).
    if !localtimer::current_ok(s, cpu, ct, csc)
        || ct.state(s) != sched::TS_RUNNING
        || !sched::is_schedulable(s, ct)
        || !localtimer::sched_quiet(s, cpu)
    {
        return false;
    }
    syscall_prefix(s, a, ct);
    let now = sched::cur_time(s);
    if !sporadic::sufficient(s, a, csc, sched::consumed(s)) || !awaken_quiet(s, cpu, now) {
        return false;
    }
    // `handle_invocation`: the lookup found `slot`; no extra caps.
    let buf = msg::lookup_ipc_buffer(s, false, ct);
    let extra = match ipc::lookup_extra_caps(s, ct, buf, info) {
        Ok(e) => e,
        Err(_) => return false,
    };
    let mut length = info.length;
    if length > msg::N_MSG_REGISTERS && buf == 0 {
        length = msg::N_MSG_REGISTERS;
    }
    match vcpu::decode(s, a, info.label, length, vc, true, buf, &extra) {
        Err(Exc::Sys(e)) => crate::syscall::reply_error(s, ct, e),
        Err(_) => {}
        Ok(()) => {
            if ct.state(s) == sched::TS_RESTART {
                msg::reply_success_empty(s, ct);
                sched::set_thread_state(s, ct, sched::TS_RUNNING);
            }
        }
    }
    finish(s, a);
    true
}

/// The check `exit` makes before an `ARMVCPURun` caller's guest runs
/// (`vcpu::check`), beside the serial gate, holding the lock of its
/// bound notification `n`: true when it would change nothing (the run
/// is in flight and `n` has no signal). Writes nothing. A signal, an
/// unbinding or a deletion after the gate opens again stalls this core
/// (`kick_guest`, `remote_tcb_stall`), which takes its guest out at
/// once, as after the general path's release of the gate.
#[cfg(feature = "aarch64")]
pub fn arm_vm_entry_ready<S: Store>(s: &S, n: u64) -> bool {
    let ct = sched::cur_thread(s);
    ct.state(s) == sched::TS_RUNNING_VM && run_vcpu(s, ct) != 0 && ct.bound_ntfn(s) == n && ntfn_quiet(s, n)
}

/// `handle_vcpu_run_exit(stop, w1, w2, w3)` for an exit of the guest
/// of the current thread `ct`'s `ARMVCPURun` on VCPU `vc` (locked),
/// beside the serial gate: `complete_run` writes `vc`, `ct` and its IPC
/// buffer frame, flushes `vc`'s state live on this core and sets `ct`'s
/// address space here; when budget is left (so `check_budget` charges
/// nothing after `ct` is back in `TS_RUNNING`) and `schedule()` keeps
/// `ct`. For an HVC, `hvc` is the guest thread and the ELR past the
/// HVC, which the entry rewound to the HVC (its own guest registers,
/// this core's while `ct` runs `vc`): restored first, as the general
/// path's entry body does. Returns false otherwise, having written only
/// the timestamp (Decline).
#[cfg(feature = "aarch64")]
pub fn handle_arm_vcpu_run_exit_local<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    vc: u64,
    stop: u64,
    w1: u64,
    w2: u64,
    w3: u64,
    hvc: Option<(Tcb, u64)>,
) -> bool {
    let ct = sched::cur_thread(s);
    let cpu = s.cur_cpu();
    let csc = sched::cur_sc(s);
    if NUM_DOMAINS != 1
        || ct.state(s) != sched::TS_RUNNING_VM
        || vc == 0
        || run_vcpu(s, ct) != vc
        || !current_vm_ok(s, cpu, ct, csc)
        || !sched::is_schedulable(s, ct)
        || !localtimer::sched_quiet(s, cpu)
    {
        return false;
    }
    if let Some((g, _)) = hvc {
        if vcpu_guest(s, vc) != g {
            return false;
        }
    }
    sched::update_timestamp(s, a);
    let now = sched::cur_time(s);
    if !sporadic::sufficient(s, a, csc, sched::consumed(s)) || !awaken_quiet(s, cpu, now) {
        return false;
    }
    if let Some((g, elr)) = hvc {
        if g.reg(s, reg::ELR_EL1) == elr.wrapping_sub(4) {
            g.set_reg(s, reg::ELR_EL1, elr);
        }
    }
    vcpu::complete_run(s, a, ct, stop, w1, w2, w3);
    let _ = sched::check_budget(s, a);
    finish(s, a);
    true
}
