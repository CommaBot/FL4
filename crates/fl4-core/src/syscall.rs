//! Kernel entry points (seL4 api/syscall.c, MCS, and the x86 c_traps.c
//! dispatch). The architecture glue saves the user registers into the
//! current TCB and calls one of the `handle_*` functions; when it returns,
//! the glue restores whichever thread is now current.

use crate::capability::Cap;
use crate::cnode;
use crate::cspace;
use crate::debug;
use crate::endpoint;
use crate::error::{Exc, Fault, KResult, LookupFault, SysError};
use crate::faults;
use crate::interrupt;
use crate::ioport;
use crate::ipc;
use crate::layout::{reg, node};
use crate::machine::{Arch, Store};
use crate::msg;
use crate::msginfo::MessageInfo;
use crate::notification;
use crate::obj::{node_set, Ntfn, Reply, Slot, Tcb};
use crate::sched;
use crate::schedcontext;
use crate::sporadic;
use crate::tcb;
use crate::untyped;
use crate::vspace;
use fl4_abi::consts::tcb_flag;
use fl4_abi::syscall as sc;

/// seL4 `MCS_DO_IF_BUDGET`'s guard.
fn budget_ok<S: Store, A: Arch>(s: &mut S, a: &mut A) -> bool {
    sched::update_timestamp(s, a);
    sched::check_budget_restart(s, a)
}

fn finish<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    sched::schedule(s, a);
    sched::activate_thread(s, a);
}

/// seL4 `replyFromKernel_error` with `setMRs_syscall_error`.
fn reply_error<S: Store>(s: &mut S, t: Tcb, e: SysError) {
    let buf = msg::lookup_ipc_buffer(s, true, t);
    t.set_reg(s, reg::BADGE, 0);
    let len = match e {
        SysError::InvalidArgument { arg } => msg::set_mr(s, t, buf, 0, arg),
        SysError::InvalidCapability { arg } => msg::set_mr(s, t, buf, 0, arg),
        SysError::RangeError { min, max } => {
            msg::set_mr(s, t, buf, 0, min);
            msg::set_mr(s, t, buf, 1, max)
        }
        SysError::FailedLookup { source, lf } => {
            msg::set_mr(s, t, buf, 0, if source { 1 } else { 0 });
            faults::set_mrs_lookup_failure_at(s, t, buf, lf, 1)
        }
        SysError::NotEnoughMemory { bytes } => msg::set_mr(s, t, buf, 0, bytes),
        _ => 0,
    };
    // KernelInvocationReportErrorIPC: the error string follows. FL4 keeps
    // no error strings, so it is always empty (l4h 0008: never the string
    // of an earlier invocation); like strlcpy, only its NUL byte is written.
    let len = if fl4_abi::config::KERNEL_INVOCATION_REPORT_ERROR_IPC && buf != 0 {
        let w = msg::buf_get(s, buf, DEBUG_MESSAGE_START + 1);
        msg::buf_set(s, buf, DEBUG_MESSAGE_START + 1, w & !0xff);
        len + 1
    } else {
        len
    };
    msg::set_msg_info(s, t, MessageInfo::new(e.code(), 0, 0, len));
}

/// seL4 `decodeInvocation` (MCS).
#[allow(clippy::too_many_arguments)]
fn decode_invocation<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    lbl: u64,
    length: u64,
    slot: Slot,
    cap: Cap,
    block: bool,
    call: bool,
    can_donate: bool,
    first_phase: bool,
    buf: u64,
    extra: &[Slot; 3],
) -> KResult<()> {
    let ct = sched::cur_thread(s);
    match cap {
        Cap::Null | Cap::Zombie { .. } => Err(Exc::Sys(SysError::InvalidCapability { arg: 0 })),
        Cap::Endpoint { ptr, badge, send, grant, grant_reply, .. } => {
            if !send {
                return Err(Exc::Sys(SysError::InvalidCapability { arg: 0 }));
            }
            sched::set_thread_state(s, ct, sched::TS_RESTART);
            endpoint::send_ipc(s, a, block, call, badge, grant, grant_reply, can_donate, ct, ptr);
            Ok(())
        }
        Cap::Notification { ptr, badge, send, .. } => {
            if !send {
                return Err(Exc::Sys(SysError::InvalidCapability { arg: 0 }));
            }
            sched::set_thread_state(s, ct, sched::TS_RESTART);
            notification::send_signal(s, a, ptr, badge);
            Ok(())
        }
        Cap::Reply { ptr, grant } => {
            sched::set_thread_state(s, ct, sched::TS_RESTART);
            ipc::do_reply_transfer(s, a, ct, Reply(ptr), grant);
            Ok(())
        }
        Cap::Thread { ptr } => {
            if first_phase {
                return Err(Exc::Sys(SysError::InvalidCapability { arg: 0 }));
            }
            let c = tcb::Ctx { length, buf, call, slot, extra };
            tcb::decode(s, a, lbl, Tcb(ptr), &c)
        }
        Cap::Domain => {
            if first_phase {
                return Err(Exc::Sys(SysError::InvalidCapability { arg: 0 }));
            }
            crate::domain::decode(s, lbl, length, buf, extra)
        }
        Cap::CNode { .. } => {
            if first_phase {
                return Err(Exc::Sys(SysError::InvalidCapability { arg: 0 }));
            }
            cnode::decode(s, a, lbl, length, cap, buf, extra)
        }
        Cap::Untyped { .. } => untyped::decode(s, a, lbl, length, slot, cap, buf, extra),
        Cap::IrqControl => interrupt::decode_irq_control(s, a, lbl, length, slot, buf, extra),
        Cap::IrqHandler { irq } => interrupt::decode_irq_handler(s, a, lbl, irq, extra),
        Cap::SchedControl { cpu } => {
            if first_phase {
                return Err(Exc::Sys(SysError::InvalidCapability { arg: 0 }));
            }
            schedcontext::decode_sched_control(s, a, lbl, cpu, length, buf, extra)
        }
        Cap::SchedContext { ptr, .. } => {
            if first_phase {
                return Err(Exc::Sys(SysError::InvalidCapability { arg: 0 }));
            }
            schedcontext::decode(s, a, lbl, crate::obj::Sc(ptr), call, extra)
        }
        Cap::IoPortControl => ioport::decode_control(s, a, lbl, length, slot, buf, extra),
        Cap::IoPort { .. } => ioport::decode(s, a, lbl, length, cap, call, buf),
        Cap::Frame { .. }
        | Cap::PageTable { .. }
        | Cap::PageDirectory { .. }
        | Cap::Pdpt { .. }
        | Cap::Pml4 { .. }
        | Cap::AsidControl
        | Cap::AsidPool { .. } => vspace::decode(s, a, lbl, length, slot, cap, call, buf, extra),
    }
}

/// seL4 `handleInvocation`. Returns Err only for preemption.
fn handle_invocation<S: Store, A: Arch>(s: &mut S, a: &mut A, is_call: bool, blocking: bool, can_donate: bool, first_phase: bool, cptr: u64) -> KResult<()> {
    let t = sched::cur_thread(s);
    let info = msg::msg_info(s, t);
    let (cap, slot) = match cspace::lookup_slot(s, t, cptr) {
        Ok(r) => (r.slot.cap(s), r.slot),
        Err(lf) => {
            if blocking {
                faults::handle_fault(s, a, t, Fault::Cap { addr: cptr, in_recv: false, lf });
            }
            return Ok(());
        }
    };
    let buf = msg::lookup_ipc_buffer(s, false, t);
    let extra = match ipc::lookup_extra_caps(s, t, buf, info) {
        Ok(e) => e,
        Err(f) => {
            if blocking {
                faults::handle_fault(s, a, t, f);
            }
            return Ok(());
        }
    };
    let mut length = info.length;
    if length > msg::N_MSG_REGISTERS && buf == 0 {
        length = msg::N_MSG_REGISTERS;
    }
    match decode_invocation(s, a, info.label, length, slot, cap, blocking, is_call, can_donate, first_phase, buf, &extra) {
        Err(Exc::Preempted) => return Err(Exc::Preempted),
        Err(Exc::Sys(e)) => {
            if is_call {
                reply_error(s, t, e);
            }
            return Ok(());
        }
        Err(_) => return Ok(()),
        Ok(()) => {}
    }
    if t.state(s) == sched::TS_RESTART {
        if is_call {
            msg::reply_success_empty(s, t);
        }
        sched::set_thread_state(s, t, sched::TS_RUNNING);
    }
    Ok(())
}

/// Where KernelInvocationReportErrorIPC puts the error string (seL4
/// DEBUG_MESSAGE_START).
const DEBUG_MESSAGE_START: u64 = 6;

fn cap_fault_recv<S: Store, A: Arch>(s: &mut S, a: &mut A, cptr: u64, lf: LookupFault) {
    let t = sched::cur_thread(s);
    faults::handle_fault(s, a, t, Fault::Cap { addr: cptr, in_recv: true, lf });
}

/// seL4 `handleRecv` (MCS).
fn handle_recv<S: Store, A: Arch>(s: &mut S, a: &mut A, blocking: bool, can_reply: bool) {
    let t = sched::cur_thread(s);
    let ep_cptr = t.reg(s, reg::CAP);
    let cap = match cspace::lookup_cap(s, t, ep_cptr) {
        Ok(c) => c,
        Err(Exc::Lookup(lf)) => return cap_fault_recv(s, a, ep_cptr, lf),
        Err(_) => return,
    };
    let missing = LookupFault::MissingCapability { bits_left: 0 };
    match cap {
        Cap::Endpoint { recv, .. } => {
            if !recv {
                return cap_fault_recv(s, a, ep_cptr, missing);
            }
            let mut reply_cap = Cap::Null;
            if can_reply {
                let rptr = t.reg(s, reg::REPLY);
                match cspace::lookup_cap(s, t, rptr) {
                    Ok(c @ Cap::Reply { .. }) => reply_cap = c,
                    Ok(_) => return cap_fault_recv(s, a, rptr, missing),
                    Err(Exc::Lookup(lf)) => return cap_fault_recv(s, a, rptr, lf),
                    Err(_) => return,
                }
            }
            endpoint::receive_ipc(s, a, t, cap, blocking, reply_cap);
        }
        Cap::Notification { ptr, recv, .. } => {
            let bound = Ntfn(ptr).bound_tcb(s);
            if !recv || (bound != 0 && bound != t.0) {
                return cap_fault_recv(s, a, ep_cptr, missing);
            }
            notification::receive_signal(s, a, t, ptr, blocking);
        }
        _ => cap_fault_recv(s, a, ep_cptr, missing),
    }
}

/// seL4 `mcsPreemptionPoint`.
fn mcs_preemption_point<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    let ct = sched::cur_thread(s);
    if sched::is_schedulable(s, ct) {
        sched::check_budget(s, a);
    } else if sporadic::sc_active(s, sched::cur_sc(s)) {
        let c = sched::consumed(s);
        sched::charge_budget(s, a, c, false);
    } else {
        let cpu = s.cur_cpu();
        node_set(s, cpu, node::CONSUMED, 0);
    }
}

fn handle_yield<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    let csc = sched::cur_sc(s);
    let total = csc.consumed(s).wrapping_add(sched::consumed(s));
    let head = sporadic::head(s, csc);
    sched::charge_budget(s, a, head.amount, false);
    csc.set_consumed(s, total);
}

fn after_invocation<S: Store, A: Arch>(s: &mut S, a: &mut A, r: KResult<()>) -> bool {
    if r.is_err() {
        mcs_preemption_point(s, a);
        let irq = a.take_pending_irq();
        check_interrupt(s, a, irq);
        false
    } else {
        true
    }
}

fn check_interrupt<S: Store, A: Arch>(s: &mut S, a: &mut A, irq: u64) {
    if irq != NO_IRQ {
        interrupt::handle_interrupt(s, a, irq);
    }
}

/// `Arch::take_pending_irq` when no interrupt is pending.
pub const NO_IRQ: u64 = u64::MAX;

/// seL4 `handleSyscall` and `slowpath`: `number` is the syscall number
/// from RDX (as a signed value).
pub fn handle_syscall<S: Store, A: Arch>(s: &mut S, a: &mut A, number: i64) {
    let t = sched::cur_thread(s);
    // The syscall instruction is two bytes long.
    let next = t.reg(s, reg::NEXT_IP);
    t.set_reg(s, reg::FAULT_IP, next.wrapping_sub(2));
    // l4h 0001: a thread with trapSyscalls set never makes seL4 calls.
    if t.flags(s) & tcb_flag::TRAP_SYSCALLS != 0 {
        unknown_syscall_fault(s, a, number as u64);
        return;
    }
    if number < sc::SYSCALL_MIN || number > sc::SYSCALL_MAX {
        handle_unknown_syscall(s, a, number);
        return;
    }
    if budget_ok(s, a) {
        let t = sched::cur_thread(s);
        let cptr = t.reg(s, reg::CAP);
        let reply = t.reg(s, reg::REPLY);
        if number == sc::SysSend {
            let r = handle_invocation(s, a, false, true, false, false, cptr);
            after_invocation(s, a, r);
        } else if number == sc::SysNBSend {
            let r = handle_invocation(s, a, false, false, false, false, cptr);
            after_invocation(s, a, r);
        } else if number == sc::SysCall {
            let r = handle_invocation(s, a, true, true, true, false, cptr);
            after_invocation(s, a, r);
        } else if number == sc::SysRecv {
            handle_recv(s, a, true, true);
        } else if number == sc::SysNBRecv {
            handle_recv(s, a, false, true);
        } else if number == sc::SysWait {
            handle_recv(s, a, true, false);
        } else if number == sc::SysNBWait {
            handle_recv(s, a, false, false);
        } else if number == sc::SysReplyRecv {
            let r = handle_invocation(s, a, false, false, true, true, reply);
            if after_invocation(s, a, r) {
                handle_recv(s, a, true, true);
            }
        } else if number == sc::SysNBSendRecv {
            let dest = t.reg(s, reg::NBSEND_RECV_DEST);
            let r = handle_invocation(s, a, false, false, true, true, dest);
            if after_invocation(s, a, r) {
                handle_recv(s, a, true, true);
            }
        } else if number == sc::SysNBSendWait {
            let r = handle_invocation(s, a, false, false, true, true, reply);
            if after_invocation(s, a, r) {
                handle_recv(s, a, true, false);
            }
        } else if number == sc::SysYield {
            handle_yield(s, a);
        }
    }
    finish(s, a);
}

fn unknown_syscall_fault<S: Store, A: Arch>(s: &mut S, a: &mut A, number: u64) {
    if budget_ok(s, a) {
        let t = sched::cur_thread(s);
        if fl4_abi::config::SET_TLS_BASE_SELF && number as i64 == sc::SysSetTLSBase {
            let base = t.reg(s, reg::CAP);
            t.set_reg(s, reg::TLS_BASE, crate::regs::sanitise(reg::TLS_BASE, base));
        } else {
            faults::handle_fault(s, a, t, Fault::UnknownSyscall { number });
        }
    }
    finish(s, a);
}

/// Debug syscalls and everything else outside the API range
/// (seL4 `handleUnknownSyscall`).
fn handle_unknown_syscall<S: Store, A: Arch>(s: &mut S, a: &mut A, number: i64) {
    let t = sched::cur_thread(s);
    if fl4_abi::config::PRINTING && number == sc::SysDebugPutChar {
        let c = t.reg(s, reg::CAP);
        a.putc(c & 0xff);
        return;
    }
    if fl4_abi::config::PRINTING && number == sc::SysDebugDumpScheduler {
        return;
    }
    if fl4_abi::config::DEBUG_BUILD {
        if number == sc::SysDebugHalt {
            a.halt();
            return;
        }
        if number == sc::SysDebugSnapshot {
            return;
        }
        if number == sc::SysDebugCapIdentify {
            let cptr = t.reg(s, reg::CAP);
            let c = match cspace::lookup_cap_and_slot(s, t, cptr) {
                Ok((c, _)) => c,
                Err(_) => Cap::Null,
            };
            t.set_reg(s, reg::CAP, cap_type_code(c));
            return;
        }
        if number == sc::SysDebugNameThread {
            let cptr = t.reg(s, reg::CAP);
            let target = match cspace::lookup_cap_and_slot(s, t, cptr) {
                Ok((Cap::Thread { ptr }, _)) => Tcb(ptr),
                _ => {
                    a.halt();
                    return;
                }
            };
            let buf = msg::lookup_ipc_buffer(s, true, t);
            if buf == 0 {
                a.halt();
                return;
            }
            name_thread(s, target, buf.wrapping_add(8));
            return;
        }
        if fl4_abi::config::ENABLE_SMP_SUPPORT && number == sc::SysDebugGetThreadAffinity {
            let cptr = t.reg(s, reg::CAP);
            match cspace::lookup_cap_and_slot(s, t, cptr) {
                Ok((Cap::Thread { ptr }, _)) => {
                    let aff = Tcb(ptr).affinity(s);
                    t.set_reg(s, reg::CAP, aff);
                }
                _ => a.halt(),
            }
            return;
        }
        if fl4_abi::config::ENABLE_SMP_SUPPORT && number == sc::SysDebugSendIPI {
            return;
        }
    }
    unknown_syscall_fault(s, a, number as u64);
}

/// seL4 `cap_get_capType` numbering, as DebugCapIdentify reports it.
fn cap_type_code(c: Cap) -> u64 {
    match c {
        Cap::Null => 0,
        Cap::Untyped { .. } => 2,
        Cap::Endpoint { .. } => 4,
        Cap::Notification { .. } => 6,
        Cap::Reply { .. } => 8,
        Cap::CNode { .. } => 10,
        Cap::Thread { .. } => 12,
        Cap::IrqControl => 14,
        Cap::IrqHandler { .. } => 16,
        Cap::Zombie { .. } => 18,
        Cap::Domain => 20,
        Cap::SchedContext { .. } => 22,
        Cap::SchedControl { .. } => 24,
        Cap::Frame { .. } => 1,
        Cap::PageTable { .. } => 3,
        Cap::PageDirectory { .. } => 5,
        Cap::Pdpt { .. } => 7,
        Cap::Pml4 { .. } => 9,
        Cap::AsidControl => 11,
        Cap::AsidPool { .. } => 13,
        Cap::IoPort { .. } => 19,
        Cap::IoPortControl => 31,
    }
}

/// Copy a NUL-terminated name of at most 63 bytes into the TCB.
fn name_thread<S: Store>(s: &mut S, t: Tcb, src: u64) {
    let mut w = 0;
    let mut done = false;
    while w < 8 {
        let mut v = if done { 0 } else { s.read(src.wrapping_add(w * 8)) };
        if !done {
            let mut k = 0;
            while k < 8 {
                if (v >> (k * 8)) & 0xff == 0 {
                    done = true;
                    v &= if k == 0 { 0 } else { (1u64 << ((k * 8) & 63)).wrapping_sub(1) };
                    break;
                }
                k += 1;
            }
        }
        if w == 7 {
            v &= 0x00ff_ffff_ffff_ffff;
        }
        s.write(t.name_addr().wrapping_add(w * 8), v);
        w += 1;
    }
}

/// An interrupt arrived while user code ran (seL4 `handleInterruptEntry`).
pub fn handle_interrupt_entry<S: Store, A: Arch>(s: &mut S, a: &mut A, irq: u64) {
    sched::update_timestamp(s, a);
    sched::check_budget(s, a);
    interrupt::handle_interrupt(s, a, irq);
    finish(s, a);
}

/// A user-level exception other than page faults and debug traps
/// (seL4 `handleUserLevelFault`).
pub fn handle_user_exception<S: Store, A: Arch>(s: &mut S, a: &mut A, number: u64, code: u64) {
    if budget_ok(s, a) {
        let t = sched::cur_thread(s);
        faults::handle_fault(s, a, t, Fault::UserException { number, code });
    }
    finish(s, a);
}

/// A user page fault (seL4 `handleVMFaultEvent`).
pub fn handle_vm_fault<S: Store, A: Arch>(s: &mut S, a: &mut A, addr: u64, code: u64) {
    if budget_ok(s, a) {
        let t = sched::cur_thread(s);
        let instruction = (code >> 4) & 1 != 0;
        faults::handle_fault(s, a, t, vspace::vm_fault(addr, code, instruction));
    }
    finish(s, a);
}

/// `int $N` from user space on a gate it may use: seL4 reports this as an
/// unknown syscall whose number combines the vector and EAX.
pub fn handle_trap_syscall<S: Store, A: Arch>(s: &mut S, a: &mut A, vector: u64) {
    let t = sched::cur_thread(s);
    let ip = t.reg(s, reg::FAULT_IP).wrapping_sub(2);
    t.set_reg(s, reg::FAULT_IP, ip);
    let eax = t.reg(s, reg::RAX);
    let num = (vector << 24) | (eax & 0x00ff_ffff);
    handle_unknown_syscall(s, a, num as i64);
}

/// #DB and #BP with the hardware debug API.
pub fn handle_debug_exception<S: Store, A: Arch>(s: &mut S, a: &mut A, vector: u64, dr6: u64) {
    let t = sched::cur_thread(s);
    match debug::debug_exception(s, t, vector, dr6) {
        Some(f) => {
            faults::handle_fault(s, a, t, f);
            finish(s, a);
        }
        None => {}
    }
}
