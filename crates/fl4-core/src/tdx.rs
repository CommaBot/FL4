//! Intel TDX attestation: `seL4_X86_TdxControl` (FL4 extension). The cap
//! exists only in a TDX guest, in slot `seL4_CapX86TdxControl` of the root
//! CNode. It can be copied or moved to the task that handles attestation.
//! Every check is here, before the backend runs the TDCALL.

use crate::capability::{Cap, FrameSize, VM_READ_WRITE};
use crate::error::{illegal, invalid_arg, invalid_cap, truncated, KResult};
use crate::layout::reg;
use crate::machine::{Arch, Store};
use crate::msg;
use crate::msginfo::MessageInfo;
use crate::obj::{Slot, Tcb};
use crate::sched;
use fl4_abi::label;

/// The largest RTMR index.
const RTMR_MAX: u64 = 3;
const PAGE: u64 = 4096;

/// The address of a writable private 4 KiB frame, which alone may receive
/// a TDREPORT: the VMM can read anything else.
fn report_frame(c: Cap) -> Option<u64> {
    match c {
        Cap::Frame { ptr, size: FrameSize::Small, rights, is_device: false, .. } => {
            if rights == VM_READ_WRITE {
                Some(ptr)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// The address and size of a writable frame from RetypeShared, which alone
/// may hold a quote buffer: its GPA goes to the VMM with the shared bit set.
fn quote_frame<A: Arch>(a: &A, c: Cap) -> Option<(u64, u64)> {
    match c {
        Cap::Frame { ptr, size, rights, is_device: true, .. } => {
            let bytes = match size {
                FrameSize::Small => 0x1000,
                FrameSize::Large => 0x20_0000,
                FrameSize::Huge => return None,
            };
            if rights == VM_READ_WRITE && a.dma_ram(ptr, bytes) {
                Some((ptr, bytes))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// A quote buffer's length: whole pages, at least one, within the frame.
fn quote_len_ok(buf_len: u64, frame_bytes: u64) -> bool {
    // A literal result: Aeneas types a boolean whose last operand is a
    // comparison as a Lean Prop.
    if buf_len >= PAGE && buf_len & (PAGE - 1) == 0 && buf_len <= frame_bytes {
        true
    } else {
        false
    }
}

/// Finish an invocation whose result is one word.
fn reply<S: Store>(s: &mut S, ct: Tcb, call: bool, status: u64) {
    if call {
        let b = msg::lookup_ipc_buffer(s, true, ct);
        ct.set_reg(s, reg::BADGE, 0);
        let n = msg::set_mr(s, ct, b, 0, status);
        msg::set_msg_info(s, ct, MessageInfo::new(0, 0, 0, n));
    }
    sched::set_thread_state(s, ct, sched::TS_RUNNING);
}

fn get_report<S: Store, A: Arch>(s: &mut S, a: &mut A, length: u64, call: bool, buf: u64, extra: &[Slot; 3]) -> KResult<()> {
    if length < 8 || extra[0].is_null() {
        return truncated();
    }
    let frame = match report_frame(extra[0].cap(s)) {
        Some(p) => p,
        None => return invalid_cap(1),
    };
    let ct = sched::cur_thread(s);
    let d0 = msg::syscall_arg(s, ct, buf, 0);
    let d1 = msg::syscall_arg(s, ct, buf, 1);
    let d2 = msg::syscall_arg(s, ct, buf, 2);
    let d3 = msg::syscall_arg(s, ct, buf, 3);
    let d4 = msg::syscall_arg(s, ct, buf, 4);
    let d5 = msg::syscall_arg(s, ct, buf, 5);
    let d6 = msg::syscall_arg(s, ct, buf, 6);
    let d7 = msg::syscall_arg(s, ct, buf, 7);
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    let status = a.tdx_report(frame, d0, d1, d2, d3, d4, d5, d6, d7);
    reply(s, ct, call, status);
    Ok(())
}

fn extend_rtmr<S: Store, A: Arch>(s: &mut S, a: &mut A, length: u64, call: bool, buf: u64) -> KResult<()> {
    if length < 7 {
        return truncated();
    }
    let ct = sched::cur_thread(s);
    let index = msg::syscall_arg(s, ct, buf, 0);
    if index > RTMR_MAX {
        return invalid_arg(0);
    }
    let d0 = msg::syscall_arg(s, ct, buf, 1);
    let d1 = msg::syscall_arg(s, ct, buf, 2);
    let d2 = msg::syscall_arg(s, ct, buf, 3);
    let d3 = msg::syscall_arg(s, ct, buf, 4);
    let d4 = msg::syscall_arg(s, ct, buf, 5);
    let d5 = msg::syscall_arg(s, ct, buf, 6);
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    let status = a.tdx_extend_rtmr(index, d0, d1, d2, d3, d4, d5);
    reply(s, ct, call, status);
    Ok(())
}

fn get_quote<S: Store, A: Arch>(s: &mut S, a: &mut A, length: u64, call: bool, buf: u64, extra: &[Slot; 3]) -> KResult<()> {
    if length < 1 || extra[0].is_null() {
        return truncated();
    }
    let (frame, bytes) = match quote_frame(a, extra[0].cap(s)) {
        Some(f) => f,
        None => return invalid_cap(1),
    };
    let ct = sched::cur_thread(s);
    let buf_len = msg::syscall_arg(s, ct, buf, 0);
    if !quote_len_ok(buf_len, bytes) {
        return invalid_arg(0);
    }
    sched::set_thread_state(s, ct, sched::TS_RESTART);
    let status = a.tdx_get_quote(frame, buf_len);
    reply(s, ct, call, status);
    Ok(())
}

/// An invocation of a `Cap::TdxControl`.
pub fn decode<S: Store, A: Arch>(s: &mut S, a: &mut A, lbl: u64, length: u64, call: bool, buf: u64, extra: &[Slot; 3]) -> KResult<()> {
    if !a.tdx_active() {
        return illegal();
    }
    if lbl == label::X86TdxControlGetReport {
        get_report(s, a, length, call, buf, extra)
    } else if lbl == label::X86TdxControlExtendRTMR {
        extend_rtmr(s, a, length, call, buf)
    } else if lbl == label::X86TdxControlGetQuote {
        get_quote(s, a, length, call, buf, extra)
    } else {
        illegal()
    }
}
