//! The confidential guest's check of a kernel-mode entry that landed on an
//! IST (entry.rs `fl4_cvm_kernel_entry_stack`). Free of hardware access, so
//! the backend's host tests run it (fl4-arch-x86_64/tests/kernel_cvm_entry.rs).
//!
//! An IST always lands at a fixed stack top: if the interrupted RSP was in
//! that IST, the fresh frame overwrote a live one. But in two places the
//! kernel runs in ring 0 on the user's RSP, which user code chooses freely
//! (entry.S): from `fl4_syscall_entry` until it loads the entry stack
//! (`fl4_syscall_on_stack`), and on the SYSRET path from loading the user's
//! RSP (`fl4_sysret_user_rsp`) through SYSRETQ (`fl4_sysret_end`). An RSP
//! that points into an IST there is no kernel frame, and taking it for one
//! would let user code end the whole guest.

use core::ops::Range;

const VEC_DB: u64 = 1;
const VEC_NMI: u64 = 2;
const VEC_MC: u64 = 18;
const RFLAGS_IF: u64 = 1 << 9;

/// Whether an entry from kernel mode on `vector` at `rip` interrupted the
/// kernel while RSP was the user's: `syscall` is `[fl4_syscall_entry,
/// fl4_syscall_on_stack)`, `sysret` `[fl4_sysret_user_rsp, fl4_sysret_end)`.
///
/// - #DB only at the first instruction of the SYSCALL entry: a
///   single-stepped SYSCALL, or a MOV SS / POP SS data breakpoint the CPU
///   held until after it (CVE-2018-8897; entry.rs `deferred_user_debug`).
///   FMASK clears TF, and the thread's breakpoints are below `USER_TOP`, so
///   no #DB can come later in either window.
/// - NMI and #MC anywhere in either window: they are asynchronous.
/// - Nothing else: no other exception, nor any interrupt (IF is clear in
///   both windows), can arrive there.
pub fn user_rsp_window(vector: u64, rip: u64, syscall: Range<u64>, sysret: Range<u64>) -> bool {
    match vector {
        VEC_DB => !syscall.is_empty() && rip == syscall.start,
        VEC_NMI | VEC_MC => syscall.contains(&rip) || sysret.contains(&rip),
        _ => false,
    }
}

/// The verdict on such an entry, as `(ist_overlap, if_clear)`; either one
/// makes the frame usable for termination only. `ist_overlap`: the
/// interrupted RSP is in `stack`, the IST the entry landed on, and is no
/// user RSP (`user_rsp_window`). `if_clear`: an interrupt taken with IF
/// clear, including after a switch to another IST.
pub fn invalid_entry(
    vector: u64,
    rip: u64,
    rsp: u64,
    rflags: u64,
    stack: Range<u64>,
    syscall: Range<u64>,
    sysret: Range<u64>,
) -> (bool, bool) {
    let ist_overlap = !user_rsp_window(vector, rip, syscall, sysret) && stack.contains(&rsp);
    let if_clear = vector >= 32 && rflags & RFLAGS_IF == 0;
    (ist_overlap, if_clear)
}
