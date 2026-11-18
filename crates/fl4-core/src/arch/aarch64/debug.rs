//! The hardware debug API on AArch64 is not implemented: FL4's AArch64
//! build has `KernelHardwareDebugAPI` off (the CMake drop-in enforces it),
//! so no invocation reaches these functions and BRK traps arrive as user
//! exceptions. They keep the interface the shared TCB and fault code uses.

use crate::error::{Fault, KResult, SysError};
use crate::machine::{Arch, Store};
use crate::obj::Tcb;

pub const DATA_BREAKPOINT: u64 = 0;
pub const INSTRUCTION_BREAKPOINT: u64 = 1;
pub const SINGLE_STEP: u64 = 2;
pub const SOFTWARE_BREAK_REQUEST: u64 = 3;

pub const BREAK_ON_READ: u64 = 0;
pub const BREAK_ON_WRITE: u64 = 1;
pub const BREAK_ON_READ_WRITE: u64 = 2;

pub const N_REGS: u64 = 0;

pub fn init_context<S: Store>(s: &mut S, t: Tcb) {
    let _ = (s, t);
}

pub fn set_breakpoint<S: Store>(s: &mut S, t: Tcb, bp: u64, vaddr: u64, ty: u64, size: u64, rw: u64) {
    let _ = (s, t, bp, vaddr, ty, size, rw);
}

pub struct Breakpoint {
    pub vaddr: u64,
    pub ty: u64,
    pub size: u64,
    pub rw: u64,
    pub enabled: bool,
}

pub fn get_breakpoint<S: Store>(s: &S, t: Tcb, bp: u64) -> Breakpoint {
    let _ = (s, t, bp);
    Breakpoint { vaddr: 0, ty: 0, size: 0, rw: 0, enabled: false }
}

pub fn unset_breakpoint<S: Store>(s: &mut S, t: Tcb, bp: u64) {
    let _ = (s, t, bp);
}

pub fn configure_single_stepping<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb, bp: u64, n_instr: u64, is_reply: bool) -> bool {
    let _ = (s, a, t, bp, n_instr, is_reply);
    false
}

pub fn single_step_enabled<S: Store>(s: &S, t: Tcb) -> bool {
    let _ = (s, t);
    false
}

pub fn check_bp_num(bp: u64) -> KResult<()> {
    let _ = bp;
    Err(crate::error::Exc::Sys(SysError::IllegalOperation))
}

pub fn debug_exception<S: Store>(s: &mut S, t: Tcb, vector: u64, dr6: u64) -> Option<Fault> {
    let _ = (s, t, vector, dr6);
    None
}
