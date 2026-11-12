//! Hardware debug API on x86 (seL4 arch/x86/machine/breakpoint.c). The
//! per-thread state is DR0-DR3 (slots 0-3), DR6 (4), DR7 (5), single-step
//! enabled (6) and the remaining single-step count (7); the exit path loads
//! it into the debug registers.

use crate::error::{Fault, KResult, SysError};
use crate::layout::reg;
use crate::machine::{Arch, Store};
use crate::obj::Tcb;

pub const DATA_BREAKPOINT: u64 = 0;
pub const INSTRUCTION_BREAKPOINT: u64 = 1;
pub const SINGLE_STEP: u64 = 2;
pub const SOFTWARE_BREAK_REQUEST: u64 = 3;

pub const BREAK_ON_READ: u64 = 0;
pub const BREAK_ON_WRITE: u64 = 1;
pub const BREAK_ON_READ_WRITE: u64 = 2;

pub const N_REGS: u64 = 4;

const DR6: u64 = 4;
const DR7: u64 = 5;
const SS_ENABLED: u64 = 6;
const SS_COUNT: u64 = 7;

const TYPE_INSTR: u64 = 0;
const TYPE_DATA_WRITE: u64 = 1;
const TYPE_DATA_READWRITE: u64 = 3;
const DR6_SINGLE_STEP: u64 = 1 << 14;
const EFLAGS_TF: u64 = 1 << 8;
const EFLAGS_RF: u64 = 1 << 16;

fn type_shift(bp: u64) -> u64 {
    16 + 4 * bp
}

fn size_shift(bp: u64) -> u64 {
    18 + 4 * bp
}

fn enable_bit(bp: u64) -> u64 {
    1u64 << (2 * bp + 1)
}

fn dr7<S: Store>(s: &S, t: Tcb) -> u64 {
    t.debug_reg(s, DR7)
}

fn set_dr7<S: Store>(s: &mut S, t: Tcb, v: u64) {
    t.set_debug_reg(s, DR7, v)
}

/// seL4 `Arch_initBreakpointContext` (DR6/DR7 hold their reserved bits).
pub fn init_context<S: Store>(s: &mut S, t: Tcb) {
    let mut i = 0;
    while i < 8 {
        t.set_debug_reg(s, i, 0);
        i += 1;
    }
    t.set_debug_reg(s, DR6, 0xffff_0ff0);
    t.set_debug_reg(s, DR7, 0x400);
}

pub fn set_breakpoint<S: Store>(s: &mut S, t: Tcb, bp: u64, vaddr: u64, ty: u64, size: u64, rw: u64) {
    let arch_type = if ty == INSTRUCTION_BREAKPOINT {
        TYPE_INSTR
    } else if rw == BREAK_ON_WRITE {
        TYPE_DATA_WRITE
    } else {
        TYPE_DATA_READWRITE
    };
    let arch_size = if ty == INSTRUCTION_BREAKPOINT {
        0
    } else if size == 1 {
        0
    } else if size == 2 {
        1
    } else if size == 8 {
        2
    } else {
        3
    };
    t.set_debug_reg(s, bp, vaddr);
    let mut v = dr7(s, t) & !((3u64 << size_shift(bp)) | (3u64 << type_shift(bp)));
    v |= (arch_type << type_shift(bp)) | (arch_size << size_shift(bp)) | enable_bit(bp);
    set_dr7(s, t, v);
}

pub struct Breakpoint {
    pub vaddr: u64,
    pub ty: u64,
    pub size: u64,
    pub rw: u64,
    pub enabled: bool,
}

fn type_and_access(dr7v: u64, bp: u64) -> (u64, u64) {
    let t = (dr7v >> type_shift(bp)) & 3;
    if t == TYPE_INSTR {
        (INSTRUCTION_BREAKPOINT, BREAK_ON_READ)
    } else if t == TYPE_DATA_WRITE {
        (DATA_BREAKPOINT, BREAK_ON_WRITE)
    } else {
        (DATA_BREAKPOINT, BREAK_ON_READ_WRITE)
    }
}

pub fn get_breakpoint<S: Store>(s: &S, t: Tcb, bp: u64) -> Breakpoint {
    let v = dr7(s, t);
    let (ty, rw) = type_and_access(v, bp);
    let size = if (v >> type_shift(bp)) & 3 == TYPE_INSTR {
        0
    } else {
        let sz = (v >> size_shift(bp)) & 3;
        if sz == 0 {
            1
        } else if sz == 1 {
            2
        } else if sz == 2 {
            8
        } else {
            4
        }
    };
    Breakpoint { vaddr: t.debug_reg(s, bp), ty, size, rw, enabled: v & enable_bit(bp) != 0 }
}

pub fn unset_breakpoint<S: Store>(s: &mut S, t: Tcb, bp: u64) {
    let v = dr7(s, t) & !enable_bit(bp) & !((3u64 << size_shift(bp)) | (3u64 << type_shift(bp)));
    set_dr7(s, t, v);
    t.set_debug_reg(s, bp, 0);
}

/// seL4 `configureSingleStepping`.
pub fn configure_single_stepping<S: Store, A: Arch>(s: &mut S, a: &mut A, t: Tcb, bp: u64, n_instr: u64, is_reply: bool) -> bool {
    let _ = (a, bp, is_reply);
    if n_instr == 0 {
        t.set_debug_reg(s, SS_ENABLED, 0);
        let f = t.reg(s, reg::FLAGS) & !EFLAGS_TF;
        t.set_reg(s, reg::FLAGS, f);
    } else {
        t.set_debug_reg(s, SS_ENABLED, 1);
    }
    t.set_debug_reg(s, SS_COUNT, n_instr);
    false
}

pub fn single_step_enabled<S: Store>(s: &S, t: Tcb) -> bool {
    t.debug_reg(s, SS_ENABLED) != 0
}

/// Checks shared by the breakpoint decoders (seL4 tcb.c and the x86
/// `Arch_decode*Breakpoint` helpers).
pub fn check_bp_num(bp: u64) -> KResult<()> {
    if bp >= N_REGS {
        return Err(crate::error::Exc::Sys(SysError::RangeError { min: 0, max: 3 }));
    }
    Ok(())
}

/// seL4 `handleUserLevelDebugException`: decide the fault, or None when a
/// single-step count has not run out yet.
pub fn debug_exception<S: Store>(s: &mut S, t: Tcb, vector: u64, dr6: u64) -> Option<Fault> {
    if vector == 3 {
        let pc = t.reg(s, reg::FAULT_IP);
        return Some(Fault::Debug { reason: SOFTWARE_BREAK_REQUEST, addr: pc, bp: 0 });
    }
    let mut bp: u64 = 4;
    let mut i = 0;
    while i < 4 {
        if dr6 & (1u64 << i) != 0 {
            bp = i;
            break;
        }
        i += 1;
    }
    if bp < 4 {
        let (ty, _) = type_and_access(dr7(s, t), bp);
        let vaddr = t.debug_reg(s, bp);
        return Some(Fault::Debug { reason: ty, addr: vaddr, bp });
    }
    if dr6 & DR6_SINGLE_STEP != 0 {
        let pc = t.reg(s, reg::FAULT_IP);
        let f = t.reg(s, reg::FLAGS) | EFLAGS_RF;
        t.set_reg(s, reg::FLAGS, f);
        let n = t.debug_reg(s, SS_COUNT);
        let n = if n > 0 { n - 1 } else { 0 };
        t.set_debug_reg(s, SS_COUNT, n);
        if n != 0 {
            return None;
        }
        return Some(Fault::Debug { reason: SINGLE_STEP, addr: pc, bp: 0 });
    }
    None
}
