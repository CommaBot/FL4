//! User register rules for AArch64 (seL4 arch/arm/64 registerset.c and
//! mode/kernel/thread.h).

use crate::layout::reg;
use crate::machine::Store;
use crate::obj::Tcb;

/// SPSR_EL1 bits a thread runs with: EL0t, FIQ and SError masked
/// (seL4 `PSTATE_USER`).
pub const PSTATE_USER: u64 = (1 << 6) | (1 << 8);
/// The condition flags, the only SPSR bits a thread chooses.
const PSTATE_FLAGS: u64 = 0xf000_0000;

/// seL4 `sanitiseRegister` without EL2: user code always runs at EL0t
/// with FIQ and SError masked and IRQs enabled.
pub fn sanitise(r: u64, v: u64) -> u64 {
    if r == reg::SPSR_EL1 {
        (v & PSTATE_FLAGS) | PSTATE_USER
    } else {
        v
    }
}

/// seL4 `Arch_initContext`.
pub fn init_context<S: Store>(s: &mut S, t: Tcb) {
    let mut i = 0;
    while i < reg::COUNT {
        t.set_reg(s, i, 0);
        i += 1;
    }
    t.set_reg(s, reg::SPSR_EL1, PSTATE_USER);
}

/// `frameRegisters` and `gpRegisters`: the order of seL4_UserContext.
pub const FRAME_REGISTERS: [u64; 17] = [
    reg::FAULT_IP,
    reg::SP_EL0,
    reg::SPSR_EL1,
    reg::X0,
    reg::X1,
    reg::X2,
    reg::X3,
    reg::X4,
    reg::X5,
    reg::X6,
    reg::X7,
    reg::X8,
    reg::X16,
    reg::X17,
    reg::X18,
    reg::X29,
    reg::X30,
];
pub const GP_REGISTERS: [u64; 19] = [
    reg::X9,
    reg::X10,
    reg::X11,
    reg::X12,
    reg::X13,
    reg::X14,
    reg::X15,
    reg::X19,
    reg::X20,
    reg::X21,
    reg::X22,
    reg::X23,
    reg::X24,
    reg::X25,
    reg::X26,
    reg::X27,
    reg::X28,
    reg::TPIDR_EL0,
    reg::TPIDRRO_EL0,
];
