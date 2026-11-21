//! User register rules for AArch64 (seL4 arch/arm/64 registerset.c and
//! mode/kernel/thread.h).

use crate::layout::reg;
use crate::machine::Store;
use crate::obj::Tcb;

/// SPSR_EL1 bits a thread runs with: EL0t, FIQ and SError masked
/// (seL4 `PSTATE_USER`).
pub const PSTATE_USER: u64 = (1 << 6) | (1 << 8);
/// The condition flags, the only SPSR bits a native EL0 thread chooses.
const PSTATE_FLAGS: u64 = 0xf000_0000;
/// PSTATE bits a VCPU-bound thread may choose (excluding M[4:0]):
/// NZCV | TCO | DIT | UAO | PAN | SS | IL | SSBS | BTYPE | DAIF.
const VCPU_PSTATE_ALLOWED: u64 = (0xf << 28)
    | (1 << 25)
    | (1 << 24)
    | (1 << 23)
    | (1 << 22)
    | (1 << 21)
    | (1 << 20)
    | (1 << 12)
    | (0x3 << 10)
    | (0xf << 6);

/// seL4 `sanitiseRegister` for native EL0 threads: user code always runs at
/// EL0t with FIQ and SError masked and IRQs enabled.
pub fn sanitise(r: u64, v: u64) -> u64 {
    if r == reg::SPSR_EL1 {
        (v & PSTATE_FLAGS) | PSTATE_USER
    } else {
        v
    }
}

/// Sanitise `SPSR_EL1` for a VCPU-bound thread: allows EL0t (0x0), EL1t (0x4),
/// and EL1h (0x5) with legal PSTATE bits; illegal modes (EL2/EL3/AArch32)
/// are forced to EL1h (0x5).
pub fn sanitise_vcpu_spsr(v: u64) -> u64 {
    let m = v & 0x1f;
    let mode = if m == 0x0 || m == 0x4 || m == 0x5 { m } else { 0x5 };
    (v & VCPU_PSTATE_ALLOWED) | mode
}

/// Sanitise register `r` for `t`: VCPU-bound threads may run in EL0t/EL1t/EL1h;
/// native threads are restricted to EL0t.
pub fn sanitise_for_tcb<S: Store>(s: &S, t: Tcb, r: u64, v: u64) -> u64 {
    if r == reg::SPSR_EL1 && crate::vcpu::bound(s, t) != 0 {
        sanitise_vcpu_spsr(v)
    } else {
        sanitise(r, v)
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
