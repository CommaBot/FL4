//! User register rules for x86_64 (seL4 arch/x86 registerset.c, thread.c).

use crate::layout::reg;
use crate::machine::Store;
use crate::obj::Tcb;

pub const FLAGS_TF: u64 = 1 << 8;
pub const FLAGS_IF: u64 = 1 << 9;
const FLAGS_HIGH: u64 = 1 << 1;
const FLAGS_LOW: u64 = (1 << 3) | (1 << 5);
const FLAGS_MASK: u64 = (1 << 12) - 1;
pub const FLAGS_USER_DEFAULT: u64 = FLAGS_IF | FLAGS_HIGH;

/// User selectors in the Linux layout (l4h 0028): SYSRET and IRET load the
/// same values.
pub const SEL_CS_3: u64 = 0x33;
pub const SEL_DS_3: u64 = 0x2b;

/// seL4 `sanitiseRegister`.
pub fn sanitise(r: u64, v: u64) -> u64 {
    let mut v = v;
    if r == reg::FAULT_IP || r == reg::NEXT_IP || r == reg::FS_BASE || r == reg::GS_BASE {
        if v > 0x0000_7fff_ffff_ffff && v < 0xffff_8000_0000_0000 {
            v = 0;
        }
    }
    if r == reg::FLAGS {
        v |= FLAGS_HIGH;
        v &= !FLAGS_LOW;
        v |= FLAGS_IF;
        v &= !FLAGS_TF;
        v &= FLAGS_MASK;
    }
    v
}

/// seL4 `Arch_initContext`.
pub fn init_context<S: Store>(s: &mut S, t: Tcb) {
    let mut i = 0;
    while i < reg::COUNT {
        t.set_reg(s, i, 0);
        i += 1;
    }
    t.set_reg(s, reg::CS, SEL_CS_3);
    t.set_reg(s, reg::FLAGS, FLAGS_USER_DEFAULT);
    t.set_reg(s, reg::SS, SEL_DS_3);
}

/// `frameRegisters` and `gpRegisters`: the order of seL4_UserContext.
pub const FRAME_REGISTERS: [u64; 18] = [
    reg::FAULT_IP,
    reg::RSP,
    reg::FLAGS,
    reg::RAX,
    reg::RBX,
    reg::RCX,
    reg::RDX,
    reg::RSI,
    reg::RDI,
    reg::RBP,
    reg::R8,
    reg::R9,
    reg::R10,
    reg::R11,
    reg::R12,
    reg::R13,
    reg::R14,
    reg::R15,
];
pub const GP_REGISTERS: [u64; 2] = [reg::FS_BASE, reg::GS_BASE];
