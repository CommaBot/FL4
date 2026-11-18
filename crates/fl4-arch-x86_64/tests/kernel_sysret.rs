//! The kernel's choice between SYSRET and IRET on the way out to a thread
//! (fl4-kernel sysret.S, used by entry.S `fl4_restore_user`), run on the
//! host on register arrays in fl4_core::layout::reg order.
#![cfg(target_arch = "x86_64")]

use fl4_core::layout::reg;

core::arch::global_asm!(
    include_str!("../../fl4-kernel/src/sysret.S"),
    ".text
    .global fl4_test_sysret_check
fl4_test_sysret_check:
    fl4_sysret_check %rdi, %rcx, 1f
    movl $1, %eax
    ret
1:
    xorl %eax, %eax
    ret",
    options(att_syntax)
);

extern "C" {
    fn fl4_test_sysret_check(regs: *const u64) -> u64;
}

fn sysret(regs: &[u64; reg::COUNT as usize]) -> bool {
    unsafe { fl4_test_sysret_check(regs.as_ptr()) == 1 }
}

/// A context as SYSCALL saved it (entry.rs `save_user`): RCX holds the
/// return address and R11 the flags, as in NextIP and FLAGS.
fn syscall_context() -> [u64; reg::COUNT as usize] {
    let mut r: [u64; reg::COUNT as usize] = core::array::from_fn(|i| 0x1111 * (i as u64 + 1));
    r[reg::ERROR as usize] = u64::MAX;
    r[reg::NEXT_IP as usize] = 0x40_1002;
    r[reg::RCX as usize] = 0x40_1002;
    r[reg::FLAGS as usize] = 0x246;
    r[reg::R11 as usize] = 0x246;
    r
}

#[test]
fn a_syscall_context_leaves_by_sysret() {
    assert!(sysret(&syscall_context()));
    let mut r = syscall_context();
    r[reg::NEXT_IP as usize] = 0x7fff_ffff_f000;
    r[reg::RCX as usize] = 0x7fff_ffff_f000;
    r[reg::FLAGS as usize] = 0x4_0a97;
    r[reg::R11 as usize] = 0x4_0a97;
    assert!(sysret(&r));
}

#[test]
fn changed_rcx_r11_or_return_address_leave_by_iret() {
    // A fault reply (UnknownSyscall, Timeout) or TCB_CopyRegisters to the
    // thread itself sets RCX or R11 and leaves Error at -1: SYSRET would
    // overwrite them with NextIP and FLAGS.
    for (i, v) in [
        (reg::RCX, 0xdead),
        (reg::R11, 0x202),
        (reg::NEXT_IP, 0x40_1000),
        (reg::FLAGS, 0x202),
    ] {
        let mut r = syscall_context();
        r[i as usize] = v;
        assert!(!sysret(&r), "register {i} changed");
    }
}

#[test]
fn other_contexts_leave_by_iret() {
    let mut r = syscall_context();
    r[reg::ERROR as usize] = 0;
    assert!(!sysret(&r));
    // Non-canonical or kernel-half return addresses.
    for ip in [0x8000_0000_0000, 0xffff_8000_0000_0000, u64::MAX] {
        let mut r = syscall_context();
        r[reg::NEXT_IP as usize] = ip;
        r[reg::RCX as usize] = ip;
        assert!(!sysret(&r), "{ip:#x}");
    }
    // TF (single-stepping, entry.rs `load_debug_state`) and RF.
    for f in [0x100, 0x1_0000, 0x1_0100] {
        let mut r = syscall_context();
        r[reg::FLAGS as usize] |= f;
        r[reg::R11 as usize] |= f;
        assert!(!sysret(&r), "{f:#x}");
    }
}
