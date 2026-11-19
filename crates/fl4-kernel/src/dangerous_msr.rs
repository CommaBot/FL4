//! The bench profile's MSR syscalls (`KernelX86DangerousMSR`, DESIGN.md
//! §3), answered in the entry outside the core: which call a syscall is.
//! No hardware access, so the backend's host tests run it
//! (fl4-arch-x86_64 tests/kernel_dangerous_msr.rs).

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Call {
    Read,
    Write,
}

/// The MSR call syscall `number` makes for a thread with TCB `flags`, in
/// a kernel with the calls `enabled`; `numbers` are SysX86DangerousRDMSR
/// and SysX86DangerousWRMSR. None: the syscall takes the ordinary path.
pub fn call(enabled: bool, number: i64, flags: u64, numbers: (i64, i64)) -> Option<Call> {
    if !enabled || flags & fl4_abi::consts::tcb_flag::TRAP_SYSCALLS != 0 {
        None
    } else if number == numbers.0 {
        Some(Call::Read)
    } else if number == numbers.1 {
        Some(Call::Write)
    } else {
        None
    }
}

/// `call` with this configuration's syscall numbers.
pub fn of(number: i64, flags: u64) -> Option<Call> {
    call(
        fl4_abi::config::KERNEL_X86_DANGEROUS_MSR,
        number,
        flags,
        (fl4_abi::syscall::SysX86DangerousRDMSR, fl4_abi::syscall::SysX86DangerousWRMSR),
    )
}
