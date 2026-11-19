// The kernel is a freestanding staticlib; exercise its decision on the
// bench profile's MSR syscalls in the backend's host-test harness.
#[allow(dead_code)]
#[path = "../../fl4-kernel/src/dangerous_msr.rs"]
mod dangerous_msr;

use dangerous_msr::{call, Call};
use fl4_abi::consts::tcb_flag::{FPU_DISABLED, TRAP_SYSCALLS};

/// seL4's numbers for the calls in a `KernelX86DangerousMSR` build.
const RD: i64 = -12;
const WR: i64 = -13;
const N: (i64, i64) = (RD, WR);

#[test]
fn msr_calls_are_answered_only_when_enabled() {
    assert_eq!(call(true, RD, 0, N), Some(Call::Read));
    assert_eq!(call(true, WR, 0, N), Some(Call::Write));
    assert_eq!(call(true, WR, FPU_DISABLED, N), Some(Call::Write));
    for n in [RD, WR] {
        assert_eq!(call(false, n, 0, N), None);
    }
    // Any other syscall takes the ordinary path.
    for n in [-1, -11, -14, 0, 7, i64::MIN, i64::MAX] {
        assert_eq!(call(true, n, 0, N), None, "{n}");
    }
}

/// Audit F4: a thread with trapSyscalls (l4h 0001) never reaches the MSR
/// fast path, so its syscall faults to its supervisor as UnknownSyscall
/// whatever its registers say.
#[test]
fn trap_syscalls_threads_never_reach_the_msr_fast_path() {
    for flags in [TRAP_SYSCALLS, TRAP_SYSCALLS | FPU_DISABLED] {
        for n in [RD, WR, -1, 0] {
            assert_eq!(call(true, n, flags, N), None, "flags {flags:#x} syscall {n}");
            assert_eq!(call(false, n, flags, N), None);
        }
    }
}

/// This configuration's numbers: the default build has no MSR calls.
#[test]
fn the_default_configuration_has_no_msr_calls() {
    if !fl4_abi::config::KERNEL_X86_DANGEROUS_MSR {
        for n in [RD, WR, i64::MIN] {
            assert_eq!(dangerous_msr::of(n, 0), None);
        }
    }
}
