//! Speculative-execution mitigations, each on exactly when the CPU needs
//! it (DESIGN.md §3).
//!
//! - Meltdown (rogue data cache load): the skim window, on Intel CPUs that
//!   do not report RDCL_NO in IA32_ARCH_CAPABILITIES (or have no such MSR).
//!   User address spaces then map only the kernel image, not the window
//!   onto physical memory, and every entry switches to the kernel's tables.
//! - Spectre v2 against the kernel: enhanced IBRS (Intel, IBRS_ALL) or
//!   automatic IBRS (AMD), set once per core when the CPU has it.
//!
//! IBPB on context switch is not used: it guards user programs against
//! each other through the branch predictor at thousands of cycles per
//! switch between address spaces, and, as in seL4's default
//! configuration, that threat is outside FL4's model for now.
use crate::cpu::{cpuid, msr, rdmsr, wrmsr};
use core::sync::atomic::{AtomicBool, Ordering};

const MSR_ARCH_CAPABILITIES: u32 = 0x10a;
const MSR_SPEC_CTRL: u32 = 0x48;
const ARCH_CAP_RDCL_NO: u64 = 1 << 0;
const ARCH_CAP_IBRS_ALL: u64 = 1 << 1;
const SPEC_CTRL_IBRS: u64 = 1 << 0;
const EFER_AIBRSE: u64 = 1 << 21;

static SKIM: AtomicBool = AtomicBool::new(false);
static EIBRS: AtomicBool = AtomicBool::new(false);
static AUTO_IBRS: AtomicBool = AtomicBool::new(false);

fn is_intel() -> bool {
    let v = cpuid(0, 0);
    v.ebx == 0x756e_6547 && v.edx == 0x4965_6e69 && v.ecx == 0x6c65_746e
}

fn arch_capabilities() -> Option<u64> {
    if cpuid(0, 0).eax >= 7 && cpuid(7, 0).edx & (1 << 29) != 0 {
        Some(rdmsr(MSR_ARCH_CAPABILITIES))
    } else {
        None
    }
}

/// Decide the mitigations on the boot core.
pub fn detect() {
    let caps = arch_capabilities();
    let intel = is_intel();
    let rdcl_no = caps.is_some_and(|c| c & ARCH_CAP_RDCL_NO != 0);
    SKIM.store(intel && !rdcl_no, Ordering::Relaxed);
    EIBRS.store(caps.is_some_and(|c| c & ARCH_CAP_IBRS_ALL != 0), Ordering::Relaxed);
    let amd_auto = cpuid(0x8000_0000, 0).eax >= 0x8000_0021 && cpuid(0x8000_0021, 0).eax & (1 << 8) != 0;
    AUTO_IBRS.store(amd_auto, Ordering::Relaxed);
}

/// Turn on this core's per-core mitigations.
pub fn init_core() {
    if EIBRS.load(Ordering::Relaxed) {
        wrmsr(MSR_SPEC_CTRL, rdmsr(MSR_SPEC_CTRL) | SPEC_CTRL_IBRS);
    }
    if AUTO_IBRS.load(Ordering::Relaxed) {
        wrmsr(msr::EFER, rdmsr(msr::EFER) | EFER_AIBRSE);
    }
}

/// The skim window is in use.
pub fn skim() -> bool {
    SKIM.load(Ordering::Relaxed)
}

/// For the boot banner.
pub fn describe() -> &'static str {
    match (skim(), EIBRS.load(Ordering::Relaxed), AUTO_IBRS.load(Ordering::Relaxed)) {
        (true, true, _) => "skim window, enhanced IBRS",
        (true, false, _) => "skim window",
        (false, true, _) => "enhanced IBRS",
        (false, false, true) => "automatic IBRS",
        (false, false, false) => "none needed",
    }
}
