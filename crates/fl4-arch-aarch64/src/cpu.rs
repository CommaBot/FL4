//! AArch64 system registers, barriers and cache maintenance.
use core::arch::asm;
use core::sync::atomic::{AtomicBool, Ordering};

/// Read a system register by name.
#[macro_export]
macro_rules! mrs {
    ($r:literal) => {{
        let v: u64;
        unsafe { core::arch::asm!(concat!("mrs {}, ", $r), out(reg) v, options(nomem, nostack, preserves_flags)) };
        v
    }};
}

/// Write a system register by name.
#[macro_export]
macro_rules! msr {
    ($r:literal, $v:expr) => {{
        let v: u64 = $v;
        unsafe { core::arch::asm!(concat!("msr ", $r, ", {}"), in(reg) v, options(nostack, preserves_flags)) };
    }};
}

/// Whether the kernel is running in EL2 (VHE host mode). Initialized once
/// on the boot core from `CurrentEL`.
static EL2_HOST: AtomicBool = AtomicBool::new(false);

/// Current exception level (0..=3).
#[inline]
pub fn current_el() -> u64 {
    (mrs!("CurrentEL") >> 2) & 0x3
}

/// Record whether the kernel booted and stayed at EL2. Call once at boot
/// before `percpu::init`.
pub fn init_el_mode() {
    EL2_HOST.store(current_el() == 2, Ordering::Relaxed);
}

/// Whether the kernel runs in EL2 VHE host mode.
#[inline]
pub fn is_el2() -> bool {
    EL2_HOST.load(Ordering::Relaxed)
}

#[inline(always)]
pub fn isb() {
    unsafe { asm!("isb", options(nostack, preserves_flags)) }
}

#[inline(always)]
pub fn dsb_ish() {
    unsafe { asm!("dsb ish", options(nostack, preserves_flags)) }
}

#[inline(always)]
pub fn dsb_ishst() {
    unsafe { asm!("dsb ishst", options(nostack, preserves_flags)) }
}

#[inline(always)]
pub fn dsb_sy() {
    unsafe { asm!("dsb sy", options(nostack, preserves_flags)) }
}

pub fn halt_forever() -> ! {
    loop {
        unsafe { asm!("msr daifset, #0xf", "wfi", options(nostack)) }
    }
}

/// The smallest data and instruction cache line sizes (CTR_EL0).
pub fn dcache_line() -> u64 {
    4 << ((mrs!("ctr_el0") >> 16) & 0xf)
}

pub fn icache_line() -> u64 {
    4 << (mrs!("ctr_el0") & 0xf)
}

fn by_line(start: u64, len: u64, line: u64, mut f: impl FnMut(u64)) {
    if len == 0 {
        return;
    }
    let mut a = start & !(line - 1);
    let end = start + len;
    while a < end {
        f(a);
        a += line;
    }
}

/// Clean [start, start + len) to the point of coherency.
pub fn clean_dcache_poc(start: u64, len: u64) {
    by_line(start, len, dcache_line(), |a| unsafe { asm!("dc cvac, {}", in(reg) a, options(nostack)) });
    dsb_sy();
}

/// Clean and invalidate [start, start + len) to the point of coherency.
pub fn clean_inval_dcache_poc(start: u64, len: u64) {
    by_line(start, len, dcache_line(), |a| unsafe { asm!("dc civac, {}", in(reg) a, options(nostack)) });
    dsb_sy();
}

/// Invalidate [start, start + len) to the point of coherency. A line only
/// partly in the range is cleaned too, so the bytes around the range keep
/// their data (seL4 `invalidateCacheRange_RAM`).
pub fn inval_dcache_poc(start: u64, len: u64) {
    let line = dcache_line();
    let end = start + len;
    by_line(start, len, line, |a| {
        if a < start || a + line > end {
            unsafe { asm!("dc civac, {}", in(reg) a, options(nostack)) }
        } else {
            unsafe { asm!("dc ivac, {}", in(reg) a, options(nostack)) }
        }
    });
    dsb_sy();
}

/// Make instructions written to [start, start + len) visible to
/// instruction fetch on every core: clean to the point of unification,
/// then invalidate all instruction caches (aliasing instruction caches
/// make invalidation by address unreliable through another mapping).
pub fn sync_icache(start: u64, len: u64) {
    let ctr = mrs!("ctr_el0");
    if ctr & (1 << 28) == 0 {
        by_line(start, len, dcache_line(), |a| unsafe { asm!("dc cvau, {}", in(reg) a, options(nostack)) });
    }
    dsb_ish();
    if ctr & (1 << 29) == 0 {
        unsafe { asm!("ic ialluis", options(nostack)) };
    }
    dsb_ish();
    isb();
}

/// MPIDR_EL1's affinity fields (Aff3 in bits 32-39, Aff2-Aff0 below).
pub fn mpidr() -> u64 {
    mrs!("mpidr_el1") & 0xff_00ff_ffff
}

/// Physical address bits (ID_AA64MMFR0_EL1.PARange), capped at 48.
pub fn pa_bits() -> u64 {
    match mrs!("id_aa64mmfr0_el1") & 0xf {
        0 => 32,
        1 => 36,
        2 => 40,
        3 => 42,
        4 => 44,
        _ => 48,
    }
}

/// The PARange field itself, for TCR_EL1.IPS (capped at 48 bits).
pub fn pa_range() -> u64 {
    (mrs!("id_aa64mmfr0_el1") & 0xf).min(5)
}

/// 16-bit ASIDs (ID_AA64MMFR0_EL1.ASIDBits).
pub fn has_asid16() -> bool {
    (mrs!("id_aa64mmfr0_el1") >> 4) & 0xf == 2
}

/// Hardware access-flag management (ID_AA64MMFR1_EL1.HAFDBS).
pub fn has_hw_af() -> bool {
    mrs!("id_aa64mmfr1_el1") & 0xf != 0
}

/// Privileged access never (ID_AA64MMFR1_EL1.PAN).
pub fn has_pan() -> bool {
    (mrs!("id_aa64mmfr1_el1") >> 20) & 0xf != 0
}

/// The GIC system-register interface (ID_AA64PFR0_EL1.GIC).
pub fn has_gic_sysregs() -> bool {
    (mrs!("id_aa64pfr0_el1") >> 24) & 0xf != 0
}

/// Virtualization Host Extensions (ID_AA64MMFR1_EL1.VH).
pub fn has_vhe() -> bool {
    (mrs!("id_aa64mmfr1_el1") >> 8) & 0xf != 0
}

/// 16-bit VMIDs (ID_AA64MMFR1_EL1.VMIDBits == 2).
pub fn vmid16() -> bool {
    (mrs!("id_aa64mmfr1_el1") >> 4) & 0xf == 2
}

/// FEAT_CLRBHB (ID_AA64ISAR2_EL1.CLRBHB, bits [31:28]).
pub fn has_clrbhb() -> bool {
    (mrs!("s3_0_c0_c6_2") >> 28) & 0xf != 0
}

/// This core's `ap_caps::Caps`.
pub fn caps() -> crate::ap_caps::Caps {
    let el2 = current_el() == 2;
    crate::ap_caps::Caps {
        asid16: has_asid16(),
        hw_af: has_hw_af(),
        pan: has_pan(),
        pa_bits: pa_bits(),
        cntfrq: mrs!("cntfrq_el0") & 0xffff_ffff,
        el2,
        vhe: el2 && has_vhe(),
        vmid16: el2 && vmid16(),
        vgic_lrs: if el2 { crate::gic::vgic_num_lrs() } else { 0 },
    }
}
