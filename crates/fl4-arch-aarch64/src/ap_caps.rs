//! What every core must share with the boot core: the kernel decides
//! these once, on the boot core, for all of them. No hardware access, so
//! the host tests run it (xtask/tests/aarch64_boot.rs).

/// A core's capabilities the kernel relies on being the boot core's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Caps {
    /// 16-bit ASIDs (ID_AA64MMFR0_EL1.ASIDBits): with 8, TCR_EL1.AS is
    /// ignored and ASIDs `n` and `n + 256` share TLB entries.
    pub asid16: bool,
    /// Hardware access-flag management (HAFDBS): the kernel clears the
    /// access flag (ARMPageTestAndClearAccessed) only with it.
    pub hw_af: bool,
    /// PAN: the kernel's guard against touching user memory.
    pub pan: bool,
    /// Physical address bits: the boot core admitted RAM and devices up to
    /// its own size, which a smaller core faults on (Address Size fault).
    pub pa_bits: u64,
    /// CNTFRQ_EL0: the rate every scheduling budget is converted at.
    pub cntfrq: u64,
}

/// Whether a core with `ap` may run beside a boot core with `bsp`.
pub fn ap_matches(bsp: &Caps, ap: &Caps) -> bool {
    ap.asid16 && ap.hw_af == bsp.hw_af && ap.pan == bsp.pan && ap.pa_bits >= bsp.pa_bits && bsp.cntfrq != 0
        && ap.cntfrq == bsp.cntfrq
}
