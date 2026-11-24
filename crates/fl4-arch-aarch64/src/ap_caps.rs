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
    /// Running at EL2 (VHE host mode).
    pub el2: bool,
    /// Virtualization Host Extensions (ID_AA64MMFR1_EL1.VH), only when `el2`.
    pub vhe: bool,
    /// 16-bit VMIDs (ID_AA64MMFR1_EL1.VMIDBits == 2), only when `el2`.
    pub vmid16: bool,
    /// Number of VGIC list registers, only when `el2` (0 in EL1).
    pub vgic_lrs: u8,
    /// Guests can run (`arch::virt_ready`, decided on the boot core).
    pub virt: bool,
    /// The VGIC type register as the VCPU ABI gives it (`gic::vgic_vtr`:
    /// `ICH_VTR_EL2` or `GICH_VTR`, ListRegs capped to the 16 ABI slots),
    /// only when `el2` (0 in EL1, or with no VGIC). BootInfo and every VCPU
    /// report it; the priority and preemption bits in it set the
    /// active-priority registers VHE and nVHE save and restore on each
    /// core. Compared only when guests can run: a guest that moves between
    /// cores must find the same interface.
    pub vgic_vtr: u64,
    /// The pointer authentication fields (`cpu::pauth_fields`: APA, API,
    /// GPA, GPI, APA3, GPA3): a thread's keys and enables (`TCBSetPACKeys`)
    /// must compute the same, and fail the same way, on every core it may
    /// run on, and TCR_EL1.TBID0 is set with FEAT_PAuth. Compared whole.
    pub pauth: u64,
}

/// `cpu::pauth_fields` of the two ID register values: ID_AA64ISAR1_EL1.APA
/// [7:4], API [11:8], GPA [27:24], GPI [31:28] where they are, and
/// ID_AA64ISAR2_EL1.APA3 [15:12], GPA3 [11:8] moved up by 32.
pub const fn pauth_fields_of(isar1: u64, isar2: u64) -> u64 {
    (isar1 & 0xff00_0ff0) | ((isar2 & 0xff00) << 32)
}

/// FEAT_PAuth in `pauth_fields_of`'s value: an address authentication
/// algorithm (APA, API or APA3), the fields boot.S also tests before it
/// writes the keys and sets TCR_EL1.TBID0.
pub const fn pauth_in(fields: u64) -> bool {
    fields & (0xff0 | (0xf000 << 32)) != 0
}

/// Whether a core with `ap` may run beside a boot core with `bsp`.
pub fn ap_matches(bsp: &Caps, ap: &Caps) -> bool {
    ap.asid16
        && ap.hw_af == bsp.hw_af
        && ap.pan == bsp.pan
        && ap.pa_bits >= bsp.pa_bits
        && bsp.cntfrq != 0
        && ap.cntfrq == bsp.cntfrq
        && ap.el2 == bsp.el2
        && ap.vhe == bsp.vhe
        && ap.vmid16 == bsp.vmid16
        && ap.vgic_lrs == bsp.vgic_lrs
        && (!bsp.virt || (ap.virt && ap.vgic_vtr == bsp.vgic_vtr))
        && ap.pauth == bsp.pauth
}
