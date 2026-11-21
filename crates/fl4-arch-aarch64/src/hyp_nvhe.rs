//! AArch64 EL2 nVHE Hyp switch stub interface and per-core EL2 state (`HypCpu`).
//!
//! When the kernel boots at EL2 without `FEAT_VHE` (`ElMode::El2Nvhe`), EL1
//! runs the FL4 kernel while a lightweight identity-mapped EL2 stub handles
//! guest world-switches, Stage-2 TLB maintenance, and GICv3 `ICH_*` register
//! access via `HVC #0`.
use crate::{el0_access, percpu};
use core::cell::UnsafeCell;
use core::mem::offset_of;
use fl4_abi::consts::vcpu_reg as vr;

core::arch::global_asm!(include_str!("hyp_nvhe.S"));

pub const HVC_HYP_ENABLE_MMU: u64 = 0;
pub const HVC_VCPU_RUN: u64 = 1;
pub const HVC_SET_VTCR: u64 = 2;
pub const HVC_TLBI_IPAS2: u64 = 3;
pub const HVC_TLBI_VMALLS12_IS: u64 = 4;
pub const HVC_TLBI_VMALLS12_LOCAL: u64 = 5;
pub const HVC_VGIC_VTR: u64 = 6;
pub const HVC_QUIESCE_VGIC: u64 = 7;
pub const HVC_READ_VGIC_EISR: u64 = 8;
pub const HVC_HYP_SAVE_HOST_REGS: u64 = 9;
pub const HVC_SET_CNTP: u64 = 10;
pub const HVC_FLUSH_VGIC: u64 = 11;
pub const HVC_TLBI_ALLE1_IS: u64 = 12;

/// Per-core EL2 Hyp state. Its physical address is permanently held in `SP_EL2`
/// once `HVC_HYP_ENABLE_MMU` runs. EL1 and EL2 share coherent Normal Write-Back
/// Inner-Shareable mappings of this struct.
#[repr(C, align(64))]
pub struct HypCpu {
    pub in_guest: u64,
    pub regs_pa: u64,
    pub vcpu_pa: u64,
    pub host_hcr_el2: u64,
    pub host_mdcr_el2: u64,
    pub guest_mdcr_el2: u64,
    pub gic_v3: u64,
    pub vgic_lrs: u64,
    pub vgic_n_apr: u64,
    pub has_ras: u64,
    // Dynamic host registers saved on every guest entry:
    pub host_elr_el2: u64,
    pub host_spsr_el2: u64,
    pub host_ttbr0_el1: u64,
    pub host_cpacr_el1: u64,
    pub host_sp_el1: u64,
    // Constant per-core host EL1 registers saved once by HVC_HYP_SAVE_HOST_REGS:
    pub host_sctlr_el1: u64,
    pub host_tcr_el1: u64,
    pub host_ttbr1_el1: u64,
    pub host_mair_el1: u64,
    pub host_vbar_el1: u64,
    pub host_tpidr_el1: u64,
    pub host_cntkctl_el1: u64,
    pub host_mdscr_el1: u64,
    // Lazy guest-state flags and cached read-only EL2 / VGIC registers:
    pub guest_mdccint_nz: u64,
    pub guest_ras_nz: u64,
    pub guest_cntvoff_nz: u64,
    pub cur_actlr: u64,
    pub cur_vttbr: u64,
    pub cur_vpidr: u64,
    pub cur_vmpidr: u64,
    pub vgic_live: u64,
    pub vgic_lr_mask: u64,
    pub cur_vmcr: u64,
    pub cur_ap0r: [u64; 4],
    pub cur_ap1r: [u64; 4],
    pub host_actlr_el1: u64,
    pub cur_cptr: u64,
    pub cur_cntv_ctl: u64,
    pub cur_cntv_cval: u64,
    pub cur_csselr: u64,
    pub cur_mdscr: u64,
    pub vgic_owner: u64,
}

impl HypCpu {
    const fn new() -> HypCpu {
        HypCpu {
            in_guest: 0,
            regs_pa: 0,
            vcpu_pa: 0,
            host_hcr_el2: 0,
            host_mdcr_el2: 0,
            guest_mdcr_el2: 0,
            gic_v3: 0,
            vgic_lrs: 0,
            vgic_n_apr: 0,
            has_ras: 0,
            host_elr_el2: 0,
            host_spsr_el2: 0,
            host_ttbr0_el1: 0,
            host_cpacr_el1: 0,
            host_sp_el1: 0,
            host_sctlr_el1: 0,
            host_tcr_el1: 0,
            host_ttbr1_el1: 0,
            host_mair_el1: 0,
            host_vbar_el1: 0,
            host_tpidr_el1: 0,
            host_cntkctl_el1: 0,
            host_mdscr_el1: 0,
            guest_mdccint_nz: 0,
            guest_ras_nz: 0,
            guest_cntvoff_nz: 0,
            cur_actlr: 0,
            cur_vttbr: u64::MAX,
            cur_vpidr: u64::MAX,
            cur_vmpidr: u64::MAX,
            vgic_live: 0,
            vgic_lr_mask: 0xffff,
            cur_vmcr: u64::MAX,
            cur_ap0r: [u64::MAX; 4],
            cur_ap1r: [u64::MAX; 4],
            host_actlr_el1: 0,
            cur_cptr: u64::MAX,
            cur_cntv_ctl: u64::MAX,
            cur_cntv_cval: u64::MAX,
            cur_csselr: u64::MAX,
            cur_mdscr: u64::MAX,
            vgic_owner: 0,
        }
    }
}

// Static assertions locking HypCpu and VCPU offsets to hyp_nvhe.S.
const _: () = assert!(offset_of!(HypCpu, in_guest) == 0x00);
const _: () = assert!(offset_of!(HypCpu, regs_pa) == 0x08);
const _: () = assert!(offset_of!(HypCpu, vcpu_pa) == 0x10);
const _: () = assert!(offset_of!(HypCpu, host_hcr_el2) == 0x18);
const _: () = assert!(offset_of!(HypCpu, host_mdcr_el2) == 0x20);
const _: () = assert!(offset_of!(HypCpu, guest_mdcr_el2) == 0x28);
const _: () = assert!(offset_of!(HypCpu, gic_v3) == 0x30);
const _: () = assert!(offset_of!(HypCpu, vgic_lrs) == 0x38);
const _: () = assert!(offset_of!(HypCpu, vgic_n_apr) == 0x40);
const _: () = assert!(offset_of!(HypCpu, has_ras) == 0x48);
const _: () = assert!(offset_of!(HypCpu, host_elr_el2) == 0x50);
const _: () = assert!(offset_of!(HypCpu, host_spsr_el2) == 0x58);
const _: () = assert!(offset_of!(HypCpu, host_ttbr0_el1) == 0x60);
const _: () = assert!(offset_of!(HypCpu, host_cpacr_el1) == 0x68);
const _: () = assert!(offset_of!(HypCpu, host_sp_el1) == 0x70);
const _: () = assert!(offset_of!(HypCpu, host_sctlr_el1) == 0x78);
const _: () = assert!(offset_of!(HypCpu, host_tcr_el1) == 0x80);
const _: () = assert!(offset_of!(HypCpu, host_ttbr1_el1) == 0x88);
const _: () = assert!(offset_of!(HypCpu, host_mair_el1) == 0x90);
const _: () = assert!(offset_of!(HypCpu, host_vbar_el1) == 0x98);
const _: () = assert!(offset_of!(HypCpu, host_tpidr_el1) == 0xa0);
const _: () = assert!(offset_of!(HypCpu, host_cntkctl_el1) == 0xa8);
const _: () = assert!(offset_of!(HypCpu, host_mdscr_el1) == 0xb0);
const _: () = assert!(offset_of!(HypCpu, guest_mdccint_nz) == 0xb8);
const _: () = assert!(offset_of!(HypCpu, guest_ras_nz) == 0xc0);
const _: () = assert!(offset_of!(HypCpu, guest_cntvoff_nz) == 0xc8);
const _: () = assert!(offset_of!(HypCpu, cur_actlr) == 0xd0);
const _: () = assert!(offset_of!(HypCpu, cur_vttbr) == 0xd8);
const _: () = assert!(offset_of!(HypCpu, cur_vpidr) == 0xe0);
const _: () = assert!(offset_of!(HypCpu, cur_vmpidr) == 0xe8);
const _: () = assert!(offset_of!(HypCpu, vgic_live) == 0xf0);
const _: () = assert!(offset_of!(HypCpu, vgic_lr_mask) == 0xf8);
const _: () = assert!(offset_of!(HypCpu, cur_vmcr) == 0x100);
const _: () = assert!(offset_of!(HypCpu, cur_ap0r) == 0x108);
const _: () = assert!(offset_of!(HypCpu, cur_ap1r) == 0x128);
const _: () = assert!(offset_of!(HypCpu, host_actlr_el1) == 0x148);
const _: () = assert!(offset_of!(HypCpu, cur_cptr) == 0x150);
const _: () = assert!(offset_of!(HypCpu, cur_cntv_ctl) == 0x158);
const _: () = assert!(offset_of!(HypCpu, cur_cntv_cval) == 0x160);
const _: () = assert!(offset_of!(HypCpu, cur_csselr) == 0x168);
const _: () = assert!(offset_of!(HypCpu, cur_mdscr) == 0x170);
const _: () = assert!(offset_of!(HypCpu, vgic_owner) == 0x178);

const _: () = assert!(fl4_core::vcpu::REGS == 0x40);
const _: () = assert!(vr::SCTLR == 0);
const _: () = assert!(vr::HCR_EL2 == 26);
const _: () = assert!(vr::MDCCINT_EL1 == 30);
const _: () = assert!(vr::VGIC_HCR == 35);
const _: () = assert!(vr::VGIC_AP0R0 == 40);
const _: () = assert!(vr::VGIC_AP1R0 == 44);
const _: () = assert!(vr::VGIC_LR0 == 48);

struct HypCpus(UnsafeCell<[HypCpu; percpu::MAX_CPUS]>);
unsafe impl Sync for HypCpus {}

static HYP_CPUS: HypCpus = HypCpus(UnsafeCell::new([const { HypCpu::new() }; percpu::MAX_CPUS]));

extern "C" {
    static fl4_hyp_vectors: u8;
}

/// Kernel virtual address of the runtime EL2 nVHE vector table.
pub fn hyp_vectors_va() -> u64 {
    unsafe { &fl4_hyp_vectors as *const u8 as u64 }
}

/// Kernel virtual address of core `core`'s `HypCpu` structure.
pub fn hyp_cpu_va(core: usize) -> u64 {
    unsafe { &(*HYP_CPUS.0.get())[core] as *const HypCpu as u64 }
}

#[inline]
fn hvc(fid: u64, a1: u64, a2: u64, a3: u64) -> u64 {
    let mut r = fid;
    unsafe {
        core::arch::asm!(
            "hvc #0",
            inout("x0") r,
            inout("x1") a1 => _,
            inout("x2") a2 => _,
            inout("x3") a3 => _,
            out("x9") _,
            out("x10") _,
            out("x11") _,
            out("x12") _,
            options(nostack),
        );
    }
    r
}

/// Enable the identity-mapped EL2 MMU and install `fl4_hyp_vectors` and
/// `SP_EL2 = hyp_cpu_pa` on the calling core.
pub fn init_core(core: usize, hyp_ttbr0: u64, vectors_pa: u64, hyp_cpu_pa: u64) {
    let mut guest_mdcr: u64 = 0xf00; // TDE | TDA | TDOSA | TDRA
    if el0_access::has_pmu(crate::mrs!("id_aa64dfr0_el1")) {
        guest_mdcr |= 0x60; // TPMCR | TPM
    }
    let has_ras = ((crate::mrs!("id_aa64pfr0_el1") >> 28) & 0xf != 0) as u64;
    unsafe {
        let hc = &mut (*HYP_CPUS.0.get())[core];
        hc.guest_mdcr_el2 = guest_mdcr;
        hc.has_ras = has_ras;
    }
    // Ensure the stores reach PoC before EL2 enables its MMU.
    crate::cpu::dsb_ishst();
    let _ = hvc(HVC_HYP_ENABLE_MMU, hyp_ttbr0, vectors_pa, hyp_cpu_pa);
}

/// Record GIC/VGIC parameters on core `core`'s `HypCpu` after GIC init.
pub fn init_gic_core(core: usize, gic_v3: bool, vgic_lrs: u8, vgic_n_apr: u64) {
    unsafe {
        let hc = &mut (*HYP_CPUS.0.get())[core];
        hc.gic_v3 = gic_v3 as u64;
        hc.vgic_lrs = vgic_lrs as u64;
        hc.vgic_n_apr = vgic_n_apr;
    }
    crate::cpu::dsb_ishst();
}

pub fn set_vtcr(vtcr: u64, empty_vttbr: u64) {
    let _ = hvc(HVC_SET_VTCR, vtcr, empty_vttbr, 0);
}

pub fn tlbi_ipas2(vttbr_vmid: u64, ipa_page: u64) {
    let _ = hvc(HVC_TLBI_IPAS2, vttbr_vmid, ipa_page, 0);
}

pub fn tlbi_vmalls12_is(vttbr_vmid: u64) {
    let _ = hvc(HVC_TLBI_VMALLS12_IS, vttbr_vmid, 0, 0);
}

pub fn tlbi_vmalls12_local() {
    let _ = hvc(HVC_TLBI_VMALLS12_LOCAL, 0, 0, 0);
}

pub fn tlbi_alle1_is() {
    let _ = hvc(HVC_TLBI_ALLE1_IS, 0, 0, 0);
}

pub fn vgic_vtr() -> u64 {
    hvc(HVC_VGIC_VTR, 0, 0, 0)
}

pub fn quiesce_vgic() {
    let _ = hvc(HVC_QUIESCE_VGIC, 0, 0, 0);
}

pub fn read_vgic_eisr() -> u64 {
    hvc(HVC_READ_VGIC_EISR, 0, 0, 0)
}

/// Snapshot constant per-core host EL1 registers into `HypCpu` once after
/// core/timer init so `HVC_VCPU_RUN` only saves dynamic host registers.
pub fn save_host_regs() {
    let _ = hvc(HVC_HYP_SAVE_HOST_REGS, 0, 0, 0);
}

/// Program `CNTP_CVAL_EL0` (when `write_cval`) and `CNTP_CTL_EL0` from EL2
/// while `CNTHCTL_EL2.EL1PCEN` stays permanently 0 in nVHE mode.
pub fn set_cntp(cval: u64, ctl: u64, write_cval: bool) {
    let _ = hvc(HVC_SET_CNTP, cval, ctl, write_cval as u64);
}

/// Sync `HypCpu.cur_cntv_ctl` after EL1 modifies `CNTV_CTL_EL0` directly.
pub fn set_cur_cntv_ctl(core: usize, val: u64) {
    unsafe {
        (*HYP_CPUS.0.get())[core].cur_cntv_ctl = val;
    }
    crate::cpu::dsb_ishst();
}

/// Physical address of the VCPU whose GICv3 `ICH_VMCR`/`ICH_AP*R` are
/// currently lazily owned on `core`, or 0 if none.
pub fn vgic_owner(core: usize) -> u64 {
    unsafe { core::ptr::read_volatile(&(*HYP_CPUS.0.get())[core].vgic_owner) }
}

/// Save and release this core's lazily owned GICv3 `ICH_VMCR`/`ICH_AP*R`.
pub fn flush_vgic() {
    let _ = hvc(HVC_FLUSH_VGIC, 0, 0, 0);
}
