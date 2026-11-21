//! AArch64 EL2 VHE hardware VCPU switching, VGICv2/v3 state, and Stage-2 IPA resolution.

use crate::{cpu, gic, percpu};
use fl4_abi::consts::vcpu_reg as vr;
use fl4_core::layout::irq;
use fl4_core::vcpu as cv;

/// Host EL2 VHE `HCR_EL2`: E2H | RW | TGE.
pub const HCR_HOST_VHE: u64 = (1 << 34) | (1 << 31) | (1 << 27);

#[inline]
fn reg_ptr(vcpu: u64, idx: u64) -> *mut u64 {
    cv::reg_addr(vcpu, idx) as *mut u64
}

#[inline]
fn rd_vcpu(vcpu: u64, idx: u64) -> u64 {
    unsafe { core::ptr::read_volatile(reg_ptr(vcpu, idx)) }
}

#[inline]
fn wr_vcpu(vcpu: u64, idx: u64, val: u64) {
    unsafe { core::ptr::write_volatile(reg_ptr(vcpu, idx), val) }
}

#[inline]
fn vppi_masked(vcpu: u64) -> u64 {
    unsafe { core::ptr::read_volatile((vcpu + cv::VPPI_MASKED) as *const u64) }
}

#[inline]
fn has_ras() -> bool {
    (crate::mrs!("id_aa64pfr0_el1") >> 28) & 0xf != 0
}

#[inline]
pub fn set_host_hcr() {
    if cpu::is_el2_vhe() {
        crate::msr!("hcr_el2", HCR_HOST_VHE);
        cpu::isb();
    }
}

/// Sync hardware auto-clear of `HCR_EL2.VSE` (bit 8) back into the VCPU object
/// on VHE guest exit before `set_host_hcr()` overwrites `HCR_EL2`.
#[inline]
pub fn sync_exit_hcr(vcpu: u64) {
    if cpu::is_el2_vhe() && vcpu != 0 {
        let sw = rd_vcpu(vcpu, vr::HCR_EL2);
        if sw & (1 << 8) != 0 && crate::mrs!("hcr_el2") & (1 << 8) == 0 {
            wr_vcpu(vcpu, vr::HCR_EL2, sw & !(1 << 8));
        }
    }
}

#[inline]
pub fn enter_guest_hcr(vcpu: u64) {
    if cpu::is_el2_vhe() && vcpu != 0 {
        let hcr = cv::sanitize_hcr(rd_vcpu(vcpu, vr::HCR_EL2));
        crate::msr!("hcr_el2", hcr);
        cpu::isb();
    }
}

/// Sanitized guest `HCR_EL2` for EL2 nVHE (strips `E2H` bit 34).
#[inline]
pub fn nvhe_guest_hcr(vcpu: u64) -> u64 {
    cv::sanitize_hcr(rd_vcpu(vcpu, vr::HCR_EL2)) & !(1 << 34)
}

#[inline]
fn set_ppi_vgic_masked(me: u64, masked: bool) -> bool {
    let pc = percpu::get();
    if pc.ppi_vgic_masked.get() != masked {
        gic::mask(irq::VGIC_MAINT_ID, me, masked);
        pc.ppi_vgic_masked.set(masked);
        true
    } else {
        false
    }
}

#[inline]
fn set_ppi_vtimer_masked(me: u64, masked: bool) -> bool {
    let pc = percpu::get();
    if pc.ppi_vtimer_masked.get() != masked {
        gic::mask(irq::TIMER_ID, me, masked);
        pc.ppi_vtimer_masked.set(masked);
        true
    } else {
        false
    }
}

/// Mask PPI 25 (VGIC maintenance) on the current core, updating the PerCpu cache.
#[inline]
pub fn mask_ppi_vgic() {
    let me = percpu::cpu_index() as u64;
    set_ppi_vgic_masked(me, true);
}

/// Mask PPI 27 (guest vTimer) on the current core, updating the PerCpu cache.
#[inline]
pub fn mask_ppi_vtimer() {
    let me = percpu::cpu_index() as u64;
    set_ppi_vtimer_masked(me, true);
}

/// Prepare per-core PPI masks and (on GICv2) GICH MMIO state before entering a
/// guest via `HVC_VCPU_RUN` in EL2 nVHE mode.
pub fn nvhe_prepare_guest(vcpu: u64) {
    if gic::version() == 2 && gic::gich() != 0 {
        let lrs = gic::vgic_num_lrs() as u64;
        wr_gich(0x8, rd_vcpu(vcpu, vr::VGIC_VMCR) as u32);
        wr_gich(0xf0, rd_vcpu(vcpu, vr::VGIC_AP0R0) as u32);
        for i in 0..lrs {
            wr_gich(0x100 + i * 4, rd_vcpu(vcpu, vr::VGIC_LR0 + i) as u32);
        }
        wr_gich(0x0, rd_vcpu(vcpu, vr::VGIC_HCR) as u32);
        cpu::dsb_sy();
    }
    let me = percpu::cpu_index() as u64;
    let c1 = set_ppi_vgic_masked(me, false);
    let c2 = set_ppi_vtimer_masked(me, vppi_masked(vcpu) & 1 != 0);
    if c1 || c2 {
        cpu::isb();
    }
}

/// Save GICv2 GICH MMIO state right after an nVHE guest exit. On non-IRQ exits
/// (`kind != 1`), quiesces `GICH_HCR = 0`; on IRQ exits, leaves it active until
/// `nvhe_quiesce_after_irq()` runs after `take_irq()`.
pub fn nvhe_post_exit(vcpu: u64, kind: u64) {
    if gic::version() == 2 && gic::gich() != 0 {
        let lrs = gic::vgic_num_lrs() as u64;
        wr_vcpu(vcpu, vr::VGIC_HCR, rd_gich(0x0) as u64);
        wr_vcpu(vcpu, vr::VGIC_VMCR, rd_gich(0x8) as u64);
        wr_vcpu(vcpu, vr::VGIC_MISR, rd_gich(0x10) as u64);
        wr_vcpu(vcpu, vr::VGIC_EISR, crate::vmid::mask_lr_bitmap(rd_gich(0x20) as u64, lrs));
        wr_vcpu(vcpu, vr::VGIC_ELRSR, crate::vmid::mask_lr_bitmap(rd_gich(0x30) as u64, lrs));
        wr_vcpu(vcpu, vr::VGIC_AP0R0, rd_gich(0xf0) as u64);
        for i in 0..lrs {
            wr_vcpu(vcpu, vr::VGIC_LR0 + i, rd_gich(0x100 + i * 4) as u64);
        }
        if kind != 1 {
            wr_gich(0x0, 0);
            cpu::dsb_sy();
        }
    }
}

/// Capture whether guest vTimer (`CNTV_CTL_EL0`) and VGIC (`VGIC_HCR`) need
/// quiescing after an nVHE IRQ exit. Must be read BEFORE `take_irq()`, which
/// may service a remote stall that allows another core to unbind/retype `vcpu`.
#[inline]
pub fn nvhe_irq_quiesce_flags(vcpu: u64) -> (bool, bool) {
    (rd_vcpu(vcpu, vr::CNTV_CTL) != 0, rd_vcpu(vcpu, vr::VGIC_HCR) != 0)
}

/// Quiesce guest vTimer (`CNTV_CTL_EL0`) and VGIC (`ICH_HCR_EL2` / `GICH_HCR`)
/// after `take_irq()` completes on an nVHE IRQ exit.
pub fn nvhe_quiesce_after_irq(quiesce_cntv: bool, quiesce_vgic: bool) {
    if quiesce_cntv {
        let me = percpu::cpu_index();
        crate::msr!("cntv_ctl_el0", 0);
        crate::hyp_nvhe::set_cur_cntv_ctl(me, 0);
    }
    if quiesce_vgic {
        if gic::version() == 3 {
            crate::hyp_nvhe::quiesce_vgic();
        } else if gic::gich() != 0 {
            wr_gich(0x0, 0);
            cpu::dsb_sy();
        }
    }
    if quiesce_cntv {
        cpu::isb();
    }
}

/// Record exception exit registers (`FAR_EL2`, `HPFAR_EL2`, `ESR_EL2`) into the VCPU object.
pub fn record_exit_regs(vcpu: u64, far: u64, hpfar: u64, esr: u64) {
    if vcpu == 0 {
        return;
    }
    wr_vcpu(vcpu, vr::FAR_EL2, far);
    wr_vcpu(vcpu, vr::HPFAR_EL2, hpfar);
    wr_vcpu(vcpu, vr::ESR_EL2, esr);
}

/// Resolve guest VA `far` to IPA via `AT S1E1R` on a Stage-2 permission fault.
/// Must be called while `HCR_EL2.TGE == 0` (before restoring host HCR_EL2).
/// Returns `None` if Stage-1 translation fails (guest should retry).
pub fn resolve_s2_perm_ipa(far: u64) -> Option<u64> {
    let saved_par = crate::mrs!("par_el1");
    unsafe { core::arch::asm!("at s1e1r, {}", "isb", in(reg) far, options(nostack)) };
    let par = crate::mrs!("par_el1");
    crate::msr!("par_el1", saved_par);
    cpu::isb();
    if par & 1 != 0 {
        None
    } else {
        Some((par & 0x0000_ffff_ffff_f000) | (far & 0xfff))
    }
}

// ---- VGICv3 / VGICv2 hardware access --------------------------------------

pub fn gicv3_n_apr() -> u64 {
    let vtr = gic::vgic_vtr();
    let prebits = ((vtr >> 26) & 0x7) + 1;
    if prebits >= 7 {
        4
    } else if prebits >= 6 {
        2
    } else {
        1
    }
}

fn rd_lr_v3(i: u64) -> u64 {
    let v: u64;
    unsafe {
        match i {
            0 => core::arch::asm!("mrs {}, s3_4_c12_c12_0", out(reg) v, options(nomem, nostack)),
            1 => core::arch::asm!("mrs {}, s3_4_c12_c12_1", out(reg) v, options(nomem, nostack)),
            2 => core::arch::asm!("mrs {}, s3_4_c12_c12_2", out(reg) v, options(nomem, nostack)),
            3 => core::arch::asm!("mrs {}, s3_4_c12_c12_3", out(reg) v, options(nomem, nostack)),
            4 => core::arch::asm!("mrs {}, s3_4_c12_c12_4", out(reg) v, options(nomem, nostack)),
            5 => core::arch::asm!("mrs {}, s3_4_c12_c12_5", out(reg) v, options(nomem, nostack)),
            6 => core::arch::asm!("mrs {}, s3_4_c12_c12_6", out(reg) v, options(nomem, nostack)),
            7 => core::arch::asm!("mrs {}, s3_4_c12_c12_7", out(reg) v, options(nomem, nostack)),
            8 => core::arch::asm!("mrs {}, s3_4_c12_c13_0", out(reg) v, options(nomem, nostack)),
            9 => core::arch::asm!("mrs {}, s3_4_c12_c13_1", out(reg) v, options(nomem, nostack)),
            10 => core::arch::asm!("mrs {}, s3_4_c12_c13_2", out(reg) v, options(nomem, nostack)),
            11 => core::arch::asm!("mrs {}, s3_4_c12_c13_3", out(reg) v, options(nomem, nostack)),
            12 => core::arch::asm!("mrs {}, s3_4_c12_c13_4", out(reg) v, options(nomem, nostack)),
            13 => core::arch::asm!("mrs {}, s3_4_c12_c13_5", out(reg) v, options(nomem, nostack)),
            14 => core::arch::asm!("mrs {}, s3_4_c12_c13_6", out(reg) v, options(nomem, nostack)),
            15 => core::arch::asm!("mrs {}, s3_4_c12_c13_7", out(reg) v, options(nomem, nostack)),
            _ => v = 0,
        }
    }
    v
}

fn wr_lr_v3(i: u64, v: u64) {
    unsafe {
        match i {
            0 => core::arch::asm!("msr s3_4_c12_c12_0, {}", in(reg) v, options(nostack)),
            1 => core::arch::asm!("msr s3_4_c12_c12_1, {}", in(reg) v, options(nostack)),
            2 => core::arch::asm!("msr s3_4_c12_c12_2, {}", in(reg) v, options(nostack)),
            3 => core::arch::asm!("msr s3_4_c12_c12_3, {}", in(reg) v, options(nostack)),
            4 => core::arch::asm!("msr s3_4_c12_c12_4, {}", in(reg) v, options(nostack)),
            5 => core::arch::asm!("msr s3_4_c12_c12_5, {}", in(reg) v, options(nostack)),
            6 => core::arch::asm!("msr s3_4_c12_c12_6, {}", in(reg) v, options(nostack)),
            7 => core::arch::asm!("msr s3_4_c12_c12_7, {}", in(reg) v, options(nostack)),
            8 => core::arch::asm!("msr s3_4_c12_c13_0, {}", in(reg) v, options(nostack)),
            9 => core::arch::asm!("msr s3_4_c12_c13_1, {}", in(reg) v, options(nostack)),
            10 => core::arch::asm!("msr s3_4_c12_c13_2, {}", in(reg) v, options(nostack)),
            11 => core::arch::asm!("msr s3_4_c12_c13_3, {}", in(reg) v, options(nostack)),
            12 => core::arch::asm!("msr s3_4_c12_c13_4, {}", in(reg) v, options(nostack)),
            13 => core::arch::asm!("msr s3_4_c12_c13_5, {}", in(reg) v, options(nostack)),
            14 => core::arch::asm!("msr s3_4_c12_c13_6, {}", in(reg) v, options(nostack)),
            15 => core::arch::asm!("msr s3_4_c12_c13_7, {}", in(reg) v, options(nostack)),
            _ => {}
        }
    }
}

fn rd_ap0r_v3(i: u64) -> u64 {
    let v: u64;
    unsafe {
        match i {
            0 => core::arch::asm!("mrs {}, s3_4_c12_c8_0", out(reg) v, options(nomem, nostack)),
            1 => core::arch::asm!("mrs {}, s3_4_c12_c8_1", out(reg) v, options(nomem, nostack)),
            2 => core::arch::asm!("mrs {}, s3_4_c12_c8_2", out(reg) v, options(nomem, nostack)),
            3 => core::arch::asm!("mrs {}, s3_4_c12_c8_3", out(reg) v, options(nomem, nostack)),
            _ => v = 0,
        }
    }
    v
}

fn wr_ap0r_v3(i: u64, v: u64) {
    unsafe {
        match i {
            0 => core::arch::asm!("msr s3_4_c12_c8_0, {}", in(reg) v, options(nostack)),
            1 => core::arch::asm!("msr s3_4_c12_c8_1, {}", in(reg) v, options(nostack)),
            2 => core::arch::asm!("msr s3_4_c12_c8_2, {}", in(reg) v, options(nostack)),
            3 => core::arch::asm!("msr s3_4_c12_c8_3, {}", in(reg) v, options(nostack)),
            _ => {}
        }
    }
}

fn rd_ap1r_v3(i: u64) -> u64 {
    let v: u64;
    unsafe {
        match i {
            0 => core::arch::asm!("mrs {}, s3_4_c12_c9_0", out(reg) v, options(nomem, nostack)),
            1 => core::arch::asm!("mrs {}, s3_4_c12_c9_1", out(reg) v, options(nomem, nostack)),
            2 => core::arch::asm!("mrs {}, s3_4_c12_c9_2", out(reg) v, options(nomem, nostack)),
            3 => core::arch::asm!("mrs {}, s3_4_c12_c9_3", out(reg) v, options(nomem, nostack)),
            _ => v = 0,
        }
    }
    v
}

fn wr_ap1r_v3(i: u64, v: u64) {
    unsafe {
        match i {
            0 => core::arch::asm!("msr s3_4_c12_c9_0, {}", in(reg) v, options(nostack)),
            1 => core::arch::asm!("msr s3_4_c12_c9_1, {}", in(reg) v, options(nostack)),
            2 => core::arch::asm!("msr s3_4_c12_c9_2, {}", in(reg) v, options(nostack)),
            3 => core::arch::asm!("msr s3_4_c12_c9_3, {}", in(reg) v, options(nostack)),
            _ => {}
        }
    }
}

#[inline]
fn rd_gich(off: u64) -> u32 {
    let h = gic::gich();
    if h == 0 { 0 } else { unsafe { core::ptr::read_volatile((h + off) as *const u32) } }
}

#[inline]
fn wr_gich(off: u64, v: u32) {
    let h = gic::gich();
    if h != 0 {
        unsafe { core::ptr::write_volatile((h + off) as *mut u32, v) };
    }
}

/// Read VGIC EISR (End-of-Interrupt Status Register) for maintenance fault.
/// In nVHE mode, also quiesces `ICH_HCR_EL2` / `GICH_HCR` to deassert PPI 25
/// before `gic::eoi()`.
pub fn read_vgic_eisr() -> u64 {
    if !cpu::has_el2() {
        return 0;
    }
    if gic::version() == 3 {
        if cpu::is_el2_nvhe() {
            crate::hyp_nvhe::read_vgic_eisr()
        } else {
            crate::mrs!("s3_4_c12_c11_3") // ICH_EISR_EL2
        }
    } else {
        let eisr = rd_gich(0x20) as u64; // GICH_EISR0
        if cpu::is_el2_nvhe() {
            wr_gich(0x0, 0);
            cpu::dsb_sy();
        }
        eisr
    }
}

#[inline]
fn rd_vgic_hcr() -> u64 {
    if gic::version() == 3 {
        crate::mrs!("s3_4_c12_c11_0")
    } else if gic::gich() != 0 {
        rd_gich(0x0) as u64
    } else {
        0
    }
}

#[inline]
fn rd_vgic_misr() -> u64 {
    if gic::version() == 3 {
        crate::mrs!("s3_4_c12_c11_2")
    } else if gic::gich() != 0 {
        rd_gich(0x10) as u64
    } else {
        0
    }
}

#[inline]
fn wr_vgic_hcr(v: u64) {
    if gic::version() == 3 {
        crate::msr!("s3_4_c12_c11_0", v);
        cpu::isb();
    } else if gic::gich() != 0 {
        wr_gich(0x0, v as u32);
        cpu::dsb_sy();
    }
}

fn save_vgic(vcpu: u64, active: bool) {
    let lrs = gic::vgic_num_lrs() as u64;
    if gic::version() == 3 {
        if active {
            wr_vcpu(vcpu, vr::VGIC_HCR, crate::mrs!("s3_4_c12_c11_0"));
            wr_vcpu(vcpu, vr::VGIC_MISR, crate::mrs!("s3_4_c12_c11_2"));
        }
        wr_vcpu(vcpu, vr::VGIC_VMCR, crate::mrs!("s3_4_c12_c11_7"));
        wr_vcpu(vcpu, vr::VGIC_EISR, crate::mrs!("s3_4_c12_c11_3"));
        wr_vcpu(vcpu, vr::VGIC_ELRSR, crate::mrs!("s3_4_c12_c11_5"));
        let n_apr = gicv3_n_apr();
        for i in 0..n_apr {
            wr_vcpu(vcpu, vr::VGIC_AP0R0 + i, rd_ap0r_v3(i));
            wr_vcpu(vcpu, vr::VGIC_AP1R0 + i, rd_ap1r_v3(i));
        }
        for i in 0..lrs {
            wr_vcpu(vcpu, vr::VGIC_LR0 + i, rd_lr_v3(i));
        }
        if active {
            crate::msr!("s3_4_c12_c11_0", 0);
            cpu::isb();
        }
    } else if gic::gich() != 0 {
        if active {
            wr_vcpu(vcpu, vr::VGIC_HCR, rd_gich(0x0) as u64);
            wr_vcpu(vcpu, vr::VGIC_MISR, rd_gich(0x10) as u64);
        }
        wr_vcpu(vcpu, vr::VGIC_VMCR, rd_gich(0x8) as u64);
        wr_vcpu(vcpu, vr::VGIC_EISR, crate::vmid::mask_lr_bitmap(rd_gich(0x20) as u64, lrs));
        wr_vcpu(vcpu, vr::VGIC_ELRSR, crate::vmid::mask_lr_bitmap(rd_gich(0x30) as u64, lrs));
        wr_vcpu(vcpu, vr::VGIC_AP0R0, rd_gich(0xf0) as u64);
        for i in 0..lrs {
            wr_vcpu(vcpu, vr::VGIC_LR0 + i, rd_gich(0x100 + i * 4) as u64);
        }
        if active {
            wr_gich(0x0, 0);
            cpu::dsb_sy();
        }
    }
}

fn restore_vgic(vcpu: u64) {
    let lrs = gic::vgic_num_lrs() as u64;
    if gic::version() == 3 {
        crate::msr!("s3_4_c12_c11_7", rd_vcpu(vcpu, vr::VGIC_VMCR));
        let n_apr = gicv3_n_apr();
        for i in 0..n_apr {
            wr_ap0r_v3(i, rd_vcpu(vcpu, vr::VGIC_AP0R0 + i));
            wr_ap1r_v3(i, rd_vcpu(vcpu, vr::VGIC_AP1R0 + i));
        }
        for i in 0..lrs {
            wr_lr_v3(i, rd_vcpu(vcpu, vr::VGIC_LR0 + i));
        }
        crate::msr!("s3_4_c12_c11_0", rd_vcpu(vcpu, vr::VGIC_HCR));
        cpu::isb();
    } else if gic::gich() != 0 {
        wr_gich(0x8, rd_vcpu(vcpu, vr::VGIC_VMCR) as u32);
        wr_gich(0xf0, rd_vcpu(vcpu, vr::VGIC_AP0R0) as u32);
        for i in 0..lrs {
            wr_gich(0x100 + i * 4, rd_vcpu(vcpu, vr::VGIC_LR0 + i) as u32);
        }
        wr_gich(0x0, rd_vcpu(vcpu, vr::VGIC_HCR) as u32);
        cpu::dsb_sy();
    }
}

// ---- Guest EL1 + Timer save/restore (lazy switching) ----------------------

/// Lightweight suspend when leaving a VCPU for a native EL0 or idle thread:
/// save & quiesce only the 4 registers that could interfere with host/native
/// execution (`CNTV_CTL`, `CNTVOFF`, `MDSCR_EL1`, `VGIC_HCR`), keeping the
/// remaining EL1 & VGIC state live in hardware under `vcpu_owner`.
fn suspend(vcpu: u64) {
    wr_vcpu(vcpu, vr::CNTV_CTL, crate::mrs!("s3_5_c14_c3_1"));
    wr_vcpu(vcpu, vr::CNTVOFF, crate::mrs!("cntvoff_el2"));
    wr_vcpu(vcpu, vr::MDSCR_EL1, crate::mrs!("mdscr_el1"));
    wr_vcpu(vcpu, vr::VGIC_HCR, rd_vgic_hcr());
    wr_vcpu(vcpu, vr::VGIC_MISR, rd_vgic_misr());
    crate::msr!("s3_5_c14_c3_1", 0); // CNTV_CTL_EL02 = 0
    crate::msr!("cntvoff_el2", 0);
    crate::msr!("mdscr_el1", crate::el0_access::MDSCR_EL1);
    wr_vgic_hcr(0);
    cpu::isb();
    percpu::get().vcpu_active.set(false);
}

/// Lightweight resume when returning to the same lazily owned VCPU.
fn resume_active(vcpu: u64) {
    crate::msr!("cntvoff_el2", rd_vcpu(vcpu, vr::CNTVOFF));
    crate::msr!("s3_5_c14_c3_1", rd_vcpu(vcpu, vr::CNTV_CTL));
    crate::msr!("mdscr_el1", rd_vcpu(vcpu, vr::MDSCR_EL1));
    wr_vgic_hcr(rd_vcpu(vcpu, vr::VGIC_HCR));
    let me = percpu::cpu_index() as u64;
    set_ppi_vgic_masked(me, false);
    set_ppi_vtimer_masked(me, vppi_masked(vcpu) & 1 != 0);
    cpu::isb();
    percpu::get().vcpu_active.set(true);
}

fn save(vcpu: u64, active: bool) {
    wr_vcpu(vcpu, vr::SCTLR, crate::mrs!("s3_5_c1_c0_0"));
    wr_vcpu(vcpu, vr::CPACR, crate::mrs!("s3_5_c1_c0_2"));
    wr_vcpu(vcpu, vr::TCR, crate::mrs!("s3_5_c2_c0_2"));
    wr_vcpu(vcpu, vr::TTBR0, crate::mrs!("s3_5_c2_c0_0"));
    wr_vcpu(vcpu, vr::TTBR1, crate::mrs!("s3_5_c2_c0_1"));
    wr_vcpu(vcpu, vr::MAIR, crate::mrs!("s3_5_c10_c2_0"));
    wr_vcpu(vcpu, vr::AMAIR, crate::mrs!("s3_5_c10_c3_0"));
    wr_vcpu(vcpu, vr::CIDR, crate::mrs!("s3_5_c13_c0_1"));
    wr_vcpu(vcpu, vr::AFSR0, crate::mrs!("s3_5_c5_c1_0"));
    wr_vcpu(vcpu, vr::AFSR1, crate::mrs!("s3_5_c5_c1_1"));
    wr_vcpu(vcpu, vr::ESR, crate::mrs!("s3_5_c5_c2_0"));
    wr_vcpu(vcpu, vr::FAR, crate::mrs!("s3_5_c6_c0_0"));
    wr_vcpu(vcpu, vr::PAR, crate::mrs!("par_el1"));
    wr_vcpu(vcpu, vr::VBAR, crate::mrs!("s3_5_c12_c0_0"));
    wr_vcpu(vcpu, vr::TPIDR_EL1, crate::mrs!("tpidr_el1"));
    wr_vcpu(vcpu, vr::VMPIDR_EL2, crate::mrs!("vmpidr_el2"));
    wr_vcpu(vcpu, vr::SP_EL1, crate::mrs!("sp_el1"));
    wr_vcpu(vcpu, vr::ELR_EL1, crate::mrs!("s3_5_c4_c0_1"));
    wr_vcpu(vcpu, vr::SPSR_EL1, crate::mrs!("s3_5_c4_c0_0"));
    wr_vcpu(vcpu, vr::CSSELR_EL1, crate::mrs!("csselr_el1"));
    if has_ras() {
        wr_vcpu(vcpu, vr::VDISR_EL2, crate::mrs!("s3_4_c12_c1_1"));
        wr_vcpu(vcpu, vr::VSESR_EL2, crate::mrs!("s3_4_c5_c2_3"));
    }
    wr_vcpu(vcpu, vr::CNTV_CVAL, crate::mrs!("s3_5_c14_c3_2"));
    wr_vcpu(vcpu, vr::CNTKCTL_EL1, crate::mrs!("s3_5_c14_c1_0"));
    wr_vcpu(vcpu, vr::VPIDR_EL2, crate::mrs!("vpidr_el2"));
    wr_vcpu(vcpu, vr::ACTLR_EL1, crate::mrs!("actlr_el1"));
    wr_vcpu(vcpu, vr::MDCCINT_EL1, crate::mrs!("s2_0_c0_c2_0"));
    if active {
        // Save and quiesce the 4 host-interfering registers (when !active,
        // `suspend` already saved and quiesced them — do not overwrite).
        wr_vcpu(vcpu, vr::CNTV_CTL, crate::mrs!("s3_5_c14_c3_1"));
        wr_vcpu(vcpu, vr::CNTVOFF, crate::mrs!("cntvoff_el2"));
        wr_vcpu(vcpu, vr::MDSCR_EL1, crate::mrs!("mdscr_el1"));
        crate::msr!("s3_5_c14_c3_1", 0); // CNTV_CTL_EL02 = 0
        crate::msr!("cntvoff_el2", 0);
        crate::msr!("mdscr_el1", crate::el0_access::MDSCR_EL1);
    }
    save_vgic(vcpu, active);
    cpu::isb();
}

fn restore(vcpu: u64) {
    crate::msr!("s3_5_c1_c0_0", rd_vcpu(vcpu, vr::SCTLR));
    crate::msr!("s3_5_c1_c0_2", rd_vcpu(vcpu, vr::CPACR));
    crate::msr!("s3_5_c2_c0_2", rd_vcpu(vcpu, vr::TCR));
    crate::msr!("s3_5_c2_c0_0", rd_vcpu(vcpu, vr::TTBR0));
    crate::msr!("s3_5_c2_c0_1", rd_vcpu(vcpu, vr::TTBR1));
    crate::msr!("s3_5_c10_c2_0", rd_vcpu(vcpu, vr::MAIR));
    crate::msr!("s3_5_c10_c3_0", rd_vcpu(vcpu, vr::AMAIR));
    crate::msr!("s3_5_c13_c0_1", rd_vcpu(vcpu, vr::CIDR));
    crate::msr!("s3_5_c5_c1_0", rd_vcpu(vcpu, vr::AFSR0));
    crate::msr!("s3_5_c5_c1_1", rd_vcpu(vcpu, vr::AFSR1));
    crate::msr!("s3_5_c5_c2_0", rd_vcpu(vcpu, vr::ESR));
    crate::msr!("s3_5_c6_c0_0", rd_vcpu(vcpu, vr::FAR));
    crate::msr!("par_el1", rd_vcpu(vcpu, vr::PAR));
    crate::msr!("s3_5_c12_c0_0", rd_vcpu(vcpu, vr::VBAR));
    crate::msr!("tpidr_el1", rd_vcpu(vcpu, vr::TPIDR_EL1));
    crate::msr!("vmpidr_el2", rd_vcpu(vcpu, vr::VMPIDR_EL2));
    crate::msr!("sp_el1", rd_vcpu(vcpu, vr::SP_EL1));
    crate::msr!("s3_5_c4_c0_1", rd_vcpu(vcpu, vr::ELR_EL1));
    crate::msr!("s3_5_c4_c0_0", rd_vcpu(vcpu, vr::SPSR_EL1));
    crate::msr!("csselr_el1", rd_vcpu(vcpu, vr::CSSELR_EL1));
    if has_ras() {
        crate::msr!("s3_4_c12_c1_1", rd_vcpu(vcpu, vr::VDISR_EL2));
        crate::msr!("s3_4_c5_c2_3", rd_vcpu(vcpu, vr::VSESR_EL2));
    }
    crate::msr!("cntvoff_el2", rd_vcpu(vcpu, vr::CNTVOFF));
    crate::msr!("s3_5_c14_c3_2", rd_vcpu(vcpu, vr::CNTV_CVAL));
    crate::msr!("s3_5_c14_c3_1", rd_vcpu(vcpu, vr::CNTV_CTL));
    crate::msr!("s3_5_c14_c1_0", rd_vcpu(vcpu, vr::CNTKCTL_EL1));
    crate::msr!("vpidr_el2", rd_vcpu(vcpu, vr::VPIDR_EL2));
    crate::msr!("actlr_el1", rd_vcpu(vcpu, vr::ACTLR_EL1));
    crate::msr!("mdscr_el1", rd_vcpu(vcpu, vr::MDSCR_EL1));
    crate::msr!("s2_0_c0_c2_0", rd_vcpu(vcpu, vr::MDCCINT_EL1));
    restore_vgic(vcpu);
    let me = percpu::cpu_index() as u64;
    set_ppi_vgic_masked(me, false);
    set_ppi_vtimer_masked(me, vppi_masked(vcpu) & 1 != 0);
    cpu::isb();
}

/// Switch this core's hardware VCPU state lazily to `vcpu` (0 = native/idle).
pub fn switch_to(vcpu: u64) {
    if !cpu::has_el2() {
        return;
    }
    if cpu::is_el2_nvhe() {
        return;
    }
    let me = percpu::cpu_index();
    let cur = percpu::vcpu_owner(me);
    let active = percpu::get().vcpu_active.get();
    if vcpu == 0 {
        if cur != 0 && active {
            suspend(cur);
        }
        return;
    }
    if cur == vcpu {
        if !active {
            resume_active(vcpu);
        } else {
            let me64 = me as u64;
            let c1 = set_ppi_vgic_masked(me64, false);
            let c2 = set_ppi_vtimer_masked(me64, vppi_masked(vcpu) & 1 != 0);
            if c1 || c2 {
                cpu::isb();
            }
        }
        return;
    }
    if cur != 0 {
        save(cur, active);
        percpu::set_vcpu_owner(0);
        percpu::get().vcpu_active.set(false);
    }
    restore(vcpu);
    percpu::set_vcpu_owner(vcpu);
    percpu::get().vcpu_active.set(true);
}

/// Save and release `vcpu` if it is live on this core (`CALL_VCPU_FLUSH` / local).
pub fn flush_local(vcpu: u64) {
    if vcpu == 0 {
        return;
    }
    if cpu::is_el2_vhe() {
        let me = percpu::cpu_index();
        if percpu::vcpu_owner(me) == vcpu {
            let active = percpu::get().vcpu_active.get();
            save(vcpu, active);
            percpu::set_vcpu_owner(0);
            percpu::get().vcpu_active.set(false);
        }
    } else if cpu::is_el2_nvhe() && gic::version() == 3 {
        let me = percpu::cpu_index();
        if crate::hyp_nvhe::vgic_owner(me) == fl4_core::layout::paddr(vcpu) {
            crate::hyp_nvhe::flush_vgic();
        }
    }
}

fn owner_core(vcpu: u64) -> Option<usize> {
    if cpu::is_el2_vhe() {
        (0..percpu::MAX_CPUS).find(|&c| percpu::vcpu_owner(c) == vcpu)
    } else if cpu::is_el2_nvhe() && gic::version() == 3 {
        let pa = fl4_core::layout::paddr(vcpu);
        (0..percpu::MAX_CPUS).find(|&c| crate::hyp_nvhe::vgic_owner(c) == pa)
    } else {
        None
    }
}

/// Flush `vcpu`'s live hardware state on whichever core owns it, and release
/// ownership. Caller holds the serial gate when another core owns it.
pub fn flush(vcpu: u64) {
    if vcpu == 0 || !cpu::has_el2() {
        return;
    }
    if !cpu::is_el2_vhe() && !(cpu::is_el2_nvhe() && gic::version() == 3) {
        return;
    }
    match owner_core(vcpu) {
        Some(c) if c == percpu::cpu_index() => flush_local(vcpu),
        Some(c) => crate::smp::remote_call(crate::smp::CALL_VCPU_FLUSH, vcpu, 0, 1 << c),
        None => {}
    }
}
