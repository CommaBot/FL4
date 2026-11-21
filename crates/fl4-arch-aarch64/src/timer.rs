//! The kernel's MCS timer: EL2 physical timer (CNTHP, PPI 26) in EL2 VHE
//! mode, EL1 physical timer (CNTP, PPI 30) in EL2 nVHE mode, or EL1 virtual
//! timer (CNTV, PPI 27) in EL1 mode. Ticks are at the CNTFRQ_EL0 rate read at
//! boot (l4h 0016).
use crate::cpu::ElMode;
use crate::{cpu, percpu};
use core::sync::atomic::{AtomicU64, Ordering};
use fl4_core::layout::irq;

static FREQ: AtomicU64 = AtomicU64::new(1);

pub const KERNEL_WCET_US: u64 = 10;
const CTL_ENABLE: u64 = 1;
const CTL_IMASK: u64 = 2;

/// The GIC PPI ID of the kernel's MCS timer (26 in EL2 VHE, 30 in EL2 nVHE, 27 in EL1).
#[inline]
pub fn timer_irq_id() -> u64 {
    match cpu::el_mode() {
        ElMode::El2Vhe => irq::HYP_TIMER_ID,
        ElMode::El2Nvhe => irq::PHYS_TIMER_ID,
        ElMode::El1 => irq::TIMER_ID,
    }
}

pub fn init() -> bool {
    let f = crate::mrs!("cntfrq_el0") & 0xffff_ffff;
    FREQ.store(f.max(1), Ordering::Relaxed);
    init_core();
    f != 0
}

/// Per core: the timer off until armed. EL0 may read the virtual counter
/// (libsel4's clock) and, as the user configuration exports them, the
/// physical counter and timer (`KernelArmExportPCNTUser`,
/// `KernelArmExportPTMRUser`).
pub fn init_core() {
    let mut k = 1 << 1; // EL0VCTEN
    if fl4_abi::config::ARM_EXPORT_PCNT_USER {
        k |= 1 << 0; // EL0PCTEN
    }
    if fl4_abi::config::ARM_EXPORT_PTMR_USER {
        k |= 1 << 9; // EL0PTEN
    }
    match cpu::el_mode() {
        ElMode::El2Vhe => {
            // CNTHP_CTL_EL2 off until armed; preserve EL1PCTEN (bit 10) = 1
            // and EL1PTEN (bit 11) = 0 in CNTHCTL_EL2 (E2H1 layout).
            crate::msr!("s3_4_c14_c2_1", 0);
            crate::msr!("cnthctl_el2", k | (1 << 10));
        }
        ElMode::El2Nvhe => {
            // CNTP_CTL_EL0 off until armed (via EL2 since CNTHCTL_EL2.EL1PCEN=0);
            // CNTV_CTL_EL0 off for host.
            crate::hyp_nvhe::set_cntp(0, 0, false);
            crate::msr!("cntv_ctl_el0", 0);
            crate::hyp_nvhe::set_cur_cntv_ctl(percpu::cpu_index(), 0);
            crate::msr!("cntkctl_el1", k);
        }
        ElMode::El1 => {
            crate::msr!("cntv_ctl_el0", 0);
            crate::msr!("cntkctl_el1", k);
        }
    }
    cpu::isb();
}

pub fn freq() -> u64 {
    FREQ.load(Ordering::Relaxed)
}

#[inline]
pub fn now() -> u64 {
    cpu::isb();
    if cpu::has_el2() {
        crate::mrs!("cntpct_el0")
    } else {
        crate::mrs!("cntvct_el0")
    }
}

/// Interrupt at counter value `ticks` (or at once if it passed).
pub fn set_deadline(ticks: u64) {
    percpu::get().armed.set(ticks);
    let v = if ticks == 0 { 1 } else { ticks };
    match cpu::el_mode() {
        ElMode::El2Vhe => {
            crate::msr!("s3_4_c14_c2_2", v); // CNTHP_CVAL_EL2
            crate::msr!("s3_4_c14_c2_1", CTL_ENABLE); // CNTHP_CTL_EL2
        }
        ElMode::El2Nvhe => {
            crate::hyp_nvhe::set_cntp(v, CTL_ENABLE, true);
        }
        ElMode::El1 => {
            crate::msr!("cntv_cval_el0", v);
            crate::msr!("cntv_ctl_el0", CTL_ENABLE);
        }
    }
    cpu::isb();
}

/// The timer interrupt was taken: stop it asserting (it is level
/// triggered) until the kernel arms it again.
pub fn quiesce() {
    match cpu::el_mode() {
        ElMode::El2Vhe => crate::msr!("s3_4_c14_c2_1", CTL_ENABLE | CTL_IMASK), // CNTHP_CTL_EL2
        ElMode::El2Nvhe => crate::hyp_nvhe::set_cntp(0, CTL_ENABLE | CTL_IMASK, false),
        ElMode::El1 => crate::msr!("cntv_ctl_el0", CTL_ENABLE | CTL_IMASK),
    }
    cpu::isb();
}

/// A timer interrupt arrived: is it stale (l4h 0012)? It is when the
/// timer is armed for a deadline still ahead, which replaced the one
/// that fired. The kernel need not run then.
pub fn early() -> bool {
    let armed = percpu::get().armed.get();
    armed != 0 && now() < armed
}

pub fn us_to_ticks(us: u64) -> u64 {
    let t = us as u128 * freq() as u128 / 1_000_000;
    if t > u64::MAX as u128 {
        u64::MAX
    } else {
        t as u64
    }
}

pub fn ticks_to_us(ticks: u64) -> u64 {
    (ticks as u128 * 1_000_000 / freq() as u128) as u64
}

/// Largest number of microseconds whose tick count fits in 64 bits.
pub fn max_us() -> u64 {
    let m = u64::MAX as u128 * 1_000_000 / freq() as u128;
    if m > u64::MAX as u128 {
        u64::MAX
    } else {
        m as u64
    }
}
