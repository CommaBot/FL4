//! `SysKernelConfig` (`seL4_KernelConfig`): what the kernel found and chose
//! at boot, one word per key (`fl4_abi::consts::kernel_config`). The boot
//! core computes every answer once (`freeze`), so a syscall only loads a
//! word: no system register read that could trap to a hypervisor, no GIC
//! access, no lock and no user memory. No hardware access here: the host
//! tests run it (xtask/tests/aarch64_boot.rs).
use core::sync::atomic::{AtomicU64, Ordering};
use fl4_abi::config;
use fl4_abi::consts::error;
use fl4_abi::consts::kernel_config::*;

/// The keys of this architecture, each with a word of `FROZEN`.
macro_rules! answered {
    ($($key:ident)*) => {
        #[allow(non_camel_case_types, clippy::upper_case_acronyms)]
        #[derive(Clone, Copy)]
        enum Slot { $($key),* }
        const KEYS: &[(u64, Slot)] = &[$((keys::$key, Slot::$key)),*];
        fn slot(key: u64) -> Option<Slot> {
            match key {
                $(keys::$key => Some(Slot::$key),)*
                _ => None,
            }
        }
    };
}

answered! {
    ARCH BUILD_FLAGS ONLINE_CPUS MAX_CPUS
    VIRT_BACKEND VIRT_REJECT VIRT_FEATURES VIRT_S2_IPA_BITS VIRT_VGIC_LRS
    CVM_TYPE CVM_FLAGS
    ARM_MITIGATIONS
    ARM_PLATFORM_FLAGS ARM_PA_BITS ARM_GIC_VERSION ARM_MAX_SPI ARM_PSCI_METHOD ARM_TIMER_FREQ_HZ
}

/// Written by `freeze`, before any core runs user code.
static FROZEN: [AtomicU64; KEYS.len()] = [const { AtomicU64::new(0) }; KEYS.len()];

/// What decides whether guests can run (fl4-kernel-aarch64 `fl4_boot`).
#[derive(Clone, Copy, Debug)]
pub struct Virt {
    pub has_el2: bool,
    /// The `novirt` command line option.
    pub novirt: bool,
    /// A usable GICv3 system-register interface or GICv2 GICH and GICV.
    pub vgic: bool,
    pub lrs: u64,
    /// The maintenance and virtual timer PPIs are the ones the kernel uses.
    pub ppis_ok: bool,
    /// One core, or PSCI not by HVC (which EL2 would take).
    pub psci_ok: bool,
}

/// Why guests cannot run (`virt_reject`); NONE if they can.
pub fn virt_reject_of(v: &Virt) -> u64 {
    if !v.has_el2 {
        virt_reject::EL1_ONLY
    } else if v.novirt {
        virt_reject::NOVIRT_CMDLINE
    } else if !v.vgic || v.lrs == 0 || !v.ppis_ok || !v.psci_ok {
        virt_reject::NO_VGIC
    } else {
        virt_reject::NONE
    }
}

/// What the answers are made of, read on the boot core with every core up.
#[derive(Clone, Copy, Debug)]
pub struct Facts {
    pub online: u64,
    pub el2_vhe: bool,
    pub el2_nvhe: bool,
    /// `virt_reject_of`.
    pub virt_reject: u64,
    /// 16-bit VMIDs, at EL2.
    pub vmid16: bool,
    pub s2_ipa_bits: u64,
    pub vgic_lrs: u64,
    pub pan: bool,
    pub pauth: bool,
    pub clrbhb: bool,
    pub asid16: bool,
    pub hw_af: bool,
    pub gicv3_sre: bool,
    pub its: bool,
    pub timer_local_ack: bool,
    pub pa_bits: u64,
    pub gic_version: u64,
    pub max_spi: u64,
    pub psci: u64,
    pub timer_hz: u64,
}

const fn bit(on: bool, flag: u64) -> u64 {
    if on {
        flag
    } else {
        0
    }
}

impl Facts {
    fn answer(&self, slot: Slot) -> u64 {
        let virt = self.virt_reject == virt_reject::NONE;
        match slot {
            Slot::ARCH => arch::AARCH64,
            Slot::BUILD_FLAGS => BUILD_FLAGS,
            Slot::ONLINE_CPUS => self.online,
            Slot::MAX_CPUS => config::MAX_NUM_NODES,
            Slot::VIRT_BACKEND => {
                if virt && self.el2_vhe {
                    virt_backend::EL2_VHE
                } else if virt && self.el2_nvhe {
                    virt_backend::EL2_NVHE
                } else {
                    virt_backend::NONE
                }
            }
            Slot::VIRT_REJECT => self.virt_reject,
            Slot::VIRT_FEATURES => {
                bit(virt, virt_features::ARM_VIRT_READY)
                    | bit(self.vmid16, virt_features::ARM_VMID16)
                    | bit(virt && self.gic_version == 2, virt_features::ARM_GICV2_VGIC)
                    | bit(virt && self.gic_version == 3, virt_features::ARM_GICV3_VGIC)
            }
            Slot::VIRT_S2_IPA_BITS => self.s2_ipa_bits,
            Slot::VIRT_VGIC_LRS => self.vgic_lrs,
            // No confidential guest of this architecture yet.
            Slot::CVM_TYPE => cvm_type::NONE,
            Slot::CVM_FLAGS => 0,
            Slot::ARM_MITIGATIONS => {
                bit(self.pan, arm_mitigations::PAN)
                    | bit(self.pauth, arm_mitigations::PAUTH)
                    | bit(self.clrbhb, arm_mitigations::CLRBHB)
            }
            Slot::ARM_PLATFORM_FLAGS => {
                bit(self.asid16, arm_platform_flags::ASID16)
                    | bit(self.hw_af, arm_platform_flags::HW_AF)
                    | bit(self.gicv3_sre, arm_platform_flags::GICV3_SRE)
                    | bit(self.its, arm_platform_flags::ITS_ACTIVE)
                    | bit(self.timer_local_ack, arm_platform_flags::TIMER_LOCAL_ACK)
                    | bit(self.el2_vhe, arm_platform_flags::EL2_VHE)
                    | bit(self.el2_nvhe, arm_platform_flags::EL2_NVHE)
            }
            Slot::ARM_PA_BITS => self.pa_bits,
            Slot::ARM_GIC_VERSION => self.gic_version,
            Slot::ARM_MAX_SPI => self.max_spi,
            Slot::ARM_PSCI_METHOD => self.psci,
            Slot::ARM_TIMER_FREQ_HZ => self.timer_hz,
        }
    }
}

const BUILD_FLAGS: u64 = bit(config::DEBUG_BUILD, build_flags::DEBUG_BUILD)
    | bit(config::PRINTING, build_flags::PRINTING)
    | bit(config::ENABLE_SMP_SUPPORT, build_flags::SMP)
    | bit(config::HARDWARE_DEBUG_API, build_flags::HW_DEBUG_API)
    | bit(config::EXPORT_PMC_USER, build_flags::EXPORT_PMC_USER)
    | bit(config::KERNEL_X86_DANGEROUS_MSR, build_flags::DANGEROUS_MSR);

/// Compute every answer: on the boot core, once every core is up, before
/// the other cores are released or any user code runs (the release
/// publishes the words to them).
pub fn freeze(f: &Facts) {
    for &(_, s) in KEYS {
        FROZEN[s as usize].store(f.answer(s), Ordering::Relaxed);
    }
}

/// The value of `key`; None if this kernel does not know it.
fn get(key: u64) -> Option<u64> {
    slot(key).map(|s| FROZEN[s as usize].load(Ordering::Relaxed))
}

/// `SysKernelConfig` of `key`: the error and the value.
pub fn reply(key: u64) -> (u64, u64) {
    match get(key) {
        Some(v) => (error::NoError, v),
        None => (error::InvalidArgument, 0),
    }
}
