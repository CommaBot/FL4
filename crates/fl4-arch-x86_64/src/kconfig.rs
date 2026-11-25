//! `SysKernelConfig` (`seL4_KernelConfig`): what the kernel found and chose
//! at boot, one word per key (`fl4_abi::consts::kernel_config`). The boot
//! core computes every answer once (`freeze`), so a syscall only loads a
//! word: no CPUID, MSR or other instruction that exits or takes #VC or #VE
//! in a confidential VM, no lock and no user memory.
use crate::spec::policy::{self, Rejected};
use crate::{apic, cpu, cvm, fpu, ioapic, sev, smp, spec, tdx, timer, tlb, vm};
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
    VIRT_BACKEND VIRT_REJECT VIRT_FEATURES
    CVM_TYPE CVM_FLAGS
    SPEC_STATUS SPEC_REJECT SPEC_FLAGS SPEC_ENTRY_ACTIONS SPEC_VMEXIT_ACTIONS
    SPEC_CTRL_MSR SPEC_TSX_CTRL_MSR SPEC_MCU_OPT_CTRL_MSR SPEC_EFER_MSR SPEC_AMD_DE_CFG_MSR SPEC_AMD_BP_CFG_MSR
    SPEC_MSR_VALID
    X86_CPU_VENDOR X86_CPU_FEATURES X86_FPU_XCR0 X86_FPU_SAVE_INSN X86_TSC_MHZ X86_TSC_SOURCE
    X86_MICROCODE_REV X86_MAX_PADDR_BITS X86_IOAPIC_COUNT X86_ARCH_CAPABILITIES
}

/// Written by `freeze`, before any core runs user code.
static FROZEN: [AtomicU64; KEYS.len()] = [const { AtomicU64::new(0) }; KEYS.len()];

/// The paging features the kernel image turned on.
#[derive(Clone, Copy, Debug)]
pub struct Paging {
    pub nx: bool,
    pub smep: bool,
    pub smap: bool,
    pub huge: bool,
}

/// What the answers are made of.
#[derive(Clone, Copy, Debug)]
struct Facts {
    online: u64,
    backend: u64,
    virt_reject: u64,
    virt_features: u64,
    /// The C-bit is on: SEV or SEV-SNP.
    sev: bool,
    snp: bool,
    tdx: bool,
    hardened: bool,
    shared_dma: bool,
    spec: spec::Facts,
    /// IA32_EFER with everything on that will be (AutoIBRS, AMD-V).
    efer: u64,
    /// `x86_vendor`.
    vendor: u64,
    paging: Paging,
    fsgsbase: bool,
    pcid: bool,
    invpcid: bool,
    x2apic: bool,
    tsc_deadline: bool,
    idle_poll: bool,
    hypervisor: bool,
    eager_fpu: bool,
    xcr0: u64,
    save_insn: u64,
    tsc_mhz: u64,
    tsc_source: u64,
    max_paddr: u64,
    ioapics: u64,
}

const fn bit(on: bool, flag: u64) -> u64 {
    if on {
        flag
    } else {
        0
    }
}

fn vendor_of(ebx: u32, edx: u32, ecx: u32) -> u64 {
    match (ebx, edx, ecx) {
        // "GenuineIntel", "AuthenticAMD", "HygonGenuine".
        (0x756e_6547, 0x4965_6e69, 0x6c65_746e) => x86_vendor::INTEL,
        (0x6874_7541, 0x6974_6e65, 0x444d_4163) => x86_vendor::AMD,
        (0x6f67_7948, 0x6e65_476e, 0x656e_6975) => x86_vendor::HYGON,
        _ => x86_vendor::OTHER,
    }
}

impl Facts {
    /// On the boot core, with every core up.
    fn read(paging: Paging) -> Facts {
        let v = cpu::cpuid(0, 0);
        Facts {
            online: smp::num_online(),
            backend: vm::backend(),
            virt_reject: vm::reject(),
            virt_features: vm::features(),
            sev: cvm::private_mask() != 0,
            snp: sev::snp::active(),
            tdx: tdx::active(),
            hardened: cvm::hardened(),
            shared_dma: cvm::active(),
            spec: spec::facts(),
            efer: cpu::rdmsr(cpu::msr::EFER),
            vendor: vendor_of(v.ebx, v.edx, v.ecx),
            paging,
            fsgsbase: cpu::fsgsbase(),
            pcid: tlb::pcid(),
            invpcid: tlb::invpcid_available(),
            x2apic: apic::is_x2apic(),
            tsc_deadline: timer::deadline_mode(),
            idle_poll: smp::idle_polls(),
            hypervisor: cpu::cpuid(1, 0).ecx & (1 << 31) != 0,
            eager_fpu: !fpu::lazy(),
            xcr0: fpu::xcr0(),
            save_insn: fpu::save_insn_id(),
            tsc_mhz: timer::tsc_mhz(),
            tsc_source: timer::source_id(),
            max_paddr: cpu::max_paddr(),
            ioapics: ioapic::count(),
        }
    }

    /// The boot core's MSR of `bit` (`spec_msr_valid`), 0 if it has none.
    fn msr(&self, bit: u64) -> u64 {
        if self.spec.msr_valid & bit != 0 {
            self.spec.msrs[bit.trailing_zeros() as usize]
        } else {
            0
        }
    }

    fn answer(&self, slot: Slot) -> u64 {
        let s = &self.spec;
        match slot {
            Slot::ARCH => arch::X86_64,
            Slot::BUILD_FLAGS => BUILD_FLAGS,
            Slot::ONLINE_CPUS => self.online,
            Slot::MAX_CPUS => config::MAX_NUM_NODES,
            Slot::VIRT_BACKEND => self.backend,
            Slot::VIRT_REJECT => self.virt_reject,
            Slot::VIRT_FEATURES => self.virt_features,
            Slot::CVM_TYPE => {
                if self.tdx {
                    cvm_type::TDX
                } else if self.snp {
                    cvm_type::SEV_SNP
                } else if self.sev {
                    cvm_type::SEV
                } else {
                    cvm_type::NONE
                }
            }
            Slot::CVM_FLAGS => bit(self.hardened, cvm_flags::HARDENED) | bit(self.shared_dma, cvm_flags::SHARED_DMA),
            Slot::SPEC_STATUS => {
                if s.plan.is_some() {
                    spec_status::COMPLETE
                } else {
                    spec_status::INCOMPLETE
                }
            }
            Slot::SPEC_REJECT => s.rejected.map_or(spec_reject::NONE, spec_reject_of),
            Slot::SPEC_FLAGS => spec_flags_of(s, self.eager_fpu),
            Slot::SPEC_ENTRY_ACTIONS => s.entry as u64,
            Slot::SPEC_VMEXIT_ACTIONS => s.plan.filter(|_| s.vm).map_or(0, |p| p.vmexit as u64),
            Slot::SPEC_CTRL_MSR => self.msr(spec_msr_valid::SPEC_CTRL),
            Slot::SPEC_TSX_CTRL_MSR => self.msr(spec_msr_valid::TSX_CTRL),
            Slot::SPEC_MCU_OPT_CTRL_MSR => self.msr(spec_msr_valid::MCU_OPT_CTRL),
            Slot::SPEC_EFER_MSR => self.efer,
            Slot::SPEC_AMD_DE_CFG_MSR => self.msr(spec_msr_valid::AMD_DE_CFG),
            Slot::SPEC_AMD_BP_CFG_MSR => self.msr(spec_msr_valid::AMD_BP_CFG),
            Slot::SPEC_MSR_VALID => s.msr_valid | spec_msr_valid::EFER,
            Slot::X86_CPU_VENDOR => self.vendor,
            Slot::X86_CPU_FEATURES => {
                bit(self.paging.nx, x86_features::NX)
                    | bit(self.paging.smep, x86_features::SMEP)
                    | bit(self.paging.smap, x86_features::SMAP)
                    | bit(self.fsgsbase, x86_features::FSGSBASE)
                    | bit(self.paging.huge, x86_features::HUGE_PAGES_1G)
                    | bit(self.pcid, x86_features::PCID)
                    | bit(self.invpcid, x86_features::INVPCID)
                    | bit(self.x2apic, x86_features::X2APIC)
                    | bit(self.tsc_deadline, x86_features::TSC_DEADLINE)
                    | bit(self.idle_poll, x86_features::IDLE_POLL)
                    | bit(self.hypervisor, x86_features::HYPERVISOR)
            }
            Slot::X86_FPU_XCR0 => self.xcr0,
            Slot::X86_FPU_SAVE_INSN => self.save_insn,
            Slot::X86_TSC_MHZ => self.tsc_mhz,
            Slot::X86_TSC_SOURCE => self.tsc_source,
            Slot::X86_MICROCODE_REV => s.microcode as u64,
            Slot::X86_MAX_PADDR_BITS => self.max_paddr.trailing_zeros() as u64,
            Slot::X86_IOAPIC_COUNT => self.ioapics,
            Slot::X86_ARCH_CAPABILITIES => self.msr(spec_msr_valid::ARCH_CAPABILITIES),
        }
    }
}

const BUILD_FLAGS: u64 = bit(config::DEBUG_BUILD, build_flags::DEBUG_BUILD)
    | bit(config::PRINTING, build_flags::PRINTING)
    | bit(config::ENABLE_SMP_SUPPORT, build_flags::SMP)
    | bit(config::HARDWARE_DEBUG_API, build_flags::HW_DEBUG_API)
    | bit(config::EXPORT_PMC_USER, build_flags::EXPORT_PMC_USER)
    | bit(config::KERNEL_X86_DANGEROUS_MSR, build_flags::DANGEROUS_MSR);

// The entry and VM-exit actions are reported as the policy has them.
const _: () = {
    assert!(policy::IBPB as u64 == spec_actions::IBPB && policy::RSB as u64 == spec_actions::RSB);
    assert!(policy::PBRSB as u64 == spec_actions::PBRSB && policy::LEGACY_IBRS as u64 == spec_actions::LEGACY_IBRS);
    assert!(policy::BHB as u64 == spec_actions::BHB && policy::IBHF as u64 == spec_actions::IBHF);
};

fn spec_reject_of(r: Rejected) -> u64 {
    match r {
        Rejected::Vendor => spec_reject::VENDOR,
        Rejected::Meltdown => spec_reject::MELTDOWN,
        Rejected::Smep => spec_reject::SMEP,
        Rejected::BeforeZen2 => spec_reject::BEFORE_ZEN2,
        Rejected::Ibpb => spec_reject::IBPB,
        Rejected::SrsoMicrocode => spec_reject::SRSO_MICROCODE,
        Rejected::BufferMicrocode => spec_reject::BUFFER_MICROCODE,
        Rejected::ItsMicrocode => spec_reject::ITS_MICROCODE,
        Rejected::Lfence => spec_reject::LFENCE,
    }
}

/// The mitigations in force, with a plan or without. The IBRS kind and
/// what goes with it are the boot core's; the rest is the system's.
fn spec_flags_of(s: &spec::Facts, eager_fpu: bool) -> u64 {
    let ibrs = s.boot.spec_ctrl & 1 != 0;
    let legacy = s.boot.entry & policy::LEGACY_IBRS != 0;
    let deferred = s.vm && s.plan.is_some_and(|p| policy::vm_ibpb_deferrable(&p, s.safe_ret));
    bit(s.skim, spec_flags::SKIM)
        | bit(s.safe_ret, spec_flags::SAFE_RET)
        | bit(s.retpoline, spec_flags::RETPOLINE)
        | bit(ibrs && !legacy, spec_flags::EIBRS)
        | bit(s.boot.auto_ibrs, spec_flags::AUTO_IBRS)
        | bit(ibrs && legacy, spec_flags::LEGACY_IBRS)
        | bit(s.boot.spec_ctrl & 2 != 0, spec_flags::STIBP)
        | bit(s.boot.spec_ctrl & (1 << 10) != 0, spec_flags::BHI_DIS_S)
        | bit(s.buffers, spec_flags::VERW_BUFFERS)
        | bit(s.no_smt, spec_flags::NO_SMT)
        | bit(s.boot.disable_tsx, spec_flags::DISABLE_TSX)
        | bit(deferred, spec_flags::VMEXIT_IBPB_DEFERRED)
        | bit(eager_fpu, spec_flags::EAGER_FPU)
}

/// Compute every answer: on the boot core, once every core is up and
/// `spec::finish_native_entry_policy` has run, before the APs are released
/// or any user code runs (the release publishes the words to them).
pub fn freeze(paging: Paging) {
    let f = Facts::read(paging);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec::policy::{native_only, select, Caps, NativeOnly, Plan, Vendor};

    const NO_SPEC: spec::Facts = spec::Facts {
        plan: None,
        rejected: None,
        boot: NativeOnly { entry: 0, spec_ctrl: 0, auto_ibrs: false, disable_tsx: false },
        entry: 0,
        buffers: false,
        vm: false,
        skim: false,
        safe_ret: false,
        retpoline: false,
        no_smt: false,
        microcode: 0,
        msrs: [0; spec::MSRS],
        msr_valid: 0,
    };

    /// Nothing found, nothing on.
    const NONE: Facts = Facts {
        online: 1,
        backend: virt_backend::NONE,
        virt_reject: virt_reject::NO_HW,
        virt_features: 0,
        sev: false,
        snp: false,
        tdx: false,
        hardened: false,
        shared_dma: false,
        spec: NO_SPEC,
        efer: 0xd01,
        vendor: x86_vendor::OTHER,
        paging: Paging { nx: false, smep: false, smap: false, huge: false },
        fsgsbase: false,
        pcid: false,
        invpcid: false,
        x2apic: false,
        tsc_deadline: false,
        idle_poll: false,
        hypervisor: false,
        eager_fpu: false,
        xcr0: 0,
        save_insn: 0,
        tsc_mhz: 1000,
        tsc_source: x86_tsc_source::PIT,
        max_paddr: 1 << 36,
        ioapics: 0,
    };

    fn ask(f: &Facts, key: u64) -> Option<u64> {
        slot(key).map(|s| f.answer(s))
    }

    /// The facts of a boot core with `plan`, as `init_core` applies it.
    fn planned(plan: Plan, vm: bool) -> spec::Facts {
        spec::Facts {
            plan: Some(plan),
            boot: NativeOnly {
                entry: plan.entry,
                spec_ctrl: plan.spec_ctrl,
                auto_ibrs: plan.auto_ibrs,
                disable_tsx: plan.disable_tsx,
            },
            entry: plan.entry,
            buffers: plan.buffers,
            vm,
            ..NO_SPEC
        }
    }

    /// The facts of a boot core without one.
    fn unplanned(c: &Caps, rejected: Rejected, no_entry_ibpb: bool) -> spec::Facts {
        let boot = native_only(c, no_entry_ibpb);
        spec::Facts { rejected: Some(rejected), boot, entry: boot.entry, buffers: true, ..NO_SPEC }
    }

    const PLAN: Plan = Plan {
        entry: policy::IBPB,
        vmexit: policy::IBPB,
        buffers: false,
        spec_ctrl: 0,
        auto_ibrs: false,
        no_smt: false,
        disable_tsx: false,
    };

    fn intel() -> Caps {
        Caps {
            vendor: Vendor::Intel,
            family: 6,
            model: 0xcf,
            stepping: 2,
            hypervisor: false,
            microcode: 0x1234,
            // RDCL_NO, IBRS_ALL, MDS_NO, TAA_NO, MMIO_NO, PBRSB_NO, RFDS_NO.
            arch: 1 | 2 | 1 << 5 | 1 << 8 | 7 << 13 | 1 << 24 | 1 << 27,
            // IBRS and IBPB, STIBP.
            leaf7_edx: 1 << 26 | 1 << 27,
            // BHI_CTRL.
            leaf7_2_edx: 1 << 4,
            smep: true,
            rtm: false,
            amd8: 0,
            amd21: 0,
            amd21_ecx: 0,
        }
    }

    #[test]
    fn every_key_is_answered_once_and_no_other() {
        for (i, &(key, s)) in KEYS.iter().enumerate() {
            assert_eq!(s as usize, i);
            assert_eq!(slot(key).map(|s| s as usize), Some(i));
            assert!(KEYS[..i].iter().all(|&(k, _)| k != key), "{key:#x}");
        }
        // Every key of the ABI but AArch64's.
        let foreign = [
            keys::VIRT_S2_IPA_BITS, keys::VIRT_VGIC_LRS, keys::ARM_MITIGATIONS, keys::ARM_PLATFORM_FLAGS,
            keys::ARM_PA_BITS, keys::ARM_GIC_VERSION, keys::ARM_MAX_SPI, keys::ARM_PSCI_METHOD, keys::ARM_TIMER_FREQ_HZ,
        ];
        assert_eq!(KEYS.len() + foreign.len(), 40);
        let unknown = [0, 5, 0xff, 0x105, 0x202, 0x30c, 0x381, 0x40a, 0x486, 0xdead_beef, 1 << 32 | 1, 1 << 63 | 1, u64::MAX];
        for key in foreign.into_iter().chain(unknown) {
            assert_eq!(get(key), None, "{key:#x}");
            assert_eq!(reply(key), (error::InvalidArgument, 0), "{key:#x}");
        }
        // All keys up to 64 Ki, by the table alone.
        assert_eq!((0..0x1_0000).filter(|&k| slot(k).is_some()).count(), KEYS.len());
    }

    #[test]
    fn common_keys() {
        let f = Facts { online: 7, ..NONE };
        assert_eq!(ask(&f, keys::ARCH), Some(1));
        assert_eq!(ask(&f, keys::ONLINE_CPUS), Some(7));
        assert_eq!(ask(&f, keys::MAX_CPUS), Some(config::MAX_NUM_NODES));
        let b = ask(&f, keys::BUILD_FLAGS).unwrap();
        assert_eq!(b & 1 != 0, config::DEBUG_BUILD);
        assert_eq!(b & 2 != 0, config::PRINTING);
        assert_eq!(b & 4 != 0, config::ENABLE_SMP_SUPPORT);
        assert_eq!(b & 8 != 0, config::HARDWARE_DEBUG_API);
        assert_eq!(b & 16 != 0, config::EXPORT_PMC_USER);
        assert_eq!(b & 32 != 0, config::KERNEL_X86_DANGEROUS_MSR);
        assert_eq!(b >> 6, 0);
    }

    #[test]
    fn virtualization_keys() {
        assert_eq!(ask(&NONE, keys::VIRT_BACKEND), Some(0));
        assert_eq!(ask(&NONE, keys::VIRT_REJECT), Some(1));
        let f = Facts { backend: 2, virt_reject: 0, virt_features: 8, ..NONE };
        assert_eq!(ask(&f, keys::VIRT_BACKEND), Some(2));
        assert_eq!(ask(&f, keys::VIRT_REJECT), Some(0));
        assert_eq!(ask(&f, keys::VIRT_FEATURES), Some(8));
    }

    #[test]
    fn confidential_vm_keys() {
        let of = |f: &Facts| (ask(f, keys::CVM_TYPE).unwrap(), ask(f, keys::CVM_FLAGS).unwrap());
        assert_eq!(of(&NONE), (0, 0));
        let sev = Facts { sev: true, shared_dma: true, ..NONE };
        assert_eq!(of(&sev), (1, 2));
        assert_eq!(of(&Facts { snp: true, hardened: true, ..sev }), (2, 3));
        assert_eq!(of(&Facts { tdx: true, hardened: true, shared_dma: true, ..NONE }), (3, 3));
    }

    #[test]
    fn cpu_keys() {
        let f = Facts {
            vendor: x86_vendor::AMD,
            xcr0: 0x2e7,
            save_insn: 4,
            tsc_mhz: 2450,
            tsc_source: 4,
            spec: spec::Facts { microcode: 0x0a00_11d7, ..NO_SPEC },
            max_paddr: 1 << 48,
            ioapics: 3,
            ..NONE
        };
        assert_eq!(ask(&f, keys::X86_CPU_VENDOR), Some(2));
        assert_eq!(ask(&f, keys::X86_FPU_XCR0), Some(0x2e7));
        assert_eq!(ask(&f, keys::X86_FPU_SAVE_INSN), Some(4));
        assert_eq!(ask(&f, keys::X86_TSC_MHZ), Some(2450));
        assert_eq!(ask(&f, keys::X86_TSC_SOURCE), Some(4));
        assert_eq!(ask(&f, keys::X86_MICROCODE_REV), Some(0x0a00_11d7));
        assert_eq!(ask(&f, keys::X86_MAX_PADDR_BITS), Some(48));
        assert_eq!(ask(&f, keys::X86_IOAPIC_COUNT), Some(3));
        for (bits, max) in [(36, 1u64 << 36), (52, 1 << 52)] {
            assert_eq!(ask(&Facts { max_paddr: max, ..NONE }, keys::X86_MAX_PADDR_BITS), Some(bits));
        }
    }

    #[test]
    fn cpu_vendors() {
        let of = |s: &[u8; 12]| {
            let w = |i: usize| u32::from_le_bytes(s[i..i + 4].try_into().unwrap());
            vendor_of(w(0), w(4), w(8))
        };
        assert_eq!(of(b"GenuineIntel"), 1);
        assert_eq!(of(b"AuthenticAMD"), 2);
        assert_eq!(of(b"HygonGenuine"), 3);
        assert_eq!(of(b"KVMKVMKVM\0\0\0"), 0);
    }

    #[test]
    fn cpu_feature_bits() {
        let on: [fn(&mut Facts); 11] = [
            |f| f.paging.nx = true,
            |f| f.paging.smep = true,
            |f| f.paging.smap = true,
            |f| f.fsgsbase = true,
            |f| f.paging.huge = true,
            |f| f.pcid = true,
            |f| f.invpcid = true,
            |f| f.x2apic = true,
            |f| f.tsc_deadline = true,
            |f| f.idle_poll = true,
            |f| f.hypervisor = true,
        ];
        assert_eq!(ask(&NONE, keys::X86_CPU_FEATURES), Some(0));
        for (i, set) in on.into_iter().enumerate() {
            let mut f = NONE;
            set(&mut f);
            assert_eq!(ask(&f, keys::X86_CPU_FEATURES), Some(1 << i), "bit {i}");
        }
    }

    #[test]
    fn frozen_tsc_source_and_save_insn_numbers_are_the_kernels() {
        use crate::timer::Source;
        assert_eq!(Source::Cpuid as u64, x86_tsc_source::CPUID);
        assert_eq!(Source::Hypervisor as u64, x86_tsc_source::HYPERVISOR);
        assert_eq!(Source::Pit as u64, x86_tsc_source::PIT);
        assert_eq!(Source::Kvm as u64, x86_tsc_source::KVM);
        assert_eq!(fpu::insn_ids(), [
            x86_fpu_insn::FXSAVE, x86_fpu_insn::XSAVE, x86_fpu_insn::XSAVEOPT, x86_fpu_insn::XSAVEC, x86_fpu_insn::XSAVES,
        ]);
    }

    #[test]
    fn spec_rejections_are_numbered_in_order() {
        for (i, r) in [
            Rejected::Vendor, Rejected::Meltdown, Rejected::Smep, Rejected::BeforeZen2, Rejected::Ibpb,
            Rejected::SrsoMicrocode, Rejected::BufferMicrocode, Rejected::ItsMicrocode, Rejected::Lfence,
        ].into_iter().enumerate() {
            let f = Facts { spec: unplanned(&intel(), r, false), ..NONE };
            assert_eq!(ask(&f, keys::SPEC_STATUS), Some(0));
            assert_eq!(ask(&f, keys::SPEC_REJECT), Some(i as u64 + 1));
        }
        let f = Facts { spec: planned(PLAN, false), ..NONE };
        assert_eq!(ask(&f, keys::SPEC_STATUS), Some(1));
        assert_eq!(ask(&f, keys::SPEC_REJECT), Some(0));
    }

    #[test]
    fn spec_flag_bits() {
        let flags = |s: &spec::Facts| spec_flags_of(s, false);
        assert_eq!(flags(&NO_SPEC), 0);
        assert_eq!(spec_flags_of(&NO_SPEC, true), 1 << 12);
        assert_eq!(flags(&spec::Facts { skim: true, ..NO_SPEC }), 1 << 0);
        assert_eq!(flags(&spec::Facts { safe_ret: true, ..NO_SPEC }), 1 << 1);
        assert_eq!(flags(&spec::Facts { safe_ret: true, retpoline: true, ..NO_SPEC }), 3 << 1);
        assert_eq!(flags(&spec::Facts { buffers: true, ..NO_SPEC }), 1 << 8);
        assert_eq!(flags(&spec::Facts { no_smt: true, ..NO_SPEC }), 1 << 9);
        let boot = |b: NativeOnly| spec::Facts { boot: b, ..NO_SPEC };
        assert_eq!(flags(&boot(NativeOnly { spec_ctrl: 1, ..NO_SPEC.boot })), spec_flags::EIBRS);
        assert_eq!(flags(&boot(NativeOnly { auto_ibrs: true, ..NO_SPEC.boot })), spec_flags::AUTO_IBRS);
        assert_eq!(
            flags(&boot(NativeOnly { spec_ctrl: 1, entry: policy::LEGACY_IBRS, ..NO_SPEC.boot })),
            spec_flags::LEGACY_IBRS
        );
        assert_eq!(flags(&boot(NativeOnly { spec_ctrl: 2, ..NO_SPEC.boot })), spec_flags::STIBP);
        assert_eq!(flags(&boot(NativeOnly { spec_ctrl: 1 << 10, ..NO_SPEC.boot })), spec_flags::BHI_DIS_S);
        assert_eq!(flags(&boot(NativeOnly { disable_tsx: true, ..NO_SPEC.boot })), spec_flags::DISABLE_TSX);
    }

    /// The same CPU with and without a plan.
    #[test]
    fn spec_flags_of_a_native_only_boot_come_from_what_it_applied() {
        let c = intel();
        let s = planned(select(&c).unwrap(), true);
        let want = spec_flags::EIBRS | spec_flags::STIBP | spec_flags::BHI_DIS_S;
        assert_eq!(spec_flags_of(&s, true) & !spec_flags::VMEXIT_IBPB_DEFERRED, want | spec_flags::EAGER_FPU);

        let n = unplanned(&c, Rejected::ItsMicrocode, false);
        assert_eq!(spec_flags_of(&n, true), want | spec_flags::VERW_BUFFERS | spec_flags::EAGER_FPU);
        let f = Facts { spec: n, ..NONE };
        assert_eq!(ask(&f, keys::SPEC_VMEXIT_ACTIONS), Some(0));

        // Without IBRS_ALL: legacy IBRS, never eIBRS too.
        let old = Caps { arch: c.arch & !2, ..c };
        for s in [planned(select(&old).unwrap(), true), unplanned(&old, Rejected::Lfence, false)] {
            let flags = spec_flags_of(&s, false);
            assert_eq!(flags & (spec_flags::EIBRS | spec_flags::LEGACY_IBRS), spec_flags::LEGACY_IBRS);
            assert_ne!(Facts { spec: s, ..NONE }.answer(Slot::SPEC_ENTRY_ACTIONS) & spec_actions::LEGACY_IBRS, 0);
        }
        // CPUID.7.EDX[26] masked: no SPEC_CTRL, so no IBRS of either kind.
        let masked = unplanned(&Caps { leaf7_edx: 1 << 27, ..c }, Rejected::Ibpb, false);
        assert_eq!(spec_flags_of(&masked, false), spec_flags::VERW_BUFFERS);
        // An unknown vendor gets nothing but buffer clearing.
        let other = unplanned(&Caps { vendor: Vendor::Other, ..c }, Rejected::Vendor, false);
        assert_eq!(spec_flags_of(&other, false), spec_flags::VERW_BUFFERS);
        // AMD: AutoIBRS and STIBP are not eIBRS.
        let amd = Caps {
            vendor: Vendor::Amd,
            family: 0x19,
            model: 0x11,
            amd8: policy::AMD_IBPB | policy::AMD_STIBP,
            amd21: policy::AUTO_IBRS,
            ..c
        };
        let s = unplanned(&amd, Rejected::BufferMicrocode, false);
        assert_eq!(spec_flags_of(&s, false), spec_flags::AUTO_IBRS | spec_flags::STIBP | spec_flags::VERW_BUFFERS);
        let f = Facts { spec: s, ..NONE };
        assert_eq!(ask(&f, keys::SPEC_ENTRY_ACTIONS), Some(spec_actions::IBPB | spec_actions::RSB));
    }

    #[test]
    fn msr_keys() {
        let all = [
            (keys::X86_ARCH_CAPABILITIES, spec_msr_valid::ARCH_CAPABILITIES),
            (keys::SPEC_CTRL_MSR, spec_msr_valid::SPEC_CTRL),
            (keys::SPEC_TSX_CTRL_MSR, spec_msr_valid::TSX_CTRL),
            (keys::SPEC_MCU_OPT_CTRL_MSR, spec_msr_valid::MCU_OPT_CTRL),
            (keys::SPEC_AMD_DE_CFG_MSR, spec_msr_valid::AMD_DE_CFG),
            (keys::SPEC_AMD_BP_CFG_MSR, spec_msr_valid::AMD_BP_CFG),
        ];
        let msrs: [u64; spec::MSRS] = core::array::from_fn(|i| 1 << 62 | 0x100 + i as u64);
        // EFER alone always has a value.
        let none = Facts { spec: spec::Facts { msrs, ..NO_SPEC }, ..NONE };
        assert_eq!(ask(&none, keys::SPEC_MSR_VALID), Some(1 << 4));
        assert_eq!(ask(&none, keys::SPEC_EFER_MSR), Some(0xd01));
        for (key, bit) in all {
            assert_eq!(ask(&none, key), Some(0), "{key:#x}");
            let f = Facts { spec: spec::Facts { msrs, msr_valid: bit, ..NO_SPEC }, ..NONE };
            assert_eq!(ask(&f, keys::SPEC_MSR_VALID), Some(bit | 1 << 4));
            for (k, b) in all {
                let want = if b == bit { 1 << 62 | 0x100 + bit.trailing_zeros() as u64 } else { 0 };
                assert_eq!(ask(&f, k), Some(want), "{key:#x} {k:#x}");
            }
        }
        // Present with the value 0.
        let zero = Facts { spec: spec::Facts { msr_valid: 1 << 1, ..NO_SPEC }, ..NONE };
        assert_eq!((ask(&zero, keys::SPEC_CTRL_MSR), ask(&zero, keys::SPEC_MSR_VALID)), (Some(0), Some(1 << 1 | 1 << 4)));
    }

    /// Which MSRs a core may be asked for: never one it does not enumerate,
    /// nor, in a confidential guest, one the kernel does not need.
    #[test]
    fn msrs_are_read_only_where_enumerated() {
        use policy::*;
        let i = intel();
        let none = Caps { arch: 0, leaf7_edx: 0, ..i };
        let amd = Caps { vendor: Vendor::Amd, family: 0x19, model: 0x11, amd8: 0, ..none };
        let other = Caps { vendor: Vendor::Other, arch: !0, leaf7_edx: !0, amd8: !0, ..i };

        assert!(spec_ctrl_readable(&i, false) && !spec_ctrl_readable(&i, true));
        assert!(!spec_ctrl_readable(&none, false));
        for bit in [14, 15, 24] {
            let c = Caps { amd8: 1 << bit, ..amd };
            assert!(spec_ctrl_readable(&c, false) && !spec_ctrl_readable(&c, true), "bit {bit}");
        }
        // IBPB alone (PRED_CMD) and VIRT_SSBD are other MSRs; Intel's bits
        // mean nothing on AMD, nor AMD's on Intel.
        assert!(!spec_ctrl_readable(&Caps { amd8: AMD_IBPB | 1 << 25, leaf7_edx: !0, ..amd }, false));
        assert!(!spec_ctrl_readable(&Caps { amd8: !0, ..none }, false));

        assert!(has_arch_capabilities(&Caps { leaf7_edx: 1 << 29, ..none }) && !has_arch_capabilities(&none));
        assert!(!has_arch_capabilities(&Caps { leaf7_edx: !0, ..amd }));

        let tsx = Caps { arch: TSX_CTRL, ..none };
        assert!(has_tsx_ctrl(&tsx, false) && !has_tsx_ctrl(&tsx, true) && !has_tsx_ctrl(&none, false));
        for arch in [FB_CLEAR_CTRL, GDS_CTRL] {
            let c = Caps { arch, ..none };
            assert!(has_mcu_opt_ctrl(&c, false) && !has_mcu_opt_ctrl(&c, true), "{arch:#x}");
        }
        assert!(!has_mcu_opt_ctrl(&Caps { arch: !(FB_CLEAR_CTRL | GDS_CTRL), ..none }, false));

        assert!(sets_de_cfg(&amd) && sets_bp_cfg(&amd));
        let zen2 = Caps { family: 0x17, model: 0x31, ..amd };
        assert!(sets_de_cfg(&zen2) && !sets_bp_cfg(&zen2));
        let zen3 = Caps { model: 0x01, ..amd };
        assert!(sets_de_cfg(&zen3) && !sets_bp_cfg(&zen3));
        for c in [Caps { hypervisor: true, ..amd }, Caps { family: 0x17, model: 1, ..amd }, i] {
            assert!(!sets_de_cfg(&c) && !sets_bp_cfg(&c));
        }

        assert!(!spec_ctrl_readable(&other, false) && !has_arch_capabilities(&other) && !has_tsx_ctrl(&other, false));
        assert!(!has_mcu_opt_ctrl(&other, false) && !sets_de_cfg(&other) && !sets_bp_cfg(&other));
    }

    /// The entry actions are every core's, the IBRS kind the boot core's.
    #[test]
    fn spec_entry_actions_are_the_union() {
        let s = spec::Facts { entry: policy::IBPB | policy::BHB, ..planned(PLAN, true) };
        let f = Facts { spec: s, ..NONE };
        assert_eq!(ask(&f, keys::SPEC_ENTRY_ACTIONS), Some(1 | 16));
    }

    #[test]
    fn vm_exit_actions_need_an_active_backend() {
        let plan = Plan { vmexit: policy::IBPB | policy::RSB | policy::IBHF, ..PLAN };
        let of = |s| Facts { spec: s, ..NONE }.answer(Slot::SPEC_VMEXIT_ACTIONS);
        assert_eq!(of(planned(plan, true)), 1 | 2 | 32);
        assert_eq!(of(planned(plan, false)), 0);
        assert_eq!(of(spec::Facts { vm: true, ..NO_SPEC }), 0);
    }

    #[test]
    fn deferred_vm_exit_ibpb_needs_a_backend_and_protected_branches() {
        let deferred = |s: spec::Facts| spec_flags_of(&s, false) & spec_flags::VMEXIT_IBPB_DEFERRED != 0;
        // eIBRS (no entry IBPB), legacy IBRS, AutoIBRS with Safe RET or not.
        let eibrs = Plan { entry: 0, spec_ctrl: 1, ..PLAN };
        assert!(deferred(planned(eibrs, true)));
        assert!(!deferred(planned(eibrs, false)));
        let legacy = Plan { entry: policy::LEGACY_IBRS, spec_ctrl: 1, ..PLAN };
        assert!(!deferred(planned(legacy, true)));
        let auto = Plan { auto_ibrs: true, ..PLAN };
        assert!(!deferred(planned(auto, true)));
        assert!(deferred(spec::Facts { safe_ret: true, ..planned(auto, true) }));
        assert!(!deferred(spec::Facts { safe_ret: true, ..planned(auto, false) }));
        // Never without a plan.
        assert!(!deferred(spec::Facts { vm: true, ..unplanned(&intel(), Rejected::Lfence, true) }));
    }
}
