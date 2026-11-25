//! Constants of FL4's libsel4 that the kernel must agree with. Values follow
//! `libsel4/` (FL4's copy); where FL4 differs from seL4 the libsel4 header
//! says so too.

/// `seL4_Error`.
pub mod error {
    pub const NoError: u64 = 0;
    pub const InvalidArgument: u64 = 1;
    pub const InvalidCapability: u64 = 2;
    pub const IllegalOperation: u64 = 3;
    pub const RangeError: u64 = 4;
    pub const AlignmentError: u64 = 5;
    pub const FailedLookup: u64 = 6;
    pub const TruncatedMessage: u64 = 7;
    pub const DeleteFirst: u64 = 8;
    pub const RevokeFirst: u64 = 9;
    pub const NotEnoughMemory: u64 = 10;
}

/// `seL4_ObjectType` for x86_64 MCS with huge pages.
#[cfg(not(feature = "aarch64"))]
pub mod object {
    pub const Untyped: u64 = 0;
    pub const Tcb: u64 = 1;
    pub const Endpoint: u64 = 2;
    pub const Notification: u64 = 3;
    pub const CapTable: u64 = 4;
    pub const SchedContext: u64 = 5;
    pub const Reply: u64 = 6;
    pub const NonArchCount: u64 = 7;
    pub const X86Pdpt: u64 = 7;
    pub const X64Pml4: u64 = 8;
    pub const X64HugePage: u64 = 9;
    pub const X86Page4K: u64 = 10;
    pub const X86LargePage: u64 = 11;
    pub const X86PageTable: u64 = 12;
    pub const X86PageDirectory: u64 = 13;
    pub const X86Vcpu: u64 = 14;
    pub const X86EptPml4: u64 = 15;
    pub const X86EptPdpt: u64 = 16;
    pub const X86EptPd: u64 = 17;
    pub const X86EptPt: u64 = 18;
    pub const Count: u64 = 19;
}

/// `seL4_ObjectType` for AArch64 MCS without EL2. The x86 types follow as
/// numbers no caller can pass, so the x86 object code in fl4-core compiles
/// and never matches.
#[cfg(feature = "aarch64")]
pub mod object {
    pub const Untyped: u64 = 0;
    pub const Tcb: u64 = 1;
    pub const Endpoint: u64 = 2;
    pub const Notification: u64 = 3;
    pub const CapTable: u64 = 4;
    pub const SchedContext: u64 = 5;
    pub const Reply: u64 = 6;
    pub const NonArchCount: u64 = 7;
    pub const ArmHugePage: u64 = 7;
    pub const ArmVSpace: u64 = 8;
    pub const ArmSmallPage: u64 = 9;
    pub const ArmLargePage: u64 = 10;
    pub const ArmPageTable: u64 = 11;
    pub const ArmVcpu: u64 = 12;
    pub const ArmStage2VSpace: u64 = 13;
    /// FL4: the TTBR1 (upper-half) EL0 window of `seL4_TCB_SetHighVSpace`,
    /// usable without EL2.
    pub const ArmHighVSpace: u64 = 14;
    pub const Count: u64 = 15;
    pub const X86Pdpt: u64 = u64::MAX - 11;
    pub const X64Pml4: u64 = u64::MAX - 10;
    pub const X64HugePage: u64 = u64::MAX - 9;
    pub const X86Page4K: u64 = u64::MAX - 8;
    pub const X86LargePage: u64 = u64::MAX - 7;
    pub const X86PageTable: u64 = u64::MAX - 6;
    pub const X86PageDirectory: u64 = u64::MAX - 5;
    pub const X86Vcpu: u64 = u64::MAX - 4;
    pub const X86EptPml4: u64 = u64::MAX - 3;
    pub const X86EptPdpt: u64 = u64::MAX - 2;
    pub const X86EptPd: u64 = u64::MAX - 1;
    pub const X86EptPt: u64 = u64::MAX;
}

/// Object sizes (`seL4_*Bits`).
pub mod bits {
    pub const WORD_BITS: u64 = 64;
    pub const WORD_SIZE_BITS: u64 = 3;
    pub const PAGE: u64 = 12;
    pub const LARGE_PAGE: u64 = 21;
    pub const HUGE_PAGE: u64 = 30;
    pub const SLOT: u64 = 5;
    /// FL4: 4 KiB, to hold the AVX-512 XSAVE image (DESIGN.md §2).
    pub const TCB: u64 = 12;
    #[cfg(not(feature = "aarch64"))]
    pub const VCPU: u64 = 15;
    #[cfg(feature = "aarch64")]
    pub const VCPU: u64 = 12;
    pub const STAGE2_VSPACE: u64 = 13;
    /// FL4 AArch64 `ArmHighVSpace`: 8 KiB, the TTBR1 level-0 table and the
    /// level-1 table its last entry points to.
    #[cfg(feature = "aarch64")]
    pub const HIGH_VSPACE: u64 = 13;
    pub const ENDPOINT: u64 = 4;
    pub const NOTIFICATION: u64 = 6;
    pub const REPLY: u64 = 5;
    pub const PAGE_TABLE: u64 = 12;
    pub const ASID_POOL: u64 = 12;
    pub const ASID_POOL_INDEX: u64 = 9;
    #[cfg(not(feature = "aarch64"))]
    pub const NUM_ASID_POOLS: u64 = 11;
    /// AArch64: 16-bit hardware ASIDs (l4h 0016, `TCR_EL1.AS`).
    #[cfg(feature = "aarch64")]
    pub const NUM_ASID_POOLS: u64 = 7;
    pub const MIN_UNTYPED: u64 = 4;
    pub const MAX_UNTYPED: u64 = 47;
    pub const MIN_SCHED_CONTEXT: u64 = 7;
    pub const IPC_BUFFER: u64 = 10;
}

pub const CORE_SCHED_CONTEXT_BYTES: u64 = 10 * 8 + 6 * 8;
pub const REFILL_SIZE_BYTES: u64 = 16;

pub const MSG_MAX_LENGTH: u64 = 120;
pub const MSG_MAX_EXTRA_CAPS: u64 = 3;
pub const FAST_MESSAGE_REGISTERS: u64 = 4;
/// The kernel's `USER_TOP` (C seL4 pc99 `hardware.h`): the last address
/// below the sign-extension hole. Not libsel4's `seL4_UserTop`, which is a
/// page lower. AArch64 without EL2 has the same value (`seL4_UserTop`).
pub const USER_TOP: u64 = 0x0000_7fff_ffff_ffff;
pub const NUM_PRIORITIES: u64 = 256;
pub const MAX_PRIO: u64 = NUM_PRIORITIES - 1;
/// FL4: standard-layout XSAVE image up to PKRU (DESIGN.md §2, §3).
#[cfg(not(feature = "aarch64"))]
pub const FPU_STATE_SIZE: u64 = 2696;
/// AArch64: V0-V31, then FPSR and FPCR as 32-bit words.
#[cfg(feature = "aarch64")]
pub const FPU_STATE_SIZE: u64 = 64 * 8 + 8;

/// `seL4_FaultType` tags.
pub mod fault {
    pub const NullFault: u64 = 0;
    pub const CapFault: u64 = 1;
    pub const UnknownSyscall: u64 = 2;
    pub const UserException: u64 = 3;
    pub const DebugException: u64 = 4;
    pub const Timeout: u64 = 5;
    pub const VMFault: u64 = 6;
    #[cfg(feature = "aarch64")]
    pub const VGICMaintenance: u64 = 7;
    #[cfg(feature = "aarch64")]
    pub const VCPUFault: u64 = 8;
    #[cfg(feature = "aarch64")]
    pub const VPPIEvent: u64 = 9;
}

/// AArch64 `seL4_VCPUReg` indices (0..=24 match upstream seL4; 25..=63 are
/// FL4 extensions for hypervisor/debug/VGIC state).
#[cfg(feature = "aarch64")]
pub mod vcpu_reg {
    pub const SCTLR: u64 = 0;
    pub const CPACR: u64 = 1;
    pub const TCR: u64 = 2;
    pub const TTBR0: u64 = 3;
    pub const TTBR1: u64 = 4;
    pub const MAIR: u64 = 5;
    pub const AMAIR: u64 = 6;
    pub const CIDR: u64 = 7;
    pub const AFSR0: u64 = 8;
    pub const AFSR1: u64 = 9;
    pub const ESR: u64 = 10;
    pub const FAR: u64 = 11;
    pub const PAR: u64 = 12;
    pub const VBAR: u64 = 13;
    pub const TPIDR_EL1: u64 = 14;
    pub const VMPIDR_EL2: u64 = 15;
    pub const SP_EL1: u64 = 16;
    pub const ELR_EL1: u64 = 17;
    pub const SPSR_EL1: u64 = 18;
    pub const CSSELR_EL1: u64 = 19;
    pub const VDISR_EL2: u64 = 20;
    pub const CNTV_CTL: u64 = 21;
    pub const CNTV_CVAL: u64 = 22;
    pub const CNTVOFF: u64 = 23;
    pub const CNTKCTL_EL1: u64 = 24;
    pub const VPIDR_EL2: u64 = 25;
    pub const HCR_EL2: u64 = 26;
    pub const VSESR_EL2: u64 = 27;
    pub const ACTLR_EL1: u64 = 28;
    pub const MDSCR_EL1: u64 = 29;
    pub const MDCCINT_EL1: u64 = 30;
    pub const FAR_EL2: u64 = 31;
    pub const HPFAR_EL2: u64 = 32;
    pub const ESR_EL2: u64 = 33;
    pub const VGIC_VTR: u64 = 34;
    pub const VGIC_HCR: u64 = 35;
    pub const VGIC_VMCR: u64 = 36;
    pub const VGIC_MISR: u64 = 37;
    pub const VGIC_EISR: u64 = 38;
    pub const VGIC_ELRSR: u64 = 39;
    pub const VGIC_AP0R0: u64 = 40;
    pub const VGIC_AP0R1: u64 = 41;
    pub const VGIC_AP0R2: u64 = 42;
    pub const VGIC_AP0R3: u64 = 43;
    pub const VGIC_AP1R0: u64 = 44;
    pub const VGIC_AP1R1: u64 = 45;
    pub const VGIC_AP1R2: u64 = 46;
    pub const VGIC_AP1R3: u64 = 47;
    pub const VGIC_LR0: u64 = 48;
    pub const VGIC_LR15: u64 = 63;
    pub const NUM: u64 = 64;
}

/// Bitmask for `ARMVCPUReadState` / `ARMVCPUWriteState`.
#[cfg(feature = "aarch64")]
pub mod vcpu_state_mask {
    pub const EL1_SYSREGS: u64 = 1 << 0;
    pub const HYP: u64 = 1 << 1;
    pub const TIMER: u64 = 1 << 2;
    pub const VGIC: u64 = 1 << 3;
    pub const GPRS: u64 = 1 << 4;
    pub const VGIC_LR: u64 = 1 << 5;
    pub const ALL: u64 = EL1_SYSREGS | HYP | TIMER | VGIC | GPRS | VGIC_LR;
    pub const SIZE: u64 = 1024;
}

/// Exit reasons (`stop` word) returned by `ARMVCPURun`.
#[cfg(feature = "aarch64")]
pub mod vcpu_run_stop {
    pub const INTERRUPT: u64 = 0;
    pub const VMFAULT: u64 = 1;
    pub const VCPUFAULT: u64 = 2;
    pub const VGIC_MAINT: u64 = 3;
    pub const VPPI: u64 = 4;
}

/// `seL4_LookupFailureType`.
pub mod lookup {
    pub const NoFailure: u64 = 0;
    pub const InvalidRoot: u64 = 1;
    pub const MissingCapability: u64 = 2;
    pub const DepthMismatch: u64 = 3;
    pub const GuardMismatch: u64 = 4;
}

/// `seL4_TCBFlag`.
pub mod tcb_flag {
    pub const FPU_DISABLED: u64 = 0x1;
    /// l4h 0001: every syscall instruction becomes an UnknownSyscall fault.
    pub const TRAP_SYSCALLS: u64 = 0x2;
    pub const MASK: u64 = FPU_DISABLED | TRAP_SYSCALLS;
}

/// `seL4_SchedContextFlag`.
pub mod sc_flag {
    pub const SPORADIC: u64 = 0x1;
}

/// `seL4_ARM_VMAttributes`.
/// FL4 AArch64: the TTBR1 addresses an `ArmHighVSpace` may map, level-0
/// entry 511, level-1 entries 384-495 (112 GiB). The kernel's own TTBR1
/// leaves level-0 entry 511 invalid: its window over RAM
/// (`PPTR_BASE..PPTR_TOP`) is entries 256-509, its device mappings and
/// image (`KERNEL_VBASE`) entry 510, below `0xffff_ff80_0000_0000`.
#[cfg(feature = "aarch64")]
pub const HIGH_VSPACE_BASE: u64 = 0xffff_ffe0_0000_0000;
#[cfg(feature = "aarch64")]
pub const HIGH_VSPACE_TOP: u64 = 0xffff_fffc_0000_0000;

/// FL4 AArch64 `seL4_TCB_SetPACKeys` flags: the SCTLR_EL1 pointer
/// authentication enables the thread runs with.
#[cfg(feature = "aarch64")]
pub mod pac_flag {
    pub const EN_IA: u64 = 1;
    pub const EN_IB: u64 = 2;
    pub const EN_DA: u64 = 4;
    pub const EN_DB: u64 = 8;
    pub const MASK: u64 = 0xf;
}

#[cfg(feature = "aarch64")]
pub mod arm_vm_attr {
    pub const PAGE_CACHEABLE: u64 = 1;
    pub const PARITY_ENABLED: u64 = 2;
    pub const EXECUTE_NEVER: u64 = 4;
}

/// `seL4_X86_VMAttributes`.
pub mod vm_attr {
    pub const WRITE_BACK: u64 = 0;
    pub const WRITE_THROUGH: u64 = 1;
    pub const CACHE_DISABLED: u64 = 2;
    pub const UNCACHEABLE: u64 = 3;
    pub const WRITE_COMBINING: u64 = 4;
    /// l4h 0009.
    pub const EXECUTE_NEVER: u64 = 8;
    /// l4h 0017.
    pub const DEFER_FLUSH: u64 = 16;
}

/// Root task CSpace slots (`seL4_RootCNodeCapSlots`).
pub mod root_slot {
    pub const Null: u64 = 0;
    pub const InitThreadTCB: u64 = 1;
    pub const InitThreadCNode: u64 = 2;
    pub const InitThreadVSpace: u64 = 3;
    pub const IRQControl: u64 = 4;
    pub const ASIDControl: u64 = 5;
    pub const InitThreadASIDPool: u64 = 6;
    pub const IOPortControl: u64 = 7;
    pub const IOSpace: u64 = 8;
    pub const BootInfoFrame: u64 = 9;
    pub const InitThreadIPCBuffer: u64 = 10;
    pub const Domain: u64 = 11;
    pub const SMMUSIDControl: u64 = 12;
    pub const SMMUCBControl: u64 = 13;
    pub const InitThreadSC: u64 = 14;
    pub const SMC: u64 = 15;
    pub const NumInitialCaps: u64 = 16;
}

/// `seL4_AArch64VirtInfo::flags` bits (`bootinfo_header::AARCH64_VIRT_INFO`).
#[cfg(feature = "aarch64")]
pub mod virt_info_flag {
    pub const VIRT_READY: u64 = 1 << 0;
    pub const EL2_VHE: u64 = 1 << 1;
    pub const VMID16: u64 = 1 << 2;
    pub const EL2_NVHE: u64 = 1 << 3;
}

/// `SEL4_BOOTINFO_HEADER_*`.
pub mod bootinfo_header {
    pub const PADDING: u64 = 0;
    pub const X86_VBE: u64 = 1;
    pub const X86_MBMMAP: u64 = 2;
    pub const X86_ACPI_RSDP: u64 = 3;
    pub const X86_FRAMEBUFFER: u64 = 4;
    pub const X86_TSC_FREQ: u64 = 5;
    pub const FDT: u64 = 6;
    pub const AARCH64_ID_REGS: u64 = 7;
    pub const X86_BOOT_MODULES: u64 = 8;
    pub const SHARED_DMA: u64 = 9;
    /// l4h 0047: untyped descriptors past the BootInfo's 230, whose caps
    /// follow `untyped.end`.
    pub const X86_EXTRA_UNTYPEDS: u64 = 10;
    /// AArch64 EL2/VHE virtualization capabilities and GIC/ID metadata.
    pub const AARCH64_VIRT_INFO: u64 = 11;
    /// UEFI TPM event log (seL4_TpmEventLog: paddr, size, flags).
    pub const TPM_EVENT_LOG: u64 = 12;
    /// UEFI confidential-computing event log (seL4_CcEventLog: paddr,
    /// size, flags; the flags are `tpm_event_log_flag`'s).
    pub const CC_EVENT_LOG: u64 = 13;
    /// Intel TDX guest facts (seL4_X86_TdxInfo: gpaw, attributes, td_ctls,
    /// num_vcpus, max_vcpus).
    pub const TDX_INFO: u64 = 14;
    /// AArch64 MSIs through a GICv3 ITS (seL4_AArch64MsiInfo: doorbell,
    /// num_lpis, num_events, num_devices), when the kernel drives one.
    pub const AARCH64_MSI_INFO: u64 = 15;
}

/// `bootinfo_header::TPM_EVENT_LOG` flags (libsel4 `seL4_TpmEventLog_*`).
pub mod tpm_event_log_flag {
    /// Events are missing at the end of the log.
    pub const TRUNCATED: u64 = 1 << 0;
    /// The log is in the TCG 1.2 (SHA-1) format; clear for TCG 2.0 crypto agile.
    pub const TCG_1_2: u64 = 1 << 1;
}

/// `bootinfo_header::CC_EVENT_LOG` flags (libsel4 `seL4_CcEventLog_*`).
pub mod cc_event_log_flag {
    pub const TRUNCATED: u64 = super::tpm_event_log_flag::TRUNCATED;
    pub const TCG_1_2: u64 = super::tpm_event_log_flag::TCG_1_2;
}

/// `SysKernelConfig` (libsel4 `seL4_KernelConfig`, whose constants
/// `seL4_KernelConfig_*` these are): what the kernel found and chose at
/// boot, one word per key. A key the kernel does not know, or one of the
/// other architecture, is `error::InvalidArgument`.
pub mod kernel_config {
    /// What `seL4_KernelConfig` can be asked for.
    pub mod keys {
        // Both architectures.
        pub const ARCH: u64 = 0x0001;
        pub const BUILD_FLAGS: u64 = 0x0002;
        /// Cores running the kernel.
        pub const ONLINE_CPUS: u64 = 0x0003;
        /// The most cores this kernel was built for (`CONFIG_MAX_NUM_NODES`).
        pub const MAX_CPUS: u64 = 0x0004;
        // Virtualization.
        pub const VIRT_BACKEND: u64 = 0x0100;
        pub const VIRT_REJECT: u64 = 0x0101;
        pub const VIRT_FEATURES: u64 = 0x0102;
        // Virtualization, AArch64 only.
        /// Stage-2 IPA width.
        pub const VIRT_S2_IPA_BITS: u64 = 0x0103;
        /// VGIC list registers (at most 16).
        pub const VIRT_VGIC_LRS: u64 = 0x0104;
        // Confidential VM (0 on AArch64).
        pub const CVM_TYPE: u64 = 0x0200;
        pub const CVM_FLAGS: u64 = 0x0201;
        // Mitigations, x86_64 only.
        pub const SPEC_STATUS: u64 = 0x0300;
        pub const SPEC_REJECT: u64 = 0x0301;
        pub const SPEC_FLAGS: u64 = 0x0302;
        /// `spec_actions` at native kernel entries (all cores').
        pub const SPEC_ENTRY_ACTIONS: u64 = 0x0303;
        /// The boot core's `spec_actions` at VM exits; 0 without a backend.
        pub const SPEC_VMEXIT_ACTIONS: u64 = 0x0304;
        // The boot core's MSRs as the kernel left them at boot; 0 for one
        // it does not have or may not read (`SPEC_MSR_VALID`).
        /// IA32_SPEC_CTRL.
        pub const SPEC_CTRL_MSR: u64 = 0x0305;
        /// IA32_TSX_CTRL.
        pub const SPEC_TSX_CTRL_MSR: u64 = 0x0306;
        /// IA32_MCU_OPT_CTRL.
        pub const SPEC_MCU_OPT_CTRL_MSR: u64 = 0x0307;
        /// IA32_EFER.
        pub const SPEC_EFER_MSR: u64 = 0x0308;
        /// MSR_AMD64_DE_CFG.
        pub const SPEC_AMD_DE_CFG_MSR: u64 = 0x0309;
        /// MSR_ZEN4_BP_CFG.
        pub const SPEC_AMD_BP_CFG_MSR: u64 = 0x030a;
        /// `spec_msr_valid`.
        pub const SPEC_MSR_VALID: u64 = 0x030b;
        // Mitigations, AArch64 only.
        pub const ARM_MITIGATIONS: u64 = 0x0380;
        // CPU and platform, x86_64 only.
        pub const X86_CPU_VENDOR: u64 = 0x0400;
        pub const X86_CPU_FEATURES: u64 = 0x0401;
        /// XCR0 (0 without XSAVE).
        pub const X86_FPU_XCR0: u64 = 0x0402;
        pub const X86_FPU_SAVE_INSN: u64 = 0x0403;
        /// TSC rate in MHz.
        pub const X86_TSC_MHZ: u64 = 0x0404;
        pub const X86_TSC_SOURCE: u64 = 0x0405;
        /// The boot core's microcode revision where the mitigation policy reads
        /// it; 0 otherwise (a hypervisor, TDX).
        pub const X86_MICROCODE_REV: u64 = 0x0406;
        /// The boot core's physical address width.
        pub const X86_MAX_PADDR_BITS: u64 = 0x0407;
        /// IOAPICs the kernel drives.
        pub const X86_IOAPIC_COUNT: u64 = 0x0408;
        /// The boot core's IA32_ARCH_CAPABILITIES (Intel's; 0 on others, or
        /// without the MSR).
        pub const X86_ARCH_CAPABILITIES: u64 = 0x0409;
        // CPU and platform, AArch64 only.
        pub const ARM_PLATFORM_FLAGS: u64 = 0x0480;
        /// Physical address bits (at most 48).
        pub const ARM_PA_BITS: u64 = 0x0481;
        /// 2 or 3.
        pub const ARM_GIC_VERSION: u64 = 0x0482;
        /// The highest SPI's INTID.
        pub const ARM_MAX_SPI: u64 = 0x0483;
        pub const ARM_PSCI_METHOD: u64 = 0x0484;
        /// CNTFRQ_EL0.
        pub const ARM_TIMER_FREQ_HZ: u64 = 0x0485;
    }
    /// `keys::ARCH`.
    pub mod arch {
        pub const X86_64: u64 = 1;
        pub const AARCH64: u64 = 2;
    }
    /// `keys::BUILD_FLAGS`: the settings the kernel was built with.
    pub mod build_flags {
        pub const DEBUG_BUILD: u64 = 1 << 0;
        pub const PRINTING: u64 = 1 << 1;
        pub const SMP: u64 = 1 << 2;
        pub const HW_DEBUG_API: u64 = 1 << 3;
        pub const EXPORT_PMC_USER: u64 = 1 << 4;
        pub const DANGEROUS_MSR: u64 = 1 << 5;
    }
    /// `keys::VIRT_BACKEND`.
    pub mod virt_backend {
        pub const NONE: u64 = 0;
        pub const VTX: u64 = 1;
        pub const AMDV: u64 = 2;
        pub const EL2_VHE: u64 = 3;
        pub const EL2_NVHE: u64 = 4;
    }
    /// `keys::VIRT_REJECT`: why `VIRT_BACKEND` is `NONE`; `NONE` exactly when
    /// a backend is active.
    pub mod virt_reject {
        pub const NONE: u64 = 0;
        pub const NO_HW: u64 = 1;
        pub const DISABLED_BY_FIRMWARE: u64 = 2;
        pub const MISSING_FEATURES: u64 = 3;
        pub const SPEC_POLICY_REJECTED: u64 = 4;
        pub const SKIM_ACTIVE: u64 = 5;
        pub const CVM_ACTIVE: u64 = 6;
        pub const VMXON_FAILED: u64 = 7;
        pub const NOVIRT_CMDLINE: u64 = 8;
        pub const NO_VGIC: u64 = 9;
        pub const EL1_ONLY: u64 = 10;
    }
    /// `keys::VIRT_FEATURES`: the x86_64 bits (`X86_*`) and, the same bits
    /// meaning something else, the AArch64 ones (`ARM_*`).
    pub mod virt_features {
        pub const X86_VPID_SINGLE: u64 = 1 << 0;
        pub const X86_VPID_ALL: u64 = 1 << 1;
        pub const X86_INVEPT_SINGLE: u64 = 1 << 2;
        pub const X86_SVM_VMCB_CLEAN: u64 = 1 << 3;
        pub const X86_VMX_PERF_GLOBAL_CTRL: u64 = 1 << 4;
        pub const ARM_VIRT_READY: u64 = 1 << 0;
        pub const ARM_VMID16: u64 = 1 << 1;
        pub const ARM_GICV2_VGIC: u64 = 1 << 2;
        pub const ARM_GICV3_VGIC: u64 = 1 << 3;
    }
    /// `keys::CVM_TYPE`.
    pub mod cvm_type {
        pub const NONE: u64 = 0;
        pub const SEV: u64 = 1;
        pub const SEV_SNP: u64 = 2;
        pub const TDX: u64 = 3;
    }
    /// `keys::CVM_FLAGS`.
    pub mod cvm_flags {
        pub const HARDENED: u64 = 1 << 0;
        pub const SHARED_DMA: u64 = 1 << 1;
    }
    /// `keys::SPEC_STATUS`.
    pub mod spec_status {
        pub const INCOMPLETE: u64 = 0;
        pub const COMPLETE: u64 = 1;
    }
    /// `keys::SPEC_REJECT`: why `SPEC_STATUS` is `INCOMPLETE`.
    pub mod spec_reject {
        pub const NONE: u64 = 0;
        pub const VENDOR: u64 = 1;
        pub const MELTDOWN: u64 = 2;
        pub const SMEP: u64 = 3;
        pub const BEFORE_ZEN2: u64 = 4;
        pub const IBPB: u64 = 5;
        pub const SRSO_MICROCODE: u64 = 6;
        pub const BUFFER_MICROCODE: u64 = 7;
        pub const ITS_MICROCODE: u64 = 8;
        pub const LFENCE: u64 = 9;
    }
    /// `keys::SPEC_FLAGS`.
    pub mod spec_flags {
        pub const SKIM: u64 = 1 << 0;
        pub const SAFE_RET: u64 = 1 << 1;
        pub const RETPOLINE: u64 = 1 << 2;
        pub const EIBRS: u64 = 1 << 3;
        pub const AUTO_IBRS: u64 = 1 << 4;
        pub const LEGACY_IBRS: u64 = 1 << 5;
        pub const STIBP: u64 = 1 << 6;
        pub const BHI_DIS_S: u64 = 1 << 7;
        pub const VERW_BUFFERS: u64 = 1 << 8;
        pub const NO_SMT: u64 = 1 << 9;
        pub const DISABLE_TSX: u64 = 1 << 10;
        pub const VMEXIT_IBPB_DEFERRED: u64 = 1 << 11;
        pub const EAGER_FPU: u64 = 1 << 12;
    }
    /// `keys::SPEC_ENTRY_ACTIONS` and `keys::SPEC_VMEXIT_ACTIONS`.
    pub mod spec_actions {
        pub const IBPB: u64 = 1 << 0;
        pub const RSB: u64 = 1 << 1;
        pub const PBRSB: u64 = 1 << 2;
        pub const LEGACY_IBRS: u64 = 1 << 3;
        pub const BHB: u64 = 1 << 4;
        pub const IBHF: u64 = 1 << 5;
    }
    /// `keys::SPEC_MSR_VALID`: the MSRs read or written at boot, so that
    /// their keys (`SPEC_*_MSR`, `X86_ARCH_CAPABILITIES`) are values.
    pub mod spec_msr_valid {
        pub const ARCH_CAPABILITIES: u64 = 1 << 0;
        pub const SPEC_CTRL: u64 = 1 << 1;
        pub const TSX_CTRL: u64 = 1 << 2;
        pub const MCU_OPT_CTRL: u64 = 1 << 3;
        pub const EFER: u64 = 1 << 4;
        pub const AMD_DE_CFG: u64 = 1 << 5;
        pub const AMD_BP_CFG: u64 = 1 << 6;
    }
    /// `keys::ARM_MITIGATIONS`.
    pub mod arm_mitigations {
        pub const PAN: u64 = 1 << 0;
        pub const PAUTH: u64 = 1 << 1;
        pub const CLRBHB: u64 = 1 << 2;
    }
    /// `keys::X86_CPU_VENDOR`.
    pub mod x86_vendor {
        pub const OTHER: u64 = 0;
        pub const INTEL: u64 = 1;
        pub const AMD: u64 = 2;
        pub const HYGON: u64 = 3;
    }
    /// `keys::X86_CPU_FEATURES`: what the kernel turned on, but `HYPERVISOR`
    /// (CPUID.1:ECX\[31\]).
    pub mod x86_features {
        pub const NX: u64 = 1 << 0;
        pub const SMEP: u64 = 1 << 1;
        pub const SMAP: u64 = 1 << 2;
        pub const FSGSBASE: u64 = 1 << 3;
        pub const HUGE_PAGES_1G: u64 = 1 << 4;
        pub const PCID: u64 = 1 << 5;
        pub const INVPCID: u64 = 1 << 6;
        pub const X2APIC: u64 = 1 << 7;
        pub const TSC_DEADLINE: u64 = 1 << 8;
        pub const IDLE_POLL: u64 = 1 << 9;
        pub const HYPERVISOR: u64 = 1 << 10;
    }
    /// `keys::X86_FPU_SAVE_INSN`.
    pub mod x86_fpu_insn {
        pub const FXSAVE: u64 = 0;
        pub const XSAVE: u64 = 1;
        pub const XSAVEOPT: u64 = 2;
        pub const XSAVEC: u64 = 3;
        pub const XSAVES: u64 = 4;
    }
    /// `keys::X86_TSC_SOURCE`.
    pub mod x86_tsc_source {
        pub const CPUID: u64 = 1;
        pub const HYPERVISOR: u64 = 2;
        pub const PIT: u64 = 3;
        pub const KVM: u64 = 4;
    }
    /// `keys::ARM_PLATFORM_FLAGS`.
    pub mod arm_platform_flags {
        pub const ASID16: u64 = 1 << 0;
        pub const HW_AF: u64 = 1 << 1;
        pub const GICV3_SRE: u64 = 1 << 2;
        pub const ITS_ACTIVE: u64 = 1 << 3;
        pub const TIMER_LOCAL_ACK: u64 = 1 << 4;
        pub const EL2_VHE: u64 = 1 << 5;
        pub const EL2_NVHE: u64 = 1 << 6;
    }
    /// `keys::ARM_PSCI_METHOD`.
    pub mod arm_psci {
        pub const ABSENT: u64 = 0;
        pub const SMC: u64 = 1;
        pub const HVC: u64 = 2;
    }
}
