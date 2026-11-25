//! Checks on the interface XML that FL4's generators do not need but other
//! bindings generators do (GitHub issue #4).

const SYSCALLS: &str = include_str!("../../../interfaces/syscall.xml");

/// rust-sel4's sel4-sys parser requires both API sections, even for an MCS
/// build. FL4 keeps the non-MCS one, empty, before the MCS one.
#[test]
fn syscall_xml_keeps_an_empty_api_master() {
    let master = SYSCALLS.find("<api-master/>").expect("syscall.xml has no empty <api-master/>");
    let mcs = SYSCALLS.find("<api-mcs>").expect("syscall.xml has no <api-mcs>");
    assert!(master < mcs, "<api-master/> must come before <api-mcs>");
    assert!(!SYSCALLS.contains("<api-master>"), "<api-master> must stay empty: FL4 has no non-MCS syscalls");
}

const BOOTINFO_TYPES: &str = include_str!("../../../libsel4/include/sel4/bootinfo_types.h");
const X86_TYPES: &str = include_str!("../../../libsel4/arch_include/x86/sel4/arch/types.h");
const EXTENSIONS: &str = include_str!("../../../interfaces/object-api-extensions.xml");

/// The BootInfo records and the cap slot `l4h` builds against, on both
/// sides of the kernel/libsel4 boundary.
#[test]
fn tdx_bootinfo_ids_and_cap_slot_match_libsel4() {
    use fl4_abi::consts::{bootinfo_header as h, cc_event_log_flag as f, root_slot};
    assert_eq!(h::CC_EVENT_LOG, 13);
    assert_eq!(h::TDX_INFO, 14);
    assert_eq!((f::TRUNCATED, f::TCG_1_2), (1, 2));
    assert_eq!(root_slot::SMC, 15);
    assert_eq!(root_slot::NumInitialCaps, 16);
    for line in [
        "SEL4_BOOTINFO_HEADER_CC_EVENT_LOG       = 13,",
        "SEL4_BOOTINFO_HEADER_TDX_INFO           = 14,",
        "#define seL4_CapX86TdxControl seL4_CapSMC",
        "#define seL4_CcEventLog_Truncated (1ul << 0)",
        "#define seL4_CcEventLog_Tcg12     (1ul << 1)",
        "typedef struct seL4_CcEventLog {",
        "typedef struct seL4_X86_TdxInfo {",
    ] {
        assert!(BOOTINFO_TYPES.contains(line), "{line}");
    }
    let info = &BOOTINFO_TYPES[BOOTINFO_TYPES.find("typedef struct seL4_X86_TdxInfo {").unwrap()..];
    let info = &info[..info.find('}').unwrap()];
    let order = ["gpaw", "attributes", "td_ctls", "num_vcpus", "max_vcpus"].map(|f| info.find(&format!("seL4_Word {f}")).expect(f));
    assert!(order.windows(2).all(|w| w[0] < w[1]), "seL4_X86_TdxInfo's field order");
    assert!(X86_TYPES.contains("typedef seL4_CPtr seL4_X86_TdxControl;"));
}

/// Every TDX method is x86_64 only, with the parameters the ABI names.
#[test]
fn tdx_methods_are_x86_only_and_have_their_parameters() {
    let iface = &EXTENSIONS[EXTENSIONS.find("<interface name=\"seL4_X86_TdxControl\"").expect("interface")..];
    let params = |id: &str, dir: &str| -> Vec<String> {
        let m = &iface[iface.find(&format!("<method id=\"{id}\"")).unwrap_or_else(|| panic!("{id}"))..];
        let m = &m[..m.find("</method>").unwrap()];
        assert!(m.contains("<condition><not><config var=\"CONFIG_ARCH_AARCH64\"/></not></condition>"), "{id}");
        let tag = format!("<param dir=\"{dir}\" name=\"");
        m.match_indices(&tag).map(|(at, _)| {
            let name = &m[at + tag.len()..];
            name[..name.find('"').unwrap()].to_string()
        }).collect()
    };
    let words = |n: usize| (0..n).map(|i| format!("d{i}")).collect::<Vec<_>>();
    let mut report = vec!["report_frame".to_string()];
    report.extend(words(8));
    assert_eq!(params("X86TdxControlGetReport", "in"), report);
    assert_eq!(params("X86TdxControlGetReport", "out"), ["tdx_status"]);
    let mut extend = vec!["rtmr_index".to_string()];
    extend.extend(words(6));
    assert_eq!(params("X86TdxControlExtendRTMR", "in"), extend);
    assert_eq!(params("X86TdxControlExtendRTMR", "out"), ["tdx_status"]);
    assert_eq!(params("X86TdxControlGetQuote", "in"), ["shared_frame", "buf_len"]);
    assert_eq!(params("X86TdxControlGetQuote", "out"), ["vmcall_status"]);
}

/// New labels go after every existing one, X86PML4FrameBatch included, so
/// that binaries built against an older libsel4 keep their numbers.
#[test]
#[cfg(not(feature = "aarch64"))]
fn tdx_labels_follow_pml4_frame_batch() {
    use fl4_abi::label as l;
    assert_eq!(l::X86TdxControlGetReport, l::X86PML4FrameBatch + 1);
    assert_eq!(l::X86TdxControlExtendRTMR, l::X86PML4FrameBatch + 2);
    assert_eq!(l::X86TdxControlGetQuote, l::X86PML4FrameBatch + 3);
    assert_eq!(l::nArchInvocationLabels, l::X86TdxControlGetQuote + 1);
}

/// No AArch64 message can carry a TDX label.
#[test]
#[cfg(feature = "aarch64")]
fn tdx_labels_do_not_exist_on_aarch64() {
    use fl4_abi::label as l;
    assert_eq!(l::X86TdxControlGetReport, u64::MAX);
    assert_eq!(l::X86TdxControlExtendRTMR, u64::MAX);
    assert_eq!(l::X86TdxControlGetQuote, u64::MAX);
    assert_eq!(l::ARMIRQIssueIRQHandlerMSI, l::UntypedRetypeShared + 1);
    assert_eq!(l::TCBSetPACKeys, l::ARMIRQIssueIRQHandlerMSI + 1);
    assert_eq!(l::TCBSetHighVSpace, l::TCBSetPACKeys + 1);
    assert_eq!(l::nArchInvocationLabels, l::TCBSetHighVSpace + 1);
}

/// AArch64 MSIs: the BootInfo record on both sides of the kernel/libsel4
/// boundary, and GetMSI's parameters.
#[test]
fn aarch64_msi_bootinfo_and_get_msi_match_libsel4() {
    use fl4_abi::consts::bootinfo_header as h;
    assert_eq!(h::AARCH64_MSI_INFO, 15);
    assert!(BOOTINFO_TYPES.contains("SEL4_BOOTINFO_HEADER_AARCH64_MSI_INFO   = 15,"));
    let info = &BOOTINFO_TYPES[BOOTINFO_TYPES.find("typedef struct seL4_AArch64MsiInfo {").expect("seL4_AArch64MsiInfo")..];
    let info = &info[..info.find('}').unwrap()];
    let order = ["doorbell", "num_lpis", "num_events", "num_devices"].map(|f| info.find(&format!("seL4_Word {f};")).expect(f));
    assert!(order.windows(2).all(|w| w[0] < w[1]), "seL4_AArch64MsiInfo's field order");
    assert_eq!(info.matches("seL4_Word ").count(), 4, "seL4_AArch64MsiInfo has four words");

    let m = &EXTENSIONS[EXTENSIONS.find("<method id=\"ARMIRQIssueIRQHandlerMSI\"").expect("ARMIRQIssueIRQHandlerMSI")..];
    let m = &m[..m.find("</method>").unwrap()];
    assert!(m.contains("<condition><config var=\"CONFIG_ARCH_AARCH64\"/></condition>"));
    let tag = "<param dir=\"in\" name=\"";
    let params: Vec<&str> = m.match_indices(tag).map(|(at, _)| {
        let name = &m[at + tag.len()..];
        &name[..name.find('"').unwrap()]
    }).collect();
    assert_eq!(params, ["irq", "device", "event", "root", "index", "depth", "target"]);
    assert!(!m.contains("<param dir=\"out\""));
}

/// The AArch64 TCB extensions exist only there: x86_64's numbering is
/// unchanged by them.
#[test]
#[cfg(not(feature = "aarch64"))]
fn aarch64_tcb_labels_do_not_exist_on_x86_64() {
    use fl4_abi::label as l;
    assert_eq!(l::TCBSetPACKeys, u64::MAX);
    assert_eq!(l::TCBSetHighVSpace, u64::MAX);
}

/// SetPACKeys and SetHighVSpace are AArch64 only, with the parameters the
/// ABI names, and the constants of libsel4 match the kernel's.
#[test]
fn aarch64_tcb_methods_and_constants() {
    let iface = &EXTENSIONS[EXTENSIONS.find("<interface name=\"seL4_TCB\"").expect("interface")..];
    let params = |id: &str| -> Vec<(String, String)> {
        let m = &iface[iface.find(&format!("<method id=\"{id}\"")).unwrap_or_else(|| panic!("{id}"))..];
        let m = &m[..m.find("</method>").unwrap()];
        assert!(m.contains("<condition><config var=\"CONFIG_ARCH_AARCH64\"/></condition>"), "{id}");
        let tag = "<param dir=\"in\" name=\"";
        m.match_indices(tag).map(|(at, _)| {
            let rest = &m[at + tag.len()..];
            let name = rest[..rest.find('"').unwrap()].to_string();
            let ty = &rest[rest.find("type=\"").unwrap() + 6..];
            (name, ty[..ty.find('"').unwrap()].to_string())
        }).collect()
    };
    let mut want = vec![("flags".to_string(), "seL4_Word".to_string())];
    for k in ["apia", "apib", "apda", "apdb", "apga"] {
        for h in ["lo", "hi"] {
            want.push((format!("{k}_{h}"), "seL4_Word".into()));
        }
    }
    assert_eq!(params("TCBSetPACKeys"), want);
    assert_eq!(params("TCBSetHighVSpace"), [("high_vspace".to_string(), "seL4_CPtr".to_string())]);
    let objs = include_str!("../../../libsel4/arch_include/arm/sel4/arch/objecttype.h");
    assert!(objs.contains("    seL4_ARM_Stage2VSpaceObject,\n    /* FL4: TTBR1 EL0 window (seL4_TCB_SetHighVSpace), no EL2 needed. */\n    seL4_ARM_HighVSpaceObject,\n"));
    let consts = include_str!("../../../libsel4/sel4_arch_include/aarch64/sel4/sel4_arch/constants.h");
    for line in [
        "#define seL4_ARM_HighVSpaceBits    13",
        "#define seL4_ARM_HighVSpaceBase    0xffffffe000000000ul",
        "#define seL4_ARM_HighVSpaceTop     0xfffffffc00000000ul",
        "#define seL4_ARM_PAC_EnIA (1ul << 0)",
        "#define seL4_ARM_PAC_EnIB (1ul << 1)",
        "#define seL4_ARM_PAC_EnDA (1ul << 2)",
        "#define seL4_ARM_PAC_EnDB (1ul << 3)",
    ] {
        assert!(consts.contains(line), "{line}");
    }
    #[cfg(feature = "aarch64")]
    {
        use fl4_abi::consts::{bits, object, pac_flag, HIGH_VSPACE_BASE, HIGH_VSPACE_TOP};
        assert_eq!((object::ArmStage2VSpace, object::ArmHighVSpace, object::Count), (13, 14, 15));
        assert_eq!(bits::HIGH_VSPACE, 13);
        assert_eq!((HIGH_VSPACE_BASE, HIGH_VSPACE_TOP), (0xffff_ffe0_0000_0000, 0xffff_fffc_0000_0000));
        assert_eq!((pac_flag::EN_IA, pac_flag::EN_IB, pac_flag::EN_DA, pac_flag::EN_DB, pac_flag::MASK), (1, 2, 4, 8, 0xf));
    }
}

const CONSTANTS: &str = include_str!("../../../libsel4/include/sel4/constants.h");

/// FL4's syscall is the last one, in every build configuration: no number
/// before it moves.
#[test]
fn kernel_config_is_syscall_minus_24_in_every_configuration() {
    use fl4_abi::syscall as s;
    assert_eq!(s::SysKernelConfig, -24);
    assert_eq!(s::SysSetTLSBase, -20);
    #[cfg(not(feature = "aarch64"))]
    assert_eq!(s::SysVMEnter, -23);
    // Outside the API's range: never decoded as one of its syscalls.
    assert!(s::SysKernelConfig < s::SYSCALL_MIN);
    let last = SYSCALLS.rfind("<syscall name=\"").unwrap();
    assert!(SYSCALLS[last..].starts_with("<syscall name=\"KernelConfig\"/>"));
    let config = &SYSCALLS[SYSCALLS.rfind("<config>").unwrap()..];
    assert!(config.contains("<condition><config var=\"CONFIG_KERNEL_MCS\"/></condition>"));
}

/// Every key, value and flag of seL4_KernelConfig by its libsel4 name: the
/// two sides agree, and neither has one the other lacks.
#[test]
fn kernel_config_constants_match_libsel4() {
    use fl4_abi::consts::kernel_config as k;
    let table: &[(&str, u64)] = &[
        ("Arch", k::keys::ARCH),
        ("BuildFlags", k::keys::BUILD_FLAGS),
        ("OnlineCpus", k::keys::ONLINE_CPUS),
        ("MaxCpus", k::keys::MAX_CPUS),
        ("VirtBackend", k::keys::VIRT_BACKEND),
        ("VirtReject", k::keys::VIRT_REJECT),
        ("VirtFeatures", k::keys::VIRT_FEATURES),
        ("VirtS2IpaBits", k::keys::VIRT_S2_IPA_BITS),
        ("VirtVgicLrs", k::keys::VIRT_VGIC_LRS),
        ("CvmType", k::keys::CVM_TYPE),
        ("CvmFlags", k::keys::CVM_FLAGS),
        ("SpecStatus", k::keys::SPEC_STATUS),
        ("SpecReject", k::keys::SPEC_REJECT),
        ("SpecFlags", k::keys::SPEC_FLAGS),
        ("SpecEntryActions", k::keys::SPEC_ENTRY_ACTIONS),
        ("SpecVmexitActions", k::keys::SPEC_VMEXIT_ACTIONS),
        ("SpecCtrlMsr", k::keys::SPEC_CTRL_MSR),
        ("SpecTsxCtrlMsr", k::keys::SPEC_TSX_CTRL_MSR),
        ("SpecMcuOptCtrlMsr", k::keys::SPEC_MCU_OPT_CTRL_MSR),
        ("SpecEferMsr", k::keys::SPEC_EFER_MSR),
        ("SpecAmdDeCfgMsr", k::keys::SPEC_AMD_DE_CFG_MSR),
        ("SpecAmdBpCfgMsr", k::keys::SPEC_AMD_BP_CFG_MSR),
        ("SpecMsrValid", k::keys::SPEC_MSR_VALID),
        ("ArmMitigations", k::keys::ARM_MITIGATIONS),
        ("X86CpuVendor", k::keys::X86_CPU_VENDOR),
        ("X86CpuFeatures", k::keys::X86_CPU_FEATURES),
        ("X86FpuXcr0", k::keys::X86_FPU_XCR0),
        ("X86FpuSaveInsn", k::keys::X86_FPU_SAVE_INSN),
        ("X86TscMhz", k::keys::X86_TSC_MHZ),
        ("X86TscSource", k::keys::X86_TSC_SOURCE),
        ("X86MicrocodeRev", k::keys::X86_MICROCODE_REV),
        ("X86MaxPaddrBits", k::keys::X86_MAX_PADDR_BITS),
        ("X86IoapicCount", k::keys::X86_IOAPIC_COUNT),
        ("X86ArchCapabilities", k::keys::X86_ARCH_CAPABILITIES),
        ("ArmPlatformFlags", k::keys::ARM_PLATFORM_FLAGS),
        ("ArmPaBits", k::keys::ARM_PA_BITS),
        ("ArmGicVersion", k::keys::ARM_GIC_VERSION),
        ("ArmMaxSpi", k::keys::ARM_MAX_SPI),
        ("ArmPsciMethod", k::keys::ARM_PSCI_METHOD),
        ("ArmTimerFreqHz", k::keys::ARM_TIMER_FREQ_HZ),
        ("Arch_X86_64", k::arch::X86_64),
        ("Arch_AArch64", k::arch::AARCH64),
        ("BuildFlag_DebugBuild", k::build_flags::DEBUG_BUILD),
        ("BuildFlag_Printing", k::build_flags::PRINTING),
        ("BuildFlag_Smp", k::build_flags::SMP),
        ("BuildFlag_HwDebugApi", k::build_flags::HW_DEBUG_API),
        ("BuildFlag_ExportPmcUser", k::build_flags::EXPORT_PMC_USER),
        ("BuildFlag_DangerousMsr", k::build_flags::DANGEROUS_MSR),
        ("VirtBackend_None", k::virt_backend::NONE),
        ("VirtBackend_Vtx", k::virt_backend::VTX),
        ("VirtBackend_AmdV", k::virt_backend::AMDV),
        ("VirtBackend_El2Vhe", k::virt_backend::EL2_VHE),
        ("VirtBackend_El2Nvhe", k::virt_backend::EL2_NVHE),
        ("VirtReject_None", k::virt_reject::NONE),
        ("VirtReject_NoHw", k::virt_reject::NO_HW),
        ("VirtReject_DisabledByFirmware", k::virt_reject::DISABLED_BY_FIRMWARE),
        ("VirtReject_MissingFeatures", k::virt_reject::MISSING_FEATURES),
        ("VirtReject_SpecPolicyRejected", k::virt_reject::SPEC_POLICY_REJECTED),
        ("VirtReject_SkimActive", k::virt_reject::SKIM_ACTIVE),
        ("VirtReject_CvmActive", k::virt_reject::CVM_ACTIVE),
        ("VirtReject_VmxonFailed", k::virt_reject::VMXON_FAILED),
        ("VirtReject_NovirtCmdline", k::virt_reject::NOVIRT_CMDLINE),
        ("VirtReject_NoVgic", k::virt_reject::NO_VGIC),
        ("VirtReject_El1Only", k::virt_reject::EL1_ONLY),
        ("VirtFeature_X86VpidSingle", k::virt_features::X86_VPID_SINGLE),
        ("VirtFeature_X86VpidAll", k::virt_features::X86_VPID_ALL),
        ("VirtFeature_X86InveptSingle", k::virt_features::X86_INVEPT_SINGLE),
        ("VirtFeature_X86SvmVmcbClean", k::virt_features::X86_SVM_VMCB_CLEAN),
        ("VirtFeature_X86VmxPerfGlobalCtrl", k::virt_features::X86_VMX_PERF_GLOBAL_CTRL),
        ("VirtFeature_ArmVirtReady", k::virt_features::ARM_VIRT_READY),
        ("VirtFeature_ArmVmid16", k::virt_features::ARM_VMID16),
        ("VirtFeature_ArmGicv2Vgic", k::virt_features::ARM_GICV2_VGIC),
        ("VirtFeature_ArmGicv3Vgic", k::virt_features::ARM_GICV3_VGIC),
        ("CvmType_None", k::cvm_type::NONE),
        ("CvmType_Sev", k::cvm_type::SEV),
        ("CvmType_SevSnp", k::cvm_type::SEV_SNP),
        ("CvmType_Tdx", k::cvm_type::TDX),
        ("CvmFlag_Hardened", k::cvm_flags::HARDENED),
        ("CvmFlag_SharedDma", k::cvm_flags::SHARED_DMA),
        ("SpecStatus_Incomplete", k::spec_status::INCOMPLETE),
        ("SpecStatus_Complete", k::spec_status::COMPLETE),
        ("SpecReject_None", k::spec_reject::NONE),
        ("SpecReject_Vendor", k::spec_reject::VENDOR),
        ("SpecReject_Meltdown", k::spec_reject::MELTDOWN),
        ("SpecReject_Smep", k::spec_reject::SMEP),
        ("SpecReject_BeforeZen2", k::spec_reject::BEFORE_ZEN2),
        ("SpecReject_Ibpb", k::spec_reject::IBPB),
        ("SpecReject_SrsoMicrocode", k::spec_reject::SRSO_MICROCODE),
        ("SpecReject_BufferMicrocode", k::spec_reject::BUFFER_MICROCODE),
        ("SpecReject_ItsMicrocode", k::spec_reject::ITS_MICROCODE),
        ("SpecReject_Lfence", k::spec_reject::LFENCE),
        ("SpecFlag_Skim", k::spec_flags::SKIM),
        ("SpecFlag_SafeRet", k::spec_flags::SAFE_RET),
        ("SpecFlag_Retpoline", k::spec_flags::RETPOLINE),
        ("SpecFlag_Eibrs", k::spec_flags::EIBRS),
        ("SpecFlag_AutoIbrs", k::spec_flags::AUTO_IBRS),
        ("SpecFlag_LegacyIbrs", k::spec_flags::LEGACY_IBRS),
        ("SpecFlag_Stibp", k::spec_flags::STIBP),
        ("SpecFlag_BhiDisS", k::spec_flags::BHI_DIS_S),
        ("SpecFlag_VerwBuffers", k::spec_flags::VERW_BUFFERS),
        ("SpecFlag_NoSmt", k::spec_flags::NO_SMT),
        ("SpecFlag_DisableTsx", k::spec_flags::DISABLE_TSX),
        ("SpecFlag_VmexitIbpbDeferred", k::spec_flags::VMEXIT_IBPB_DEFERRED),
        ("SpecFlag_EagerFpu", k::spec_flags::EAGER_FPU),
        ("SpecAction_Ibpb", k::spec_actions::IBPB),
        ("SpecAction_Rsb", k::spec_actions::RSB),
        ("SpecAction_Pbrsb", k::spec_actions::PBRSB),
        ("SpecAction_LegacyIbrs", k::spec_actions::LEGACY_IBRS),
        ("SpecAction_Bhb", k::spec_actions::BHB),
        ("SpecAction_Ibhf", k::spec_actions::IBHF),
        ("SpecMsrValid_ArchCapabilities", k::spec_msr_valid::ARCH_CAPABILITIES),
        ("SpecMsrValid_SpecCtrl", k::spec_msr_valid::SPEC_CTRL),
        ("SpecMsrValid_TsxCtrl", k::spec_msr_valid::TSX_CTRL),
        ("SpecMsrValid_McuOptCtrl", k::spec_msr_valid::MCU_OPT_CTRL),
        ("SpecMsrValid_Efer", k::spec_msr_valid::EFER),
        ("SpecMsrValid_AmdDeCfg", k::spec_msr_valid::AMD_DE_CFG),
        ("SpecMsrValid_AmdBpCfg", k::spec_msr_valid::AMD_BP_CFG),
        ("ArmMitigation_Pan", k::arm_mitigations::PAN),
        ("ArmMitigation_Pauth", k::arm_mitigations::PAUTH),
        ("ArmMitigation_Clrbhb", k::arm_mitigations::CLRBHB),
        ("X86Vendor_Other", k::x86_vendor::OTHER),
        ("X86Vendor_Intel", k::x86_vendor::INTEL),
        ("X86Vendor_Amd", k::x86_vendor::AMD),
        ("X86Vendor_Hygon", k::x86_vendor::HYGON),
        ("X86Feature_Nx", k::x86_features::NX),
        ("X86Feature_Smep", k::x86_features::SMEP),
        ("X86Feature_Smap", k::x86_features::SMAP),
        ("X86Feature_Fsgsbase", k::x86_features::FSGSBASE),
        ("X86Feature_HugePages1G", k::x86_features::HUGE_PAGES_1G),
        ("X86Feature_Pcid", k::x86_features::PCID),
        ("X86Feature_Invpcid", k::x86_features::INVPCID),
        ("X86Feature_X2apic", k::x86_features::X2APIC),
        ("X86Feature_TscDeadline", k::x86_features::TSC_DEADLINE),
        ("X86Feature_IdlePoll", k::x86_features::IDLE_POLL),
        ("X86Feature_Hypervisor", k::x86_features::HYPERVISOR),
        ("X86FpuInsn_Fxsave", k::x86_fpu_insn::FXSAVE),
        ("X86FpuInsn_Xsave", k::x86_fpu_insn::XSAVE),
        ("X86FpuInsn_Xsaveopt", k::x86_fpu_insn::XSAVEOPT),
        ("X86FpuInsn_Xsavec", k::x86_fpu_insn::XSAVEC),
        ("X86FpuInsn_Xsaves", k::x86_fpu_insn::XSAVES),
        ("X86TscSource_Cpuid", k::x86_tsc_source::CPUID),
        ("X86TscSource_Hypervisor", k::x86_tsc_source::HYPERVISOR),
        ("X86TscSource_Pit", k::x86_tsc_source::PIT),
        ("X86TscSource_Kvm", k::x86_tsc_source::KVM),
        ("ArmPlatformFlag_Asid16", k::arm_platform_flags::ASID16),
        ("ArmPlatformFlag_HwAf", k::arm_platform_flags::HW_AF),
        ("ArmPlatformFlag_Gicv3Sre", k::arm_platform_flags::GICV3_SRE),
        ("ArmPlatformFlag_ItsActive", k::arm_platform_flags::ITS_ACTIVE),
        ("ArmPlatformFlag_TimerLocalAck", k::arm_platform_flags::TIMER_LOCAL_ACK),
        ("ArmPlatformFlag_El2Vhe", k::arm_platform_flags::EL2_VHE),
        ("ArmPlatformFlag_El2Nvhe", k::arm_platform_flags::EL2_NVHE),
        ("ArmPsci_Absent", k::arm_psci::ABSENT),
        ("ArmPsci_Smc", k::arm_psci::SMC),
        ("ArmPsci_Hvc", k::arm_psci::HVC),
    ];
    let mut defined = 0;
    for line in CONSTANTS.lines() {
        let Some(rest) = line.strip_prefix("#define seL4_KernelConfig_") else { continue };
        let (name, value) = rest.split_once(' ').unwrap();
        let word = |t: &str| {
            let t = t.strip_suffix("UL").unwrap_or(t);
            match t.strip_prefix("0x") {
                Some(h) => u64::from_str_radix(h, 16).unwrap(),
                None => t.parse().unwrap(),
            }
        };
        let value = match value.strip_prefix('(') {
            Some(v) => {
                let (a, b) = v.strip_suffix(')').unwrap().split_once(" << ").unwrap();
                word(a) << word(b)
            }
            None => word(value),
        };
        let (_, want) = table.iter().find(|(n, _)| *n == name).unwrap_or_else(|| panic!("{name} is not the kernel's"));
        assert_eq!(value, *want, "{name}");
        defined += 1;
    }
    assert_eq!(defined, table.len());
    // Visible in every build: the block is after the last conditional.
    let block = CONSTANTS.find("#define seL4_KernelConfig_").unwrap();
    assert!(!CONSTANTS[block..].contains("#if") && !CONSTANTS[block..].contains("#endif"));
    let open = |w: &str| CONSTANTS[..block].lines().filter(|l| l.starts_with(w)).count();
    assert_eq!(open("#if"), open("#endif"));
}

#[test]
fn kernel_config_keys_are_unique() {
    use fl4_abi::consts::kernel_config::keys::*;
    let mut all = [
        ARCH, BUILD_FLAGS, ONLINE_CPUS, MAX_CPUS, VIRT_BACKEND, VIRT_REJECT, VIRT_FEATURES, VIRT_S2_IPA_BITS,
        VIRT_VGIC_LRS, CVM_TYPE, CVM_FLAGS, SPEC_STATUS, SPEC_REJECT, SPEC_FLAGS, SPEC_ENTRY_ACTIONS,
        SPEC_VMEXIT_ACTIONS, SPEC_CTRL_MSR, SPEC_TSX_CTRL_MSR, SPEC_MCU_OPT_CTRL_MSR, SPEC_EFER_MSR,
        SPEC_AMD_DE_CFG_MSR, SPEC_AMD_BP_CFG_MSR, SPEC_MSR_VALID, ARM_MITIGATIONS, X86_CPU_VENDOR, X86_CPU_FEATURES, X86_FPU_XCR0,
        X86_FPU_SAVE_INSN, X86_TSC_MHZ, X86_TSC_SOURCE, X86_MICROCODE_REV, X86_MAX_PADDR_BITS, X86_IOAPIC_COUNT,
        X86_ARCH_CAPABILITIES, ARM_PLATFORM_FLAGS, ARM_PA_BITS, ARM_GIC_VERSION, ARM_MAX_SPI, ARM_PSCI_METHOD, ARM_TIMER_FREQ_HZ,
    ];
    // All the header has: the keys are the ones written in hex.
    assert_eq!(CONSTANTS.lines().filter(|l| l.starts_with("#define seL4_KernelConfig_") && l.contains(" 0x")).count(), all.len());
    all.sort_unstable();
    assert!(all.windows(2).all(|w| w[0] < w[1]));
}

/// The C stubs: the key in the capability register, the error in the badge
/// register and the value in the first message register.
#[test]
fn kernel_config_stubs_use_the_fast_message_registers() {
    for (text, call) in [
        (include_str!("../../../libsel4/sel4_arch_include/x86_64/sel4/sel4_arch/syscalls.h"), "x64_sys_send_recv"),
        (include_str!("../../../libsel4/arch_include/arm/sel4/arch/syscalls.h"), "arm_sys_send_recv"),
    ] {
        let line = format!("{call}(seL4_SysKernelConfig, key, &error, 0, &info, &value, &unused0, &unused1, &unused2, 0);");
        assert!(text.contains(&line), "{line}");
    }
}
