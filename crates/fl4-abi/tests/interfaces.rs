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
