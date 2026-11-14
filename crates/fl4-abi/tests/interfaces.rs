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
