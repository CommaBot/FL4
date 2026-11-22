//! Every core walks the boot core's page tables (fl4-kernel paging.rs):
//! the kernel window, with 1 GiB pages when the boot core takes them, and
//! the user tables, whose entries reach up to the top of device memory.
//! An AP checks it can do both (cpu::paging_compatible) before it loads
//! them natively, or once its own IDT is in on SNP, as for CR4.
#![cfg(target_arch = "x86_64")]

use fl4_arch_x86_64::cpu;

const SMP: &str = include_str!("../../fl4-kernel/src/smp.rs");
const LIB: &str = include_str!("../../fl4-kernel/src/lib.rs");

/// The statements of `fl4_ap_main`, trimmed.
fn ap_main() -> Vec<&'static str> {
    let at = SMP.find("extern \"C\" fn fl4_ap_main(").expect("fl4_ap_main");
    let end = at + SMP[at..].find("\n}\n").unwrap();
    SMP[at..end].lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with("//")).collect()
}

#[test]
fn an_ap_needs_the_boot_cores_page_sizes_and_the_systems_address_top() {
    const G: u64 = 1 << 30;
    let top47 = 1u64 << 47;
    // The boot core chose 1 GiB pages: a core without them is refused,
    // whatever its address width.
    assert!(cpu::paging_compatible(true, top47, true, top47));
    assert!(!cpu::paging_compatible(true, top47, false, 1 << 52));
    // 2 MiB windows: either core will do.
    assert!(cpu::paging_compatible(false, top47, false, top47));
    assert!(cpu::paging_compatible(false, top47, true, top47));
    // The top is what the kernel maps or hands out (device memory
    // included), not the window's: a core that reaches the window but not
    // the device top is refused; one that reaches past it is fine.
    let window = 510 * G;
    assert!(!cpu::paging_compatible(false, top47, false, 1 << 46));
    assert!(cpu::paging_compatible(false, window, false, 1 << 46));
    assert!(cpu::paging_compatible(true, 1 << 39, true, 1 << 52));
    assert!(!cpu::paging_compatible(true, 1 << 39, true, 1 << 38));
    assert!(cpu::page_1g(1 << 26) && !cpu::page_1g(!(1 << 26)));
}

#[test]
fn an_ap_checks_its_paging_before_the_boot_cores_tables() {
    let m = ap_main();
    let find = |f: &dyn Fn(&str) -> bool, what: &str| m.iter().position(|l| f(l)).unwrap_or_else(|| panic!("{what} missing"));
    let checks = |snp: bool| move |l: &str| {
        l.contains("core_paging_supported(f.huge, f.paddr_top)")
            && l.contains("REJECT_PAGING")
            && l.contains(if snp { "if snp::active()" } else { "if !snp::active()" })
    };
    let native = find(&checks(false), "the native check");
    let snp = find(&checks(true), "the SNP check");
    let cr3 = find(&|l| l.contains("write_cr3(paging::root_paddr())"), "the switch to the boot core's tables");
    let idt = find(&|l| l.contains("gdt::init_core("), "the core's IDT");
    let online = find(&|l| l.contains("smp::set_online("), "going online");
    // Natively before the boot core's tables; on SNP (CPUID by #VC) once
    // the core's IDT is in; both before the core counts as online.
    assert!(native < cr3, "native check after the switch");
    assert!(idt < snp, "SNP check before the IDT");
    assert!(native < online && snp < online, "checks after going online");
    assert!(SMP.contains("REJECT_PAGING =>"), "the rejection is reported");
}

/// One CPUID read of Page1GB on the boot core decides the window's page
/// size, what the other cores must take, and whether user space may map
/// 1 GiB frames; the device top, not the window's, is what the other
/// cores must reach.
#[test]
fn one_page_size_decision_drives_the_window_the_aps_and_user_mappings() {
    let paging = include_str!("../../fl4-kernel/src/paging.rs");
    assert_eq!(LIB.matches("has_1g_pages()").count(), 1, "the boot core reads Page1GB once");
    assert!(!paging.contains("has_1g_pages") && !paging.contains("cpuid(0x8000_0001"), "paging.rs reads it again");
    let read = LIB.find("let huge = cpu::has_1g_pages();").expect("the read");
    let init = LIB.find("paging::init(").expect("paging::init");
    let init_call = &LIB[init..init + LIB[init..].find(';').unwrap()];
    assert!(read < init && init_call.contains("huge"), "{init_call}");
    let start = LIB.find("smp::start_aps(").expect("start_aps call");
    let start_call = &LIB[start..start + LIB[start..].find(';').unwrap()];
    assert!(start_call.contains("huge") && start_call.contains("paddr_top: device_top"), "{start_call}");
    let dev = LIB.find("let device_top =").expect("device_top");
    assert!(dev < start, "device_top is known before the APs start");
    let feat = LIB.find("ks::FEATURES,").expect("FEATURES");
    let feat_call = &LIB[feat..feat + LIB[feat..].find(';').unwrap()];
    assert!(feat_call.contains("if huge { ks::FEATURE_HUGE_PAGES }"), "{feat_call}");
}
