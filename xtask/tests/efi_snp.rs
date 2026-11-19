//! The x86 UEFI loader's SEV-SNP memory map rule (fl4-efi snp_map.rs,
//! used by x86.rs `memory_map`): the CPUID and secrets pages must lie in
//! the firmware's memory map, which marks them ACPI NVS for the kernel to
//! keep out of every capability. A page in a hole would become device
//! memory a user could map.
#[path = "../../crates/fl4-efi/src/snp_map.rs"]
mod snp_map;

const PAGE: u64 = 4096;

#[test]
fn a_descriptor_holds_exactly_its_pages() {
    assert!(snp_map::holds(0x10_0000, 2 * PAGE, 0x10_0000));
    assert!(snp_map::holds(0x10_0000, 2 * PAGE, 0x10_1000));
    assert!(!snp_map::holds(0x10_0000, 2 * PAGE, 0x10_2000));
    assert!(!snp_map::holds(0x10_1000, PAGE, 0x10_0000));
    assert!(!snp_map::holds(0, PAGE, 0), "page zero means no page");
    assert!(!snp_map::holds(0x10_0000, 0, 0x10_0000));
}

#[test]
fn snp_pages_outside_the_memory_map_are_refused() {
    let map = [(0x0, 0xa0 * PAGE), (0x80_0000, 4 * PAGE), (0x100_0000, 0x1000 * PAGE)];
    let cpuid = 0x80_1000;
    let secrets = 0x80_3000;
    assert!(snp_map::all_held(map.iter().copied(), &[cpuid, secrets]));
    // Without SNP there are no pages to look for.
    assert!(snp_map::all_held(map.iter().copied(), &[0, 0]));
    assert!(snp_map::all_held([].into_iter(), &[0, 0]));
    // Either page in a hole: between descriptors, just past one, or with
    // no map at all.
    for (c, s) in [(0x90_0000, secrets), (cpuid, 0x80_4000), (0xa0 * PAGE, secrets)] {
        assert!(!snp_map::all_held(map.iter().copied(), &[c, s]), "{c:#x} {s:#x}");
    }
    assert!(!snp_map::all_held([].into_iter(), &[cpuid, 0]));
}

/// `memory_map` checks both pages before it writes a descriptor, and fails
/// the boot (its caller's `handoff_failed`) when one is missing.
#[test]
fn the_loader_checks_the_snp_pages_before_writing_the_map() {
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    let start = x86.find("fn memory_map(").expect("memory_map");
    let body = &x86[start..];
    let check = body.find("snp_map::all_held(").expect("memory_map does not check that the SNP pages are in the map");
    let first_write = body.find("info.tag(6").expect("memory map tag");
    assert!(check < first_write);
    assert!(body[check..first_write].contains("return Err("));
}
