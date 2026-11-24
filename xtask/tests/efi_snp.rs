//! The x86 UEFI loader's memory map (fl4-efi x86_mmap.rs and snp_map.rs,
//! used by x86.rs `memory_map`): every descriptor whole and inside 2^64,
//! and the SEV-SNP CPUID and secrets pages in the map, which marks them
//! ACPI NVS for the kernel to keep out of every capability. A page in a
//! hole would become device memory a user could map.
#[path = "../../crates/fl4-efi/src/snp_map.rs"]
mod snp_map;
#[allow(dead_code)]
#[path = "../../crates/fl4-efi/src/x86_mmap.rs"]
mod x86_mmap;

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

/// `regions` checks both pages before it emits a region, and x86.rs
/// `memory_map` fails the boot (its caller's `handoff_failed`) on its error.
#[test]
fn the_loader_checks_the_snp_pages_before_writing_the_map() {
    let m = include_str!("../../crates/fl4-efi/src/x86_mmap.rs");
    let body = &m[m.find("pub fn regions(").expect("regions")..];
    let check = body.find("snp_map::all_held(").expect("regions does not check that the SNP pages are in the map");
    let first_emit = body.find("emit(").expect("emit");
    assert!(check < first_emit);
    assert!(body[check..first_emit].contains("return Err("));
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    let mm = &x86[x86.find("fn memory_map(").expect("memory_map")..];
    assert!(mm[..mm.find("\n}\n").unwrap()].contains("x86_mmap::regions(map, stride, cpuid, secrets,"));
    assert!(mm[..mm.find("\n}\n").unwrap()].contains("})?;"));
}

/// One EFI memory descriptor of `stride` bytes.
fn desc(stride: usize, ty: u32, base: u64, pages: u64) -> Vec<u8> {
    let mut d = vec![0u8; stride];
    d[0..4].copy_from_slice(&ty.to_le_bytes());
    d[8..16].copy_from_slice(&base.to_le_bytes());
    d[24..32].copy_from_slice(&pages.to_le_bytes());
    d
}

fn map_of(stride: usize, ds: &[(u32, u64, u64)]) -> Vec<u8> {
    ds.iter().flat_map(|&(ty, base, pages)| desc(stride, ty, base, pages)).collect()
}

fn regions(map: &[u8], stride: usize, cpuid: u64, secrets: u64) -> Result<Vec<(u64, u64, u32)>, &'static str> {
    let mut out = vec![];
    x86_mmap::regions(map, stride, cpuid, secrets, |r| {
        out.push(r);
        Ok(())
    })?;
    Ok(out)
}

/// Audit r8 F2: two descriptors whose merge wraps past 2^64. The first
/// starts at the secrets page and runs to 2^64 (no product overflows), the
/// second covers [0, secrets): `start + len` wraps to 0, the second's base,
/// and `len + bytes` to 0, so the loader handed the kernel (secrets, 0,
/// NVS) and nothing else. The kernel then keeps no page of the map out of
/// device memory: the secrets page (the VMPCKs) and the CPUID page would go
/// to user space as device untypeds. No descriptor may end past 2^64.
#[test]
fn a_merge_that_wraps_cannot_drop_the_secrets_page() {
    let cpuid = 0x80_1000;
    let secrets = 0x80_3000;
    let map = map_of(48, &[(10, secrets, 0u64.wrapping_sub(secrets) / PAGE), (10, 0, secrets / PAGE)]);
    let r = regions(&map, 48, cpuid, secrets);
    assert!(r.is_err(), "a wrapping map was accepted: {r:x?}");
    // The same with a FREE first half or an end exactly at 2^64.
    let map = map_of(48, &[(7, secrets, 0u64.wrapping_sub(secrets) / PAGE)]);
    assert!(regions(&map, 48, 0, secrets).is_err());
    let map = map_of(40, &[(7, 0x1000, 1 << 52)]);
    assert!(regions(&map, 40, 0, 0).is_err(), "pages * 4096 wraps");
    let map = map_of(40, &[(7, u64::MAX - 0xfff, 1)]);
    assert!(regions(&map, 40, 0, 0).is_err(), "base + bytes wraps to 0");
    let map = map_of(40, &[(7, u64::MAX - 0x1fff, 1)]);
    assert_eq!(regions(&map, 40, 0, 0), Ok(vec![(u64::MAX - 0x1fff, 0x1000, 1)]));
}

/// Every region the kernel gets ends past its base and inside 2^64, and
/// the regions covering the SNP pages are private reserved memory whole
/// (audit TDX r4, R3-3: kept private and out of every capability, but no
/// ACPI memory to read); the ACPI NVS page between them stays NVS.
#[test]
fn snp_pages_stay_private_in_a_merged_map() {
    let cpuid = 0x80_1000;
    let secrets = 0x80_3000;
    let map = map_of(48, &[(7, 0, 0x800), (7, 0x80_0000, 1), (7, 0x80_1000, 1), (10, 0x80_2000, 1), (7, 0x80_3000, 1), (7, 0x80_4000, 4)]);
    let r = regions(&map, 48, cpuid, secrets).unwrap();
    let private = x86_mmap::PRIVATE_RESERVED;
    assert_eq!(r, vec![(0, 0x80_1000, 1), (0x80_1000, 0x1000, private), (0x80_2000, 0x1000, 4), (0x80_3000, 0x1000, private), (0x80_4000, 0x4000, 1)]);
    for (base, bytes, _) in &r {
        assert!(base.checked_add(*bytes).is_some());
    }
}

/// A descriptor not on a page boundary is not taken (EFI requires 4 KiB
/// aligned physical starts): the kernel rounds regions outwards, so one
/// could put half of a free page in front of the secrets page.
#[test]
fn descriptors_off_a_page_boundary_are_refused() {
    let map = map_of(40, &[(7, 0x10_0800, 1)]);
    assert!(regions(&map, 40, 0, 0).is_err());
    let map = map_of(40, &[(10, 0x80_2800, 2)]);
    assert!(regions(&map, 40, 0, 0x80_3000).is_err());
}

/// A page is held only by a descriptor covering all of its 4 KiB, whatever
/// the arithmetic would wrap to.
#[test]
fn a_page_is_held_only_whole() {
    assert!(!snp_map::holds(0x80_3000, 1, 0x80_3000), "one byte of the page");
    assert!(!snp_map::holds(0x80_3000, 0x800, 0x80_3000));
    assert!(!snp_map::holds(0x80_2800, 0x1000, 0x80_3000));
    assert!(snp_map::holds(0x80_2800, 0x1800, 0x80_3000));
    assert!(!snp_map::holds(u64::MAX - 0xfff, u64::MAX, u64::MAX - 0xfff), "end past 2^64");
    assert!(!snp_map::holds(0x80_3000, u64::MAX, 0x80_3000));
}

/// The map buffer leaves room for 16 descriptors of at least 48 bytes,
/// without wrapping, and a map larger than the buffer (GetMemoryMap
/// returning SUCCESS with a larger size) or not of whole descriptors is
/// refused before it is read. Before, size was not checked against the
/// buffer, and a stride of 0 from the sizing call left no room at all.
#[test]
fn the_map_buffer_bounds_what_is_read() {
    assert_eq!(x86_mmap::capacity(4800, 48), Some(4800 + 16 * 48));
    assert_eq!(x86_mmap::capacity(4800, 0), Some(4800 + 16 * 48));
    assert_eq!(x86_mmap::capacity(4800, 40), Some(4800 + 16 * 48));
    assert_eq!(x86_mmap::capacity(usize::MAX - 10, 48), None);
    assert_eq!(x86_mmap::capacity(0, usize::MAX / 8), None);
    let cap = x86_mmap::capacity(4800, 48).unwrap();
    assert!(x86_mmap::layout_ok(4800, 48, cap));
    assert!(x86_mmap::layout_ok(cap, 48, cap));
    assert!(!x86_mmap::layout_ok(cap + 48, 48, cap), "size past the buffer");
    assert!(!x86_mmap::layout_ok(96, 36, cap));
    assert!(!x86_mmap::layout_ok(100, 48, cap));
    assert!(!x86_mmap::layout_ok(0, 0, cap));
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    assert!(x86.contains("x86_mmap::layout_ok(size, stride, capacity)"));
    assert!(x86.find("x86_mmap::layout_ok(size, stride, capacity)").unwrap() < x86.find("from_raw_parts(buffer as *const u8, size)").unwrap());
}

/// `EfiUnacceptedMemoryType` (15: UEFI 2.10 table 7.10, EDK2
/// `UefiMultiPhase.h`, Linux `efi.h`) keeps a kind of its own: type 2
/// (reserved) would make it device memory, and type 1 RAM the kernel
/// touches before accepting it. 14 is `EfiPersistentMemory`, 16
/// `EfiMaxMemoryType`: no unaccepted memory, and 16 and later nothing the
/// kernel keeps private either (audit TDX r2, R1-1).
#[test]
fn unaccepted_memory_is_neither_ram_nor_reserved() {
    assert_eq!(x86_mmap::UNACCEPTED, 0x464c_3410);
    assert_eq!(x86_mmap::EFI_UNACCEPTED, 15);
    assert_eq!(x86_mmap::kind(15, 0), x86_mmap::UNACCEPTED);
    assert_eq!(x86_mmap::kind(15, 8), x86_mmap::UNACCEPTED);
    for other in [0, 1, 2, 7, 9, 10, 11, 14, 16, 17] {
        assert_ne!(x86_mmap::kind(other, 0), x86_mmap::UNACCEPTED, "EFI type {other}");
    }
    // Only ACPI NVS is ACPI NVS: runtime services code and data and
    // persistent memory are firmware's private memory (audit TDX r5, fix 4).
    assert_eq!(x86_mmap::kind(10, 0), 4);
    for private in [5, 6, 14] {
        assert_eq!(x86_mmap::kind(private, 0), x86_mmap::PRIVATE_RESERVED, "EFI type {private}");
        assert_eq!(x86_mmap::kind(private, 8), x86_mmap::PRIVATE_RESERVED, "EFI type {private}");
    }
    // Write-back reserved memory is private, but not ACPI NVS (audit TDX
    // r3, R2-2); without write-back it is plain reserved memory.
    assert_eq!(x86_mmap::PRIVATE_RESERVED, 0x464c_3411);
    assert_eq!(x86_mmap::kind(0, 8), x86_mmap::PRIVATE_RESERVED);
    assert_eq!(x86_mmap::kind(0, 1), 2);
    for past in [16, 17, 0x7000_0000, 0x8000_0000] {
        assert_eq!(x86_mmap::kind(past, 8), 2, "EFI type {past:#x}");
    }
}

#[test]
fn adjacent_unaccepted_regions_merge_and_stay_apart_from_ram() {
    let stride = 48;
    let mut map = desc(stride, 7, 0x10_0000, 16);
    map.extend(desc(stride, 15, 0x11_0000, 16));
    map.extend(desc(stride, 15, 0x12_0000, 16));
    map.extend(desc(stride, 7, 0x13_0000, 16));
    let mut out = Vec::new();
    x86_mmap::regions(&map, stride, 0, 0, |r| {
        out.push(r);
        Ok(())
    })
    .unwrap();
    assert_eq!(
        out,
        [(0x10_0000, 0x1_0000, 1), (0x11_0000, 0x2_0000, x86_mmap::UNACCEPTED), (0x13_0000, 0x1_0000, 1)]
    );
}

/// Audit (TDX r5, R1-M2): descriptors that share a byte make a map the
/// loader refuses, before it reads anything by it (x86.rs `EfiMap::get`) and
/// before it hands the kernel any region (`regions`): one range must not be
/// ACPI NVS by one descriptor and reserved, unaccepted or MMIO by another.
/// Order does not matter, adjacent and empty descriptors are fine.
#[test]
fn overlapping_descriptors_are_refused_in_any_order() {
    let (a, b) = (0x10_0000u64, 0x20_0000u64);
    let ok = |ds: &[(u32, u64, u64)]| x86_mmap::validate_map(&map_of(48, ds), 48);
    let overlap = Err("overlapping EFI memory descriptors");
    for ds in [
        vec![(10, a, 16), (11, a, 16)],                 // the same range
        vec![(10, a, 16), (0, a + 0xf000, 1)],          // the other's last page
        vec![(10, a + 0x1000, 16), (11, a, 2)],         // the other's first page
        vec![(7, a, 256), (10, a + 0x8000, 1)],         // inside the other
        vec![(10, a + 0x8000, 1), (7, a, 256)],         // inside, listed first
        vec![(7, b, 1), (10, a, 16), (15, a + 0x4000, 1)], // a later pair
    ] {
        assert_eq!(ok(&ds), overlap, "{ds:x?}");
        let mut rev = ds.clone();
        rev.reverse();
        assert_eq!(ok(&rev), overlap, "{rev:x?}");
        assert!(regions(&map_of(48, &ds), 48, 0, 0).is_err(), "{ds:x?}");
    }
    // Out of order, adjacent, or empty: no overlap.
    assert_eq!(ok(&[(7, b, 16), (10, a, 16), (9, a + 0x10000, 1)]), Ok(()));
    assert_eq!(ok(&[(10, a, 16), (7, a + 0x10000, 16)]), Ok(()));
    assert_eq!(ok(&[(10, a, 16), (11, a + 0x4000, 0), (0, a, 0)]), Ok(()));
    assert_eq!(ok(&[]), Ok(()));
    assert_eq!(regions(&map_of(48, &[(7, b, 16), (10, a, 16)]), 48, 0, 0).unwrap(), vec![(b, 0x10000, 1), (a, 0x10000, 4)]);
    // What every descriptor needs as before.
    assert_eq!(x86_mmap::validate_map(&map_of(48, &[(7, a + 1, 1)]), 48), Err("EFI memory descriptor off a page boundary or past 2^64"));
    assert_eq!(x86_mmap::validate_map(&map_of(48, &[(7, u64::MAX - 0xfff, 1)]), 48), Err("EFI memory descriptor off a page boundary or past 2^64"));
    assert_eq!(x86_mmap::validate_map(&map_of(48, &[(7, a, 1)])[..40], 48), Err("invalid EFI memory map"));
    assert_eq!(x86_mmap::validate_map(&map_of(36, &[(7, a, 1)]), 36), Err("invalid EFI memory map"));
    // The loader checks the map it reads by and the one it hands on.
    let x86 = include_str!("../../crates/fl4-efi/src/x86.rs");
    let get = &x86[x86.find("pub(super) fn get() -> Option<EfiMap> {").unwrap()..];
    let get = &get[..get.find("\n    }\n").unwrap()];
    assert!(get.find("x86_mmap::layout_ok(size, stride, capacity)").unwrap() < get.find("x86_mmap::validate_map(").unwrap());
    assert!(get.find("x86_mmap::validate_map(").unwrap() < get.find("Some(map)").unwrap());
    let mmap = include_str!("../../crates/fl4-efi/src/x86_mmap.rs");
    let regions_src = &mmap[mmap.find("pub fn regions(").unwrap()..];
    assert!(regions_src.find("validate_map(map, stride)?;").unwrap() < regions_src.find("snp_map::all_held(").unwrap());
}

/// Audit (TDX r5, R2-M2): `validate_map` does bounded work. A sorted map
/// takes one pass however many descriptors it has; an unsorted one has
/// its runs of adjacent descriptors sorted (at most `MAX_UNSORTED_RUNS`,
/// beyond which it is refused).
#[test]
fn validating_a_map_is_bounded_and_still_finds_every_overlap() {
    use x86_mmap::{validate_map, MAX_UNSORTED_RUNS};
    let base = 0x100_0000u64;
    let pages = 4096u64;
    // 4096 one-page descriptors, two kinds alternating in blocks of 256.
    let page = |i: u64| (if (i / 256) % 2 == 0 { 7 } else { 4 }, base + i * PAGE, 1);
    let sorted: Vec<_> = (0..pages).map(page).collect();
    // The same in blocks of 64 listed in reverse block order: unsorted, 64
    // runs.
    let blocks: Vec<_> = (0..pages / 64).rev().flat_map(|b| (b * 64..(b + 1) * 64).map(page)).collect();
    for ds in [&sorted, &blocks] {
        let map = map_of(48, ds);
        assert_eq!(validate_map(&map, 48), Ok(()));
        let r = regions(&map, 48, 0, 0).unwrap();
        assert_eq!(r.iter().map(|e| e.1).sum::<u64>(), pages * PAGE);
        assert!(r.len() <= 64 + 16, "merged: {}", r.len());
    }
    // One overlapping pair among them is found wherever it is.
    for (at, what) in [(0, "first"), (pages / 2 + 17, "inside a merged run"), (pages - 1, "last")] {
        for ds in [&sorted, &blocks] {
            let mut ds = ds.clone();
            ds.insert(ds.len() / 3, (11, base + at * PAGE, 1));
            assert_eq!(validate_map(&map_of(48, &ds), 48), Err("overlapping EFI memory descriptors"), "{what}");
            let last = ds.len() - 1;
            ds.swap(0, last);
            assert_eq!(validate_map(&map_of(48, &ds), 48), Err("overlapping EFI memory descriptors"), "{what}, swapped");
        }
    }
    // A run overlapping another run only past its first descriptor.
    let ds = [(7, base + 4 * PAGE, 4), (7, base + 8 * PAGE, 4), (4, base, 4), (10, base + 10 * PAGE, 1)];
    assert_eq!(validate_map(&map_of(48, &ds), 48), Err("overlapping EFI memory descriptors"));
    // Unsorted and with no two adjacent: refused past MAX_UNSORTED_RUNS
    // runs, taken at that many.
    let scattered = |n: u64| -> Vec<(u32, u64, u64)> { (0..n).rev().map(|i| (7, base + 2 * i * PAGE, 1)).collect() };
    assert_eq!(validate_map(&map_of(48, &scattered(MAX_UNSORTED_RUNS as u64)), 48), Ok(()));
    assert_eq!(validate_map(&map_of(48, &scattered(MAX_UNSORTED_RUNS as u64 + 1)), 48), Err("too many unsorted EFI memory descriptors"));
    // Sorted, any number is fine.
    let spaced: Vec<_> = (0..4 * MAX_UNSORTED_RUNS as u64).map(|i| (7, base + 2 * i * PAGE, 1)).collect();
    assert_eq!(validate_map(&map_of(48, &spaced), 48), Ok(()));
    // Empty descriptors neither break the order nor count.
    let mut with_empty = spaced.clone();
    with_empty.insert(5, (7, 0, 0));
    assert_eq!(validate_map(&map_of(48, &with_empty), 48), Ok(()));
}
