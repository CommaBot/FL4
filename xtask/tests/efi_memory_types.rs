//! Audit (TDX r2, R1-1, R1-4, R1-5): EFI memory types from raw descriptors
//! to what the loader and the kernel do with them. `EfiUnacceptedMemoryType`
//! is 15: unaccepted RAM the kernel accepts (bootmem `unaccepted`), never
//! read as ACPI and never a mailbox or CC log; the wakeup mailbox must be
//! `EfiACPIMemoryNVS` (10) to both the loader (acpi.rs `mailbox_ok`) and the
//! kernel (bootmem `mailbox_ok`, ACPI NVS only, plus the loader's tag); the
//! CC log area ACPI reclaim or NVS memory (ccel.rs `ccel_area_in_map`).
extern crate self as fl4_core;

pub mod boot {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct Region {
        pub start: u64,
        pub end: u64,
    }
    impl Region {
        pub const EMPTY: Region = Region { start: 0, end: 0 };
    }
}

#[allow(dead_code)]
#[path = "../../crates/fl4-kernel/src/bootmem.rs"]
mod bootmem;
#[allow(dead_code)]
#[path = "../../crates/fl4-efi/src/snp_map.rs"]
mod snp_map;
#[allow(dead_code)]
#[path = "../../crates/fl4-efi/src/x86_mmap.rs"]
mod x86_mmap;
#[allow(dead_code)]
#[path = "../../crates/fl4-efi/src/acpi.rs"]
mod acpi;
#[allow(dead_code)]
#[path = "../../crates/fl4-efi/src/tcg2.rs"]
mod tcg2;
#[allow(dead_code)]
#[path = "../../crates/fl4-efi/src/ccel.rs"]
mod ccel;

const PAGE: u64 = 4096;
const STRIDE: usize = 48;
const GIB: u64 = 1 << 30;

fn desc(ty: u32, base: u64, pages: u64, attributes: u64) -> Vec<u8> {
    let mut d = vec![0u8; STRIDE];
    d[0..4].copy_from_slice(&ty.to_le_bytes());
    d[8..16].copy_from_slice(&base.to_le_bytes());
    d[24..32].copy_from_slice(&pages.to_le_bytes());
    d[32..40].copy_from_slice(&attributes.to_le_bytes());
    d
}

/// A TD's map: RAM, firmware memory of every kind that matters, MMIO,
/// unaccepted RAM and a type past `EfiMaxMemoryType`.
const CONVENTIONAL: u64 = 0x10_0000;
const NVS: u64 = 0x7f00_0000;
const RECLAIM: u64 = 0x7f80_0000;
const RT_CODE: u64 = 0x7f90_0000;
const RT_DATA: u64 = 0x7fa0_0000;
const PERSISTENT: u64 = 0x7fb0_0000;
const MMIO: u64 = 0xfe00_0000;
const MAX_TYPE: u64 = 0x8000_0000;
const RESERVED_WB: u64 = 0x7fc0_0000;
const UNACCEPTED: u64 = GIB * 4;

fn map() -> Vec<u8> {
    [
        desc(7, CONVENTIONAL, 0x100, 8),
        desc(10, NVS, 4, 8),
        desc(9, RECLAIM, 1, 8),
        desc(5, RT_CODE, 1, 8),
        desc(6, RT_DATA, 1, 8),
        desc(14, PERSISTENT, 1, 8),
        desc(16, MAX_TYPE, 1, 8),
        desc(0, RESERVED_WB, 1, 8),
        desc(11, MMIO, 1, 1),
        desc(15, UNACCEPTED, GIB / PAGE, 8),
    ]
    .concat()
}

/// The Multiboot 2 entries fl4-efi hands the kernel for `map`.
fn mb2(map: &[u8]) -> Vec<(u64, u64, u32)> {
    let mut out = Vec::new();
    x86_mmap::regions(map, STRIDE, 0, 0, |r| {
        out.push(r);
        Ok(())
    })
    .unwrap();
    out
}

fn raw(map: &[u8]) -> Vec<(u64, u64, u32)> {
    x86_mmap::descriptors(map, STRIDE).map(|(b, n, t, _)| (b, n, t)).collect()
}

#[test]
fn unaccepted_ram_is_type_15_and_the_kernel_accepts_only_it() {
    let m = map();
    let entries = mb2(&m);
    assert!(entries.contains(&(UNACCEPTED, GIB, x86_mmap::UNACCEPTED)));
    assert_eq!(bootmem::UNACCEPTED, x86_mmap::UNACCEPTED);
    let acc = bootmem::unaccepted(entries.iter().copied(), 0x10_0000, 8 * GIB);
    assert_eq!(&acc.r[..acc.n], [boot::Region { start: UNACCEPTED, end: UNACCEPTED + GIB }]);
    // None of it is RAM the kernel uses before accepting it.
    let ram = bootmem::ram(entries.iter().copied(), 0x10_0000, 8 * GIB);
    assert!(!ram.contains(UNACCEPTED, UNACCEPTED + PAGE));
    // 14 is persistent memory (kept as ACPI NVS), 16 and later reserved.
    assert!(entries.contains(&(PERSISTENT, PAGE, 4)));
    assert!(entries.contains(&(MAX_TYPE, PAGE, 2)));
}

/// Audit (TDX r3, R2-2): write-back `EfiReservedMemoryType` is private
/// firmware memory of its own kind: no RAM, no ACPI NVS (so no ACPI tables
/// and no mailbox), no unaccepted memory.
#[test]
fn write_back_reserved_memory_is_private_but_no_acpi_memory() {
    let m = map();
    let entries = mb2(&m);
    assert_eq!(bootmem::PRIVATE_RESERVED, x86_mmap::PRIVATE_RESERVED);
    assert!(entries.contains(&(RESERVED_WB, PAGE, x86_mmap::PRIVATE_RESERVED)));
    assert!(!bootmem::ram(entries.iter().copied(), 0x10_0000, 8 * GIB).contains(RESERVED_WB, RESERVED_WB + PAGE));
    let acc = bootmem::unaccepted(entries.iter().copied(), 0x10_0000, 8 * GIB);
    assert!(acc.r[..acc.n].iter().all(|r| r.start != RESERVED_WB));
    assert!(!bootmem::mailbox_ok(RESERVED_WB, 8 * GIB, entries.iter().copied()));
    assert!(!acpi::mailbox_ok(RESERVED_WB, raw(&m), &[]));
    assert!(!x86_mmap::readable(0));
    assert!(!ccel::ccel_area_in_map(RESERVED_WB, PAGE as usize, raw(&m)));
}

#[test]
fn the_loader_reads_acpi_only_from_firmware_memory() {
    // By the EFI type alone (audit TDX r3, R2-2): loader, boot services,
    // conventional, ACPI reclaim and NVS memory.
    for (ty, ok) in [(1, true), (2, true), (3, true), (4, true), (7, true), (9, true), (10, true), (0, false), (5, false), (6, false), (8, false), (11, false), (12, false), (13, false), (14, false), (15, false), (16, false)] {
        assert_eq!(x86_mmap::readable(ty), ok, "EFI type {ty}");
    }
    let m = map();
    let readable = |addr: u64, len: u64| {
        x86_mmap::within(addr, len, x86_mmap::descriptors(&m, STRIDE).map(|(b, n, t, _)| (b, n, x86_mmap::readable(t))))
    };
    assert!(readable(NVS, 4 * PAGE));
    assert!(readable(RECLAIM, 36));
    assert!(!readable(MMIO, 4));
    assert!(!readable(UNACCEPTED, 36));
    assert!(!readable(NVS + 3 * PAGE, 2 * PAGE), "past its descriptor");
    assert!(!readable(RESERVED_WB, 36), "write-back reserved memory");
    assert!(!readable(RT_DATA, 36), "runtime services data");
}

#[test]
fn only_an_nvs_page_is_a_wakeup_mailbox_to_loader_and_kernel() {
    let m = map();
    let entries = mb2(&m);
    let window = 8 * GIB;
    let loader = |page: u64| acpi::mailbox_ok(page, raw(&m), &[]).then_some(page);
    // The kernel: ACPI NVS by its map, and the loader's own answer.
    let kernel = |page: u64| bootmem::mailbox_ok(page, window, entries.iter().copied()) && loader(page) == Some(page);
    assert!(kernel(NVS) && kernel(NVS + 3 * PAGE));
    for (page, what) in [(RT_CODE, "runtime services code"), (RT_DATA, "runtime services data"), (RECLAIM, "ACPI reclaim"), (CONVENTIONAL, "conventional"), (MMIO, "MMIO"), (UNACCEPTED, "unaccepted"), (PERSISTENT, "persistent"), (MAX_TYPE, "past EfiMaxMemoryType")] {
        assert!(!kernel(page), "{what}");
        assert_eq!(loader(page), None, "{what}");
    }
    // The kernel's map alone cannot tell runtime services memory from NVS
    // (both kind 4): the loader's check is what refuses it.
    assert!(bootmem::mailbox_ok(RT_DATA, window, entries.iter().copied()));
    assert!(!bootmem::mailbox_ok(RECLAIM, window, entries.iter().copied()));
}

#[test]
fn the_cc_log_area_is_acpi_reclaim_or_nvs_only() {
    let m = map();
    assert!(ccel::ccel_area_in_map(NVS, 4 * PAGE as usize, raw(&m)));
    assert!(ccel::ccel_area_in_map(RECLAIM, PAGE as usize, raw(&m)));
    for at in [CONVENTIONAL, RT_CODE, RT_DATA, PERSISTENT, MAX_TYPE, MMIO, UNACCEPTED] {
        assert!(!ccel::ccel_area_in_map(at, PAGE as usize, raw(&m)), "{at:#x}");
    }
}

/// Audit (TDX r4, R3-3): the SEV-SNP CPUID and secrets pages reach the
/// kernel as private reserved memory: kept private and out of device
/// memory by a confidential guest's kernel (as ACPI NVS is), but nothing it
/// reads ACPI tables from (`acpi_readable`: RAM, reclaim or NVS) and no
/// mailbox; the ACPI NVS between them stays readable.
#[test]
fn snp_pages_are_private_and_no_acpi_memory() {
    let (cpuid, secrets) = (NVS + PAGE, NVS + 3 * PAGE);
    let m = map();
    let mut entries = Vec::new();
    x86_mmap::regions(&m, STRIDE, cpuid, secrets, |r| {
        entries.push(r);
        Ok(())
    })
    .unwrap();
    // The NVS descriptor holds both pages: the whole of it is private.
    assert!(entries.contains(&(NVS, 4 * PAGE, x86_mmap::PRIVATE_RESERVED)));
    // fl4_boot's `acpi_readable` takes RAM, ACPI reclaim and NVS only.
    let acpi_readable = |p: u64, len: u64| entries.iter().any(|&(b, n, ty)| matches!(ty, 1 | 3 | 4) && b <= p && p + len <= b + n);
    assert!(!acpi_readable(cpuid, 36) && !acpi_readable(secrets, 36));
    assert!(acpi_readable(RECLAIM, 36));
    assert!(!bootmem::mailbox_ok(secrets, 8 * GIB, entries.iter().copied()));
    // Split from a separate NVS page: that one stays NVS, readable.
    let split = [desc(10, NVS, 1, 8), desc(10, NVS + PAGE, 1, 8), desc(10, NVS + 2 * PAGE, 1, 8)].concat();
    let mut entries = Vec::new();
    x86_mmap::regions(&split, STRIDE, NVS + PAGE, 0, |r| {
        entries.push(r);
        Ok(())
    })
    .unwrap();
    assert_eq!(entries, [(NVS, PAGE, 4), (NVS + PAGE, PAGE, x86_mmap::PRIVATE_RESERVED), (NVS + 2 * PAGE, PAGE, 4)]);
    let lib = include_str!("../../crates/fl4-kernel/src/lib.rs");
    assert!(lib.contains("mb.mmap[..mb.n_mmap].iter().any(|e| matches!(e.ty, 1 | 3 | 4) && e.base <= p && end <= e.base.saturating_add(e.len))"));
    assert!(lib.contains("if matches!(e.ty, 1 | 4 | bootmem::PRIVATE_RESERVED) {"));
    assert!(lib.contains("matches!(e.ty, 1 | 3 | 4 | bootmem::PRIVATE_RESERVED)"));
}
