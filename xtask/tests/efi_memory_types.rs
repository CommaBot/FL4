//! Audit (TDX r2, R1-1, R1-4, R1-5): EFI memory types from raw descriptors
//! to what the loader and the kernel do with them. `EfiUnacceptedMemoryType`
//! is 15: unaccepted RAM the kernel accepts (bootmem `unaccepted`), never
//! read as ACPI and never a mailbox or CC log; the wakeup mailbox must be
//! `EfiACPIMemoryNVS` (10) to both the loader (acpi.rs `mailbox_ok`) and the
//! kernel (bootmem `mailbox_ok`, ACPI NVS only, plus the loader's tag); the
//! CC log area ACPI reclaim or NVS memory (ccel.rs `ccel_area_in_map`).
//! Runtime services code and data and persistent memory (5, 6, 14) are
//! firmware's private memory, never ACPI NVS (audit TDX r5, fix 4).
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
    // 14 is persistent memory (kept private), 16 and later reserved.
    assert!(entries.contains(&(PERSISTENT, PAGE, x86_mmap::PRIVATE_RESERVED)));
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
    // The kernel's map alone now refuses runtime services and persistent
    // memory too: none of it is kind 4 any more.
    for page in [RT_CODE, RT_DATA, PERSISTENT, RECLAIM] {
        assert!(!bootmem::mailbox_ok(page, window, entries.iter().copied()), "{page:#x}");
    }
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
    let acpi_readable = |p: u64, len: u64| bootmem::acpi_readable(p, len, entries.iter().copied());
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
    assert!(lib.contains("!cvm::hardened() || bootmem::acpi_readable(p, len, mb.mmap[..mb.n_mmap].iter().map(|e| (e.base, e.len, e.ty)))"));
    assert!(lib.contains("if matches!(e.ty, 1 | 4 | bootmem::PRIVATE_RESERVED) {"));
    assert!(lib.contains("matches!(e.ty, 1 | 3 | 4 | bootmem::PRIVATE_RESERVED)"));
}

/// Audit (TDX r5, fix 4): fl4-efi gave runtime services code and data and
/// persistent memory (EFI 5, 6, 14) kind 4, ACPI NVS, so the kernel read
/// ACPI tables from them (`acpi_readable`) and took a mailbox there
/// (`mailbox_ok`) where the loader (x86_mmap `readable`, acpi.rs
/// `mailbox_ok`) refuses both. They are firmware's private memory now:
/// still private and out of device memory in a confidential guest, but
/// neither. Nor does the kernel read ACPI tables from physical page 0.
#[test]
fn runtime_services_and_persistent_memory_are_private_but_no_acpi_memory() {
    let m = map();
    let entries = mb2(&m);
    let readable = |p: u64, len: u64| bootmem::acpi_readable(p, len, entries.iter().copied());
    let window = 8 * GIB;
    for (at, what) in [(RT_CODE, "runtime services code"), (RT_DATA, "runtime services data"), (PERSISTENT, "persistent")] {
        let kind = entries.iter().find(|e| e.0 == at).expect(what).2;
        assert_eq!(kind, x86_mmap::PRIVATE_RESERVED, "{what}");
        assert!(!readable(at, 36), "{what}");
        assert!(!bootmem::mailbox_ok(at, window, entries.iter().copied()), "{what}");
        // The loader agrees.
        let ty = raw(&m).iter().find(|e| e.0 == at).unwrap().2;
        assert!(!x86_mmap::readable(ty), "{what}");
        // fl4_boot keeps it out of device memory and private.
        assert!(matches!(kind, 1 | 4 | bootmem::PRIVATE_RESERVED), "{what}");
        assert!(matches!(kind, 1 | 3 | 4 | bootmem::PRIVATE_RESERVED), "{what}");
        assert!(!bootmem::ram(entries.iter().copied(), 0x10_0000, window).contains(at, at + PAGE), "{what}");
    }
    // What the loader reads, the kernel reads.
    assert!(readable(NVS, 36) && readable(RECLAIM, 36) && readable(CONVENTIONAL, 36));
    assert!(readable(RECLAIM, PAGE) && !readable(RECLAIM, PAGE + 1), "whole in one entry");
    assert!(!readable(RECLAIM, 0) && !readable(u64::MAX - 8, 36), "empty or wrapping");
    for (at, what) in [(MMIO, "MMIO"), (UNACCEPTED, "unaccepted"), (RESERVED_WB, "reserved"), (MAX_TYPE, "past EfiMaxMemoryType")] {
        assert!(!readable(at, 36), "{what}");
    }
}

#[test]
fn the_kernel_reads_no_acpi_table_from_page_0() {
    let low = [(0, 0xa_0000, 1), (0x10_0000, 0x10_0000, 1)];
    let readable = |p: u64, len: u64| bootmem::acpi_readable(p, len, low.iter().copied());
    for (p, len) in [(0, 36), (0, 20), (0x40e, 2), (PAGE - 36, 36), (PAGE - 1, 2)] {
        assert!(!readable(p, len), "{p:#x}+{len}");
    }
    assert!(readable(PAGE, 36) && readable(0x9_f000, 20));
    assert!(!readable(0xa_0000, 20), "past the entry");
    // Only in a confidential guest: elsewhere the window alone bounds it.
    let lib = include_str!("../../crates/fl4-kernel/src/lib.rs");
    assert!(lib.contains("let acpi_readable = |p: u64, len: u64| {\n        !cvm::hardened() || bootmem::acpi_readable("));
}

/// Audit (TDX r5, R1-M2): fl4-efi hands on no overlapping entries, but the
/// kernel does not rely on it: an ACPI read or the mailbox needs every
/// non-empty entry it touches to be of an allowed type and to hold it
/// whole, so a private, unaccepted, MMIO or reserved entry over it wins.
#[test]
fn an_overlapping_entry_of_another_type_refuses_acpi_reads_and_the_mailbox() {
    const NVS_AT: u64 = 0x7f00_0000;
    let window = 8 * GIB;
    let acpi = |m: &[(u64, u64, u32)], p: u64, len: u64| bootmem::acpi_readable(p, len, m.iter().copied());
    let mailbox = |m: &[(u64, u64, u32)], p: u64| bootmem::mailbox_ok(p, window, m.iter().copied());
    let nvs = (NVS_AT, 4 * PAGE, 4);
    assert!(acpi(&[nvs], NVS_AT + PAGE, 36) && mailbox(&[nvs], NVS_AT + PAGE));
    for other in [bootmem::PRIVATE_RESERVED, bootmem::UNACCEPTED, 2] {
        for (base, len, what) in [
            (NVS_AT, 4 * PAGE, "the same range"),
            (NVS_AT + PAGE, PAGE, "just the page"),
            (NVS_AT - PAGE, 2 * PAGE + 1, "the page's first byte"),
            (NVS_AT + 2 * PAGE - 1, PAGE, "the page's last byte"),
            (0, 1 << 40, "around everything"),
        ] {
            let bad = (base, len, other);
            for m in [[nvs, bad], [bad, nvs]] {
                assert!(!acpi(&m, NVS_AT + PAGE, PAGE), "{other:#x} {what}");
                assert!(!mailbox(&m, NVS_AT + PAGE), "{other:#x} {what}");
            }
        }
        // Next to it, or empty: no effect.
        for bad in [(NVS_AT + 4 * PAGE, PAGE, other), (NVS_AT - PAGE, PAGE, other), (NVS_AT + PAGE, 0, other)] {
            for m in [[nvs, bad], [bad, nvs]] {
                assert!(acpi(&m, NVS_AT + PAGE, PAGE) && mailbox(&m, NVS_AT + PAGE), "{bad:x?}");
            }
        }
    }
    // Two allowed entries over the same range still each hold it whole.
    let ram_over = (NVS_AT, 4 * PAGE, 1);
    assert!(acpi(&[nvs, ram_over], NVS_AT + PAGE, 36));
    // An allowed entry holding only part of it does not.
    assert!(!acpi(&[nvs, (NVS_AT + PAGE + 8, PAGE, 3)], NVS_AT + PAGE, 36));
    assert!(!mailbox(&[nvs, (NVS_AT + PAGE, 8, 4)], NVS_AT + PAGE));
    // RAM over the NVS page is no mailbox.
    assert!(!mailbox(&[nvs, ram_over], NVS_AT + PAGE));
}
