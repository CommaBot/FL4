//! The AArch64 kernel's boot-time decisions on the host: its memory lists
//! (fl4-kernel-aarch64 bootmem.rs), its ACPI parsing (hw.rs, over
//! host-allocated tables), the GIC layout arithmetic and the cache
//! maintenance rule (fl4-arch-aarch64 gic_layout.rs, cache_rule.rs). Only
//! the window, the console and the boot core's MPIDR are replaced.
extern crate self as fl4_core;
extern crate self as fl4_arch_aarch64;

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

/// Physical memory: a host buffer (`MEMORY`: its address and length), so
/// tables hold small physical addresses (an RSDT's are 32 bits).
pub mod layout {
    use std::cell::Cell;
    thread_local! {
        pub static MEMORY: Cell<(u64, u64)> = const { Cell::new((0, 0)) };
    }
    pub fn pptr(p: u64) -> u64 {
        let (base, len) = MEMORY.get();
        assert!(p < len, "read outside physical memory: {p:#x}");
        base + p
    }
}

/// The window maps all of the buffer.
pub mod mmu {
    pub fn in_window(start: u64, len: u64) -> bool {
        start.checked_add(len).is_some_and(|end| end <= super::layout::MEMORY.get().1)
    }
}

pub mod serial {
    pub const KIND_NONE: u64 = 0;
    pub const KIND_PL011: u64 = 1;
    pub const KIND_16550: u64 = 2;
}

pub mod smp {
    pub const PSCI_NONE: u64 = 0;
    pub const PSCI_SMC: u64 = 1;
    pub const PSCI_HVC: u64 = 2;
}

pub mod cpu {
    pub fn mpidr() -> u64 {
        0
    }
}

#[path = "../../crates/fl4-arch-aarch64/src/gic_layout.rs"]
pub mod gic_layout;
#[path = "../../crates/fl4-arch-aarch64/src/cache_rule.rs"]
mod cache_rule;
#[allow(dead_code)]
#[path = "../../crates/fl4-kernel-aarch64/src/bootmem.rs"]
mod bootmem;
#[allow(dead_code)]
#[path = "../../crates/fl4-kernel-aarch64/src/hw.rs"]
mod hw;

// ---- GIC ---------------------------------------------------------------------

#[test]
fn the_distributor_never_touches_the_special_intids() {
    assert_eq!(gic_layout::dist_lines(0), 32);
    assert_eq!(gic_layout::dist_lines(2), 96);
    assert_eq!(gic_layout::dist_lines(30), 992);
    // ITLinesNumber 31: 1024 lines, of which 1020..1023 are special.
    assert_eq!(gic_layout::dist_lines(31), 1020);
    assert_eq!(gic_layout::dist_lines(0xffff_ffff), 1020);
    assert_eq!(gic_layout::bank_bits(960, 1020), u32::MAX);
    assert_eq!(gic_layout::bank_bits(992, 1020), 0x0fff_ffff);
    assert_eq!(gic_layout::bank_bits(32, 64), u32::MAX);
    assert_eq!(gic_layout::bank_bits(64, 64), 0);
    // The registers init_dist writes stay inside the defined ones:
    // IPRIORITYR/ITARGETSR up to n = 254, IROUTER up to n = 1019.
    let lines = gic_layout::dist_lines(31);
    assert!((32..lines).step_by(4).all(|i| i / 4 <= 254));
    assert!((32..lines).all(|i| i <= 1019));
}

#[test]
fn gicv2_spis_go_to_the_boot_cores_interface() {
    assert_eq!(gic_layout::v2_targets(0x0404_0404), 0x0404_0404);
    assert_eq!(gic_layout::v2_targets(0x0000_0080), 0x8080_8080);
    // A uniprocessor GIC reads zero.
    assert_eq!(gic_layout::v2_targets(0), 0x0101_0101);
}

/// GICR_TYPER values at frame addresses.
fn frames(list: &[(u64, u64)]) -> impl Fn(u64) -> u64 + '_ {
    move |a| list.iter().find(|f| f.0 == a).map(|f| f.1).unwrap_or_else(|| panic!("read of an unknown frame {a:#x}"))
}

const VLPIS: u64 = 1 << 1;
const LAST: u64 = 1 << 4;

#[test]
fn redistributors_are_found_only_inside_their_mapping() {
    let b = 0x800_0000;
    let t = [(b, 0 << 32), (b + 0x2_0000, 1 << 32), (b + 0x4_0000, 2 << 32 | LAST)];
    assert_eq!(gic_layout::find_frame(b, 0x6_0000, 1, frames(&t)), Some(b + 0x2_0000));
    assert_eq!(gic_layout::find_frame(b, 0x6_0000, 2, frames(&t)), Some(b + 0x4_0000));
    assert_eq!(gic_layout::find_frame(b, 0x6_0000, 3, frames(&t)), None);
    // A mapping that ends inside the third frame: never that one, and its
    // GICR_TYPER is not read (`frames` would panic).
    assert_eq!(gic_layout::find_frame(b, 0x5_0000, 2, frames(&t)), None);
    assert_eq!(gic_layout::find_frame(b, 0x1_0000, 0, frames(&t)), None);
    assert_eq!(gic_layout::find_frame(b, 0, 0, frames(&t)), None);
    // GICv4: 256 KiB per redistributor.
    let v4 = [(b, 0 << 32 | VLPIS), (b + 0x4_0000, 1 << 32 | VLPIS | LAST)];
    assert_eq!(gic_layout::find_frame(b, 0x8_0000, 1, frames(&v4)), Some(b + 0x4_0000));
    assert_eq!(gic_layout::find_frame(b, 0x6_0000, 1, frames(&v4)), Some(b + 0x4_0000));
    assert_eq!(gic_layout::find_frame(u64::MAX - 0xffff, 0x1_0000, 0, frames(&[])), None);
}

#[test]
fn a_gicv4_redistributor_reserves_its_vlpi_frames() {
    let b = 0x800_0000;
    // A MADT GICC entry's range: one core's RD and SGI frames.
    assert_eq!(gic_layout::span(b, 0x2_0000, frames(&[(b, VLPIS)])), 0x4_0000);
    assert_eq!(gic_layout::span(b, 0x2_0000, frames(&[(b, 0)])), 0x2_0000);
    // A GICR range: all of it, the last frame's VLPI frames included.
    let v4 = [(b, VLPIS), (b + 0x4_0000, VLPIS | LAST)];
    assert_eq!(gic_layout::span(b, 0x8_0000, frames(&v4)), 0x8_0000);
    assert_eq!(gic_layout::span(b, 0x1_0000, frames(&v4)), 0);
}

// ---- cache maintenance ------------------------------------------------------------

#[test]
fn cache_maintenance_through_the_user_mapping_waits_for_the_gate() {
    assert!(cache_rule::needs_gate(true, true));
    assert!(cache_rule::needs_gate(true, false));
    // Clean, clean+invalidate and unify through TTBR0.
    assert!(cache_rule::needs_gate(false, false));
    assert!(!cache_rule::needs_gate(false, true));
}

// ---- memory lists -----------------------------------------------------------------

#[test]
fn a_full_range_list_reports_what_it_lost() {
    let mut r = bootmem::Ranges::new();
    for i in 0..bootmem::MAX_RANGES as u64 {
        r.add(i * 0x2000, i * 0x2000 + 0x1000);
    }
    assert!(!r.lost);
    assert_eq!(r.n, bootmem::MAX_RANGES);
    // One more disjoint range, at the top where fl4-efi puts the root task.
    r.add(1 << 40, (1 << 40) + 0x1000);
    assert!(r.lost);
    // And a split by `remove` of a full list.
    let mut r2 = bootmem::Ranges::new();
    for i in 0..bootmem::MAX_RANGES as u64 {
        r2.add(i * 0x4000, i * 0x4000 + 0x3000);
    }
    r2.remove(0x1000, 0x2000);
    assert!(r2.lost);
    // Every entry of the loader's largest memory map fits.
    assert!(bootmem::MAX_RANGES >= fl4_bootinfo::MAX_MMAP + 16);
}

#[test]
fn memory_map_entries_never_wrap() {
    assert_eq!(bootmem::entry_pages(0x1000, 0x3000, u64::MAX), Some((0x1000, 0x4000)));
    assert_eq!(bootmem::entry_pages(0x1800, 0x3000, u64::MAX), Some((0x2000, 0x4000)));
    assert_eq!(bootmem::entry_pages(0x1000, 0x3000, 0x2000), Some((0x1000, 0x2000)));
    assert_eq!(bootmem::entry_pages(u64::MAX - 0xfff, 0x2000, u64::MAX), None);
    assert_eq!(bootmem::entry_pages(0xffff_ffff_ffff_f001, 0x10, u64::MAX), None);
    assert_eq!(bootmem::entry_pages(0x1000, 0, u64::MAX), None);
}

#[test]
fn device_mappings_stay_below_the_physical_address_size() {
    let top = 1 << 40;
    assert_eq!(bootmem::device_pages(0x900_0000, 0x1000, top), Some((0x900_0000, 0x1000)));
    assert_eq!(bootmem::device_pages(0x900_0800, 0x1000, top), Some((0x900_0000, 0x2000)));
    assert_eq!(bootmem::device_pages(top - 0x1000, 0x1000, top), Some((top - 0x1000, 0x1000)));
    assert_eq!(bootmem::device_pages(top - 0x1000, 0x1001, top), None);
    assert_eq!(bootmem::device_pages(1 << 52, 0x1000, top), None);
    assert_eq!(bootmem::device_pages(u64::MAX - 0xff, 0x1000, u64::MAX), None);
    assert_eq!(bootmem::device_pages(0x900_0000, 0, top), None);
}

// ---- ACPI -------------------------------------------------------------------------

fn checksum(table: &mut [u8], offset: usize) {
    table[offset] = 0;
    table[offset] = table.iter().fold(0u8, |sum, byte| sum.wrapping_add(*byte)).wrapping_neg();
}

/// A MADT GICC entry (type 0x0b, 80 bytes): enabled core `mpidr` with its
/// redistributor at `gicr`.
fn gicc(mpidr: u64, gicr: u64) -> Vec<u8> {
    let mut e = vec![0u8; 80];
    e[0] = 0x0b;
    e[1] = 80;
    e[12..16].copy_from_slice(&1u32.to_le_bytes());
    e[60..68].copy_from_slice(&gicr.to_le_bytes());
    e[68..76].copy_from_slice(&mpidr.to_le_bytes());
    e
}

/// A GICD entry (type 0x0c, 24 bytes), GICv3.
fn gicd() -> Vec<u8> {
    let mut e = vec![0u8; 24];
    e[0] = 0x0c;
    e[1] = 24;
    e[8..16].copy_from_slice(&0x800_0000u64.to_le_bytes());
    e[20] = 3;
    e
}

/// A GICR entry (type 0x0e, 16 bytes).
fn gicr(base: u64, len: u32) -> Vec<u8> {
    let mut e = vec![0u8; 16];
    e[0] = 0x0e;
    e[1] = 16;
    e[4..12].copy_from_slice(&base.to_le_bytes());
    e[12..16].copy_from_slice(&len.to_le_bytes());
    e
}

/// Where the tables are in physical memory.
const BASE: u64 = 0x1000;

struct Tables {
    mem: Vec<u8>,
}

impl Tables {
    fn rsdp(&self) -> u64 {
        layout::MEMORY.set((self.mem.as_ptr() as u64, self.mem.len() as u64));
        BASE
    }
    fn buf(&mut self) -> &mut [u8] {
        &mut self.mem[BASE as usize..]
    }
}

/// RSDP (at 0, revision `rev`), XSDT or RSDT (at 64) and a MADT of
/// `entries` (at 128), from physical `BASE` on.
fn tables(entries: &[u8], rev: u8, root_sig: &[u8; 4]) -> Tables {
    let mut mem = vec![0u8; BASE as usize + 128 + 44 + entries.len()];
    let buf = &mut mem[BASE as usize..];
    let base = BASE;
    let madt = &mut buf[128..];
    madt[44..].copy_from_slice(entries);
    let len = madt.len() as u32;
    madt[..4].copy_from_slice(b"APIC");
    madt[4..8].copy_from_slice(&len.to_le_bytes());
    checksum(madt, 9);
    let xsdt = root_sig == b"XSDT";
    let root_len = if xsdt { 44 } else { 40 };
    let root = &mut buf[64..64 + root_len];
    root[..4].copy_from_slice(root_sig);
    root[4..8].copy_from_slice(&(root_len as u32).to_le_bytes());
    if xsdt {
        root[36..44].copy_from_slice(&(base + 128).to_le_bytes());
    } else {
        root[36..40].copy_from_slice(&((base + 128) as u32).to_le_bytes());
    }
    checksum(root, 9);
    let rsdp = &mut buf[..36];
    rsdp[..8].copy_from_slice(b"RSD PTR ");
    rsdp[15] = rev;
    if rev >= 2 {
        rsdp[20..24].copy_from_slice(&36u32.to_le_bytes());
        rsdp[24..32].copy_from_slice(&(base + 64).to_le_bytes());
    } else {
        rsdp[16..20].copy_from_slice(&((base + 64) as u32).to_le_bytes());
    }
    checksum(&mut rsdp[..20], 8);
    checksum(rsdp, 32);
    Tables { mem }
}

fn madt(entries: &[Vec<u8>]) -> Vec<u8> {
    entries.concat()
}

#[test]
fn every_cores_redistributor_is_kept_from_user_space() {
    // Sixteen cores, each with its redistributor in its GICC entry: all
    // sixteen ranges are recorded, so the kernel reserves all of them.
    let mut e = vec![gicd()];
    for c in 0..16u64 {
        e.push(gicc(c, 0x80a_0000 + c * 0x2_0000));
    }
    let t = tables(&madt(&e), 2, b"XSDT");
    let h = hw::discover(t.rsdp(), 0).expect("ACPI");
    assert_eq!(h.n_gicr, 16);
    assert!(!h.gicr_lost);
    for c in 0..16u64 {
        assert!(h.gicr[..h.n_gicr].contains(&(0x80a_0000 + c * 0x2_0000, 0x2_0000)), "core {c}");
    }
}

#[test]
fn redistributors_past_the_table_are_a_boot_failure() {
    let mut e = vec![gicd()];
    for c in 0..hw::MAX_GICR as u64 + 1 {
        e.push(gicr(0x1000_0000 + c * 0x10_0000, 0x2_0000));
    }
    let t = tables(&madt(&e), 2, b"XSDT");
    let h = hw::discover(t.rsdp(), 0).expect("ACPI");
    assert_eq!(h.n_gicr, hw::MAX_GICR);
    assert!(h.gicr_lost);
}

#[test]
fn acpi_1_0_rsdps_use_the_rsdt_and_copy_20_bytes() {
    let e = madt(&[gicd(), gicc(0, 0x80a_0000)]);
    let mut t = tables(&e, 0, b"RSDT");
    let h = hw::discover(t.rsdp(), 0).expect("ACPI 1.0");
    assert_eq!(h.n_gicr, 1);
    assert!(h.rsdp[20..].iter().all(|&b| b == 0));
    assert_eq!(&h.rsdp[..20], &t.buf()[..20]);
}

#[test]
fn rsdp_extended_checksum_and_root_signature_are_checked() {
    let e = madt(&[gicd(), gicc(0, 0x80a_0000)]);
    // A revision 2 RSDP whose extended checksum fails: only its ACPI 1.0
    // part is used, and that points at no RSDT.
    let mut t = tables(&e, 2, b"XSDT");
    t.buf()[32] ^= 0xff;
    assert!(hw::discover(t.rsdp(), 0).is_none());
    // An XSDT pointer to something that is not an XSDT.
    let mut t = tables(&e, 2, b"XSDT");
    t.buf()[64..68].copy_from_slice(b"FACP");
    checksum(&mut t.buf()[64..108], 9);
    assert!(hw::discover(t.rsdp(), 0).is_none());
    // Both sound.
    let mut t = tables(&e, 2, b"XSDT");
    let h = hw::discover(t.rsdp(), 0).expect("ACPI 2.0");
    assert_eq!(&h.rsdp[..], &t.buf()[..36]);
}
