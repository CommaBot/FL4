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
#[path = "../../crates/fl4-arch-aarch64/src/el0_access.rs"]
mod el0_access;
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

// ---- EL0 access to per-core registers (audit F3) -------------------------------

#[test]
fn el0_debug_channel_and_trace_registers_trap() {
    // MDSCR_EL1.TDCC; no debug events (MDE, KDE, SS clear).
    assert_eq!(el0_access::MDSCR_EL1, 1 << 12);
    // CPACR_EL1.TTA in both FP/SIMD states, which differ only in FPEN.
    for v in [el0_access::CPACR_FP_EL0_TRAP, el0_access::CPACR_FP_NONE] {
        assert_ne!(v & (1 << 28), 0, "{v:#x}");
        // SVE and SME stay trapped (ZEN, SMEN clear).
        assert_eq!(v & (3 << 16 | 3 << 24), 0, "{v:#x}");
    }
    assert_eq!((el0_access::CPACR_FP_EL0_TRAP >> 20) & 3, 1);
    assert_eq!((el0_access::CPACR_FP_NONE >> 20) & 3, 3);
}

#[test]
fn pmuserenr_is_written_only_with_a_pmu() {
    // PMUVer: neither absent nor IMPLEMENTATION DEFINED.
    assert!(!el0_access::has_pmu(0));
    assert!(!el0_access::has_pmu(0xf << 8));
    assert!(el0_access::has_pmu(4 << 8));
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

// ---- device tree (audit F5) -----------------------------------------------------

/// A flattened device tree under construction.
#[derive(Default)]
struct Dtb {
    structs: Vec<u8>,
    strings: Vec<u8>,
}

impl Dtb {
    fn word(&mut self, w: u32) {
        self.structs.extend_from_slice(&w.to_be_bytes());
    }
    fn pad(&mut self) {
        while self.structs.len() % 4 != 0 {
            self.structs.push(0);
        }
    }
    fn begin(&mut self, name: &str) {
        self.word(1);
        self.structs.extend_from_slice(name.as_bytes());
        self.structs.push(0);
        self.pad();
    }
    fn end(&mut self) {
        self.word(2);
    }
    fn prop(&mut self, name: &str, val: &[u8]) {
        let off = self.strings.len() as u32;
        self.strings.extend_from_slice(name.as_bytes());
        self.strings.push(0);
        self.word(3);
        self.word(val.len() as u32);
        self.word(off);
        self.structs.extend_from_slice(val);
        self.pad();
    }
    fn prop_u32(&mut self, name: &str, v: u32) {
        self.prop(name, &v.to_be_bytes());
    }
    fn prop_str(&mut self, name: &str, v: &str) {
        let mut b = v.as_bytes().to_vec();
        b.push(0);
        self.prop(name, &b);
    }
    /// The blob: header, an empty reservation map, then the blocks.
    fn blob(mut self) -> Vec<u8> {
        self.word(9);
        let rsv = 40u32;
        let st = rsv + 16;
        let strs = st + self.structs.len() as u32;
        let total = strs + self.strings.len() as u32;
        let mut b = Vec::new();
        for w in [0xd00d_feed, total, st, strs, rsv, 17, 16, 0, self.strings.len() as u32, self.structs.len() as u32] {
            b.extend_from_slice(&u32::to_be_bytes(w));
        }
        b.extend_from_slice(&[0; 16]);
        b.extend_from_slice(&self.structs);
        b.extend_from_slice(&self.strings);
        b
    }
}

/// `reg` of (address, size) pairs, two cells each.
fn reg2(regs: &[(u64, u64)]) -> Vec<u8> {
    regs.iter().flat_map(|&(a, s)| [a.to_be_bytes(), s.to_be_bytes()].concat()).collect()
}

/// The hardware a device tree with one interrupt controller node
/// (`compat`, `reg`, `#redistributor-regions` if given) describes.
fn dt_hw(compat: &str, regs: &[(u64, u64)], redist: Option<u32>) -> hw::Hw {
    let mut d = Dtb::default();
    d.begin("");
    d.prop_u32("#address-cells", 2);
    d.prop_u32("#size-cells", 2);
    d.begin("intc@8000000");
    d.prop_str("compatible", compat);
    d.prop_u32("#interrupt-cells", 3);
    // reg before #redistributor-regions: a node's facts are used at its end.
    d.prop("reg", &reg2(regs));
    if let Some(n) = redist {
        d.prop_u32("#redistributor-regions", n);
    }
    // A child (an ITS) with its own reg, which is not the GIC's.
    d.begin("msi-controller@8080000");
    d.prop_str("compatible", "arm,gic-v3-its");
    d.prop("reg", &reg2(&[(0x808_0000, 0x2_0000)]));
    d.end();
    d.end();
    d.end();
    let blob = d.blob();
    let mut mem = vec![0u8; BASE as usize + blob.len()];
    mem[BASE as usize..].copy_from_slice(&blob);
    layout::MEMORY.set((mem.as_ptr() as u64, mem.len() as u64));
    let h = hw::discover(0, BASE).expect("device tree");
    layout::MEMORY.set((0, 0));
    h
}

const GICD: (u64, u64) = (0x800_0000, 0x1_0000);

fn gicr_regions(n: u64) -> Vec<(u64, u64)> {
    (0..n).map(|i| (0x1_0000_0000 + i * 0x100_0000, 0x40_0000)).collect()
}

#[test]
fn every_redistributor_region_of_the_device_tree_is_kept() {
    // Five regions (six reg entries), then GICC, GICH and GICV.
    let regions = gicr_regions(5);
    let tail = [(0x2c00_0000, 0x2_0000), (0x2c01_0000, 0x2_0000), (0x2c02_0000, 0x2_0000)];
    for with_tail in [false, true] {
        let mut regs = vec![GICD];
        regs.extend_from_slice(&regions);
        if with_tail {
            regs.extend_from_slice(&tail);
        }
        let h = dt_hw("arm,gic-v3", &regs, Some(5));
        assert_eq!(h.gic_version, 3);
        assert_eq!(h.gicd, GICD.0);
        assert!(!h.gicr_lost, "tail {with_tail}");
        assert_eq!(&h.gicr[..h.n_gicr], &regions[..], "tail {with_tail}");
    }
}

#[test]
fn more_redistributor_regions_than_recorded_are_a_boot_failure() {
    let n = hw::MAX_GICR as u64 + 1;
    let mut regs = vec![GICD];
    regs.extend(gicr_regions(n));
    let h = dt_hw("arm,gic-v3", &regs, Some(n as u32));
    assert!(h.gicr_lost);
    // So is a count the reg property does not hold, or none at all.
    let mut regs = vec![GICD];
    regs.extend(gicr_regions(2));
    assert!(dt_hw("arm,gic-v3", &regs, Some(3)).gicr_lost);
    assert!(dt_hw("arm,gic-v3", &regs, Some(0)).gicr_lost);
    // Exactly as many as recorded is fine.
    let mut regs = vec![GICD];
    regs.extend(gicr_regions(hw::MAX_GICR as u64));
    let h = dt_hw("arm,gic-v3", &regs, Some(hw::MAX_GICR as u32));
    assert!(!h.gicr_lost);
    assert_eq!(h.n_gicr, hw::MAX_GICR);
}

#[test]
fn gicc_gich_and_gicv_are_not_redistributor_regions() {
    // One region (the default, or said), then 128 KiB GICC, GICH and
    // GICV (64 KiB-spaced aliases): none of them is a redistributor.
    let regs = [GICD, (0x80a_0000, 0xf6_0000), (0x2c00_0000, 0x2_0000), (0x2c01_0000, 0x2_0000), (0x2c02_0000, 0x2_0000)];
    for redist in [None, Some(1)] {
        let h = dt_hw("arm,gic-v3", &regs, redist);
        assert!(!h.gicr_lost);
        assert_eq!(&h.gicr[..h.n_gicr], &[(0x80a_0000, 0xf6_0000)], "{redist:?}");
    }
}

#[test]
fn a_gicv2_cpu_interface_is_kept_whole() {
    let h = dt_hw("arm,gic-400", &[(0x2c00_1000, 0x1000), (0x2c02_0000, 0x2_0000)], None);
    assert_eq!(h.gic_version, 2);
    assert_eq!((h.gicc, h.gicc_len), (0x2c02_0000, 0x2_0000));
}

#[test]
fn kernel_device_ranges_are_kept_in_whole_pages() {
    assert_eq!(bootmem::pages_covering(0x800_0000, 0x801_0000), (0x800_0000, 0x801_0000));
    assert_eq!(bootmem::pages_covering(0x800_0800, 0x801_0800), (0x800_0000, 0x801_1000));
    assert_eq!(bootmem::pages_covering(0x800_0fff, 0x800_1001), (0x800_0000, 0x800_2000));
    assert_eq!(bootmem::pages_covering(u64::MAX - 0x10, u64::MAX), (u64::MAX & !0xfff, u64::MAX & !0xfff));
    // Through the device list: no page of an unaligned GIC is left over.
    let mut dev = bootmem::Ranges::new();
    dev.add(0, 0x1000_0000);
    let (s, e) = bootmem::pages_covering(0x800_0800, 0x800_0800 + 0x1_0000);
    dev.remove(s, e);
    assert_eq!(dev.n, 2);
    assert_eq!((dev.r[0].end, dev.r[1].start), (0x800_0000, 0x801_1000));
}

#[test]
fn an_unbounded_redistributor_range_must_end_inside_the_mapping() {
    let b = 0x800_0000;
    // No bound from the tables, mapped for two cores: two redistributors
    // and the last frame, or more redistributors past the mapping.
    let closed = [(b, 0), (b + 0x2_0000, LAST)];
    assert_eq!(gic_layout::reserve(b, 0, 0x8_0000, frames(&closed)), Some(0x8_0000));
    let open = [(b, 0), (b + 0x2_0000, 0), (b + 0x4_0000, 0), (b + 0x6_0000, 0)];
    assert_eq!(gic_layout::reserve(b, 0, 0x8_0000, frames(&open)), None);
    // GICv4: the last frame's VLPI frames may pass the mapping.
    let v4 = [(b, VLPIS), (b + 0x4_0000, VLPIS | LAST)];
    assert_eq!(gic_layout::reserve(b, 0, 0x6_0000, frames(&v4)), Some(0x8_0000));
    // A bound from the tables: all of it, last frame seen or not.
    assert_eq!(gic_layout::reserve(b, 0x8_0000, 0x8_0000, frames(&open)), Some(0x8_0000));
    assert_eq!(gic_layout::reserve(b, 0x2_0000, 0x2_0000, frames(&[(b, VLPIS)])), Some(0x4_0000));
}

/// The hardware a device tree describes whose root has `root` cells and
/// whose GICv3 sits under /soc with `soc` cells and a raw `reg`.
fn dt_soc(root: (u32, u32), soc: (u32, u32), reg: &[u8], redist: u32) -> Option<hw::Hw> {
    let mut d = Dtb::default();
    d.begin("");
    d.prop_u32("#address-cells", root.0);
    d.prop_u32("#size-cells", root.1);
    d.begin("cpus");
    d.prop_u32("#address-cells", 1);
    d.prop_u32("#size-cells", 0);
    d.begin("cpu@0");
    d.prop("reg", &0u32.to_be_bytes());
    d.end();
    d.end();
    d.begin("soc");
    d.prop_u32("#address-cells", soc.0);
    d.prop_u32("#size-cells", soc.1);
    // The root's cells for /soc's own reg.
    d.prop("reg", &[0u8; 12]);
    d.begin("interrupt-controller@8000000");
    d.prop_str("compatible", "arm,gic-v3");
    // The GIC's cells are its children's (an ITS), not its own reg's.
    d.prop_u32("#address-cells", 1);
    d.prop_u32("#size-cells", 1);
    d.prop("reg", reg);
    d.prop_u32("#redistributor-regions", redist);
    d.end();
    d.end();
    d.end();
    let blob = d.blob();
    let mut mem = vec![0u8; BASE as usize + blob.len()];
    mem[BASE as usize..].copy_from_slice(&blob);
    layout::MEMORY.set((mem.as_ptr() as u64, mem.len() as u64));
    let h = hw::discover(0, BASE);
    layout::MEMORY.set((0, 0));
    h
}

/// Proposal 5: reg is read in its parent's cells, not the root's.
#[test]
fn reg_uses_the_parents_cells() {
    let regions = gicr_regions(3);
    let mut regs = vec![GICD];
    regs.extend_from_slice(&regions);
    let h = dt_soc((2, 1), (2, 2), &reg2(&regs), 3).expect("device tree");
    assert_eq!(h.gicd, GICD.0);
    assert!(!h.gicr_lost);
    assert_eq!(&h.gicr[..h.n_gicr], &regions[..]);
    assert_eq!(&h.cpus[..h.n_cpus], &[0]);
    // One address cell and one size cell under /soc.
    let one: Vec<u8> = [(0x800_0000u32, 0x1_0000u32), (0x80a_0000, 0xf6_0000)]
        .iter()
        .flat_map(|&(a, s)| [a.to_be_bytes(), s.to_be_bytes()].concat())
        .collect();
    let h = dt_soc((2, 2), (1, 1), &one, 1).expect("device tree");
    assert_eq!(h.gicd, 0x800_0000);
    assert!(!h.gicr_lost);
    assert_eq!(&h.gicr[..h.n_gicr], &[(0x80a_0000, 0xf6_0000)]);
}

#[test]
fn a_gic_reg_the_kernel_cannot_read_whole_is_never_used() {
    let mut regs = vec![GICD];
    regs.extend(gicr_regions(2));
    // Cells the kernel does not handle: no GIC found, so no boot.
    assert!(dt_soc((2, 2), (3, 2), &reg2(&regs), 2).is_none());
    assert!(dt_soc((2, 2), (2, 0), &reg2(&regs), 2).is_none());
    // A reg that is not whole entries is not read at all: no GIC either.
    let mut bytes = reg2(&regs);
    bytes.extend_from_slice(&[0; 8]);
    assert!(dt_soc((2, 2), (2, 2), &bytes, 2).is_none());
    assert!(dt_soc((2, 2), (2, 2), &reg2(&regs), 2).is_some());
}
