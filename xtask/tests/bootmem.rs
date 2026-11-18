//! The kernel's boot-time RAM and device memory carving (fl4-kernel
//! bootmem.rs), with fl4-core's `Region` replaced by an identical type.
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

#[path = "../../crates/fl4-kernel/src/bootmem.rs"]
mod bootmem;

use bootmem::Ranges;
use boot::Region;

const MIB: u64 = 1 << 20;
const TOP: u64 = 1 << 47;
const KERNEL: u64 = MIB;

fn list(r: &Ranges) -> Vec<(u64, u64)> {
    r.r[..r.n].iter().map(|x| (x.start, x.end)).collect()
}

fn overlaps(r: &Ranges, start: u64, end: u64) -> bool {
    r.r[..r.n].iter().any(|x: &Region| x.start < end && start < x.end)
}

#[test]
fn ram_that_starts_in_low_memory_counts_from_1_mib() {
    // One available entry from 0 used to be dropped whole.
    let ram = bootmem::ram([(0, 0x8000_0000, 1)], MIB, 1 << 40);
    assert_eq!(list(&ram), [(MIB, 0x8000_0000)]);
}

#[test]
fn ram_takes_whole_pages_below_the_top_and_never_wraps() {
    let ram = bootmem::ram(
        [(0x20_0001, 0x2000, 1), (0x40_0000, 0x10_0000, 2), (u64::MAX - 0x800, 0x1000, 1), (0x1_0000_0000, u64::MAX, 1)],
        MIB,
        0x2_0000_0000,
    );
    assert_eq!(list(&ram), [(0x20_1000, 0x20_2000), (0x1_0000_0000, 0x2_0000_0000)]);
}

#[test]
fn the_kernel_and_root_task_are_never_device_memory() {
    // The loader reports its own allocations (kernel, modules) as reserved
    // (UEFI GRUB), so the RAM list misses them.
    let image_end = 0x80_0000;
    let ram = bootmem::ram([(image_end, 0x1000_0000, 1)], MIB, 1 << 40);
    let dev = bootmem::device(&ram, TOP, [(KERNEL, image_end), (0xfee0_0000, 0xfee0_1000)]);
    assert!(!overlaps(&dev, KERNEL, image_end));
    assert!(!overlaps(&dev, image_end, image_end + 0x1000_0000));
    assert!(!overlaps(&dev, 0xfee0_0000, 0xfee0_1000));
    // Low memory and everything else stays device memory.
    assert!(overlaps(&dev, 0, KERNEL));
    assert!(overlaps(&dev, 0xfec0_0000, 0xfec0_1000));
}

#[test]
fn reserved_ranges_widen_to_whole_pages() {
    // An IOAPIC whose registers are not page aligned, or cross a page.
    let ram = Ranges::new();
    let dev = bootmem::device(&ram, TOP, [(0xfec0_0400, 0xfec0_0420), (0xfec0_1ff0, 0xfec0_2010)]);
    assert!(!overlaps(&dev, 0xfec0_0000, 0xfec0_3000));
    assert!(overlaps(&dev, 0xfebf_f000, 0xfec0_0000));
    assert!(overlaps(&dev, 0xfec0_3000, 0xfec0_4000));
}

#[test]
fn the_root_task_goes_to_ram_that_holds_it() {
    let mut ram = Ranges::new();
    ram.add(MIB, 0x9f_0000);
    ram.add(0x100_0000, 0x200_0000);
    // Above the modules, page aligned.
    assert_eq!(ram.find(0x80_0001, 0x1000), Some(0x80_1000));
    // Not across the hole: the next region that fits.
    assert_eq!(ram.find(0x90_0000, 0x10_0000), Some(0x100_0000));
    assert_eq!(ram.find(0x90_0000, 0x200_0000), None);
    assert_eq!(ram.find(u64::MAX - 10, 1), None);
    assert!(ram.contains(0x100_0000, 0x200_0000));
    assert!(!ram.contains(0x9f_0000, 0xa0_0000));
}
