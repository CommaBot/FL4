//! The kernel's root-task ELF checks and loader on host-allocated images.
//! Only the physical-to-virtual address translation is replaced.
extern crate self as fl4_core;

pub mod layout {
    pub fn pptr(p: u64) -> u64 {
        p
    }
}

#[path = "../../crates/fl4-kernel/src/elf.rs"]
mod elf;

const LIMIT: u64 = 0x0000_8000_0000_0000 - 3 * 4096;

/// A loadable segment: (offset, vaddr, filesz, memsz).
type Seg = (u64, u64, u64, u64);

/// `p_flags`: executable, and readable and executable (ordinary code).
const PF_X: u32 = 1;
const PF_RX: u32 = 4 | PF_X;

/// An x86_64 ELF image: header, program headers (each segment executable)
/// right after it, then `body`.
fn image(entry: u64, segs: &[Seg], body: &[u8]) -> Vec<u8> {
    let segs: Vec<_> = segs.iter().map(|&s| (s, PF_RX)).collect();
    image_flags(entry, &segs, body)
}

/// `image` with each segment's `p_flags`.
fn image_flags(entry: u64, segs: &[(Seg, u32)], body: &[u8]) -> Vec<u8> {
    let mut e = vec![0u8; 64];
    e[..4].copy_from_slice(b"\x7fELF");
    e[4] = 2;
    e[5] = 1;
    e[18..20].copy_from_slice(&0x3eu16.to_le_bytes());
    e[24..32].copy_from_slice(&entry.to_le_bytes());
    e[32..40].copy_from_slice(&64u64.to_le_bytes());
    e[54..56].copy_from_slice(&56u16.to_le_bytes());
    e[56..58].copy_from_slice(&(segs.len() as u16).to_le_bytes());
    for &((off, vaddr, filesz, memsz), flags) in segs {
        let mut p = [0u8; 56];
        p[..4].copy_from_slice(&1u32.to_le_bytes());
        p[4..8].copy_from_slice(&flags.to_le_bytes());
        p[8..16].copy_from_slice(&off.to_le_bytes());
        p[16..24].copy_from_slice(&vaddr.to_le_bytes());
        p[32..40].copy_from_slice(&filesz.to_le_bytes());
        p[40..48].copy_from_slice(&memsz.to_le_bytes());
        e.extend_from_slice(&p);
    }
    e.extend_from_slice(body);
    e
}

fn check(img: &[u8]) -> Option<elf::Layout> {
    elf::check(img.as_ptr() as u64, img.len() as u64, LIMIT)
}

const BODY: u64 = 64 + 56;

#[test]
fn loads_segments_and_zeroes_the_rest() {
    let img = image(0x40_1000, &[(BODY, 0x40_1000, 4, 0x1800)], &[1, 2, 3, 4]);
    let l = check(&img).expect("valid image");
    assert_eq!(l, elf::Layout { v_start: 0x40_1000, v_end: 0x40_3000, entry: 0x40_1000 });
    let mut dest = vec![0xffu8; 0x2000 + 4096];
    let base = (dest.as_mut_ptr() as u64 + 4095) & !4095;
    elf::load(img.as_ptr() as u64, &l, base);
    let off = (base - dest.as_ptr() as u64) as usize;
    assert_eq!(&dest[off..off + 4], &[1, 2, 3, 4]);
    assert!(dest[off + 4..off + 0x2000].iter().all(|&b| b == 0));
}

#[test]
fn file_bytes_beyond_memory_bytes_are_refused() {
    // filesz > memsz: the copy would run past the zeroed image.
    let img = image(0x40_1000, &[(BODY, 0x40_1000, 0x2000, 0x10)], &[0; 0x2000]);
    assert!(check(&img).is_none());
}

#[test]
fn headers_and_segments_must_lie_in_the_module() {
    let good = image(0x40_1000, &[(BODY, 0x40_1000, 4, 4)], &[1, 2, 3, 4]);
    assert!(check(&good).is_some());
    // Truncated: header only, then program headers cut short.
    assert!(check(&good[..63]).is_none());
    assert!(check(&good[..100]).is_none());
    // Segment file bytes past the module's end, and an offset that wraps.
    assert!(check(&image(0x40_1000, &[(BODY, 0x40_1000, 5, 5)], &[1, 2, 3, 4])).is_none());
    assert!(check(&image(0x40_1000, &[(u64::MAX - 1, 0x40_1000, 4, 4)], &[1, 2, 3, 4])).is_none());
    // Program headers too small for their fields.
    let mut small = good.clone();
    small[54..56].copy_from_slice(&32u16.to_le_bytes());
    assert!(check(&small).is_none());
    // A program header table that runs past the module.
    let mut many = good.clone();
    many[56..58].copy_from_slice(&0xffffu16.to_le_bytes());
    assert!(check(&many).is_none());
}

#[test]
fn segments_must_stay_in_user_space() {
    // vaddr + memsz wraps.
    assert!(check(&image(0x40_1000, &[(BODY, u64::MAX - 0xfff, 0, 0x2000), (BODY, 0x40_1000, 0, 4)], &[])).is_none());
    // In the kernel half: the boot code would write PML4 entries 256..511.
    assert!(check(&image(0xffff_ff80_0000_0000, &[(BODY, 0xffff_ff80_0000_0000, 0, 4096)], &[])).is_none());
    // Up to the limit (room for the boot frames after it), not past it.
    assert!(check(&image(LIMIT - 4096, &[(BODY, LIMIT - 4096, 0, 4096)], &[])).is_some());
    assert!(check(&image(LIMIT - 4096, &[(BODY, LIMIT - 4096, 0, 4097)], &[])).is_none());
}

#[test]
fn the_entry_point_lies_in_the_image() {
    assert!(check(&image(0x40_0000, &[(BODY, 0x40_1000, 0, 4096)], &[])).is_none());
    assert!(check(&image(0x40_2000, &[(BODY, 0x40_1000, 0, 4096)], &[])).is_none());
    assert!(check(&image(0x40_1fff, &[(BODY, 0x40_1000, 0, 4096)], &[])).is_some());
}

#[test]
fn no_loadable_bytes_no_image() {
    assert!(check(&image(0x40_1000, &[], &[])).is_none());
    assert!(check(&image(0x40_1000, &[(BODY, 0x40_1000, 0, 0)], &[])).is_none());
    let mut not64 = image(0x40_1000, &[(BODY, 0x40_1000, 0, 4096)], &[]);
    not64[4] = 1;
    assert!(check(&not64).is_none());
}

/// Audit r13 T2-03: the entry point lies inside an executable segment.
/// Before, any address between the lowest and the highest segment (page
/// rounded) was taken: a gap between segments, or a data segment.
#[test]
fn the_entry_point_lies_in_an_executable_segment() {
    let text = (BODY, 0x40_1000, 0, 0x1000);
    let data = (BODY, 0x40_4000, 0, 0x1000);
    let both = |entry| check(&image_flags(entry, &[(text, PF_RX), (data, 4 | 2)], &[]));
    assert_eq!(both(0x40_1000).map(|l| l.entry), Some(0x40_1000));
    assert_eq!(both(0x40_1fff).map(|l| l.entry), Some(0x40_1fff));
    // In the gap between the segments.
    assert!(both(0x40_2000).is_none());
    assert!(both(0x40_3fff).is_none());
    // In the data segment, which has no PF_X.
    assert!(both(0x40_4000).is_none());
    assert!(both(0x40_4fff).is_none());
    // A lone segment without PF_X.
    assert!(check(&image_flags(0x40_1000, &[(text, 4 | 2)], &[])).is_none());
    assert!(check(&image_flags(0x40_1000, &[(text, PF_X)], &[])).is_some());
    // Past a segment's memory bytes, inside its last page.
    assert!(check(&image(0x40_1800, &[(BODY, 0x40_1000, 0, 0x800)], &[])).is_none());
}
