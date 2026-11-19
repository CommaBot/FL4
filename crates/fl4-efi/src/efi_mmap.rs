//! The AArch64 loader's memory map: the firmware's EFI memory descriptors
//! as fl4-bootinfo regions, adjacent ones of the same kind merged. The
//! kernel hands out what the map leaves out as device memory, so every
//! descriptor must fit, whole and without wrapping. Host-tested by
//! xtask/tests/aarch64_boot.rs.

use fl4_bootinfo::{mem, MemRegion};

const PAGE: u64 = 4096;

/// EFI_MEMORY_DESCRIPTOR up to its attributes: type at 0, physical start
/// at 8, pages at 24, attributes at 32.
pub const DESCRIPTOR_MIN: usize = 40;

/// The firmware's stride and map size describe whole descriptors (as the
/// x86_64 loader requires).
pub fn layout_ok(size: usize, stride: usize) -> bool {
    stride >= DESCRIPTOR_MIN && size % stride == 0
}

pub fn kind(ty: u32) -> u32 {
    match ty {
        // Loader code/data, boot services code/data, conventional.
        1 | 2 | 3 | 4 | 7 => mem::FREE,
        // Runtime services, ACPI reclaim and NVS, persistent memory.
        5 | 6 | 9 | 10 | 14 => mem::FIRMWARE,
        _ => mem::OTHER,
    }
}

fn rd64(b: &[u8], o: usize) -> u64 {
    u64::from_le_bytes(b[o..o + 8].try_into().unwrap())
}

/// The regions of `map` (descriptors `stride` bytes apart) into `out`;
/// how many. None for a map whose layout is not `layout_ok`, a
/// descriptor whose size or end does not fit in 64 bits, or more regions
/// than `out` holds.
pub fn regions(map: &[u8], stride: usize, out: &mut [MemRegion]) -> Option<usize> {
    if !layout_ok(map.len(), stride) {
        return None;
    }
    let mut n = 0;
    for d in map.chunks_exact(stride) {
        let ty = u32::from_le_bytes(d[0..4].try_into().unwrap());
        let base = rd64(d, 8);
        let len = rd64(d, 24).checked_mul(PAGE)?;
        base.checked_add(len)?;
        let e = MemRegion { base, len, kind: kind(ty), cacheable: (rd64(d, 32) & 8 != 0) as u32 };
        if n > 0 {
            // `p` ends where `e` starts, and `e`'s end fits.
            let p = &mut out[n - 1];
            if p.kind == e.kind && p.cacheable == e.cacheable && p.base + p.len == e.base {
                p.len += e.len;
                continue;
            }
        }
        *out.get_mut(n)? = e;
        n += 1;
    }
    Some(n)
}
