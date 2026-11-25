//! Physical memory at boot: RAM and device ranges from the loader's memory
//! map. No kernel dependencies but `Region` and the boot record's types,
//! so the host tests include this file too (xtask/tests/aarch64_boot.rs).
use fl4_bootinfo::{mem, MemRegion};
use fl4_core::boot::Region;

const PAGE: u64 = 4096;

/// Ranges a list holds: every entry of the loader's memory map
/// (`fl4_bootinfo::MAX_MMAP`), and room for the splits the kernel's own
/// memory and devices make in them.
pub const MAX_RANGES: usize = 272;

/// A sorted list of disjoint half-open physical ranges.
#[derive(Clone, Copy)]
pub struct Ranges {
    pub r: [Region; MAX_RANGES],
    pub n: usize,
    /// A range did not fit and is missing. A list the kernel decides
    /// RAM from must then not be used: what it misses would count as
    /// device memory.
    pub lost: bool,
}

impl Ranges {
    pub const fn new() -> Ranges {
        Ranges { r: [Region::EMPTY; MAX_RANGES], n: 0, lost: false }
    }

    pub fn add(&mut self, start: u64, end: u64) {
        if start >= end {
            return;
        }
        if self.n == self.r.len() {
            self.lost = true;
            return;
        }
        let mut i = self.n;
        while i > 0 && self.r[i - 1].start > start {
            self.r[i] = self.r[i - 1];
            i -= 1;
        }
        self.r[i] = Region { start, end };
        self.n += 1;
        let mut out = 0;
        for j in 0..self.n {
            let cur = self.r[j];
            if out > 0 && cur.start <= self.r[out - 1].end {
                if cur.end > self.r[out - 1].end {
                    self.r[out - 1].end = cur.end;
                }
            } else {
                self.r[out] = cur;
                out += 1;
            }
        }
        self.n = out;
    }

    pub fn remove(&mut self, start: u64, end: u64) {
        let mut res = Ranges::new();
        res.lost = self.lost;
        for j in 0..self.n {
            let c = self.r[j];
            if c.end <= start || c.start >= end {
                res.add(c.start, c.end);
            } else {
                if c.start < start {
                    res.add(c.start, start);
                }
                if c.end > end {
                    res.add(end, c.end);
                }
            }
        }
        *self = res;
    }

    /// Take `len` bytes, page aligned, from the top of the highest range
    /// that has them.
    pub fn take(&mut self, len: u64) -> Option<u64> {
        let len = len.checked_add(PAGE - 1)? & !(PAGE - 1);
        for j in (0..self.n).rev() {
            let c = self.r[j];
            if c.end - c.start >= len {
                let start = c.end - len;
                self.remove(start, c.end);
                return Some(start);
            }
        }
        None
    }
}

/// What the memory map says, in whole pages below `pa_top` (what the
/// processor addresses).
pub struct MemLists {
    /// Write-back RAM, free or the firmware's, in the window (below
    /// `window_top`): what the window maps.
    pub ram: Ranges,
    /// Free write-back RAM in the window: what boot hands out as memory.
    pub usable: Ranges,
    /// The part of `usable` the loader zeroed.
    pub zeroed: Ranges,
    /// Free write-back RAM anywhere below `pa_top`, in the window or not:
    /// never device memory, though what is past the window is not handed
    /// out at all.
    pub all_usable: Ranges,
}

pub fn classify(mmap: &[MemRegion], window_top: u64, pa_top: u64) -> MemLists {
    let mut l = MemLists { ram: Ranges::new(), usable: Ranges::new(), zeroed: Ranges::new(), all_usable: Ranges::new() };
    for e in mmap {
        let wb = e.cacheable & 1 != 0;
        if wb && e.kind == mem::FREE {
            if let Some((start, end)) = entry_pages(e.base, e.len, pa_top) {
                l.all_usable.add(start, end);
            }
        }
        let Some((start, end)) = entry_pages(e.base, e.len, window_top.min(pa_top)) else { continue };
        if wb && (e.kind == mem::FREE || e.kind == mem::FIRMWARE) {
            l.ram.add(start, end);
        }
        if wb && e.kind == mem::FREE {
            l.usable.add(start, end);
            if e.cacheable & mem::ZEROED != 0 {
                l.zeroed.add(start, end);
            }
        }
    }
    l
}

/// The whole pages of a memory map entry of `len` bytes at `base`, below
/// `top`: none for one that wraps past 2^64.
pub fn entry_pages(base: u64, len: u64, top: u64) -> Option<(u64, u64)> {
    let start = base.checked_add(PAGE - 1)? & !(PAGE - 1);
    let end = base.checked_add(len)? & !(PAGE - 1);
    let end = end.min(top);
    (start < end).then_some((start, end))
}

/// The whole pages that hold [start, end): what boot keeps of a kernel
/// device range from user space's device memory, which comes in pages.
/// An end in the last page of the address space saturates.
pub fn pages_covering(start: u64, end: u64) -> (u64, u64) {
    (start & !(PAGE - 1), end.saturating_add(PAGE - 1) & !(PAGE - 1))
}

/// The pages a device mapping of `len` bytes at `pa` takes, as (first
/// page, bytes): none unless all of it lies below `pa_top` (what the
/// processor can address, which a descriptor's output address must not
/// pass), or for nothing at all.
pub fn device_pages(pa: u64, len: u64, pa_top: u64) -> Option<(u64, u64)> {
    let end = pa.checked_add(len)?;
    if len == 0 || end > pa_top {
        return None;
    }
    let base = pa & !(PAGE - 1);
    let size = end.checked_add(PAGE - 1)? & !(PAGE - 1);
    Some((base, size - base))
}

/// Where the next device mapping of `size` bytes goes in the kernel's
/// device area, which ends at `top`: `next` (the end of the previous
/// mapping) rounded up to 64 KiB. Returns that address and the new end;
/// none for a mapping past `top`, or whose address or end would wrap past
/// 2^64 (a firmware range of 512 GiB or more from the device area's base
/// did, and mapped over the kernel image above `top`).
pub fn device_va(next: u64, size: u64, top: u64) -> Option<(u64, u64)> {
    let va = next.checked_add(0xffff)? & !0xffff;
    let end = va.checked_add(size)?;
    (end <= top).then_some((va, end))
}
