//! Physical memory at boot: RAM and device ranges from the loader's memory
//! map. No kernel dependencies but `Region`, so the host tests include
//! this file too (xtask/tests/aarch64_boot.rs).
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

/// The whole pages of a memory map entry of `len` bytes at `base`, below
/// `top`: none for one that wraps past 2^64.
pub fn entry_pages(base: u64, len: u64, top: u64) -> Option<(u64, u64)> {
    let start = base.checked_add(PAGE - 1)? & !(PAGE - 1);
    let end = base.checked_add(len)? & !(PAGE - 1);
    let end = end.min(top);
    (start < end).then_some((start, end))
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
