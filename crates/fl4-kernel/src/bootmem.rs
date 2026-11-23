//! Physical memory at boot: which ranges are RAM, where the root task's
//! image goes, and what user space gets as device memory. No kernel
//! dependencies but `Region`, so xtask's host tests include this file too.
use fl4_core::boot::Region;

const PAGE: u64 = 4096;

/// A sorted list of half-open physical ranges: room for one per memory
/// map entry (`mboot::MAX_MMAP`, 256) and the splits the kernel's own
/// memory and devices make in them.
pub type Ranges = RangeList<272>;

pub struct RangeList<const N: usize> {
    pub r: [Region; N],
    pub n: usize,
    /// A range did not fit and is missing. A list the kernel decides RAM
    /// or private memory from must then not be used: what it misses would
    /// become user space's (shared) device memory.
    pub lost: bool,
}

impl<const N: usize> RangeList<N> {
    pub const fn new() -> Self {
        Self { r: [Region::EMPTY; N], n: 0, lost: false }
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
        // Merge overlapping or touching neighbours.
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
        let mut res = Self::new();
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

    /// Whether one range holds all of `[start, end)`.
    pub fn contains(&self, start: u64, end: u64) -> bool {
        start <= end && (0..self.n).any(|j| self.r[j].start <= start && end <= self.r[j].end)
    }

    /// The lowest page-aligned address from `min` on where one range holds
    /// `size` bytes (seL4 `find_load_paddr`).
    pub fn find(&self, min: u64, size: u64) -> Option<u64> {
        self.find_below(min, size, u64::MAX)
    }

    /// As with find, with an additional exclusive upper bound on the span.
    pub fn find_below(&self, min: u64, size: u64, top: u64) -> Option<u64> {
        self.r[..self.n].iter().find_map(|r| {
            let start = r.start.max(min).checked_add(PAGE - 1)? & !(PAGE - 1);
            (start.checked_add(size)? <= r.end.min(top)).then_some(start)
        })
    }
}

/// The lowest of `limits`: where boot memory stops.
pub fn top(limits: &[u64]) -> u64 {
    limits.iter().copied().min().unwrap_or(0)
}

/// The RAM the kernel may use: the whole pages of each available (type 1)
/// memory map entry `(base, len, type)` from `low` on and below `top`. An
/// entry that starts below `low` (one that covers low memory and more)
/// counts from `low`; one that ends past 2^64 ends there.
pub fn ram(entries: impl IntoIterator<Item = (u64, u64, u32)>, low: u64, top: u64) -> Ranges {
    let mut ram = Ranges::new();
    for (base, len, ty) in entries {
        if ty != 1 {
            continue;
        }
        let Some(start) = base.max(low).checked_add(PAGE - 1) else { continue };
        let end = base.saturating_add(len) & !(PAGE - 1);
        ram.add(start & !(PAGE - 1), end.min(top));
    }
    ram
}

/// fl4-efi's memory map type for RAM a confidential guest has not yet
/// accepted (UEFI's EfiUnacceptedMemoryType). It is neither usable RAM nor
/// device memory: touching it before TDG.MEM.PAGE.ACCEPT faults.
pub const UNACCEPTED: u32 = 0x464c_3410;

/// fl4-efi's memory map type for firmware's private memory: write-back
/// `EfiReservedMemoryType`, EFI runtime services code and data, persistent
/// memory and the SEV-SNP CPUID and secrets pages. A confidential guest
/// keeps it private and out of device memory, but reads no ACPI tables from
/// it (`acpi_readable`) and puts no mailbox there (`mailbox_ok`).
pub const PRIVATE_RESERVED: u32 = 0x464c_3411;

/// The whole pages of each unaccepted memory map entry from `low` on and
/// below `top`.
pub fn unaccepted(entries: impl IntoIterator<Item = (u64, u64, u32)>, low: u64, top: u64) -> Ranges {
    let mut r = Ranges::new();
    for (base, len, ty) in entries {
        if ty != UNACCEPTED {
            continue;
        }
        let Some(start) = base.max(low).checked_add(PAGE - 1) else { continue };
        let end = base.saturating_add(len) & !(PAGE - 1);
        r.add(start & !(PAGE - 1), end.min(top));
    }
    r
}

/// Piece `index` of `ranges` when each is cut at multiples of `chunk`, so
/// that cores can take pieces by counting: None past the last.
pub fn chunk_of(ranges: &[Region], index: u64, chunk: u64) -> Option<(u64, u64)> {
    let mut left = index;
    for r in ranges {
        if r.start >= r.end {
            continue;
        }
        let first = r.start / chunk;
        let count = (r.end - 1) / chunk - first + 1;
        if left < count {
            let base = (first + left) * chunk;
            return Some((base.max(r.start), (base + chunk).min(r.end)));
        }
        left -= count;
    }
    None
}

/// How many pieces `chunk_of` cuts `ranges` into.
pub fn chunk_count(ranges: &[Region], chunk: u64) -> u64 {
    ranges.iter().filter(|r| r.start < r.end).map(|r| (r.end - 1) / chunk - r.start / chunk + 1).sum()
}

/// The type of the memory map entry holding the whole page at `addr`.
pub fn mmap_type_of(addr: u64, mmap: impl IntoIterator<Item = (u64, u64, u32)>) -> Option<u32> {
    let end = addr.checked_add(PAGE)?;
    mmap.into_iter().find(|&(base, len, _)| base <= addr && end <= base.saturating_add(len)).map(|e| e.2)
}

/// Whether a confidential guest's fl4_boot may read ACPI tables at
/// `[p, p + len)`: non-empty, not wrapping, off physical page 0 (no table
/// belongs there, and a zeroed table pointer leads there), and whole in one
/// entry of the memory map that is RAM (1), ACPI reclaim (3) or ACPI NVS
/// (4), the firmware memory fl4-efi reads tables from too (x86_mmap
/// `readable`), overlapped by no entry of another type (`held_only_by`). Never unaccepted memory, MMIO, a hole, nor firmware's
/// private memory (`PRIVATE_RESERVED`: EFI runtime services, persistent
/// memory, the SNP pages). Outside a confidential guest firmware may keep
/// its tables in reserved memory (SeaBIOS), and the kernel window alone
/// bounds the reads.
pub fn acpi_readable(p: u64, len: u64, mmap: impl IntoIterator<Item = (u64, u64, u32)>) -> bool {
    let Some(end) = p.checked_add(len) else { return false };
    len != 0 && p >= PAGE && held_only_by(p, end, mmap, |ty| matches!(ty, 1 | 3 | 4))
}

/// Whether `[p, end)` (non-empty) lies whole in an entry of `mmap` whose
/// type is `ok`, and every non-empty entry it shares a byte with is such
/// an entry holding it whole. fl4-efi hands on no overlapping entries
/// (x86_mmap `validate_map`), but another loader might: then a type that
/// must not be read or written (private, unaccepted, MMIO) overrides
/// whatever an overlapping entry says.
fn held_only_by(p: u64, end: u64, mmap: impl IntoIterator<Item = (u64, u64, u32)>, ok: impl Fn(u32) -> bool) -> bool {
    let mut held = false;
    for (base, n, ty) in mmap {
        let e = base.saturating_add(n);
        if n == 0 || e <= p || end <= base {
            continue;
        }
        if !ok(ty) || p < base || e < end {
            return false;
        }
        held = true;
    }
    held
}

/// Whether the AP wakeup mailbox page the MADT names is firmware's: inside
/// the window, whole in one ACPI NVS (4) entry of the memory map, as ACPI
/// (Multiprocessor Wakeup Structure) and TDVF have it. The VMM writes the
/// MADT, and the kernel will write to this address and wait on it, so it
/// must not be RAM or the kernel's own, ACPI reclaim memory (3), nor
/// reserved memory of any other kind (2: memory-mapped I/O, uncached or
/// unusable memory, which may be the VMM's shared memory; `PRIVATE_RESERVED`:
/// firmware's private memory, which is where fl4-efi puts EFI runtime
/// services and persistent memory). The loader also checks the EFI type
/// itself (`EfiACPIMemoryNVS`, mboot `tdx_mailbox`). No other entry may
/// overlap the page (`held_only_by`). It is not RAM to the kernel (`ram`),
/// and fl4_boot keeps the page out of device memory.
pub fn mailbox_ok(mailbox: u64, window_top: u64, mmap: impl IntoIterator<Item = (u64, u64, u32)>) -> bool {
    let Some(end) = mailbox.checked_add(PAGE) else { return false };
    if mailbox == 0 || mailbox % PAGE != 0 || end > window_top {
        return false;
    }
    held_only_by(mailbox, end, mmap, |ty| ty == 4)
}

/// What user space gets as device memory: everything below `top` that is
/// neither RAM nor in one of the `reserved` ranges (the kernel's own image
/// and boot modules, the local APIC, the IOAPICs), each widened to whole
/// pages.
pub fn device(ram: &Ranges, top: u64, reserved: impl IntoIterator<Item = (u64, u64)>) -> Ranges {
    let mut dev = Ranges::new();
    dev.add(0, top);
    for i in 0..ram.n {
        dev.remove(ram.r[i].start, ram.r[i].end);
    }
    for (start, end) in reserved {
        dev.remove(start & !(PAGE - 1), end.saturating_add(PAGE - 1) & !(PAGE - 1));
    }
    dev
}

/// Partition each device range at firmware RAM boundaries. Both inputs are
/// ordered and coalesced. Each emitted range has a single visibility state.
pub fn device_regions(dev: &[Region], firmware: &[Region], mut emit: impl FnMut(Region, bool)) {
    for r in dev {
        let mut start = r.start;
        for f in firmware {
            let lo = start.max(f.start);
            let hi = r.end.min(f.end);
            if lo >= hi { continue; }
            if start < lo { emit(Region { start, end: lo }, false); }
            emit(Region { start: lo, end: hi }, true);
            start = hi;
        }
        if start < r.end { emit(Region { start, end: r.end }, false); }
    }
}
