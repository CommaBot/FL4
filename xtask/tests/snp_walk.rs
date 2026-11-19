//! The SEV-SNP user #VC handler's page walk (fl4-kernel snp_walk.rs, used
//! by snp.rs `user_vc`) on host page tables. The kernel reads the tables and
//! the faulting instruction's bytes through its physical window
//! (`pptr(pa)`), which maps only [0, window_top): above it lie a hole up to
//! 510 GiB, the kernel image's alias at [510 GiB, 510 GiB + 32 MiB), and
//! from 512 GiB on `pptr` wraps into the lower half.
use std::cell::RefCell;
use std::collections::HashMap;

#[allow(dead_code)]
#[path = "../../crates/fl4-kernel/src/snp_walk.rs"]
mod snp_walk;
use snp_walk::{translate, Access};

const GIB: u64 = 1 << 30;
const USER_TOP: u64 = 0x0000_7fff_ffff_ffff;
const C_BIT: u64 = 1 << 51;
const P: u64 = 1;
const W: u64 = 2;
const U: u64 = 4;
const PS: u64 = 1 << 7;
const NX: u64 = 1 << 63;

/// Page tables in a sparse physical memory, read only inside the window.
struct Mem {
    window_top: u64,
    words: HashMap<u64, u64>,
    outside: RefCell<Vec<u64>>,
}

impl Mem {
    fn new(window_top: u64) -> Mem {
        Mem { window_top, words: HashMap::new(), outside: RefCell::new(vec![]) }
    }
    fn read(&self, pa: u64) -> u64 {
        if pa.checked_add(8).is_none_or(|e| e > self.window_top) {
            self.outside.borrow_mut().push(pa);
            return 0;
        }
        self.words.get(&pa).copied().unwrap_or(0)
    }
    /// Map the 4 KiB page at `va` to `leaf` (an entry with its flags),
    /// through tables at `tables` (PML4, PDPT, PD, PT).
    fn map(&mut self, tables: [u64; 4], va: u64, leaf: u64) {
        for (i, shift) in [39u64, 30, 21].into_iter().enumerate() {
            self.words.insert(tables[i] + ((va >> shift) & 511) * 8, tables[i + 1] | P | W | U);
        }
        self.words.insert(tables[3] + ((va >> 12) & 511) * 8, leaf);
    }
    fn walk(&self, va: u64, access: Access) -> Option<u64> {
        translate(va, access, 0x1000 | C_BIT, C_BIT, USER_TOP, self.window_top, |pa| self.read(pa))
    }
    /// What `user_vc`'s `fetch` does: the byte at the instruction's
    /// physical address, read through the window.
    fn fetch(&self, va: u64) -> Option<u64> {
        let pa = self.walk(va, Access::Execute)?;
        Some(self.read(pa & !7))
    }
}

const TABLES: [u64; 4] = [0x1000, 0x2000, 0x3000, 0x4000];
const CODE: u64 = 0x40_0000;

/// Audit r8 F3: a private, executable user frame above the window (a
/// private device untyped from an ACPI reclaim range past window_top, or
/// RAM above a 16 GiB window without 1 GiB pages) is never read through
/// `pptr`: not in the hole below 510 GiB (a kernel #PF and SNP terminate),
/// not over the kernel image's alias (the kernel's own bytes decoded as the
/// user's instruction), not past 512 GiB (a lower-half address). The walk
/// refuses it, and `user_vc` leaves the #VC to the thread's fault handler.
#[test]
fn instruction_bytes_above_the_window_are_never_read() {
    for window_top in [16 * GIB, 510 * GIB, 4 * GIB] {
        for frame in [window_top, window_top + 0x1000, 509 * GIB, 510 * GIB, 510 * GIB + 0x10_0000, 511 * GIB,
            512 * GIB, 600 * GIB, (1 << 51) - 0x1000]
        {
            if frame < window_top {
                continue;
            }
            let mut m = Mem::new(window_top);
            m.map(TABLES, CODE, frame | C_BIT | P | U);
            assert_eq!(m.walk(CODE + 5, Access::Execute), None, "frame {frame:#x}, window {window_top:#x}");
            assert_eq!(m.fetch(CODE + 5), None);
            assert!(m.outside.borrow().is_empty(), "read outside the window: {:x?}", m.outside.borrow());
        }
        // Just below the top: read as before.
        let mut m = Mem::new(window_top);
        m.map(TABLES, CODE, (window_top - 0x1000) | C_BIT | P | U);
        assert_eq!(m.walk(CODE + 5, Access::Execute), Some(window_top - 0x1000 + 5));
        assert!(m.fetch(CODE + 5).is_some());
        assert!(m.outside.borrow().is_empty());
    }
}

/// The same for a large page: a 2 MiB or 1 GiB private executable mapping
/// whose byte lies above the window.
#[test]
fn large_pages_above_the_window_are_refused() {
    let window_top = 16 * GIB;
    let mut m = Mem::new(window_top);
    m.words.insert(TABLES[0], TABLES[1] | P | W | U);
    m.words.insert(TABLES[1], (20 * GIB) | C_BIT | P | U | PS);
    assert_eq!(m.walk(0x1234, Access::Execute), None);
    m.words.insert(TABLES[1], TABLES[2] | P | W | U);
    m.words.insert(TABLES[2], (17 * GIB) | C_BIT | P | U | PS);
    assert_eq!(m.walk(0x1234, Access::Execute), None);
    m.words.insert(TABLES[2], (15 * GIB) | C_BIT | P | U | PS);
    assert_eq!(m.walk(0x1234, Access::Execute), Some(15 * GIB + 0x1234));
    assert!(m.outside.borrow().is_empty());
}

/// A table pointer above the window is not followed (the kernel allocates
/// tables from RAM inside it, so this only guards the invariant).
#[test]
fn tables_above_the_window_are_not_read() {
    let window_top = 16 * GIB;
    for table in [window_top, 510 * GIB, 512 * GIB] {
        let mut m = Mem::new(window_top);
        m.map([TABLES[0], table & !0xfff, TABLES[2], TABLES[3]], CODE, 0x5000 | C_BIT | P | U);
        assert_eq!(m.walk(CODE, Access::Execute), None, "table {table:#x}");
        assert!(m.outside.borrow().is_empty(), "read outside the window: {:x?}", m.outside.borrow());
    }
    // The root itself.
    let m = Mem::new(window_top);
    assert_eq!(translate(CODE, Access::Execute, (20 * GIB) | C_BIT, C_BIT, USER_TOP, window_top, |pa| m.read(pa)), None);
    assert!(m.outside.borrow().is_empty());
}

/// MMIO goes to the hypervisor by physical address (GHCB), never through
/// the window: a shared device page above it (a 64-bit BAR past 510 GiB)
/// still translates for a read or a write, and a private one does not.
#[test]
fn mmio_above_the_window_still_translates() {
    let window_top = 510 * GIB;
    let bar = 600 * GIB;
    let mut m = Mem::new(window_top);
    m.map(TABLES, 0x50_0000, bar | P | W | U | NX);
    assert_eq!(m.walk(0x50_0010, Access::Read), Some(bar + 0x10));
    assert_eq!(m.walk(0x50_0010, Access::Write), Some(bar + 0x10));
    assert_eq!(m.walk(0x50_0010, Access::Execute), None);
    m.map(TABLES, 0x50_0000, bar | C_BIT | P | W | U | NX);
    assert_eq!(m.walk(0x50_0010, Access::Read), None);
    // Not writable, not user, not present.
    m.map(TABLES, 0x50_0000, bar | P | U | NX);
    assert_eq!(m.walk(0x50_0010, Access::Write), None);
    m.map(TABLES, 0x50_0000, bar | P | W | NX);
    assert_eq!(m.walk(0x50_0010, Access::Read), None);
    assert_eq!(m.walk(USER_TOP + 1, Access::Read), None);
    assert!(m.outside.borrow().is_empty());
}

/// snp.rs walks through snp_walk with the window's top, and `user_vc`
/// reads instruction bytes only at what an Execute walk returned.
#[test]
fn user_vc_uses_the_bounded_walk() {
    let snp = include_str!("../../crates/fl4-kernel/src/snp.rs");
    assert!(snp.contains("crate::snp_walk::translate("));
    assert!(snp.contains("crate::paging::window_top(),"));
    let fetch = &snp[snp.find("let fetch = |off| {").expect("fetch")..];
    let fetch = &fetch[..fetch.find("};").unwrap()];
    assert!(fetch.contains("translate(f.rip.checked_add(off)?, Access::Execute)?"));
    assert_eq!(snp.matches("pptr(pa)").count(), 2, "pptr(pa) used outside the walk's reader and fetch");
    let paging = include_str!("../../crates/fl4-kernel/src/paging.rs");
    assert!(paging.contains("WINDOW_TOP.store(window_top, Ordering::Release);"));
}
