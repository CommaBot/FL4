//! The SEV-SNP user #VC and TDX user #VE handlers' page walk (fl4-kernel
//! cvm_walk.rs, used by snp.rs `user_vc` and tdx.rs `user_ve`) on host page
//! tables. The kernel reads the tables and
//! the faulting instruction's bytes through its physical window
//! (`pptr(pa)`), which maps only [0, window_top): above it lie a hole up to
//! 510 GiB, the kernel image's alias at [510 GiB, 510 GiB + 32 MiB), and
//! from 512 GiB on `pptr` wraps into the lower half.
use std::cell::RefCell;
use std::collections::HashMap;

#[allow(dead_code)]
#[path = "../../crates/fl4-kernel/src/cvm_walk.rs"]
mod cvm_walk;
use cvm_walk::{translate, Access};

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
        translate(va, access, 0x1000 | C_BIT, C_BIT, 0, USER_TOP, self.window_top, |pa| self.read(pa))
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
    assert_eq!(translate(CODE, Access::Execute, (20 * GIB) | C_BIT, C_BIT, 0, USER_TOP, window_top, |pa| m.read(pa)), None);
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

/// snp.rs walks through cvm_walk with the window's top, and `user_vc` and
/// the MMIO emulation it shares with TDX read instruction bytes only at what
/// an Execute walk returned.
#[test]
fn user_vc_uses_the_bounded_walk() {
    let snp = include_str!("../../crates/fl4-kernel/src/snp.rs");
    let mmio = include_str!("../../crates/fl4-kernel/src/cvm_mmio.rs");
    assert!(snp.contains("crate::cvm_walk::translate("));
    assert!(snp.contains("crate::paging::window_top(),"));
    let fetch = &snp[snp.find("let fetch = |off| {").expect("fetch")..];
    let fetch = &fetch[..fetch.find("};").unwrap()];
    assert!(fetch.contains("translate(f.rip.checked_add(off)?, Access::Execute)?"));
    assert_eq!(snp.matches("pptr(pa)").count(), 2, "pptr(pa) used outside the walk's reader and fetch");
    let fetch = &mmio[mmio.find("let fetch = |off| {").expect("fetch")..];
    let fetch = &fetch[..fetch.find("};").unwrap()];
    assert!(fetch.contains("translate(rip.checked_add(off)?, Access::Execute)?"));
    assert_eq!(mmio.matches("pptr(pa)").count(), 1, "pptr(pa) used outside the fetch");
    let paging = include_str!("../../crates/fl4-kernel/src/paging.rs");
    assert!(paging.contains("WINDOW_TOP.store(window_top, Ordering::Release);"));
}

// Intel TDX: the shared bit (S-bit) marks shared leaves, so private is the
// absence of a bit, and no bit may appear on a table pointer.
const S_BIT_48: u64 = 1 << 47;
const S_BIT_52: u64 = 1 << 51;

fn td_walk(m: &Mem, s_bit: u64, va: u64, access: Access) -> Option<u64> {
    translate(va, access, 0x1000, 0, s_bit, USER_TOP, m.window_top, |pa| m.read(pa))
}

/// An instruction fetch needs a private leaf and MMIO a shared one, for
/// both TDX address widths, and neither result carries the S-bit.
#[test]
fn tdx_fetches_need_private_leaves_and_mmio_needs_shared_ones() {
    for s_bit in [S_BIT_48, S_BIT_52] {
        let frame = 0x20_0000;
        let mut m = Mem::new(16 * GIB);
        m.map(TABLES, CODE, frame | P | U);
        assert_eq!(td_walk(&m, s_bit, CODE + 5, Access::Execute), Some(frame + 5));
        assert_eq!(td_walk(&m, s_bit, CODE + 5, Access::Read), None, "MMIO to a private page");
        m.map(TABLES, CODE, frame | s_bit | P | W | U | NX);
        assert_eq!(td_walk(&m, s_bit, CODE + 5, Access::Read), Some(frame + 5));
        assert_eq!(td_walk(&m, s_bit, CODE + 5, Access::Write), Some(frame + 5));
        m.map(TABLES, CODE, frame | s_bit | P | U);
        assert_eq!(td_walk(&m, s_bit, CODE, Access::Execute), None, "fetch from a shared page");
        assert_eq!(td_walk(&m, s_bit, CODE, Access::Write), None, "read-only");
        assert!(m.outside.borrow().is_empty());
    }
}

/// Large leaves follow the same rule, and their offset survives.
#[test]
fn tdx_large_leaves_keep_the_visibility_rule() {
    let mut m = Mem::new(16 * GIB);
    m.words.insert(TABLES[0], TABLES[1] | P | W | U);
    m.words.insert(TABLES[1], TABLES[2] | P | W | U);
    m.words.insert(TABLES[2], (2 * GIB) | S_BIT_52 | P | W | U | PS | NX);
    assert_eq!(td_walk(&m, S_BIT_52, 0x1234, Access::Read), Some(2 * GIB + 0x1234));
    assert_eq!(td_walk(&m, S_BIT_52, 0x1234, Access::Execute), None);
    m.words.insert(TABLES[1], GIB | P | U | PS);
    assert_eq!(td_walk(&m, S_BIT_52, 0x1234, Access::Execute), Some(GIB + 0x1234));
    assert_eq!(td_walk(&m, S_BIT_52, 0x1234, Access::Read), None);
}

/// A table pointer with the S-bit would be a table in memory the VMM can
/// write: the walk stops there, at every level.
#[test]
fn tdx_table_pointers_with_the_shared_bit_are_not_followed() {
    for level in 0..3 {
        let mut m = Mem::new(16 * GIB);
        m.map(TABLES, CODE, 0x20_0000 | P | U);
        let slot = TABLES[level] + ((CODE >> [39, 30, 21][level]) & 511) * 8;
        let e = m.words[&slot];
        m.words.insert(slot, e | S_BIT_52);
        assert_eq!(td_walk(&m, S_BIT_52, CODE, Access::Execute), None, "level {level}");
        assert_eq!(td_walk(&m, S_BIT_52, CODE, Access::Read), None, "level {level}");
    }
}

/// Under SEV the walk is unchanged: the C-bit marks private leaves.
#[test]
fn sev_still_needs_the_c_bit_for_fetches_only() {
    let mut m = Mem::new(16 * GIB);
    m.map(TABLES, CODE, 0x20_0000 | C_BIT | P | U);
    assert_eq!(m.walk(CODE, Access::Execute), Some(0x20_0000));
    assert_eq!(m.walk(CODE, Access::Read), None);
    m.map(TABLES, CODE, 0x20_0000 | P | U);
    assert_eq!(m.walk(CODE, Access::Execute), None);
    assert_eq!(m.walk(CODE, Access::Read), Some(0x20_0000));
}

/// A TDX fetch or table read stays in the window too.
#[test]
fn tdx_instruction_bytes_above_the_window_are_never_read() {
    let window_top = 16 * GIB;
    for frame in [window_top, 510 * GIB, 512 * GIB, S_BIT_52 - 0x1000] {
        let mut m = Mem::new(window_top);
        m.map(TABLES, CODE, frame | P | U);
        assert_eq!(td_walk(&m, S_BIT_52, CODE, Access::Execute), None, "{frame:#x}");
        assert!(m.outside.borrow().is_empty());
    }
}

/// tdx.rs walks with both masks, from the core's record of the user's
/// tables (the kernel's CR3 is loaded by then under the skim window), and
/// never trusts the GPA in the #VE information.
#[test]
fn user_ve_uses_the_bounded_walk_and_not_the_vmm_gpa() {
    let tdx = include_str!("../../crates/fl4-kernel/src/tdx.rs");
    let walk = &tdx[tdx.find("fn translate(").expect("translate")..];
    let walk = &walk[..walk.find("\n}\n").unwrap()];
    assert!(walk.contains("percpu::get().cr3.get()") && walk.contains("cvm::shared_mask()") && walk.contains("paging::window_top()"));
    assert!(!tdx.contains("info.gpa"), "the kernel must not act on VEINFO.GPA");
    assert!(!tdx.contains("info.gla"), "the kernel must not act on VEINFO.GLA");
}
