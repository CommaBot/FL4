//! The order of one core's TTBR0/TTBR1 writes and TLB maintenance on an
//! address-space switch (mmu.rs), over the registers and per-CPU fields it
//! reads and writes (`Hw`), so the host can run it on a recording backend
//! (xtask/tests/aarch64_boot.rs). No `unsafe`, no assembly: mmu.rs supplies
//! the hardware.
//!
//! What every switch keeps true, between any two register writes (each
//! followed by an ISB, so each is a state the table walker can see):
//!
//! 1. TTBR1 on an `ArmHighVSpace` `W` only beside the TTBR0 ASID `a` of the
//!    core's pair (`high_pair() == (W, a)`): no other ASID ever runs with a
//!    window, so no other ASID's TLB entries can come from one.
//! 2. Translations under the window (TTBR1 level-0 entry 511, all nG, so
//!    tagged with the TTBR0 ASID) may be in the TLB only for the pair: the
//!    kernel's TTBR1 has level-0 entry 511 invalid, and an invalid entry is
//!    never cached. A pair is replaced only after TTBR1 is back on the
//!    kernel's tables and both its ASID and the new one are flushed.
//!
//! So `(owner, W) -> (other, kernel) -> (owner, W)` flushes nothing: the
//! pair stays, and the owner's window translations stay right.
//!
//! A window's TTBR1 value is a physical address and may be 0; so "none" is
//! `None` throughout (no kernel TTBR1 yet, no TTBR1 published yet, no
//! pair), never a value.

/// One core's MMU registers and the per-CPU state of mmu.rs.
pub trait Hw {
    /// The kernel's TTBR1 (None before boot set it).
    fn kernel_ttbr1(&self) -> Option<u64>;
    /// The TTBR0 / TTBR1 values this core published (what it runs; TTBR1
    /// None before its first switch, on the kernel's from boot).
    fn ttbr0(&self) -> u64;
    fn ttbr1(&self) -> Option<u64>;
    /// `msr ttbr0_el1` + `isb`; `msr ttbr1_el1` + `isb`.
    fn write_ttbr0(&mut self, v: u64);
    fn write_ttbr1(&mut self, v: u64);
    /// Publish to the other cores (sequentially consistent).
    fn publish_ttbr0(&mut self, v: u64);
    fn publish_ttbr1(&mut self, v: u64);
    /// `ASID_GEN` (sequentially consistent) and the count this core saw.
    fn asid_gen(&self) -> u64;
    fn seen_asid_gen(&self) -> u64;
    fn set_seen_asid_gen(&mut self, g: u64);
    /// `HIGH_GEN` (sequentially consistent) and the count this core saw.
    fn high_gen(&self) -> u64;
    fn seen_high_gen(&self) -> u64;
    fn set_seen_high_gen(&mut self, g: u64);
    /// `(PerCpu::high_ttbr1, PerCpu::high_asid)`; None: no pair. A pair's
    /// ASID is never 0.
    fn high_pair(&self) -> Option<(u64, u64)>;
    fn set_high_pair(&mut self, pair: Option<(u64, u64)>);
    fn gate_held(&self) -> bool;
    fn multi(&self) -> bool;
    fn set_vspace_stale(&mut self);
    /// `tlbi aside1` / `tlbi vmalle1`, each with `dsb nsh` + `isb`.
    fn tlbi_asid(&mut self, asid: u64);
    fn tlbi_all(&mut self);
}

/// Write TTBR1 and publish it if it differs from what this core runs;
/// true if it did. No TLB maintenance.
#[inline(always)]
pub fn set_ttbr1<H: Hw>(h: &mut H, v: u64) -> bool {
    if h.ttbr1() != Some(v) {
        h.write_ttbr1(v);
        h.publish_ttbr1(v);
        true
    } else {
        false
    }
}

/// Run on TTBR0 value `v` (table address and ASID). A new value first takes
/// TTBR1 back to the kernel's tables, so the new ASID never runs beside the
/// window the old one had (invariant 1); the pair stays, and the
/// `ArmHighVSpace` that goes with `v`, if any, comes back with `switch_high`.
#[inline(always)]
pub fn switch_to<H: Hw>(h: &mut H, v: u64) {
    if h.ttbr0() != v {
        if let Some(k) = h.kernel_ttbr1() {
            set_ttbr1(h, k);
        }
        h.write_ttbr0(v);
    }
    // Publish before reading the count (mmu.rs `ASID_GEN`); also when the
    // value is unchanged, which costs one store.
    h.publish_ttbr0(v);
    let g = h.asid_gen();
    // Also when the value is unchanged: a root freed and made again at the
    // same address can take back the same ASID.
    if h.seen_asid_gen() != g {
        // After the switch, so the old tables cannot refill it.
        h.tlbi_all();
        h.set_seen_asid_gen(g);
    }
}

/// Leave whatever window this core runs for the kernel's TTBR1 (a window
/// retired, or the ASID beside it), flushing this core's TLB.
#[inline(always)]
pub fn leave_window_flush<H: Hw>(h: &mut H) {
    if let Some(k) = h.kernel_ttbr1() {
        set_ttbr1(h, k);
    }
    h.set_high_pair(None);
    h.tlbi_all();
}

/// The window with TTBR1 value `w` is going (`invalidate_high_vspace`):
/// if this core runs it, back to the kernel's TTBR1, the address space
/// marked stale, and with `flush` this core's TLB flushed (the remote side;
/// the retiring core broadcasts instead); if only its pair names it, the
/// pair goes (the broadcast drops its translations). A core that has not
/// published a TTBR1 yet runs no window.
#[inline(always)]
pub fn retire_window<H: Hw>(h: &mut H, w: u64, flush: bool) {
    if h.ttbr1() == Some(w) {
        if flush {
            leave_window_flush(h);
        } else {
            if let Some(k) = h.kernel_ttbr1() {
                set_ttbr1(h, k);
            }
            h.set_high_pair(None);
        }
        h.set_vspace_stale();
    } else if matches!(h.high_pair(), Some((p, _)) if p == w) {
        h.set_high_pair(None);
    }
}

/// Run with TTBR1 on the `ArmHighVSpace` with TTBR1 value `v` (physical,
/// 0 included; None: the kernel's own tables) beside TTBR0 ASID `asid`,
/// which the core already runs (`switch_to` first). Nothing before boot set
/// the kernel's TTBR1.
///
/// - No window (or ASID 0): the kernel's TTBR1; if the pair is this ASID's,
///   its window translations go (the ASID now runs without them) and so
///   does the pair.
/// - The pair's window and ASID: TTBR1 on it, no TLB maintenance.
/// - Any other pair: TTBR1 back on the kernel's tables first, then the old
///   pair's ASID and this one flushed, then the new pair, and only then
///   TTBR1 on the new window (invariant 2: two windows' translations for
///   one ASID never meet).
///
/// Then `HIGH_GEN`, read after publishing TTBR1 (against
/// `invalidate_high_vspace`, which counts, then scans which cores run the
/// window): outside the serial gate on an SMP kernel a moved count leaves
/// the window and marks the address space stale, the exit setting it again
/// under the gate.
#[inline(always)]
pub fn switch_high<H: Hw>(h: &mut H, v: Option<u64>, asid: u64) {
    let Some(k) = h.kernel_ttbr1() else { return };
    let v = match v {
        Some(v) if asid != 0 => v,
        _ => {
            set_ttbr1(h, k);
            if asid != 0 && matches!(h.high_pair(), Some((_, a)) if a == asid) {
                h.tlbi_asid(asid);
                h.set_high_pair(None);
            }
            return;
        }
    };
    let old = h.high_pair();
    if old != Some((v, asid)) {
        set_ttbr1(h, k);
        if let Some((_, old_asid)) = old {
            h.tlbi_asid(old_asid);
        }
        if old.map(|p| p.1) != Some(asid) {
            h.tlbi_asid(asid);
        }
        h.set_high_pair(Some((v, asid)));
    }
    set_ttbr1(h, v);
    // Publish before reading HIGH_GEN, also when unchanged (as `switch_to`
    // does for TTBR0).
    h.publish_ttbr1(v);
    let g = h.high_gen();
    if h.seen_high_gen() != g {
        if !h.gate_held() && h.multi() {
            leave_window_flush(h);
            h.set_vspace_stale();
            return;
        }
        h.set_seen_high_gen(g);
    }
}

/// How `cache_op` reaches a user range.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CacheVia {
    /// The kernel window maps it: no address-space change.
    Window,
    /// Neither the window nor a root (`root == 0`, e.g. Stage-2 frames,
    /// never loaded into TTBR0): nothing to do.
    Skip,
    /// Through the user mapping itself, borrowing this TTBR0 value.
    Borrow(u64),
}

/// `in_window`: the kernel window maps the range; `root`: the user tables
/// (0: none) and `ttbr0` the TTBR0 value with them.
#[inline(always)]
pub fn cache_via(in_window: bool, root: u64, ttbr0: u64) -> CacheVia {
    if in_window {
        CacheVia::Window
    } else if root == 0 {
        CacheVia::Skip
    } else {
        CacheVia::Borrow(ttbr0)
    }
}

/// `cache_op`'s detour onto another address space's TTBR0 value `v`:
/// returns what to come back to (`unborrow`). A different TTBR0 leaves the
/// window on the way (`switch_to`), so the borrowed ASID never runs beside
/// it.
#[inline(always)]
pub fn borrow<H: Hw>(h: &mut H, v: u64) -> (u64, Option<u64>) {
    let old = (h.ttbr0(), h.ttbr1());
    switch_to(h, v);
    old
}

/// Back from `borrow`: the old TTBR0 first, then, if the core ran a window,
/// that window again by `switch_high`'s rules (its pair unchanged: no TLB
/// maintenance).
#[inline(always)]
pub fn unborrow<H: Hw>(h: &mut H, (ttbr0, ttbr1): (u64, Option<u64>)) {
    switch_to(h, ttbr0);
    if let (Some(k), Some(t1)) = (h.kernel_ttbr1(), ttbr1) {
        if t1 != k {
            switch_high(h, Some(t1), ttbr0 >> 48);
        }
    }
}
