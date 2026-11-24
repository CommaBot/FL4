//! Address-space switches, broadcast TLB maintenance (l4h 0015: no IPIs)
//! and user cache maintenance.
use crate::{cpu, percpu};
use core::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use fl4_core::layout;

/// Physical ranges the kernel window maps (for cache maintenance through
/// it), set at boot.
/// As many as the kernel's window can have (fl4-kernel-aarch64 `fl4_boot`,
/// `bootmem::MAX_RANGES`: every memory map entry and then some).
pub const MAX_RANGES: usize = 272;
static RANGES: [(AtomicU64, AtomicU64); MAX_RANGES] = [const { (AtomicU64::new(0), AtomicU64::new(0)) }; MAX_RANGES];
static NRANGES: AtomicUsize = AtomicUsize::new(0);

/// Note a range the window maps; false, with nothing noted, when there is
/// no room (the caller fails the boot).
#[must_use]
pub fn add_window_range(start: u64, end: u64) -> bool {
    let n = NRANGES.load(Ordering::Relaxed);
    if n == MAX_RANGES {
        return false;
    }
    RANGES[n].0.store(start, Ordering::Relaxed);
    RANGES[n].1.store(end, Ordering::Relaxed);
    NRANGES.store(n + 1, Ordering::Release);
    true
}

/// `[start, start + len)` (physical) lies in one range the kernel window
/// maps.
pub fn in_window(start: u64, len: u64) -> bool {
    let n = NRANGES.load(Ordering::Acquire);
    (0..n).any(|i| {
        let s = RANGES[i].0.load(Ordering::Relaxed);
        let e = RANGES[i].1.load(Ordering::Relaxed);
        s <= start && start.wrapping_add(len) <= e && start.wrapping_add(len) >= start
    })
}

/// Any byte of `[start, start + len)` (physical) is in a range the kernel
/// window maps.
pub fn overlaps_window(start: u64, len: u64) -> bool {
    let end = start.saturating_add(len);
    let n = NRANGES.load(Ordering::Acquire);
    (0..n).any(|i| {
        let s = RANGES[i].0.load(Ordering::Relaxed);
        let e = RANGES[i].1.load(Ordering::Relaxed);
        s < end && start < e
    })
}

/// Whole-address-space invalidations so far (`invalidate_asid`).
///
/// ASIDs are the hardware ASIDs, so an ASID deleted while another core
/// still runs its old address space can be refilled there with the old
/// translations after the broadcast invalidation; once the ASID names a
/// new address space, that core would use them. So a core that switches
/// address space after any such invalidation first flushes its own TLB.
/// An invalidation counts itself before it broadcasts; a switch that
/// installs an ASID's new root follows the reassignment under the serial
/// gate, so it sees the count of the invalidation that retired the ASID.
///
/// As on x86_64 (tlb.rs), a switch publishes the core's new TTBR0 value,
/// then reads the count; an invalidation bumps the count, then reads which
/// cores run the ASID (`cores_on`). Both are sequentially consistent, so
/// either the invalidating core sees the switching one and calls it, or
/// the switching core sees the new count and flushes.
static ASID_GEN: AtomicU64 = AtomicU64::new(0);

/// The empty user table (fl4-core's `ks::KERNEL_ROOT`, kernel virtual),
/// which a core runs with ASID 0 once the ASID it ran is retired.
static EMPTY_ROOT: AtomicU64 = AtomicU64::new(0);

/// Set once at boot, before any core runs user code.
pub fn set_empty_root(root: u64) {
    EMPTY_ROOT.store(root, Ordering::Relaxed);
}

/// Run on the address space `root` (kernel virtual) with `asid`.
pub fn switch(root: u64, asid: u64) {
    switch_to(layout::paddr(root) | (asid << 48));
}

/// Run on TTBR0 value `v` (table address and ASID): `switch`, and the way
/// back from `cache_op`'s detour, so that too follows the module comment.
fn switch_to(v: u64) {
    let me = percpu::cpu_index();
    if percpu::ttbr0(me) != v {
        crate::msr!("ttbr0_el1", v);
        cpu::isb();
    }
    // Publish before reading the count (module comment); also when the
    // value is unchanged, which costs one store.
    percpu::set_ttbr0(v);
    let g = ASID_GEN.load(Ordering::SeqCst);
    // Also when the value is unchanged: a root freed and made again at
    // the same address can take back the same ASID.
    let pc = percpu::get();
    if pc.asid_gen.get() != g {
        // After the switch, so the old tables cannot refill it.
        unsafe { core::arch::asm!("tlbi vmalle1", "dsb nsh", "isb", options(nostack)) };
        pc.asid_gen.set(g);
    }
}

/// Make page-table writes visible to the table walkers before user code
/// runs (exit path).
#[inline(always)]
pub fn publish_tables() {
    cpu::dsb_ishst();
}

pub fn invalidate_page(asid: u64, vaddr: u64) {
    let arg = (asid << 48) | ((vaddr >> 12) & 0xfff_ffff_ffff);
    unsafe {
        core::arch::asm!("dsb ishst", "tlbi vae1is, {}", "dsb ish", "isb", in(reg) arg, options(nostack));
    }
}

pub fn invalidate_asid(asid: u64) {
    ASID_GEN.fetch_add(1, Ordering::SeqCst);
    let arg = asid << 48;
    unsafe {
        core::arch::asm!("dsb ishst", "tlbi aside1is, {}", "dsb ish", "isb", in(reg) arg, options(nostack));
    }
}

/// The cores other than this one whose current ASID is `asid`.
pub fn cores_on(asid: u64) -> u64 {
    let me = percpu::cpu_index();
    let online = crate::smp::online_mask();
    let mut m = 0;
    for c in 0..percpu::MAX_CPUS {
        if c != me && online & (1 << c) != 0 && percpu::ttbr0(c) >> 48 == asid {
            m |= 1 << c;
        }
    }
    m
}

/// Remote side of `invalidate_asid` (`smp::CALL_ASID`): the broadcast
/// invalidation has run, but if the ASID was deleted its tables can be
/// freed and reused as soon as the call returns, while this core goes on
/// in the kernel with TTBR0 on them: its table walker may still walk them
/// (speculatively too), refilling the TLB from whatever they have become
/// and, with hardware access flags, setting bit 10 of words in them. So
/// it leaves them now for the empty table with ASID 0 (whose switch, the
/// count having moved, also flushes this core's TLB), and the exit sets
/// the address space again from the current thread's VSpace cap.
///
/// Its high window goes too (`switch_high`): the broadcast invalidation of
/// the ASID dropped the translations tagged with it, and ASID 0 never has
/// an `ArmHighVSpace`.
pub fn retired(asid: u64) {
    if percpu::ttbr0(percpu::cpu_index()) >> 48 == asid {
        switch(EMPTY_ROOT.load(Ordering::Relaxed), 0);
        switch_high(0, 0);
        percpu::get().vspace_stale.set(true);
    }
}

// ---- The high window (TTBR1 EL0 mappings, `ArmHighVSpace`) -----------------
//
// A thread may run with TTBR1 on an `ArmHighVSpace` instead of the
// kernel's tables: a copy of them whose level-1 entries 384-495 map user
// pages (nG, EL0 permissions, never executable by the kernel). TCR_EL1.A1
// is 0, so those translations are tagged with the TTBR0 ASID, the same for
// every thread of a VSpace, while only some of them have the high window,
// and a TTBR1 change without an ASID change is not seen by the TLB. So a
// core keeps one fact (`PerCpu::high_ttbr1`, `high_asid`): translations
// of the high window tagged with ASID `high_asid` may be in its TLB, and
// all came from `high_ttbr1`; with any other ASID, none came from an
// `ArmHighVSpace`; while TTBR1 is the kernel's, none came from one.
// `switch_high` keeps that true (its comment lists the cases). Besides,
// every change of TTBR1 flushes the core's whole TLB
// (`TTBR1_CHANGE_FLUSHES_ALL`); see there for why.
//
// Translations of the window itself go when it changes: one page by VA in
// every ASID on every core (`invalidate_high_page`), the whole of it when a
// table is unmapped or the window deleted (`invalidate_high_vspace`, which
// also makes every core running it leave it).

/// The kernel's own TTBR1 (physical), set at boot.
static KERNEL_TTBR1: AtomicU64 = AtomicU64::new(0);
/// The kernel's TTBR1 level-0 table and the level-1 table its entry 511
/// points to, as the kernel reaches them (`kernel_ttbr1_entry`).
static KERNEL_L0: AtomicU64 = AtomicU64::new(0);
static KERNEL_L1_TOP: AtomicU64 = AtomicU64::new(0);

/// Set once at boot, after the kernel's tables are complete and before
/// any user code runs: `ttbr1` physical, the tables kernel virtual.
pub fn set_kernel_ttbr1(ttbr1: u64, l0: u64, l1_top: u64) {
    KERNEL_TTBR1.store(ttbr1, Ordering::Relaxed);
    KERNEL_L0.store(l0, Ordering::Relaxed);
    KERNEL_L1_TOP.store(l1_top, Ordering::Relaxed);
}

pub fn kernel_ttbr1() -> u64 {
    KERNEL_TTBR1.load(Ordering::Relaxed)
}

/// Entry `index` of the kernel's TTBR1 level-0 (`level` 0) or top level-1
/// table (`level` 1); 0 before boot set them.
pub fn kernel_ttbr1_entry(level: u64, index: u64) -> u64 {
    let t = if level == 0 { KERNEL_L0.load(Ordering::Relaxed) } else { KERNEL_L1_TOP.load(Ordering::Relaxed) };
    if t == 0 || index >= 512 {
        return 0;
    }
    unsafe { core::ptr::read_volatile((t + index * 8) as *const u64) }
}

fn tlbi_asid_local(asid: u64) {
    unsafe { core::arch::asm!("tlbi aside1, {}", "dsb nsh", "isb", in(reg) asid << 48, options(nostack)) };
}

fn tlbi_all_local() {
    unsafe { core::arch::asm!("tlbi vmalle1", "dsb nsh", "isb", options(nostack)) };
}

/// Whether a change of TTBR1 flushes this core's whole TLB (`tlbi vmalle1`)
/// rather than the incoming TTBR0 ASID alone (`tlbi aside1`).
///
/// Level-0 entry 511 of a window and of the kernel's tables point to
/// different level-1 tables, and the kernel runs below that entry in both.
/// A walk cache may hold that entry: tagged with the TTBR0 ASID the core
/// ran when it walked it (the kernel walks the old TTBR1 between `switch`
/// and the TTBR1 write), which the ASID flush drops, or as a global entry
/// (the kernel's pages below it are global, and a table descriptor has no
/// nG bit), which only the whole flush drops.
///
/// What was measured (2026-11-24, FL4HVS0001-0003 on Apple M4 under HVF,
/// one and two cores, twice each): the whole flush, the ASID flush and no
/// flush on a TTBR1 change at all (the switch's pair flushes only) all
/// passed, so these tests do not tell the two apart. Before the whole flush
/// was added, l4h's EL0 XNU on the same M4 and HVF took level-1
/// translation faults in its window through the kernel's level-1 table
/// after its core ran another thread on the kernel's TTBR1, and the whole
/// flush ended them. It stays until a test reproduces that fault and shows
/// the ASID flush enough.
const TTBR1_CHANGE_FLUSHES_ALL: bool = true;

/// `invalidate_high_vspace`s so far: the count `switch_high` checks after it
/// publishes its TTBR1 (`PerCpu::high_gen`), apart from `ASID_GEN`, so a
/// window's retirement costs other address-space switches nothing.
static HIGH_GEN: AtomicU64 = AtomicU64::new(0);

/// Write TTBR1 and publish it if it differs from what this core runs;
/// true if it did. No TLB maintenance: the caller's (`switch_high`).
fn set_ttbr1(v: u64) -> bool {
    let me = percpu::cpu_index();
    if v != 0 && percpu::ttbr1(me) != v {
        crate::msr!("ttbr1_el1", v);
        cpu::isb();
        percpu::set_ttbr1(v);
        true
    } else {
        false
    }
}

/// Leave whatever window this core runs for the kernel's TTBR1 (a window
/// retired, or the ASID beside it), flushing this core's TLB.
fn leave_window_flush() {
    set_ttbr1(KERNEL_TTBR1.load(Ordering::Relaxed));
    let pc = percpu::get();
    pc.high_ttbr1.set(0);
    pc.high_asid.set(0);
    tlbi_all_local();
}

/// Run with TTBR1 on the `ArmHighVSpace` at `root` (kernel virtual; 0 =
/// the kernel's own tables) beside TTBR0 ASID `ttbr0_asid`, which the
/// switch of TTBR0 (`switch`) has already installed. (In VHE mode the name
/// TTBR1_EL1 reaches TTBR1_EL2.)
///
/// Invariant: translations (walk caches included) that came from a window
/// are tagged with `high_asid` only, and all came from `high_ttbr1`; while
/// TTBR1 is the kernel's, there are none (the pair is empty).
///
/// - A TTBR1 change flushes (`TTBR1_CHANGE_FLUSHES_ALL`): the whole TLB, or
///   the incoming ASID, which since `switch` has walked the old TTBR1 (the
///   kernel runs below level-0 entry 511 of either table, which point to
///   different level-1 tables);
/// - leaving a window for the kernel's TTBR1 also flushes the pair's ASID;
/// - entering a window with another pair flushes the old pair's ASID and the
///   incoming one: `(a1, W) -> (a2, W) -> (a3, k) -> (a1, k)` must not leave
///   `a1` anything from `W`.
pub fn switch_high(root: u64, ttbr0_asid: u64) {
    let k = KERNEL_TTBR1.load(Ordering::Relaxed);
    let pc = percpu::get();
    if root == 0 || ttbr0_asid == 0 {
        let changed = set_ttbr1(k);
        let old = pc.high_asid.get();
        if changed && TTBR1_CHANGE_FLUSHES_ALL {
            tlbi_all_local();
        } else {
            if changed {
                tlbi_asid_local(ttbr0_asid);
            }
            if old != 0 && !(changed && old == ttbr0_asid) {
                tlbi_asid_local(old);
            }
        }
        pc.high_asid.set(0);
        pc.high_ttbr1.set(0);
        return;
    }
    let v = layout::paddr(root);
    let changed = set_ttbr1(v);
    // Publish before reading the count, also when unchanged (as `switch_to`
    // does for TTBR0): against `invalidate_high_vspace`, which counts, then
    // reads which cores run the window, either it sees this core and calls
    // it, or this core sees the new count here. A switch outside the gate
    // (a local path's ReplyRecv) then cannot trust the window it read, so it
    // leaves it and lets the exit, under the gate, set the address space
    // again. Under the gate, an invalidation counted is over (it runs under
    // the gate and its broadcast flush ends it): nothing to flush.
    percpu::set_ttbr1(v);
    let g = HIGH_GEN.load(Ordering::SeqCst);
    if pc.high_gen.get() != g {
        // (A single core never takes the gate, and nothing runs beside it.)
        if !pc.gate_held.get() && crate::smp::multi() {
            leave_window_flush();
            pc.vspace_stale.set(true);
            return;
        }
        pc.high_gen.set(g);
    }
    let old = pc.high_asid.get();
    let same_pair = pc.high_ttbr1.get() == v && old == ttbr0_asid;
    if changed && TTBR1_CHANGE_FLUSHES_ALL {
        tlbi_all_local();
    } else {
        if old != 0 && old != ttbr0_asid && !same_pair {
            tlbi_asid_local(old);
        }
        if changed || !same_pair {
            tlbi_asid_local(ttbr0_asid);
        }
    }
    pc.high_ttbr1.set(v);
    pc.high_asid.set(ttbr0_asid);
}

/// Before this core enters a guest: the kernel's TTBR1 (in nVHE mode the
/// EL2 stub restores the boot TTBR1_EL1 when the guest exits).
pub fn leave_high() {
    let asid = percpu::ttbr0(percpu::cpu_index()) >> 48;
    switch_high(0, asid);
}

/// Drop the translations of high-window address `vaddr`, for every ASID,
/// on every core (VA bits 55:12 in the operand: bit 55 set for TTBR1).
pub fn invalidate_high_page(vaddr: u64) {
    let arg = (vaddr >> 12) & 0xfff_ffff_ffff;
    unsafe {
        core::arch::asm!("dsb ishst", "tlbi vaae1is, {}", "dsb ish", "isb", in(reg) arg, options(nostack));
    }
}

/// Remote side of `invalidate_high_vspace` (`smp::CALL_HIGH_VSPACE`): leave
/// the window `ttbr1` if this core runs it; the exit sets the address
/// space again from the current thread's caps.
pub fn high_retired(ttbr1: u64) {
    if percpu::ttbr1(percpu::cpu_index()) == ttbr1 {
        leave_window_flush();
        percpu::get().vspace_stale.set(true);
    }
}

/// No core may go on with the `ArmHighVSpace` at `root` (deleted, or one of
/// its tables unmapped and about to be freed): the cores running it leave
/// it (and their table walkers its tables) before this returns, and every
/// core's TLB is flushed. Under the serial gate.
pub fn invalidate_high_vspace(root: u64) {
    let target = layout::paddr(root);
    // Counted first, as `invalidate_asid` does (`switch_high` publishes its
    // TTBR1, then reads the count).
    HIGH_GEN.fetch_add(1, Ordering::SeqCst);
    let me = percpu::cpu_index();
    let online = crate::smp::online_mask();
    let mut mask = 0u64;
    for c in 0..percpu::MAX_CPUS {
        if c != me && online & (1 << c) != 0 && percpu::ttbr1(c) == target {
            mask |= 1 << c;
        }
    }
    if mask != 0 {
        crate::smp::remote_call(crate::smp::CALL_HIGH_VSPACE, target, 0, mask);
    }
    if percpu::ttbr1(me) == target {
        set_ttbr1(KERNEL_TTBR1.load(Ordering::Relaxed));
        let pc = percpu::get();
        pc.high_ttbr1.set(0);
        pc.high_asid.set(0);
        pc.vspace_stale.set(true);
    }
    // Every core's pairs may name the window's translations: drop them all
    // (the pairs stay true, now naming nothing).
    unsafe {
        core::arch::asm!("dsb ishst", "tlbi vmalle1is", "dsb ish", "isb", options(nostack));
    }
}

/// Everything, on every core (boot).
pub fn invalidate_all() {
    unsafe {
        core::arch::asm!("dsb ishst", "tlbi vmalle1is", "dsb ish", "isb", options(nostack));
    }
}

// ---- Stage-2 MMU & VMIDs (EL2 VHE / nVHE) ---------------------------------

/// Physical address of the empty 8 KiB Stage-2 root (2 zeroed pages, 8 KiB
/// aligned), set once at boot.
static EMPTY_S2_ROOT: AtomicU64 = AtomicU64::new(0);
/// Unified Stage-2 IPA width & VTCR_EL2.PS decided once on the boot core so
/// heterogeneous APs (`ap.pa_bits >= bsp.pa_bits`) program identical Stage-2
/// geometry and `VTCR_EL2`.
static S2_IPA_BITS: AtomicU64 = AtomicU64::new(0);
static S2_PS: AtomicU64 = AtomicU64::new(u64::MAX);
/// 8-bit VMID table (used when `FEAT_VMID16` is absent).
static VMID_TABLE: crate::vmid::VmidTable = crate::vmid::VmidTable::new();

pub fn set_empty_s2_root(pa: u64) {
    EMPTY_S2_ROOT.store(pa, Ordering::Relaxed);
}

/// Stage-2 IPA width used by all cores (40, 44, or 48), locked on the BSP.
pub fn s2_ipa_bits() -> u64 {
    let cached = S2_IPA_BITS.load(Ordering::Acquire);
    if cached != 0 {
        cached
    } else {
        crate::vmid::s2_ipa_bits_for_pa(cpu::pa_bits())
    }
}

/// Program `VTCR_EL2` and point `VTTBR_EL2` at the empty Stage-2 root.
pub fn init_stage2_core() {
    if !cpu::has_el2() {
        return;
    }
    let (ipa, ps) = {
        let cached = S2_IPA_BITS.load(Ordering::Acquire);
        if cached != 0 {
            (cached, S2_PS.load(Ordering::Relaxed))
        } else {
            let ipa = crate::vmid::s2_ipa_bits_for_pa(cpu::pa_bits());
            let ps = cpu::pa_range(); // capped at 5 (48-bit)
            S2_PS.store(ps, Ordering::Relaxed);
            S2_IPA_BITS.store(ipa, Ordering::Release);
            (ipa, ps)
        }
    };
    let (t0sz, sl0) = match ipa {
        40 => (64 - 40, 0b01u64), // 3 levels, L1 concatenated (2 pages = 8 KiB)
        44 => (64 - 44, 0b10u64), // 4 levels, L0
        _ => (64 - 48, 0b10u64),  // 4 levels, L0
    };
    let vs = if cpu::vmid16() { 1u64 << 19 } else { 0 };
    // RES1(31) | VS(19) | PS[18:16] | TG0=4K(0) | SH0=IS(3) | ORGN0=WB(1) | IRGN0=WB(1) | SL0 | T0SZ
    let vtcr = (1u64 << 31) | vs | (ps << 16) | (3 << 12) | (1 << 10) | (1 << 8) | (sl0 << 6) | t0sz;
    let empty = EMPTY_S2_ROOT.load(Ordering::Relaxed);
    if cpu::is_el2_nvhe() {
        crate::hyp_nvhe::set_vtcr(vtcr, empty);
    } else {
        crate::msr!("vtcr_el2", vtcr);
        crate::msr!("vttbr_el2", empty);
        cpu::isb();
        unsafe { core::arch::asm!("tlbi alle1", "dsb nsh", "isb", options(nostack)) };
    }
    percpu::set_vttbr(empty);
    percpu::set_s2_asid(0);
}

/// Non-allocating lookup of the hardware VMID currently assigned to `asid`.
pub fn lookup_vmid(asid: u64) -> Option<u64> {
    if asid == 0 {
        return Some(0);
    }
    if cpu::vmid16() {
        return Some(asid & 0xffff);
    }
    VMID_TABLE.lookup(asid)
}

/// Allocate or look up the hardware VMID for `asid`. On 8-bit VMID hardware,
/// any allocation (and wrap-around `CALL_VMID_RETIRE`) runs under the serial
/// gate (`arch.rs` `set_stage2_vspace`).
fn hw_vmid_for(asid: u64) -> u64 {
    if let Some(v) = lookup_vmid(asid) {
        return v;
    }
    let (slot, wrapped) = VMID_TABLE.alloc_step(asid);
    if wrapped {
        let new_gen = VMID_TABLE.bump_gen();
        // 1. Synchronously retire every remote core from old-generation VMIDs.
        crate::smp::remote_call(crate::smp::CALL_VMID_RETIRE, 0, 0, u64::MAX);
        // 2. Retire this core to the empty Stage-2 root as well.
        let empty = EMPTY_S2_ROOT.load(Ordering::Relaxed);
        if cpu::is_el2_vhe() {
            crate::msr!("vttbr_el2", empty);
            cpu::isb();
        }
        percpu::set_vttbr(empty);
        percpu::set_s2_asid(0);
        percpu::get().vmid_gen.set(new_gen);
        // 3. Broadcast-invalidate ALL EL1&0 Stage-1+2 TLB entries across all VMIDs.
        if cpu::is_el2_nvhe() {
            crate::hyp_nvhe::tlbi_alle1_is();
        } else {
            unsafe { core::arch::asm!("dsb ishst", "tlbi alle1is", "dsb ish", "isb", options(nostack)) };
        }
        // 4. Only after every core has left old VMIDs and TLBs are clean, reuse slot 1.
        VMID_TABLE.install_slot(slot, new_gen, asid);
    }
    slot
}

/// Remote handler for `CALL_VMID_RETIRE`: if `asid == 0` (8-bit VMID wrap) or
/// this core is running `asid`, switch `VTTBR_EL2` to the empty Stage-2 root,
/// flush local Stage-1+2 TLB (all VMIDs on wrap), and mark `vspace_stale`.
pub fn vmid_retired(asid: u64) {
    if !cpu::has_el2() {
        return;
    }
    let me = percpu::cpu_index();
    if asid == 0 || percpu::s2_asid(me) == asid {
        let empty = EMPTY_S2_ROOT.load(Ordering::Relaxed);
        if cpu::is_el2_nvhe() {
            if asid == 0 {
                crate::hyp_nvhe::tlbi_vmalls12_local();
            }
        } else {
            crate::msr!("vttbr_el2", empty);
            cpu::isb();
            if asid == 0 {
                unsafe { core::arch::asm!("tlbi alle1", "dsb nsh", "isb", options(nostack)) };
            }
        }
        percpu::set_vttbr(empty);
        percpu::set_s2_asid(0);
        let pc = percpu::get();
        pc.vmid_gen.set(VMID_TABLE.generation());
        pc.vspace_stale.set(true);
    }
}

/// Install Stage-2 root (`root` kernel VA, or 0 for empty Stage-2 root) & ASID into `VTTBR_EL2`.
pub fn switch_stage2(root: u64, asid: u64) {
    if !cpu::has_el2() {
        return;
    }
    let (vttbr, pub_asid) = if root == 0 || asid == 0 {
        (EMPTY_S2_ROOT.load(Ordering::Relaxed), 0)
    } else {
        let vmid = hw_vmid_for(asid);
        (layout::paddr(root) | (vmid << 48), asid)
    };
    let me = percpu::cpu_index();
    if cpu::is_el2_vhe() && percpu::vttbr(me) != vttbr {
        crate::msr!("vttbr_el2", vttbr);
        cpu::isb();
    }
    // Publish before reading VMID_GEN (symmetric with Stage-1 `switch_to`).
    percpu::set_vttbr(vttbr);
    percpu::set_s2_asid(pub_asid);
    let g = VMID_TABLE.generation();
    let pc = percpu::get();
    if pc.vmid_gen.get() != g {
        if cpu::is_el2_nvhe() {
            crate::hyp_nvhe::tlbi_vmalls12_local();
        } else {
            unsafe { core::arch::asm!("tlbi alle1", "dsb nsh", "isb", options(nostack)) };
        }
        pc.vmid_gen.set(g);
    }
}

/// Invalidate Stage-2 TLB for one IPA in `asid` across all cores.
pub fn invalidate_stage2_page(asid: u64, ipa: u64) {
    if !cpu::has_el2() || asid == 0 {
        return;
    }
    let Some(vmid) = lookup_vmid(asid) else {
        return;
    };
    let arg = (ipa >> 12) & 0xfff_ffff_ffff;
    if cpu::is_el2_nvhe() {
        crate::hyp_nvhe::tlbi_ipas2(vmid << 48, arg);
        return;
    }
    let old = crate::mrs!("vttbr_el2");
    crate::msr!("vttbr_el2", vmid << 48);
    cpu::isb();
    unsafe {
        core::arch::asm!(
            "dsb ishst",
            "tlbi ipas2e1is, {}",
            "dsb ish",
            "tlbi vmalle1is",
            "dsb ish",
            "isb",
            in(reg) arg,
            options(nostack)
        );
    }
    crate::msr!("vttbr_el2", old);
    cpu::isb();
}

/// Invalidate all Stage-1 + Stage-2 TLB entries for `asid`'s VMID across all
/// cores, and retire `VTTBR_EL2` on every core still running `asid`.
/// Caller holds the serial gate.
pub fn invalidate_stage2_vmid(asid: u64) {
    if !cpu::has_el2() || asid == 0 {
        return;
    }
    let old_vmid = lookup_vmid(asid);
    // 1. Synchronously retire every core currently running `asid` so no table
    //    walker can refill from the retiring Stage-2 tables after TLBI.
    let me = percpu::cpu_index();
    let online = crate::smp::online_mask();
    let mut mask = 0u64;
    for c in 0..percpu::MAX_CPUS {
        if c != me && online & (1 << c) != 0 && percpu::s2_asid(c) == asid {
            mask |= 1 << c;
        }
    }
    if mask != 0 {
        crate::smp::remote_call(crate::smp::CALL_VMID_RETIRE, asid, 0, mask);
    }
    if percpu::s2_asid(me) == asid {
        let empty = EMPTY_S2_ROOT.load(Ordering::Relaxed);
        if cpu::is_el2_vhe() {
            crate::msr!("vttbr_el2", empty);
            cpu::isb();
        }
        percpu::set_vttbr(empty);
        percpu::set_s2_asid(0);
        percpu::get().vspace_stale.set(true);
    }
    // 2. Broadcast TLBI for `old_vmid`, then release its 8-bit slot (if any).
    if let Some(vmid) = old_vmid {
        if cpu::is_el2_nvhe() {
            crate::hyp_nvhe::tlbi_vmalls12_is(vmid << 48);
        } else {
            let old = crate::mrs!("vttbr_el2");
            crate::msr!("vttbr_el2", vmid << 48);
            cpu::isb();
            unsafe {
                core::arch::asm!("dsb ishst", "tlbi vmalls12e1is", "dsb ish", "isb", options(nostack));
            }
            crate::msr!("vttbr_el2", old);
            cpu::isb();
        }
        if !cpu::vmid16() && (1..256).contains(&vmid) {
            VMID_TABLE.release_slot(vmid);
        }
    }
}

/// seL4 `doFlush` for `len` bytes at user address `vaddr` of (`root`,
/// `asid`), physically `paddr`: through the kernel window when it maps
/// the range, otherwise through the user mapping itself (skipped when
/// `root == 0`, e.g. Stage-2 frames that must never be loaded into TTBR0).
pub fn cache_op(op: u64, root: u64, asid: u64, vaddr: u64, len: u64, paddr: u64) {
    use fl4_core::vspace::{CACHE_CLEAN, CACHE_CLEAN_INVALIDATE, CACHE_INVALIDATE};
    let (va, switched) = if in_window(paddr, len) {
        (layout::pptr(paddr), None)
    } else if root == 0 {
        return;
    } else {
        // Under the serial gate in an SMP kernel. Page-table
        // writes of this entry reach the walker before it walks them.
        // PSTATE.PAN does not apply ("no effect on ... data cache
        // instructions, except DC ZVA", DDI 0487J.a).
        let old = percpu::ttbr0(percpu::cpu_index());
        publish_tables();
        switch(root, asid);
        (vaddr, Some(old))
    };
    if op == CACHE_CLEAN {
        cpu::clean_dcache_poc(va, len);
    } else if op == CACHE_INVALIDATE {
        cpu::inval_dcache_poc(va, len);
    } else if op == CACHE_CLEAN_INVALIDATE {
        cpu::clean_inval_dcache_poc(va, len);
    } else {
        cpu::sync_icache(va, len);
    }
    if let Some(old) = switched {
        switch_to(old);
    }
}
