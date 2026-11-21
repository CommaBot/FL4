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
pub fn retired(asid: u64) {
    if percpu::ttbr0(percpu::cpu_index()) >> 48 == asid {
        switch(EMPTY_ROOT.load(Ordering::Relaxed), 0);
        percpu::get().vspace_stale.set(true);
    }
}

/// Everything, on every core (boot).
pub fn invalidate_all() {
    unsafe {
        core::arch::asm!("dsb ishst", "tlbi vmalle1is", "dsb ish", "isb", options(nostack));
    }
}

// ---- Stage-2 MMU & VMIDs (EL2 VHE) ----------------------------------------

/// Physical address of the empty 8 KiB Stage-2 root (2 zeroed pages, 8 KiB
/// aligned), set once at boot.
static EMPTY_S2_ROOT: AtomicU64 = AtomicU64::new(0);
/// Generation counter for 8-bit VMID wrap-around.
static VMID_GEN: AtomicU64 = AtomicU64::new(1);
/// 8-bit VMID table: slot `i` (1..=255) holds `(gen << 16) | asid`.
static VMID_SLOTS: [AtomicU64; 256] = [const { AtomicU64::new(0) }; 256];
static VMID_NEXT: AtomicU64 = AtomicU64::new(1);

pub fn set_empty_s2_root(pa: u64) {
    EMPTY_S2_ROOT.store(pa, Ordering::Relaxed);
}

/// Stage-2 IPA width supported by this hardware (40, 44, or 48).
pub fn s2_ipa_bits() -> u64 {
    let pb = cpu::pa_bits();
    if pb <= 42 {
        40
    } else if pb == 44 {
        44
    } else {
        48
    }
}

/// Program `VTCR_EL2` and point `VTTBR_EL2` at the empty Stage-2 root.
pub fn init_stage2_core() {
    if !cpu::has_el2() {
        return;
    }
    let ipa = s2_ipa_bits();
    let (t0sz, sl0) = match ipa {
        40 => (64 - 40, 0b01u64), // 3 levels, L1 concatenated (2 pages = 8 KiB)
        44 => (64 - 44, 0b10u64), // 4 levels, L0
        _ => (64 - 48, 0b10u64),  // 4 levels, L0
    };
    let ps = cpu::pa_range(); // capped at 5 (48-bit)
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
        unsafe { core::arch::asm!("tlbi vmalls12e1", "dsb nsh", "isb", options(nostack)) };
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
    let gen = VMID_GEN.load(Ordering::SeqCst);
    let tag = (gen << 16) | (asid & 0xffff);
    for (v, slot) in VMID_SLOTS.iter().enumerate().skip(1) {
        if slot.load(Ordering::Acquire) == tag {
            return Some(v as u64);
        }
    }
    None
}

/// Allocate or look up the hardware VMID for `asid`. On 8-bit VMID hardware,
/// any allocation (and wrap-around `CALL_VMID_RETIRE`) runs under the serial
/// gate (`arch.rs` `set_stage2_vspace`).
fn hw_vmid_for(asid: u64) -> u64 {
    if let Some(v) = lookup_vmid(asid) {
        return v;
    }
    let gen = VMID_GEN.load(Ordering::SeqCst);
    let tag = (gen << 16) | (asid & 0xffff);
    let next = VMID_NEXT.fetch_add(1, Ordering::AcqRel);
    let slot = ((next - 1) % 255) + 1;
    if next > 255 && slot == 1 {
        let new_gen = VMID_GEN.fetch_add(1, Ordering::SeqCst) + 1;
        let new_tag = (new_gen << 16) | (asid & 0xffff);
        VMID_SLOTS[slot as usize].store(new_tag, Ordering::Release);
        if cpu::is_el2_nvhe() {
            crate::hyp_nvhe::tlbi_vmalls12_local();
        } else {
            unsafe { core::arch::asm!("dsb ishst", "tlbi vmalls12e1is", "dsb ish", "isb", options(nostack)) };
        }
        crate::smp::remote_call(crate::smp::CALL_VMID_RETIRE, 0, 0, u64::MAX);
        return slot;
    }
    VMID_SLOTS[slot as usize].store(tag, Ordering::Release);
    slot
}

/// Remote handler for `CALL_VMID_RETIRE`: if `asid == 0` (8-bit VMID wrap) or
/// this core is running `asid`, switch `VTTBR_EL2` to the empty Stage-2 root,
/// flush local Stage-1+2 TLB, and mark `vspace_stale` so exit re-evaluates.
pub fn vmid_retired(asid: u64) {
    if !cpu::has_el2() {
        return;
    }
    let me = percpu::cpu_index();
    if asid == 0 || percpu::s2_asid(me) == asid {
        let empty = EMPTY_S2_ROOT.load(Ordering::Relaxed);
        if cpu::is_el2_nvhe() {
            crate::hyp_nvhe::tlbi_vmalls12_local();
        } else {
            crate::msr!("vttbr_el2", empty);
            cpu::isb();
            unsafe { core::arch::asm!("tlbi vmalls12e1", "dsb nsh", "isb", options(nostack)) };
        }
        percpu::set_vttbr(empty);
        percpu::set_s2_asid(0);
        let pc = percpu::get();
        pc.vmid_gen.set(VMID_GEN.load(Ordering::SeqCst));
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
    let g = VMID_GEN.load(Ordering::SeqCst);
    let pc = percpu::get();
    if pc.vmid_gen.get() != g {
        if cpu::is_el2_nvhe() {
            crate::hyp_nvhe::tlbi_vmalls12_local();
        } else {
            unsafe { core::arch::asm!("tlbi vmalls12e1", "dsb nsh", "isb", options(nostack)) };
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
/// cores, and retire `VTTBR_EL2` on any remote core still running `asid`.
/// Caller holds the serial gate.
pub fn invalidate_stage2_vmid(asid: u64) {
    if !cpu::has_el2() || asid == 0 {
        return;
    }
    VMID_GEN.fetch_add(1, Ordering::SeqCst);
    if let Some(vmid) = lookup_vmid(asid) {
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
            VMID_SLOTS[vmid as usize].store(0, Ordering::Release);
        }
    }
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
