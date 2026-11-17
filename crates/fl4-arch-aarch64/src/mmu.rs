//! Address-space switches, broadcast TLB maintenance (l4h 0015: no IPIs)
//! and user cache maintenance.
use crate::{cpu, percpu};
use core::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use fl4_core::layout;

/// Physical ranges the kernel window maps (for cache maintenance through
/// it), set at boot.
const MAX_RANGES: usize = 64;
static RANGES: [(AtomicU64, AtomicU64); MAX_RANGES] = [const { (AtomicU64::new(0), AtomicU64::new(0)) }; MAX_RANGES];
static NRANGES: AtomicUsize = AtomicUsize::new(0);

pub fn add_window_range(start: u64, end: u64) {
    let n = NRANGES.load(Ordering::Relaxed);
    if n < MAX_RANGES {
        RANGES[n].0.store(start, Ordering::Relaxed);
        RANGES[n].1.store(end, Ordering::Relaxed);
        NRANGES.store(n + 1, Ordering::Release);
    }
}

fn in_window(start: u64, len: u64) -> bool {
    let n = NRANGES.load(Ordering::Acquire);
    (0..n).any(|i| {
        let s = RANGES[i].0.load(Ordering::Relaxed);
        let e = RANGES[i].1.load(Ordering::Relaxed);
        s <= start && start.wrapping_add(len) <= e && start.wrapping_add(len) >= start
    })
}

/// Run on the address space `root` (kernel virtual) with `asid`.
pub fn switch(root: u64, asid: u64) {
    let v = layout::paddr(root) | (asid << 48);
    let pc = percpu::get();
    if pc.ttbr0 != v {
        crate::msr!("ttbr0_el1", v);
        cpu::isb();
        pc.ttbr0 = v;
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
    let arg = asid << 48;
    unsafe {
        core::arch::asm!("dsb ishst", "tlbi aside1is, {}", "dsb ish", "isb", in(reg) arg, options(nostack));
    }
}

/// Everything, on every core (boot).
pub fn invalidate_all() {
    unsafe {
        core::arch::asm!("dsb ishst", "tlbi vmalle1is", "dsb ish", "isb", options(nostack));
    }
}

/// seL4 `doFlush` for `len` bytes at user address `vaddr` of (`root`,
/// `asid`), physically `paddr`: through the kernel window when it maps
/// the range, otherwise through the user mapping itself.
pub fn cache_op(op: u64, root: u64, asid: u64, vaddr: u64, len: u64, paddr: u64) {
    use fl4_core::vspace::{CACHE_CLEAN, CACHE_CLEAN_INVALIDATE, CACHE_INVALIDATE};
    let (va, switched) = if in_window(paddr, len) {
        (layout::pptr(paddr), None)
    } else {
        let old = percpu::get().ttbr0;
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
        crate::msr!("ttbr0_el1", old);
        cpu::isb();
        percpu::get().ttbr0 = old;
    }
}
