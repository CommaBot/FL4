//! Confidential guest memory: AMD SEV(-SNP) and Intel TDX. Physical
//! addresses in capabilities, BootInfo and device descriptors are always
//! GPAs without a visibility bit. A page-table leaf adds the private mask
//! (SEV's C-bit) or the shared mask (TDX's S-bit, the top GPA bit); only one
//! of them is ever nonzero.
use core::arch::asm;
use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicPtr, AtomicU64, Ordering};
use fl4_core::boot::Region;
use fl4_core::layout::{paddr, pptr};

use crate::sev::snp;
use crate::tdx;

pub mod mmio;

static PRIVATE_MASK: AtomicU64 = AtomicU64::new(0);
static SHARED_MASK: AtomicU64 = AtomicU64::new(0);

// Read by the entry and return stubs, including on skim page tables.
#[no_mangle]
#[cfg_attr(target_os = "none", link_section = ".bss.skim")]
static FL4_CVM_POISONED: AtomicBool = AtomicBool::new(false);
// SNP or TDX: the host is untrusted, so every kernel entry validates its
// frame and runs on an IST (entry.S). Read like the flag above.
#[no_mangle]
#[cfg_attr(target_os = "none", link_section = ".bss.skim")]
static FL4_CVM_HARDENED: AtomicBool = AtomicBool::new(false);

/// Adjacent to the private physical window in PML4 slot 511.
pub const SHARED_SLOT: usize = 510;
const SHARED_BASE: u64 = 0xffff_ff00_0000_0000;

/// The boot core detected these masks before it built its page tables.
pub fn init(private: u64, shared: u64) {
    PRIVATE_MASK.store(private, Ordering::Relaxed);
    SHARED_MASK.store(shared, Ordering::Relaxed);
}

/// Address bits of a private page-table leaf (SEV's C-bit).
#[inline]
pub fn private_mask() -> u64 {
    PRIVATE_MASK.load(Ordering::Relaxed)
}

/// Address bits of a shared page-table leaf (TDX's S-bit).
#[inline]
pub fn shared_mask() -> u64 {
    SHARED_MASK.load(Ordering::Relaxed)
}

/// Guest memory has a private and a shared view.
#[inline]
pub fn active() -> bool {
    private_mask() | shared_mask() != 0
}

/// The boot core runs under SNP or TDX (`FL4_CVM_HARDENED`).
pub fn set_hardened() {
    FL4_CVM_HARDENED.store(true, Ordering::Release);
}

#[inline]
pub fn hardened() -> bool {
    FL4_CVM_HARDENED.load(Ordering::Acquire)
}

/// Stop every core: it halts at its next kernel entry or exit. Returns
/// whether a core had done so already.
pub fn poison() -> bool {
    FL4_CVM_POISONED.swap(true, Ordering::AcqRel)
}

#[inline]
pub fn halt_if_poisoned() {
    if FL4_CVM_POISONED.load(Ordering::Acquire) {
        crate::cpu::halt_forever();
    }
}

/// Report a fatal error to the host and stop every core.
pub fn terminate(reason: u8) -> ! {
    if tdx::active() {
        tdx::terminate(reason)
    }
    snp::terminate(reason)
}

/// End of the contiguous GPA range below both MAXPHYADDR and the visibility
/// bit, `private_mask | shared_mask`. AMD APM vol. 2 §15.34.6 applies
/// PhysAddrReduction to the system physical address after nested
/// translation. The guest uses its advertised width.
pub fn gpa_top(max_paddr: u64, visibility_mask: u64) -> u64 {
    if visibility_mask == 0 { max_paddr } else { max_paddr.min(visibility_mask) }
}

pub(crate) fn shared_ptr(pa: u64) -> u64 {
    if !active() { pptr(pa) } else { SHARED_BASE + pa }
}

/// Only form a direct-window pointer after the complete MMIO span fits.
pub fn mmio_ptr(pa: u64, bytes: u64, window_top: u64) -> Option<u64> {
    (bytes != 0 && pa < window_top && bytes <= window_top - pa).then(|| shared_ptr(pa))
}

/// # Safety
/// The caller owns the MMIO register at a validated device-window address.
pub unsafe fn read_mmio32(addr: u64) -> u32 {
    if snp::active() {
        snp::mmio(addr - SHARED_BASE, 4, None) as u32
    } else if tdx::active() {
        tdx::mmio((addr - SHARED_BASE) | shared_mask(), 4, None) as u32
    } else {
        unsafe { ptr::read_volatile(addr as *const u32) }
    }
}

/// # Safety
/// The caller owns the MMIO register at a validated device-window address.
pub unsafe fn write_mmio32(addr: u64, value: u32) {
    if snp::active() {
        snp::mmio(addr - SHARED_BASE, 4, Some(value as u64));
    } else if tdx::active() {
        tdx::mmio((addr - SHARED_BASE) | shared_mask(), 4, Some(value as u64));
    } else {
        unsafe { ptr::write_volatile(addr as *mut u32, value) }
    }
}

/// Installed once before the BSP releases the APs. RAM handed to userspace
/// as ordinary untypeds is disjoint from all the initial device untypeds.
pub struct Memory {
    pub ram: &'static [Region],
    pub private_devices: &'static [Region],
}

static MEMORY: AtomicPtr<Memory> = AtomicPtr::new(ptr::null_mut());

pub fn install(memory: &'static Memory) {
    MEMORY.store(ptr::from_ref(memory).cast_mut(), Ordering::Release);
}

fn memory() -> Option<&'static Memory> {
    // install publishes a static snapshot before the APs start.
    unsafe { MEMORY.load(Ordering::Acquire).as_ref() }
}

pub fn private_device(pa: u64) -> bool {
    memory().is_some_and(|m| m.private_devices.iter().any(|r| r.start <= pa && pa < r.end))
}

/// A shared device frame in allocatable RAM can only come from RetypeShared.
/// Device caps cannot be used as IPC buffers, kernel objects or subframe
/// sources. Thus no core uses the private alias during this frame's lifetime.
pub fn is_dma_ram(base: u64, bytes: u64) -> bool {
    let pa = paddr(base);
    active() && bytes > 0 && bytes <= 1 << 21 && (pa | bytes) & 4095 == 0
        && memory().is_some_and(|m| m.ram.iter().any(|r| r.start <= pa && pa < r.end && bytes <= r.end - pa))
}

/// Evict the entire representation, waiting for writeback before an alias
/// can be touched or the frame published. Base SEV CPUs use 64-byte lines.
fn flush(base: u64, bytes: u64, optimized: bool) {
    unsafe {
        if optimized {
            for offset in (0..bytes).step_by(64) {
                asm!("clflushopt [{}]", in(reg) base + offset, options(nostack, preserves_flags));
            }
        } else {
            for offset in (0..bytes).step_by(64) {
                asm!("clflush [{}]", in(reg) base + offset, options(nostack, preserves_flags));
            }
        }
        asm!("mfence", options(nostack, preserves_flags));
    }
}

/// Called under the serial gate after exclusive ownership or the last unmap
/// and its synchronous shootdown. A new shared range must reach memory even
/// when its first consumer uses uncached loads or non-snooping DMA.
pub fn transition(base: u64, bytes: u64, shared: bool) {
    transition_inner(base, bytes, shared, true);
}

/// How this guest changes a page's visibility.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Platform {
    /// Base SEV: no page state, only the view changes.
    Sev,
    Snp,
    Tdx,
}

/// One step of a visibility transition.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Step {
    /// Zero through the old representation (TDX, leaving private memory).
    ZeroOld,
    /// Flush the old representation's cache lines.
    FlushOld,
    /// INVLPG both aliases on this core.
    LocalInvlpg,
    /// The same on every online core, synchronously.
    RemoteInvlpg,
    /// PVALIDATE and the page state change, or TDX's MapGPA.
    ChangeState,
    /// TDG.MEM.PAGE.ACCEPT (TDX, entering private memory).
    Accept,
    /// Zero through the new representation.
    ZeroNew,
    /// Flush the new representation's cache lines.
    FlushNew,
}

/// The steps of a transition, in order. Under SNP and TDX both aliases
/// leave every core's TLB before the page state changes and again after:
/// a core can refill an entry (speculatively, or for a neighbour sharing a
/// large page or RMP entry) between the first shootdown and the change, and
/// PVALIDATE invalidates only the executing core's entries. Nothing touches
/// the new representation before the second shootdown.
///
/// TDX zeroes private memory before the VMM can reach it, and zeroes again
/// after TDG.MEM.PAGE.ACCEPT unconditionally: a page the VMM never really
/// removed is reported as already accepted, with its old contents.
fn steps(platform: Platform, shootdown: bool, shared: bool, mut step: impl FnMut(Step)) {
    let tdx = platform == Platform::Tdx;
    if tdx && shared {
        step(Step::ZeroOld);
    }
    step(Step::FlushOld);
    if platform != Platform::Sev {
        step(Step::LocalInvlpg);
        if shootdown {
            step(Step::RemoteInvlpg);
        }
        step(Step::ChangeState);
        if tdx && !shared {
            step(Step::Accept);
        }
        step(Step::LocalInvlpg);
        if shootdown {
            step(Step::RemoteInvlpg);
        }
    }
    step(Step::ZeroNew);
    if shared {
        step(Step::FlushNew);
    }
}

pub(crate) fn transition_inner(base: u64, bytes: u64, shared: bool, shootdown: bool) {
    let alias = shared_ptr(paddr(base));
    let (old, new) = if shared { (base, alias) } else { (alias, base) };
    let optimized = crate::cpu::cpuid(7, 0).ebx & (1 << 23) != 0;
    let platform = if tdx::active() {
        Platform::Tdx
    } else if snp::active() {
        Platform::Snp
    } else {
        Platform::Sev
    };
    unsafe { asm!("mfence", options(nostack, preserves_flags)); }
    steps(platform, shootdown, shared, |s| match s {
        Step::ZeroOld => unsafe {
            ptr::write_bytes(old as *mut u8, 0, bytes as usize);
            asm!("mfence", options(nostack, preserves_flags));
        },
        Step::FlushOld => flush(old, bytes, optimized),
        Step::LocalInvlpg => invalidate_aliases(base, bytes),
        Step::RemoteInvlpg => {
            crate::smp::remote_call(crate::smp::CALL_CVM_INVLPG, base, bytes, crate::smp::online_mask());
        }
        Step::ChangeState if platform == Platform::Tdx => {
            let gpa = paddr(base) | if shared { shared_mask() } else { 0 };
            tdx::map_gpa(gpa, bytes);
        }
        Step::ChangeState => snp::change_state(base, paddr(base), bytes, shared),
        Step::Accept => tdx::accept_pages(paddr(base), bytes),
        Step::ZeroNew => unsafe {
            ptr::write_bytes(new as *mut u8, 0, bytes as usize);
            asm!("mfence", options(nostack, preserves_flags));
        },
        Step::FlushNew => flush(new, bytes, optimized),
    });
}

/// Used by both ends of a synchronous shootdown around a page state change.
pub(crate) fn invalidate_aliases(base: u64, bytes: u64) {
    let alias = shared_ptr(paddr(base));
    for offset in (0..bytes).step_by(4096) {
        crate::cpu::invlpg(base + offset);
        crate::cpu::invlpg(alias + offset);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn contiguous_gpas_stop_at_the_guest_width_or_the_visibility_bit() {
        assert_eq!(gpa_top(1 << 52, 0), 1 << 52);
        assert_eq!(gpa_top(1 << 52, 1 << 51), 1 << 51);
        assert_eq!(gpa_top(1 << 48, 1 << 39), 1 << 39);
        assert_eq!(gpa_top(1 << 36, 1 << 51), 1 << 36);
    }

    #[test]
    fn tdx_gpa_top_stops_below_the_shared_bit_for_both_widths() {
        for gpaw in [48u64, 52] {
            let shared = tdx::shared_mask_of(gpaw).unwrap();
            assert_eq!(shared, 1 << (gpaw - 1));
            assert_eq!(gpa_top(1 << 52, shared), shared);
            assert_eq!(gpa_top(1 << 46, shared), 1 << 46);
        }
    }

    fn record(platform: Platform, shootdown: bool, shared: bool) -> ([Option<Step>; 10], usize) {
        let mut out = [None; 10];
        let mut n = 0;
        steps(platform, shootdown, shared, |s| {
            out[n] = Some(s);
            n += 1;
        });
        (out, n)
    }

    /// Audit round 5 F1: after the page state change no core may keep a
    /// TLB entry of either alias from before it, and the new alias is
    /// first touched only after every core dropped them.
    #[test]
    fn snp_transitions_shoot_down_both_aliases_after_the_state_change() {
        use Step::*;
        for shared in [false, true] {
            let (s, n) = record(Platform::Snp, true, shared);
            let change = s.iter().position(|&x| x == Some(ChangeState)).unwrap();
            let zero = s.iter().position(|&x| x == Some(ZeroNew)).unwrap();
            let before = &s[..change];
            let after = &s[change + 1..zero];
            for set in [before, after] {
                assert!(set.contains(&Some(LocalInvlpg)) && set.contains(&Some(RemoteInvlpg)));
            }
            assert_eq!(s[0], Some(FlushOld));
            assert_eq!(s[n - 1], Some(if shared { FlushNew } else { ZeroNew }));
            // Early boot (no other core yet): local invalidation only.
            let (s, _) = record(Platform::Snp, false, shared);
            let change = s.iter().position(|&x| x == Some(ChangeState)).unwrap();
            assert_eq!(s[change + 1], Some(LocalInvlpg));
            assert!(!s.contains(&Some(RemoteInvlpg)));
            // Without SNP there is no RMP state to change.
            let (s, n) = record(Platform::Sev, true, shared);
            assert_eq!(&s[..n], if shared { &[Some(FlushOld), Some(ZeroNew), Some(FlushNew)][..] } else { &[Some(FlushOld), Some(ZeroNew)][..] });
        }
    }

    /// Private to shared: nothing private is left for the VMM to read, in
    /// memory or in a cache, before MapGPA; the shared view is touched only
    /// after every core dropped both aliases, and its zeroes reach memory.
    #[test]
    fn tdx_private_to_shared_zeroes_flushes_and_shoots_down_around_map_gpa() {
        use Step::*;
        let (s, n) = record(Platform::Tdx, true, true);
        assert_eq!(
            &s[..n],
            &[ZeroOld, FlushOld, LocalInvlpg, RemoteInvlpg, ChangeState, LocalInvlpg, RemoteInvlpg, ZeroNew, FlushNew].map(Some)
        );
    }

    /// A zeroed shared frame reaches memory before user space can map it
    /// uncached or a device reads it, on every platform that shares.
    #[test]
    fn every_private_to_shared_transition_ends_by_flushing_the_new_view() {
        for p in [Platform::Sev, Platform::Snp, Platform::Tdx] {
            let (s, n) = record(p, true, true);
            assert_eq!(&s[n - 2..n], &[Some(Step::ZeroNew), Some(Step::FlushNew)], "{p:?}");
        }
    }

    /// Shared to private: accept before the second shootdown, and zero
    /// through the private view last and unconditionally.
    #[test]
    fn tdx_shared_to_private_accepts_then_zeroes_the_private_view() {
        use Step::*;
        let (s, n) = record(Platform::Tdx, true, false);
        assert_eq!(
            &s[..n],
            &[FlushOld, LocalInvlpg, RemoteInvlpg, ChangeState, Accept, LocalInvlpg, RemoteInvlpg, ZeroNew].map(Some)
        );
        assert_eq!(s[n - 1], Some(ZeroNew));
        // Only TDX accepts, and only on the way to private.
        for (p, shared) in [(Platform::Tdx, true), (Platform::Snp, false), (Platform::Snp, true), (Platform::Sev, false)] {
            let (s, _) = record(p, true, shared);
            assert!(!s.contains(&Some(Accept)), "{p:?} shared={shared}");
        }
    }

    #[test]
    fn uninstalled_memory_and_mmio_bounds() {
        assert!(!private_device(0));
        assert!(!is_dma_ram(pptr(0x200000), 4096));
        let top = 16 << 30;
        assert_eq!(mmio_ptr(top - 4096, 4096, top), Some(pptr(top - 4096)));
        assert_eq!(mmio_ptr(top - 1, 2, top), None);
        assert_eq!(mmio_ptr(u64::MAX, 4096, top), None);
        assert_eq!(mmio_ptr(0, 0, top), None);
    }
}
