//! Address-space switches and TLB invalidation, with PCIDs when the CPU has
//! them (DESIGN.md §3: CPUID.01H:ECX[17], INVPCID from CPUID.07H:EBX[10]).
//!
//! ASIDs are 20 bits and PCIDs 12, so each core caches ASIDs in PCIDs of
//! its own: PCID 1 + `slot(asid)` of a direct-mapped table of `SLOTS`
//! entries, each holding the ASID it last ran and the invalidation
//! generation it saw then. A core keeps the TLB entries of the address
//! spaces in its table. Invalidating an address space bumps a generation
//! shared by the ASIDs with the same `gen_index`; a core that switches to
//! an ASID its slot does not hold, or whose generation moved, flushes that
//! PCID. A shared generation only causes extra flushes. Cores running the
//! address space at the time are shot down by IPI.
//!
//! A switch publishes the core's new ASID, then reads the generation; an
//! invalidation bumps the generation, then reads which cores run the ASID.
//! Both are sequentially consistent, so either the invalidating core sees
//! the switching one and interrupts it, or the switching core sees the new
//! generation and flushes. Without PCIDs every switch flushes, and the
//! same order keeps a switching core from missing an invalidation.
//!
//! The memory this takes does not depend on the number of ASIDs: `GENS`
//! words, and `SLOTS` entries per core.
use crate::cpu::{self, cpuid};
use crate::percpu;
use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};

/// PCIDs per core (PCID 0 is the kernel's).
pub const SLOTS: usize = 512;
const GENS: usize = 4096;
const NOFLUSH: u64 = 1 << 63;
const CR4_PCIDE: u64 = 1 << 17;

static PCID: AtomicBool = AtomicBool::new(false);
static SKIM: AtomicBool = AtomicBool::new(false);
static INVPCID: AtomicBool = AtomicBool::new(false);
static GEN: [AtomicU64; GENS] = [const { AtomicU64::new(0) }; GENS];

/// A PCID of this core: the ASID it holds and the generation it saw.
#[derive(Clone, Copy)]
pub struct Slot {
    asid: u64,
    seen: u64,
}

impl Slot {
    pub const EMPTY: Slot = Slot { asid: u64::MAX, seen: 0 };

    /// Run `asid`, whose generation is `g`, on this PCID; returns whether
    /// the PCID must be flushed first.
    fn claim(&mut self, asid: u64, g: u64) -> bool {
        let flush = self.asid != asid || self.seen != g;
        *self = Slot { asid, seen: g };
        flush
    }
}

/// ASIDs of one pool (the low 9 bits) get different slots; the pool
/// number is folded in so that pools' first ASIDs do not all collide.
fn slot(asid: u64) -> usize {
    ((asid ^ (asid >> 9)) as usize) & (SLOTS - 1)
}

fn gen_index(asid: u64) -> usize {
    ((asid ^ (asid >> 12)) as usize) & (GENS - 1)
}

/// Detect PCIDs on the boot core; returns the CR4 bit to set on every core
/// (which must happen while CR3 names PCID 0, as it does at boot). With the
/// skim window (spec.rs) the kernel runs on its own tables, so it can
/// invalidate a user PCID only with INVPCID: without it, PCIDs stay off.
pub fn init(skim: bool) -> u64 {
    SKIM.store(skim, Ordering::Relaxed);
    let invpcid = cpuid(7, 0).ebx & (1 << 10) != 0;
    let pcid = cpuid(1, 0).ecx & (1 << 17) != 0 && (!skim || invpcid);
    PCID.store(pcid, Ordering::Relaxed);
    INVPCID.store(pcid && invpcid, Ordering::Relaxed);
    if pcid {
        CR4_PCIDE
    } else {
        0
    }
}

pub fn pcid() -> bool {
    PCID.load(Ordering::Relaxed)
}

pub fn invpcid_available() -> bool {
    INVPCID.load(Ordering::Relaxed)
}

fn tag(asid: u64) -> u64 {
    if pcid() {
        slot(asid) as u64 + 1
    } else {
        0
    }
}

/// This core's PCID holds `asid`'s TLB entries, if any are cached.
fn holds(asid: u64) -> bool {
    pcid() && percpu::get().pcids[slot(asid)].get().asid == asid
}

/// Run address space `cr3` (a page-table root's physical address) with
/// ASID `asid` on this core.
pub fn switch(cr3: u64, asid: u64) {
    let pc = percpu::get();
    let t = tag(asid);
    if pc.cr3.get() == cr3 | t && percpu::current_asid(percpu::cpu_index()) == asid {
        // Still current: invalidations of it reached this core by IPI.
        return;
    }
    // Publish the ASID before looking at its generation (module comment).
    percpu::publish_asid(asid);
    let mut flush = true;
    if pcid() {
        let g = GEN[gen_index(asid)].load(Ordering::SeqCst);
        let cell = &pc.pcids[slot(asid)];
        let mut slot = cell.get();
        flush = slot.claim(asid, g);
        cell.set(slot);
    }
    let v = cr3 | t | if flush { 0 } else { NOFLUSH };
    pc.cr3.set(cr3 | t);
    if SKIM.load(Ordering::Relaxed) {
        // The kernel stays on its own tables; the exit loads these.
        pc.exit_cr3.set(v);
    } else {
        cpu::write_cr3(v);
    }
}

/// The CR3 value an exit to user code loads with the skim window, which
/// it then resets so the next exit does not flush again.
pub fn take_exit_cr3() -> u64 {
    let pc = percpu::get();
    let v = pc.exit_cr3.get();
    pc.exit_cr3.set(pc.cr3.get() | if pcid() { NOFLUSH } else { 0 });
    v
}

/// The kernel's CR3 value (PCID 0, whose mappings never change).
pub fn kernel_cr3(root: u64) -> u64 {
    root | if pcid() { NOFLUSH } else { 0 }
}

pub fn skim() -> bool {
    SKIM.load(Ordering::Relaxed)
}

/// Every core flushes `asid` the next time it switches to it.
fn bump(asid: u64) {
    GEN[gen_index(asid)].fetch_add(1, Ordering::SeqCst);
}

/// INVPCID: type 0 (one address in one PCID) or 1 (one PCID).
fn invpcid(kind: u64, pcid: u64, addr: u64) {
    let desc: [u64; 2] = [pcid, addr];
    unsafe { core::arch::asm!("invpcid {}, [{}]", in(reg) kind, in(reg) desc.as_ptr(), options(nostack, preserves_flags)) }
}

/// Invalidate `vaddr` in `asid` here; returns the other cores running
/// `asid`, which the caller shoots down. Called after the page tables
/// changed.
pub fn invalidate_page(asid: u64, vaddr: u64) -> u64 {
    bump(asid);
    local_invalidate_page(asid, vaddr);
    cores_on(asid)
}

/// With the skim window the kernel runs on its own tables: a user PCID is
/// reached with INVPCID, and without PCIDs every exit's CR3 load flushes.
/// A PCID that holds another ASID has no entries for this one (taking it
/// flushed them).
fn local_invalidate_page(asid: u64, vaddr: u64) {
    if skim() {
        if holds(asid) {
            invpcid(0, tag(asid), vaddr);
        }
    } else if percpu::current_asid(percpu::cpu_index()) == asid {
        cpu::invlpg(vaddr);
    } else if invpcid_available() && holds(asid) {
        invpcid(0, tag(asid), vaddr);
    }
}

fn local_invalidate_asid(asid: u64) {
    let pc = percpu::get();
    if skim() {
        if holds(asid) {
            invpcid(1, tag(asid), 0);
        }
    } else if percpu::current_asid(percpu::cpu_index()) == asid {
        cpu::write_cr3(pc.cr3.get());
    } else if invpcid_available() && holds(asid) {
        invpcid(1, tag(asid), 0);
    }
}

/// Invalidate all of `asid` here; returns the other cores running it.
pub fn invalidate_asid(asid: u64) -> u64 {
    bump(asid);
    local_invalidate_asid(asid);
    cores_on(asid)
}

/// Remote side of a shootdown.
pub fn remote_invalidate_page(asid: u64, vaddr: u64) {
    if percpu::current_asid(percpu::cpu_index()) == asid {
        local_invalidate_page(asid, vaddr);
    }
}

/// If the ASID was deleted, this core still runs its tables, which can be
/// reused once the call returns: the exit sets the address space again
/// from the current thread's VSpace cap.
pub fn remote_invalidate_asid(asid: u64) {
    if percpu::current_asid(percpu::cpu_index()) == asid {
        local_invalidate_asid(asid);
        percpu::get().vspace_stale.set(true);
    }
}

/// Other cores whose current address space is `asid`.
fn cores_on(asid: u64) -> u64 {
    let me = percpu::cpu_index();
    let mut m = 0;
    for c in 0..percpu::MAX_CPUS {
        if c != me && crate::smp::online_mask() & (1 << c) != 0 && percpu::current_asid(c) == asid {
            m |= 1 << c;
        }
    }
    m
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_pool_and_the_first_asids_of_pools_get_distinct_slots() {
        let base = 77 << 9;
        let mut seen = [false; SLOTS];
        for i in 0..512 {
            assert!(!core::mem::replace(&mut seen[slot(base + i)], true));
        }
        let mut seen = [false; SLOTS];
        for p in 0..512 {
            assert!(!core::mem::replace(&mut seen[slot(p << 9)], true));
        }
        assert!((0..1 << 20).all(|a| slot(a) < SLOTS && gen_index(a) < GENS));
    }

    #[test]
    fn a_slot_flushes_for_a_new_asid_or_generation() {
        let mut e = Slot::EMPTY;
        assert!(e.claim(0, 0));
        assert!(e.claim(5, 0));
        assert!(!e.claim(5, 0));
        assert!(e.claim(5, 1));
        assert!(!e.claim(5, 1));
        assert!(e.claim(5 + 512 * 512, 1));
        assert!(e.claim(5, 1));
    }
}
