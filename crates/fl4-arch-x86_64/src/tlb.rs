//! Address-space switches and TLB invalidation, with PCIDs when the CPU has
//! them (DESIGN.md §3: CPUID.01H:ECX[17], INVPCID from CPUID.07H:EBX[10]).
//!
//! The PCID of an address space is its ASID (12 bits, as wide as a PCID),
//! so a core keeps the entries of address spaces it ran before. Each ASID
//! has an invalidation generation: invalidating an address space bumps it,
//! and a core that switches to the ASID after a bump flushes that PCID.
//! Cores running the address space at the time are shot down by IPI.
//!
//! A switch publishes the core's new ASID, then reads the generation; an
//! invalidation bumps the generation, then reads which cores run the ASID.
//! Both are sequentially consistent, so either the invalidating core sees
//! the switching one and interrupts it, or the switching core sees the new
//! generation and flushes. Without PCIDs every switch flushes, and the
//! same order keeps a switching core from missing an invalidation.
use crate::cpu::{self, cpuid};
use crate::percpu;
use core::sync::atomic::{fence, AtomicBool, AtomicU64, Ordering};

pub const ASIDS: usize = 4096;
const NOFLUSH: u64 = 1 << 63;
const CR4_PCIDE: u64 = 1 << 17;

static PCID: AtomicBool = AtomicBool::new(false);
static INVPCID: AtomicBool = AtomicBool::new(false);
static GEN: [AtomicU64; ASIDS] = [const { AtomicU64::new(0) }; ASIDS];

/// Detect PCIDs on the boot core; returns the CR4 bit to set on every core
/// (which must happen while CR3 names PCID 0, as it does at boot).
pub fn init() -> u64 {
    let pcid = cpuid(1, 0).ecx & (1 << 17) != 0;
    PCID.store(pcid, Ordering::Relaxed);
    INVPCID.store(pcid && cpuid(7, 0).ebx & (1 << 10) != 0, Ordering::Relaxed);
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
        asid & (ASIDS as u64 - 1)
    } else {
        0
    }
}

/// Run address space `cr3` (a page-table root's physical address) with
/// ASID `asid` on this core.
pub fn switch(cr3: u64, asid: u64) {
    let pc = percpu::get();
    let t = tag(asid);
    if pc.cr3 == cr3 | t && pc.asid == asid {
        // Still current: invalidations of it reached this core by IPI.
        return;
    }
    // Publish the ASID before looking at its generation (module comment).
    unsafe { core::ptr::write_volatile(&mut pc.asid, asid) };
    fence(Ordering::SeqCst);
    let mut flush = true;
    if pcid() {
        let g = GEN[t as usize].load(Ordering::SeqCst);
        flush = pc.tlb_seen[t as usize] != g;
        pc.tlb_seen[t as usize] = g;
    }
    cpu::write_cr3(cr3 | t | if flush { 0 } else { NOFLUSH });
    pc.cr3 = cr3 | t;
}

/// Every core flushes `asid` the next time it switches to it.
fn bump(asid: u64) {
    GEN[tag(asid) as usize].fetch_add(1, Ordering::SeqCst);
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
    let pc = percpu::get();
    if pc.asid == asid {
        cpu::invlpg(vaddr);
    } else if invpcid_available() {
        invpcid(0, tag(asid), vaddr);
    }
    cores_on(asid)
}

/// Invalidate all of `asid` here; returns the other cores running it.
pub fn invalidate_asid(asid: u64) -> u64 {
    bump(asid);
    let pc = percpu::get();
    if pc.asid == asid {
        cpu::write_cr3(pc.cr3);
    } else if invpcid_available() {
        invpcid(1, tag(asid), 0);
    }
    cores_on(asid)
}

/// Remote side of a shootdown.
pub fn remote_invalidate_page(asid: u64, vaddr: u64) {
    if percpu::get().asid == asid {
        cpu::invlpg(vaddr);
    }
}

pub fn remote_invalidate_asid(asid: u64) {
    let pc = percpu::get();
    if pc.asid == asid {
        cpu::write_cr3(pc.cr3);
    }
}

/// Other cores whose current address space is `asid`.
fn cores_on(asid: u64) -> u64 {
    fence(Ordering::SeqCst);
    let me = percpu::cpu_index();
    let mut m = 0;
    for c in 0..percpu::MAX_CPUS {
        if c != me && crate::smp::online_mask() & (1 << c) != 0 && unsafe { core::ptr::read_volatile(&percpu::get_for(c).asid) } == asid {
            m |= 1 << c;
        }
    }
    m
}
