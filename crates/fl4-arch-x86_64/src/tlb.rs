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
static SKIM: AtomicBool = AtomicBool::new(false);
static INVPCID: AtomicBool = AtomicBool::new(false);
static GEN: [AtomicU64; ASIDS] = [const { AtomicU64::new(0) }; ASIDS];

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
    // Publish the ASID before looking at its generation (module comment);
    // with one core there is no one to race with.
    unsafe { core::ptr::write_volatile(&mut pc.asid, asid) };
    if crate::smp::multi() {
        fence(Ordering::SeqCst);
    }
    let mut flush = true;
    if pcid() {
        let g = GEN[t as usize].load(Ordering::SeqCst);
        flush = pc.tlb_seen[t as usize] != g;
        pc.tlb_seen[t as usize] = g;
    }
    let v = cr3 | t | if flush { 0 } else { NOFLUSH };
    pc.cr3 = cr3 | t;
    if SKIM.load(Ordering::Relaxed) {
        // The kernel stays on its own tables; the exit loads these.
        pc.exit_cr3 = v;
    } else {
        cpu::write_cr3(v);
    }
}

/// The CR3 value an exit to user code loads with the skim window, which
/// it then resets so the next exit does not flush again.
pub fn take_exit_cr3() -> u64 {
    let pc = percpu::get();
    let v = pc.exit_cr3;
    pc.exit_cr3 = pc.cr3 | if pcid() { NOFLUSH } else { 0 };
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
    local_invalidate_page(asid, vaddr);
    cores_on(asid)
}

/// With the skim window the kernel runs on its own tables: a user PCID is
/// reached with INVPCID, and without PCIDs every exit's CR3 load flushes.
fn local_invalidate_page(asid: u64, vaddr: u64) {
    let pc = percpu::get();
    if skim() {
        if pcid() {
            invpcid(0, tag(asid), vaddr);
        }
    } else if pc.asid == asid {
        cpu::invlpg(vaddr);
    } else if invpcid_available() {
        invpcid(0, tag(asid), vaddr);
    }
}

fn local_invalidate_asid(asid: u64) {
    let pc = percpu::get();
    if skim() {
        if pcid() {
            invpcid(1, tag(asid), 0);
        }
    } else if pc.asid == asid {
        cpu::write_cr3(pc.cr3);
    } else if invpcid_available() {
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
    if percpu::get().asid == asid {
        local_invalidate_page(asid, vaddr);
    }
}

pub fn remote_invalidate_asid(asid: u64) {
    if percpu::get().asid == asid {
        local_invalidate_asid(asid);
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
