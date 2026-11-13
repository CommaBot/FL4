//! The kernel address space: the physical-memory window at PPTR_BASE and
//! the kernel image at KERNEL_OFFSET, both in the top PML4 slot (so every
//! user address space shares them through copyGlobalMappings). 1 GiB pages
//! when the CPU has them, 2 MiB pages otherwise.
use core::cell::UnsafeCell;
use fl4_arch_x86_64::cpu::{cpuid, write_cr3};
use fl4_core::layout::{PADDR_TOP, PPTR_BASE};

pub const KERNEL_OFFSET: u64 = 0xffff_ffff_8000_0000;
/// With 2 MiB pages the window covers at most this much physical memory.
pub const SMALL_WINDOW_GIB: usize = 16;

const P: u64 = 1;
const RW: u64 = 2;
const PS: u64 = 1 << 7;
const G: u64 = 1 << 8;
const NX: u64 = 1 << 63;

#[repr(C, align(4096))]
struct Table([u64; 512]);

struct Tables {
    pml4: Table,
    pdpt: Table,
    pds: [Table; SMALL_WINDOW_GIB],
    /// Application processors start on this: the kernel's mappings plus
    /// an identity map of the first GiB, for the trampoline.
    ap_pml4: Table,
    ap_pdpt: Table,
    ap_pd: Table,
    /// The skim window (spec.rs): the kernel half of every user address
    /// space when the CPU needs it, mapping the kernel image only.
    skim_pml4: Table,
    skim_pdpt: Table,
    skim_pd: Table,
    skim_pts: [Table; SKIM_PTS],
}

/// Page tables for the skim window: room for a 16 MiB kernel image.
const SKIM_PTS: usize = 8;

struct Cell(UnsafeCell<Tables>);
unsafe impl Sync for Cell {}

static TABLES: Cell = Cell(UnsafeCell::new(Tables {
    pml4: Table([0; 512]),
    pdpt: Table([0; 512]),
    pds: [const { Table([0; 512]) }; SMALL_WINDOW_GIB],
    ap_pml4: Table([0; 512]),
    ap_pdpt: Table([0; 512]),
    ap_pd: Table([0; 512]),
    skim_pml4: Table([0; 512]),
    skim_pdpt: Table([0; 512]),
    skim_pd: Table([0; 512]),
    skim_pts: [const { Table([0; 512]) }; SKIM_PTS],
}));

/// Physical address of something in the kernel image.
pub fn image_paddr(v: u64) -> u64 {
    v - KERNEL_OFFSET
}

pub fn has_huge_pages() -> bool {
    cpuid(0x8000_0001, 0).edx & (1 << 26) != 0
}

/// Build the tables and switch to them. Returns the PML4's address in the
/// window (what fl4-core uses as the kernel root) and the top of the
/// physical memory the window maps. With the skim window the window's
/// mappings are not global, so none survives a switch to user tables.
pub fn init(nx: bool, skim: bool) -> (u64, u64) {
    let t = unsafe { &mut *TABLES.0.get() };
    let nx_bit = if nx { NX } else { 0 };
    let wg = if skim { 0 } else { G };
    let window_top;
    if has_huge_pages() {
        let n = (PADDR_TOP >> 30) as usize;
        for i in 0..n {
            t.pdpt.0[i] = ((i as u64) << 30) | P | RW | PS | wg | nx_bit;
        }
        // The image's alias of the low 2 GiB: global only without the skim
        // window, where it must not outlive a switch to user tables either.
        t.pdpt.0[510] = P | RW | PS | wg;
        t.pdpt.0[511] = (1 << 30) | P | RW | PS | wg;
        window_top = PADDR_TOP;
    } else {
        for (g, pd) in t.pds.iter_mut().enumerate() {
            for (j, e) in pd.0.iter_mut().enumerate() {
                *e = ((g as u64) << 30) | ((j as u64) << 21) | P | RW | PS | wg;
            }
        }
        for g in 0..SMALL_WINDOW_GIB {
            t.pdpt.0[g] = image_paddr(&t.pds[g] as *const Table as u64) | P | RW;
        }
        t.pdpt.0[510] = image_paddr(&t.pds[0] as *const Table as u64) | P | RW;
        t.pdpt.0[511] = image_paddr(&t.pds[1] as *const Table as u64) | P | RW;
        window_top = (SMALL_WINDOW_GIB as u64) << 30;
    }
    t.pml4.0[511] = image_paddr(&t.pdpt as *const Table as u64) | P | RW;
    let root = image_paddr(&t.pml4 as *const Table as u64);
    write_cr3(root);
    (root + PPTR_BASE, window_top)
}

/// The skim window's kernel half: the image's pages at KERNEL_OFFSET, from
/// `start` to `end` (physical). Returns the template PML4's address in the
/// window, which user address spaces copy their kernel half from.
pub fn init_skim(start: u64, end: u64) -> u64 {
    let t = unsafe { &mut *TABLES.0.get() };
    let first = start & !0xfff;
    let pages = (((end + 0xfff) & !0xfff) - first) / 4096;
    for i in 0..pages {
        let pa = first + i * 4096;
        let pd_i = (pa >> 21) as usize;
        let pt_i = pd_i - (first >> 21) as usize;
        assert!(pt_i < SKIM_PTS && pd_i < 512, "FL4: kernel image too large for the skim window");
        t.skim_pts[pt_i].0[((pa >> 12) & 511) as usize] = pa | P | RW | G;
        t.skim_pd.0[pd_i] = image_paddr(&t.skim_pts[pt_i] as *const Table as u64) | P | RW;
    }
    t.skim_pdpt.0[510] = image_paddr(&t.skim_pd as *const Table as u64) | P | RW;
    t.skim_pml4.0[511] = image_paddr(&t.skim_pdpt as *const Table as u64) | P | RW;
    image_paddr(&t.skim_pml4 as *const Table as u64) + PPTR_BASE
}

pub fn root_paddr() -> u64 {
    let t = unsafe { &*TABLES.0.get() };
    image_paddr(&t.pml4 as *const Table as u64)
}

/// Physical address of the page table application processors start on.
pub fn ap_boot_root() -> u64 {
    let t = unsafe { &mut *TABLES.0.get() };
    for (j, e) in t.ap_pd.0.iter_mut().enumerate() {
        *e = ((j as u64) << 21) | P | RW | PS;
    }
    t.ap_pdpt.0[0] = image_paddr(&t.ap_pd as *const Table as u64) | P | RW;
    t.ap_pml4.0[0] = image_paddr(&t.ap_pdpt as *const Table as u64) | P | RW;
    t.ap_pml4.0[511] = t.pml4.0[511];
    image_paddr(&t.ap_pml4 as *const Table as u64)
}
