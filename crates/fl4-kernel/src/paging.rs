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
}

struct Cell(UnsafeCell<Tables>);
unsafe impl Sync for Cell {}

static TABLES: Cell = Cell(UnsafeCell::new(Tables {
    pml4: Table([0; 512]),
    pdpt: Table([0; 512]),
    pds: [const { Table([0; 512]) }; SMALL_WINDOW_GIB],
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
/// physical memory the window maps.
pub fn init(nx: bool) -> (u64, u64) {
    let t = unsafe { &mut *TABLES.0.get() };
    let nx_bit = if nx { NX } else { 0 };
    let window_top;
    if has_huge_pages() {
        let n = (PADDR_TOP >> 30) as usize;
        for i in 0..n {
            t.pdpt.0[i] = ((i as u64) << 30) | P | RW | PS | G | nx_bit;
        }
        t.pdpt.0[510] = P | RW | PS | G;
        t.pdpt.0[511] = (1 << 30) | P | RW | PS | G;
        window_top = PADDR_TOP;
    } else {
        for (g, pd) in t.pds.iter_mut().enumerate() {
            for (j, e) in pd.0.iter_mut().enumerate() {
                *e = ((g as u64) << 30) | ((j as u64) << 21) | P | RW | PS | G;
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

pub fn root_paddr() -> u64 {
    let t = unsafe { &*TABLES.0.get() };
    image_paddr(&t.pml4 as *const Table as u64)
}
