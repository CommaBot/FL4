//! The kernel's own page tables (TTBR1): the kernel region at
//! `KERNEL_VBASE` with W^X permissions, the window over RAM at
//! `PPTR_BASE`, and device mappings above the window. Tables come from a
//! pool in the image. Also the identity map application processors start
//! on, and the empty user table of threads without an address space.
use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicBool, Ordering};
use fl4_arch_aarch64::{cpu, mmu};
use fl4_bootinfo::{KERNEL_REGION_TOP, KERNEL_VBASE};
use fl4_core::layout::{PPTR_BASE, PPTR_TOP};
use fl4_abi::consts::HIGH_VSPACE_BASE;
use fl4_core::vspace::{ATTR_DEVICE_NGNRNE, ATTR_NORMAL};

const PAGE: u64 = 4096;
const POOL_PAGES: usize = 768;

const D_VALID: u64 = 1;
const D_TABLE: u64 = 1 << 1;
const D_PAGE: u64 = 1 << 1;
const D_AF: u64 = 1 << 10;
const D_SH_INNER: u64 = 3 << 8;
/// AP[2:1] = 2: read-only at EL1, nothing at EL0.
const D_AP_RO: u64 = 2 << 6;
const D_PXN: u64 = 1 << 53;
const D_UXN: u64 = 1 << 54;
const ADDR_MASK: u64 = 0x0000_ffff_ffff_f000;

/// Device mappings occupy L0[510] below the kernel image (`KERNEL_VBASE`),
/// keeping L0[511] (`HIGH_VSPACE_BASE..`) completely empty in the kernel's
/// TTBR1 tables.
const DEVICE_BASE: u64 = PPTR_TOP;
const DEVICE_TOP: u64 = KERNEL_VBASE;
const _: () = assert!(DEVICE_TOP <= HIGH_VSPACE_BASE);
// The window ends where level-0 entry 510 starts; the devices and the
// image are in entry 510, the region ending at entry 511's start, the
// first address of the level-0 entry the high window has.
const _: () = assert!((PPTR_TOP >> 39) & 511 == 510 && PPTR_TOP & ((1 << 39) - 1) == 0);
const _: () = assert!((KERNEL_VBASE >> 39) & 511 == 510);
const _: () = assert!((KERNEL_REGION_TOP >> 39) & 511 == 511 && KERNEL_REGION_TOP & ((1 << 39) - 1) == 0);
const _: () = assert!(KERNEL_REGION_TOP <= HIGH_VSPACE_BASE && (HIGH_VSPACE_BASE >> 39) & 511 == 511);

#[repr(C, align(8192))]
struct Pool(UnsafeCell<[[u64; 512]; POOL_PAGES]>);
unsafe impl Sync for Pool {}
static POOL: Pool = Pool(UnsafeCell::new([[0; 512]; POOL_PAGES]));

struct State {
    used: usize,
    /// Kernel-region physical base and length.
    region_pa: u64,
    region_len: u64,
    root: u64,
    ident: u64,
    hyp_ident: u64,
    empty: u64,
    empty_s2: u64,
    next_device: u64,
    /// What the processor can address (and the window's RAM, none of
    /// which is a device).
    pa_top: u64,
}

struct Cell(UnsafeCell<State>);
unsafe impl Sync for Cell {}
static ST: Cell = Cell(UnsafeCell::new(State { used: 0, region_pa: 0, region_len: 0, root: 0, ident: 0, hyp_ident: 0, empty: 0, empty_s2: 0, next_device: DEVICE_BASE, pa_top: 0 }));

/// The kernel's level-0 table and the level-1 table of its image (level-0
/// entry 510) take no new entries once user code can run: an
/// `ArmHighVSpace` is made as a copy of the level-0 one (fl4-core aarch64
/// `vspace::init_high_vspace`), which a later entry would be missing from.
static FROZEN: AtomicBool = AtomicBool::new(false);

/// After boot's last kernel mapping, before the root task runs. Level-0
/// entry 511 of the kernel's tables is still invalid: the high window's
/// TLB bookkeeping (fl4-arch-aarch64 mmu_switch.rs) counts on the kernel's
/// TTBR1 caching nothing there.
pub fn freeze_kernel_tables() {
    let s = st();
    let e = unsafe { (entry(s.root, KERNEL_REGION_TOP, 39) as *const u64).read_volatile() };
    if e != 0 {
        crate::fail("kernel level-0 entry 511 in use");
    }
    FROZEN.store(true, Ordering::Release);
}

/// A new entry at level 0 (`shift` 39) of the kernel's tables, or in the
/// level-1 table of the image: never once frozen.
fn check_not_frozen(s: &State, table: u64, shift: u64) {
    if !FROZEN.load(Ordering::Acquire) {
        return;
    }
    let top = unsafe { (entry(s.root, KERNEL_VBASE, 39) as *const u64).read_volatile() };
    let l1_top = if top & D_VALID != 0 { image_va_of(s, top & ADDR_MASK) } else { 0 };
    assert!(!(table == s.root && shift == 39), "new kernel level-0 entry after the tables were frozen");
    assert!(!(table == l1_top && shift == 30), "new kernel top level-1 entry after the tables were frozen");
}

/// The boot state. Only the public entry points take it, once each, and
/// pass it down: no two references to it are live at once (none of them
/// calls another).
fn st() -> &'static mut State {
    unsafe { &mut *ST.0.get() }
}

extern "C" {
    static __text_end: u8;
    static __rodata_end: u8;
}

/// A kernel-image virtual address as physical (valid before and after the
/// switch: the region is mapped linearly).
pub fn image_pa(va: u64) -> u64 {
    image_pa_of(st(), va)
}

fn image_pa_of(s: &State, va: u64) -> u64 {
    va - KERNEL_VBASE + s.region_pa
}

fn alloc_table(s: &mut State) -> u64 {
    if s.used == POOL_PAGES {
        crate::fail("out of kernel page tables");
    }
    let p = unsafe { (*POOL.0.get())[s.used].as_mut_ptr() as u64 };
    s.used += 1;
    unsafe { core::ptr::write_bytes(p as *mut u8, 0, PAGE as usize) };
    p
}

fn entry(table: u64, va: u64, shift: u64) -> *mut u64 {
    (table + ((va >> shift) & 511) * 8) as *mut u64
}

/// The table below `table`'s entry for `va` at `shift`, made if absent.
fn next(s: &mut State, table: u64, va: u64, shift: u64) -> u64 {
    let e = entry(table, va, shift);
    let v = unsafe { e.read_volatile() };
    if v & D_VALID != 0 {
        if v & D_TABLE == 0 {
            crate::fail("kernel mapping overlaps a block");
        }
        return image_va_of(s, v & ADDR_MASK);
    }
    if table == s.root || shift == 30 {
        check_not_frozen(s, table, shift);
    }
    let t = alloc_table(s);
    unsafe { e.write_volatile(image_pa_of(s, t) | D_VALID | D_TABLE) };
    t
}

/// A pool table's virtual address from its physical one.
fn image_va_of(s: &State, pa: u64) -> u64 {
    pa - s.region_pa + KERNEL_VBASE
}

/// Map [va, va + len) to pa with descriptor attributes `attr`, using
/// 1 GiB and 2 MiB blocks where alignment allows.
fn map(s: &mut State, root: u64, va: u64, pa: u64, len: u64, attr: u64) {
    let mut off = 0;
    while off < len {
        let v = va + off;
        // Output address bits only, whatever the caller passed.
        let p = (pa + off) & ADDR_MASK;
        let left = len - off;
        let l1 = next(s, root, v, 39);
        if v & ((1 << 30) - 1) == 0 && p & ((1 << 30) - 1) == 0 && left >= 1 << 30 {
            if root == s.root {
                check_not_frozen(s, l1, 30);
            }
            unsafe { entry(l1, v, 30).write_volatile(p | attr | D_VALID) };
            off += 1 << 30;
            continue;
        }
        let l2 = next(s, l1, v, 30);
        if v & ((1 << 21) - 1) == 0 && p & ((1 << 21) - 1) == 0 && left >= 1 << 21 {
            unsafe { entry(l2, v, 21).write_volatile(p | attr | D_VALID) };
            off += 1 << 21;
            continue;
        }
        let l3 = next(s, l2, v, 21);
        unsafe { entry(l3, v, 12).write_volatile(p | attr | D_VALID | D_PAGE) };
        off += PAGE;
    }
}

fn normal() -> u64 {
    (ATTR_NORMAL << 2) | D_SH_INNER | D_AF
}

/// Build the kernel's tables: the kernel region with W^X, and the window
/// over `ram` (physical ranges). Device mappings stay below `pa_top`.
/// Returns the TTBR1 value. Runs on the loader's boot tables.
pub fn init(region_pa: u64, region_len: u64, ram: &[(u64, u64)], pa_top: u64) -> u64 {
    let s = st();
    let text_end = unsafe { &__text_end as *const u8 as u64 } - KERNEL_VBASE;
    let ro_end = unsafe { &__rodata_end as *const u8 as u64 } - KERNEL_VBASE;
    // The loader checked it (fl4-bootinfo `kernel_region_fits`); the
    // region must stay in level-0 entry 510 and hold the image.
    if !fl4_bootinfo::kernel_region_fits(region_len) || region_len < ro_end {
        crate::fail("kernel region past level-0 entry 510");
    }
    s.region_pa = region_pa;
    s.region_len = region_len;
    s.pa_top = pa_top;
    let root = alloc_table(s);
    s.root = root;
    // Text: read-only, executable at EL1. Read-only data. Everything else
    // in the region (data, bss, the loader's tables, the boot record):
    // read-write, never executable.
    map(s, root, KERNEL_VBASE, region_pa, text_end, normal() | D_AP_RO | D_UXN);
    map(s, root, KERNEL_VBASE + text_end, region_pa + text_end, ro_end - text_end, normal() | D_AP_RO | D_UXN | D_PXN);
    map(s, root, KERNEL_VBASE + ro_end, region_pa + ro_end, region_len - ro_end, normal() | D_UXN | D_PXN);
    for &(start, end) in ram {
        if end <= start || end > PPTR_TOP - PPTR_BASE {
            continue;
        }
        map(s, root, PPTR_BASE + start, start, end - start, normal() | D_UXN | D_PXN);
        if !mmu::add_window_range(start, end) {
            crate::fail("too many RAM ranges for the window");
        }
    }
    // The identity map of the kernel region, for cores starting up, and
    // the empty table of threads without an address space.
    let ident = alloc_table(s);
    map(s, ident, region_pa, region_pa, region_len, normal());
    s.ident = ident;
    // In EL2 nVHE mode, build an identity map for EL2 (TTBR0_EL2, E2H=0),
    // with the same W^X split as TTBR1_EL1: text read-only and executable,
    // read-only data read-only and never executable, the rest of the region
    // (data with `HypCpu`, bss, the loader's tables) and all other RAM
    // (`Vcpu`/`Regs` objects) read-write and never executable. EL2 code
    // (boot.S, hyp_nvhe.S) writes only `HypCpu` and those objects. All
    // Normal WB Inner-Shareable, matching TTBR1_EL1 for cache coherency.
    // The EL2 regime has one privilege level: AP[2:1] = 0b01 is RW, 0b11
    // RO; bit 54 is XN.
    if cpu::is_el2_nvhe() {
        const D_AP_RW_EL2: u64 = 1 << 6;
        const D_AP_RO_EL2: u64 = 3 << 6;
        let hyp = alloc_table(s);
        let r_start = region_pa;
        let r_end = region_pa + region_len;
        map(s, hyp, r_start, r_start, text_end, normal() | D_AP_RO_EL2);
        map(s, hyp, r_start + text_end, r_start + text_end, ro_end - text_end, normal() | D_AP_RO_EL2 | D_UXN);
        map(s, hyp, r_start + ro_end, r_start + ro_end, region_len - ro_end, normal() | D_AP_RW_EL2 | D_UXN);
        let ram_attr = normal() | D_AP_RW_EL2 | D_UXN;
        for &(start, end) in ram {
            if end <= start || end > PPTR_TOP - PPTR_BASE {
                continue;
            }
            if start < r_start {
                let hi = end.min(r_start);
                map(s, hyp, start, start, hi - start, ram_attr);
            }
            if end > r_end {
                let lo = start.max(r_end);
                map(s, hyp, lo, lo, end - lo, ram_attr);
            }
        }
        s.hyp_ident = hyp;
    }
    s.empty = alloc_table(s);
    // 8 KiB-aligned empty Stage-2 root (two contiguous zeroed 4 KiB pages).
    if s.used & 1 != 0 {
        let _ = alloc_table(s);
    }
    let s2 = alloc_table(s);
    let _ = alloc_table(s);
    s.empty_s2 = s2;
    cpu::dsb_ishst();
    image_pa_of(s, root)
}

/// Switch to the kernel's tables.
pub fn activate(ttbr1: u64) {
    fl4_arch_aarch64::msr!("ttbr1_el1", ttbr1);
    let s = st();
    fl4_arch_aarch64::msr!("ttbr0_el1", image_pa_of(s, s.empty));
    cpu::isb();
    mmu::invalidate_all();
}

/// The kernel's TTBR1 level-0 table and the level-1 table of its entry 510
/// (`KERNEL_VBASE`: the devices and the kernel image), as the kernel
/// reaches them; a new `ArmHighVSpace` copies the level-0 one.
pub fn kernel_tables() -> (u64, u64) {
    let s = st();
    let e = unsafe { (entry(s.root, KERNEL_VBASE, 39) as *const u64).read_volatile() };
    if e & D_VALID == 0 || e & D_TABLE == 0 {
        crate::fail("no kernel level-1 table");
    }
    (s.root, image_va_of(s, e & ADDR_MASK))
}

/// TTBR0 for application processors starting up.
pub fn ident_ttbr0() -> u64 {
    let s = st();
    image_pa_of(s, s.ident)
}

/// TTBR0_EL2 identity map for the EL2 nVHE Hyp switch stub.
pub fn hyp_ttbr0() -> u64 {
    let s = st();
    image_pa_of(s, s.hyp_ident)
}

/// The empty user table, as a kernel window address (`ks::KERNEL_ROOT`).
pub fn empty_root() -> u64 {
    let s = st();
    PPTR_BASE + image_pa_of(s, s.empty)
}

/// Physical address of the empty 8 KiB Stage-2 root.
pub fn empty_s2_root_pa() -> u64 {
    let s = st();
    image_pa_of(s, s.empty_s2)
}

/// Map `len` bytes of device registers at `pa`; returns their address.
/// None for registers past what the processor can address (a descriptor
/// with them would have reserved bits set) or on RAM the window maps as
/// normal memory (two mappings with different memory types).
pub fn map_device(pa: u64, len: u64) -> Option<u64> {
    let s = st();
    let (base, size) = crate::bootmem::device_pages(pa, len, s.pa_top)?;
    if mmu::overlaps_window(base, size) {
        return None;
    }
    // Keep each mapping 64 KiB aligned.
    let (va, end) = match crate::bootmem::device_va(s.next_device, size, DEVICE_TOP) {
        Some(r) => r,
        None => crate::fail("out of device mappings"),
    };
    s.next_device = end;
    let root = s.root;
    map(s, root, va, base, size, (ATTR_DEVICE_NGNRNE << 2) | D_AF | D_UXN | D_PXN);
    cpu::dsb_ishst();
    cpu::isb();
    Some(va + (pa - base))
}
