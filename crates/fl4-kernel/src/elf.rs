//! The root task's ELF image: checking it and loading it (seL4
//! arch/x86/kernel/elf.c and boot_sys.c `load_boot_module`). Only physical
//! memory reads and writes through `pptr`, so xtask's host tests include
//! this file too.
use fl4_core::layout::pptr;

const PAGE: u64 = 4096;
const EHDR_SIZE: u64 = 64;
const PHDR_SIZE: u64 = 56;
const PT_LOAD: u32 = 1;

fn rd8(p: u64) -> u8 {
    unsafe { core::ptr::read_volatile(pptr(p) as *const u8) }
}

fn rd16(p: u64) -> u16 {
    unsafe { core::ptr::read_unaligned(pptr(p) as *const u16) }
}

fn rd32(p: u64) -> u32 {
    unsafe { core::ptr::read_unaligned(pptr(p) as *const u32) }
}

fn rd64(p: u64) -> u64 {
    unsafe { core::ptr::read_unaligned(pptr(p) as *const u64) }
}

/// Where a checked image goes: its loadable segments cover `[v_start,
/// v_end)` (page aligned).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Layout {
    pub v_start: u64,
    pub v_end: u64,
    pub entry: u64,
}

impl Layout {
    pub fn size(&self) -> u64 {
        self.v_end - self.v_start
    }
}

/// The program header `i` of the image at `elf`.
fn phdr(elf: u64, i: u64) -> u64 {
    elf + rd64(elf + 32) + i * rd16(elf + 54) as u64
}

/// Check the x86_64 ELF image in the `len` bytes at physical `elf`
/// (seL4 `elf_checkFile` and `load_boot_module`): the headers and every
/// loadable segment's file bytes lie inside the module, no segment has
/// more file than memory bytes or wraps, the segments end at or below
/// `v_limit` (user space, less what the boot frames after the image need)
/// and the entry point lies inside them.
pub fn check(elf: u64, len: u64, v_limit: u64) -> Option<Layout> {
    if len < EHDR_SIZE || rd32(elf) != 0x464c_457f || rd8(elf + 4) != 2 || rd8(elf + 5) != 1 || rd16(elf + 18) != 0x3e {
        return None;
    }
    let phoff = rd64(elf + 32);
    let phentsize = rd16(elf + 54) as u64;
    let phnum = rd16(elf + 56) as u64;
    if phentsize < PHDR_SIZE || phnum == 0 || phoff > len || phnum * phentsize > len - phoff {
        return None;
    }
    let mut lo = u64::MAX;
    let mut hi = 0;
    for i in 0..phnum {
        let ph = phdr(elf, i);
        if rd32(ph) != PT_LOAD {
            continue;
        }
        let offset = rd64(ph + 8);
        let vaddr = rd64(ph + 16);
        let filesz = rd64(ph + 32);
        let memsz = rd64(ph + 40);
        if offset > len || filesz > len - offset || filesz > memsz {
            return None;
        }
        let end = vaddr.checked_add(memsz)?;
        if memsz > 0 {
            lo = lo.min(vaddr);
            hi = hi.max(end);
        }
    }
    if lo >= hi || hi > v_limit {
        return None;
    }
    let v_start = lo & !(PAGE - 1);
    let v_end = hi.checked_add(PAGE - 1)? & !(PAGE - 1);
    if v_end > v_limit {
        return None;
    }
    let entry = rd64(elf + 24);
    if entry < v_start || entry >= v_end {
        return None;
    }
    Some(Layout { v_start, v_end, entry })
}

/// Copy the image `check` accepted as `l` to physical memory from `dest`
/// (page aligned): `[dest, dest + l.size())` is zeroed, then each loadable
/// segment's file bytes are copied to their place in it.
pub fn load(elf: u64, l: &Layout, dest: u64) {
    let off = dest.wrapping_sub(l.v_start);
    unsafe { core::ptr::write_bytes(pptr(dest) as *mut u8, 0, l.size() as usize) };
    for i in 0..rd16(elf + 56) as u64 {
        let ph = phdr(elf, i);
        if rd32(ph) != PT_LOAD || rd64(ph + 40) == 0 {
            continue;
        }
        let offset = rd64(ph + 8);
        let vaddr = rd64(ph + 16);
        let filesz = rd64(ph + 32);
        unsafe {
            core::ptr::copy(pptr(elf + offset) as *const u8, pptr(vaddr.wrapping_add(off)) as *mut u8, filesz as usize);
        }
    }
}
