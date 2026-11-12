//! Multiboot 1 and 2 boot information, and loading the root task's ELF
//! image (seL4 arch/x86/kernel/boot_sys.c).
use fl4_core::layout::pptr;

pub const MB1_MAGIC: u32 = 0x2bad_b002;
pub const MB2_MAGIC: u32 = 0x36d7_6289;
pub const MAX_MMAP: usize = 50;
pub const MAX_MODULES: usize = 4;

#[derive(Clone, Copy, Default)]
pub struct MemRegion {
    pub base: u64,
    pub len: u64,
    pub ty: u32,
}

pub struct BootInfo {
    pub mmap: [MemRegion; MAX_MMAP],
    pub n_mmap: usize,
    pub modules: [(u64, u64); MAX_MODULES],
    pub n_modules: usize,
    /// RSDP copied from Multiboot 2 tags, if any.
    pub rsdp: Option<u64>,
}

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

pub fn parse(magic: u32, info: u64) -> Option<BootInfo> {
    let mut b = BootInfo { mmap: [MemRegion::default(); MAX_MMAP], n_mmap: 0, modules: [(0, 0); MAX_MODULES], n_modules: 0, rsdp: None };
    if magic == MB1_MAGIC {
        let flags = rd32(info);
        if flags & (1 << 3) != 0 {
            let n = rd32(info + 20) as u64;
            let addr = rd32(info + 24) as u64;
            for i in 0..n.min(MAX_MODULES as u64) {
                let m = addr + 16 * i;
                b.modules[b.n_modules] = (rd32(m) as u64, rd32(m + 4) as u64);
                b.n_modules += 1;
            }
        }
        if flags & (1 << 6) == 0 {
            return None;
        }
        let len = rd32(info + 44) as u64;
        let addr = rd32(info + 48) as u64;
        let mut p = addr;
        while p < addr + len && b.n_mmap < MAX_MMAP {
            let size = rd32(p) as u64;
            b.mmap[b.n_mmap] = MemRegion { base: rd64(p + 4), len: rd64(p + 12), ty: rd32(p + 20) };
            b.n_mmap += 1;
            p += size + 4;
        }
        Some(b)
    } else if magic == MB2_MAGIC {
        let total = rd32(info) as u64;
        let mut t = info + 8;
        while t + 8 <= info + total {
            let ty = rd32(t);
            let size = rd32(t + 4) as u64;
            match ty {
                0 => break,
                3 => {
                    if b.n_modules < MAX_MODULES {
                        b.modules[b.n_modules] = (rd32(t + 8) as u64, rd32(t + 12) as u64);
                        b.n_modules += 1;
                    }
                }
                6 => {
                    let esz = rd32(t + 8) as u64;
                    let mut e = t + 16;
                    while e + esz <= t + size && b.n_mmap < MAX_MMAP && esz >= 20 {
                        b.mmap[b.n_mmap] = MemRegion { base: rd64(e), len: rd64(e + 8), ty: rd32(e + 16) };
                        b.n_mmap += 1;
                        e += esz;
                    }
                }
                14 | 15 => {
                    if b.rsdp.is_none() || ty == 15 {
                        b.rsdp = Some(t + 8);
                    }
                }
                _ => {}
            }
            t += (size + 7) & !7;
        }
        if b.n_mmap == 0 {
            return None;
        }
        Some(b)
    } else {
        None
    }
}

/// A loaded root task image.
pub struct Image {
    pub p_start: u64,
    pub p_end: u64,
    pub v_start: u64,
    pub entry: u64,
}

const PAGE: u64 = 4096;

fn round_up(v: u64) -> u64 {
    (v + PAGE - 1) & !(PAGE - 1)
}

/// The virtual range an ELF64 image's loadable segments cover.
fn elf_range(elf: u64) -> Option<(u64, u64)> {
    if rd32(elf) != 0x464c_457f || rd8(elf + 4) != 2 || rd16(elf + 18) != 0x3e {
        return None;
    }
    let phoff = rd64(elf + 32);
    let phentsize = rd16(elf + 54) as u64;
    let phnum = rd16(elf + 56) as u64;
    let mut lo = u64::MAX;
    let mut hi = 0;
    for i in 0..phnum {
        let ph = elf + phoff + i * phentsize;
        if rd32(ph) == 1 {
            let vaddr = rd64(ph + 16);
            let memsz = rd64(ph + 40);
            lo = lo.min(vaddr);
            hi = hi.max(vaddr + memsz);
        }
    }
    if lo >= hi {
        return None;
    }
    Some((lo & !(PAGE - 1), round_up(hi)))
}

/// Copy the ELF image at physical `elf` to physical memory from `dest`
/// (page aligned), seL4 `load_boot_module`.
pub fn load_elf(elf: u64, dest: u64) -> Option<Image> {
    let (v_start, v_end) = elf_range(elf)?;
    let off = dest.wrapping_sub(v_start);
    let phoff = rd64(elf + 32);
    let phentsize = rd16(elf + 54) as u64;
    let phnum = rd16(elf + 56) as u64;
    unsafe { core::ptr::write_bytes(pptr(dest) as *mut u8, 0, (v_end - v_start) as usize) };
    for i in 0..phnum {
        let ph = elf + phoff + i * phentsize;
        if rd32(ph) != 1 {
            continue;
        }
        let offset = rd64(ph + 8);
        let vaddr = rd64(ph + 16);
        let filesz = rd64(ph + 32);
        unsafe {
            core::ptr::copy(pptr(elf + offset) as *const u8, pptr(vaddr.wrapping_add(off)) as *mut u8, filesz as usize);
        }
    }
    Some(Image { p_start: dest, p_end: dest + (v_end - v_start), v_start, entry: rd64(elf + 24) })
}
