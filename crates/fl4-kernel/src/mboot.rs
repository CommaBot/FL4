//! Multiboot 1 and 2 boot information (seL4 arch/x86/kernel/boot_sys.c).
use fl4_core::layout::pptr;

pub const MB1_MAGIC: u32 = 0x2bad_b002;
pub const MB2_MAGIC: u32 = 0x36d7_6289;
/// Memory map entries kept, adjacent ones of a type merged. UEFI maps
/// often have more than the 50 the BootInfo record holds (`lib.rs`,
/// `BI_MMAP`); every entry counts for finding RAM, so a map with more is
/// refused (`BootInfo::mmap_lost`) rather than cut short.
pub const MAX_MMAP: usize = 256;
/// The root task's image and up to eight more modules (l4h 0021).
pub const MAX_MODULES: usize = 9;
const MODULE_NAME_LEN: usize = 64;
/// boot.S maps [0, 4 GiB) when the kernel parses the information: every
/// read stays below this, whatever addresses and sizes it holds.
const BOOT_MAP_TOP: u64 = 1 << 32;
/// Multiboot 1 information up to the framebuffer type byte.
const MB1_INFO_LEN: u64 = 110;

/// Whether `[p, p + len)` lies in the boot mapping.
fn inside(p: u64, len: u64) -> bool {
    p <= BOOT_MAP_TOP && len <= BOOT_MAP_TOP - p
}

#[derive(Clone, Copy, Default)]
pub struct MemRegion {
    pub base: u64,
    pub len: u64,
    pub ty: u32,
}

#[derive(Clone, Copy)]
pub struct Module {
    pub start: u64,
    pub end: u64,
    /// NUL-terminated name for seL4_X86_BootModules_t. Own the bytes before
    /// starting APs: their trampoline can overwrite the boot loader's data.
    pub name: [u8; MODULE_NAME_LEN],
}

impl Module {
    const EMPTY: Self = Self { start: 0, end: 0, name: [0; MODULE_NAME_LEN] };
}

pub struct BootInfo {
    pub mmap: [MemRegion; MAX_MMAP],
    pub n_mmap: usize,
    /// The memory map had more entries than `mmap` holds. What it left out
    /// could be RAM or firmware memory, which would become user space's
    /// device memory: the kernel does not boot.
    pub mmap_lost: bool,
    pub modules: [Module; MAX_MODULES],
    pub n_modules: usize,
    /// RSDP copied from Multiboot 2 tags, if any.
    pub rsdp: Option<u64>,
    /// The command line (a C string's physical address), or 0, and how
    /// many bytes of it may be read (it may end earlier, at a NUL).
    pub cmdline: u64,
    pub cmdline_len: u64,
    /// The framebuffer the boot loader set up, if any.
    pub fb: Option<Framebuffer>,
}

/// seL4's `multiboot2_fb_t`.
#[derive(Clone, Copy)]
pub struct Framebuffer {
    pub addr: u64,
    pub pitch: u32,
    pub width: u32,
    pub height: u32,
    pub bpp: u8,
    pub ty: u8,
}

fn rd8(p: u64) -> u8 {
    unsafe { core::ptr::read_volatile(pptr(p) as *const u8) }
}

fn rd32(p: u64) -> u32 {
    unsafe { core::ptr::read_unaligned(pptr(p) as *const u32) }
}

fn rd64(p: u64) -> u64 {
    unsafe { core::ptr::read_unaligned(pptr(p) as *const u64) }
}

impl BootInfo {
    /// Note a memory map entry: merged into the one before it if it has
    /// the same type and starts where that ends.
    fn add_mmap(&mut self, base: u64, len: u64, ty: u32) {
        if let Some(last) = self.mmap[..self.n_mmap].last_mut() {
            if last.ty == ty && last.base.checked_add(last.len) == Some(base) {
                if let Some(l) = last.len.checked_add(len) {
                    last.len = l;
                    return;
                }
            }
        }
        if self.n_mmap == MAX_MMAP {
            self.mmap_lost = true;
            return;
        }
        self.mmap[self.n_mmap] = MemRegion { base, len, ty };
        self.n_mmap += 1;
    }

    /// Note a module. One that ends before it starts is ignored (l4h 0021:
    /// its 32-bit difference looks positive), as are any past the limit.
    fn add_module(&mut self, start: u64, end: u64, name_addr: u64, name_len: u64) {
        if end < start {
            crate::kprintln!("FL4: boot module ends before it starts: ignored");
            return;
        }
        if self.n_modules == MAX_MODULES {
            crate::kprintln!("FL4: more than {} boot modules: the rest are ignored", MAX_MODULES - 1);
            return;
        }
        let mut module = Module { start, end, ..Module::EMPTY };
        if name_addr != 0 {
            let limit = name_len.min((MODULE_NAME_LEN - 1) as u64).min(BOOT_MAP_TOP.saturating_sub(name_addr));
            for i in 0..limit {
                let byte = rd8(name_addr + i);
                if byte == 0 {
                    break;
                }
                module.name[i as usize] = byte;
            }
        }
        self.modules[self.n_modules] = module;
        self.n_modules += 1;
    }
}

/// Whether the command line has the word `opt` (a boolean option such as
/// `fb_console`; `opt=1`, `opt=true` and `opt=on` count too).
pub fn has_option(b: &BootInfo, opt: &[u8]) -> bool {
    if b.cmdline == 0 {
        return false;
    }
    // The line ends at its NUL or its last readable byte, whichever comes
    // first: past it reads as NUL.
    let end = b.cmdline + b.cmdline_len;
    let rd8 = |p: u64| if p < end { rd8(p) } else { 0 };
    let mut p = b.cmdline;
    loop {
        while rd8(p) == b' ' {
            p += 1;
        }
        if rd8(p) == 0 {
            return false;
        }
        let start = p;
        while rd8(p) != 0 && rd8(p) != b' ' {
            p += 1;
        }
        let word = |i: u64| rd8(start + i);
        let len = p - start;
        let n = opt.len() as u64;
        if len >= n && (0..n).all(|i| word(i) == opt[i as usize]) {
            if len == n {
                return true;
            }
            if word(n) == b'=' {
                let v = |s: &[u8]| len == n + 1 + s.len() as u64 && (0..s.len() as u64).all(|i| word(n + 1 + i) == s[i as usize]);
                return v(b"1") || v(b"true") || v(b"on");
            }
        }
    }
}

pub fn parse(magic: u32, info: u64) -> Option<BootInfo> {
    let mut b = BootInfo { mmap: [MemRegion::default(); MAX_MMAP], n_mmap: 0, mmap_lost: false, modules: [Module::EMPTY; MAX_MODULES], n_modules: 0, rsdp: None, cmdline: 0, cmdline_len: 0, fb: None };
    if magic == MB1_MAGIC {
        if !inside(info, MB1_INFO_LEN) {
            return None;
        }
        let flags = rd32(info);
        if flags & (1 << 2) != 0 {
            b.cmdline = rd32(info + 16) as u64;
            b.cmdline_len = BOOT_MAP_TOP - b.cmdline;
        }
        if flags & (1 << 12) != 0 {
            b.fb = Some(Framebuffer { addr: rd64(info + 88), pitch: rd32(info + 96), width: rd32(info + 100), height: rd32(info + 104), bpp: rd8(info + 108), ty: rd8(info + 109) });
        }
        if flags & (1 << 3) != 0 {
            // Entries past the ones kept are only counted (add_module).
            let n = (rd32(info + 20) as u64).min(MAX_MODULES as u64 + 1);
            let addr = rd32(info + 24) as u64;
            for i in 0..n {
                let m = addr + 16 * i;
                if !inside(m, 12) {
                    break;
                }
                b.add_module(rd32(m) as u64, rd32(m + 4) as u64, rd32(m + 8) as u64, MODULE_NAME_LEN as u64);
            }
        }
        if flags & (1 << 6) == 0 {
            return None;
        }
        let len = rd32(info + 44) as u64;
        let addr = rd32(info + 48) as u64;
        let end = (addr + len).min(BOOT_MAP_TOP);
        let mut p = addr;
        // An entry's size word does not count itself; the entry is at
        // least base, length and type (20 bytes).
        while p + 24 <= end {
            let size = rd32(p) as u64;
            if size < 20 {
                break;
            }
            b.add_mmap(rd64(p + 4), rd64(p + 12), rd32(p + 20));
            p += size + 4;
        }
        Some(b)
    } else if magic == MB2_MAGIC {
        // The whole information, as its total size gives it, in the
        // mapping: every tag the walk visits lies inside it.
        if !inside(info, 8) || !inside(info, rd32(info) as u64) {
            return None;
        }
        crate::mb2::tags(info, rd32, |t, ty, size| match ty {
            1 => {
                b.cmdline = t + 8;
                b.cmdline_len = size - 8;
            }
            8 if size >= 30 => b.fb = Some(Framebuffer { addr: rd64(t + 8), pitch: rd32(t + 16), width: rd32(t + 20), height: rd32(t + 24), bpp: rd8(t + 28), ty: rd8(t + 29) }),
            3 if size >= 16 => b.add_module(rd32(t + 8) as u64, rd32(t + 12) as u64, t + 16, size - 16),
            6 if size >= 16 => {
                let esz = rd32(t + 8) as u64;
                let mut e = t + 16;
                while e + esz <= t + size && esz >= 20 {
                    b.add_mmap(rd64(e), rd64(e + 8), rd32(e + 16));
                    e += esz;
                }
            }
            // RSDP 1.0 is 20 bytes, 2.0 36.
            14 | 15 if size >= 8 + if ty == 14 { 20 } else { 36 } => {
                if b.rsdp.is_none() || ty == 15 {
                    b.rsdp = Some(t + 8);
                }
            }
            _ => {}
        });
        if b.n_mmap == 0 {
            return None;
        }
        Some(b)
    } else {
        None
    }
}
