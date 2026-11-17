//! The AArch64 boot protocol between FL4's UEFI loader (`fl4-efi`) and the
//! kernel. The loader puts the kernel image, its boot page tables and this
//! record in one physically contiguous "kernel region", 2 MiB aligned,
//! which the boot tables map both at its physical address and at
//! `KERNEL_VBASE`. It enters the kernel's `_start` at its physical address
//! with the MMU and caches off, at EL2 or EL1, with x0 the record's offset
//! in the region.
#![no_std]

/// Where the kernel region is mapped.
pub const KERNEL_VBASE: u64 = 0xffff_ffff_8000_0000;
pub const MAGIC: u64 = 0x464c_345f_424f_4f54; // "FL4_BOOT"
pub const VERSION: u64 = 1;

pub const MAX_MMAP: usize = 256;
pub const MAX_MODULES: usize = 8;
pub const CMDLINE_LEN: usize = 256;
pub const NAME_LEN: usize = 64;

/// Memory map entry kinds (from the UEFI memory types).
pub mod mem {
    /// Free after ExitBootServices: conventional, loader and boot
    /// services memory (minus what the record names).
    pub const FREE: u32 = 1;
    /// Firmware memory with RAM behind it that must stay: runtime
    /// services, ACPI tables and NVS, persistent memory.
    pub const FIRMWARE: u32 = 2;
    /// Anything else: reserved, unusable, MMIO.
    pub const OTHER: u32 = 3;
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct MemRegion {
    pub base: u64,
    pub len: u64,
    pub kind: u32,
    /// The region is ordinary write-back cacheable RAM (EFI_MEMORY_WB).
    pub cacheable: u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Module {
    pub paddr: u64,
    pub size: u64,
    pub name: [u8; NAME_LEN],
}

impl Default for Module {
    fn default() -> Self {
        Module { paddr: 0, size: 0, name: [0; NAME_LEN] }
    }
}

/// The root task, loaded by the loader: its segments occupy
/// [p_start, p_end), mapped at p - pv_offset.
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct RootTask {
    pub p_start: u64,
    pub p_end: u64,
    pub v_start: u64,
    pub entry: u64,
}

#[repr(C)]
pub struct BootInfo {
    pub magic: u64,
    pub version: u64,
    /// The kernel region: physical base and length.
    pub region_paddr: u64,
    pub region_len: u64,
    /// Boot page tables (in the region): TTBR0 identity, TTBR1 high.
    pub ttbr0: u64,
    pub ttbr1: u64,
    /// ACPI RSDP and device tree blob (physical; 0 if none).
    pub rsdp: u64,
    pub dtb: u64,
    pub dtb_len: u64,
    pub root: RootTask,
    /// Further boot modules (l4h 0021), as the loader read them.
    pub n_modules: u64,
    pub modules: [Module; MAX_MODULES],
    pub n_mmap: u64,
    pub mmap: [MemRegion; MAX_MMAP],
    /// NUL-terminated kernel command line.
    pub cmdline: [u8; CMDLINE_LEN],
}
