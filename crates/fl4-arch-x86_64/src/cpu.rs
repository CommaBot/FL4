//! Instruction wrappers.
use core::arch::asm;

#[inline]
pub fn outb(port: u16, v: u8) {
    unsafe { asm!("out dx, al", in("dx") port, in("al") v, options(nomem, nostack, preserves_flags)) }
}

#[inline]
pub fn inb(port: u16) -> u8 {
    let v: u8;
    unsafe { asm!("in al, dx", in("dx") port, out("al") v, options(nomem, nostack, preserves_flags)) }
    v
}

#[inline]
pub fn outw(port: u16, v: u16) {
    unsafe { asm!("out dx, ax", in("dx") port, in("ax") v, options(nomem, nostack, preserves_flags)) }
}

#[inline]
pub fn inw(port: u16) -> u16 {
    let v: u16;
    unsafe { asm!("in ax, dx", in("dx") port, out("ax") v, options(nomem, nostack, preserves_flags)) }
    v
}

#[inline]
pub fn outl(port: u16, v: u32) {
    unsafe { asm!("out dx, eax", in("dx") port, in("eax") v, options(nomem, nostack, preserves_flags)) }
}

#[inline]
pub fn inl(port: u16) -> u32 {
    let v: u32;
    unsafe { asm!("in eax, dx", in("dx") port, out("eax") v, options(nomem, nostack, preserves_flags)) }
    v
}

#[derive(Clone, Copy, Debug)]
pub struct Cpuid {
    pub eax: u32,
    pub ebx: u32,
    pub ecx: u32,
    pub edx: u32,
}

#[inline]
pub fn cpuid(leaf: u32, sub: u32) -> Cpuid {
    let r = core::arch::x86_64::__cpuid_count(leaf, sub);
    Cpuid { eax: r.eax, ebx: r.ebx, ecx: r.ecx, edx: r.edx }
}

#[inline]
pub fn rdmsr(msr: u32) -> u64 {
    let (lo, hi): (u32, u32);
    unsafe { asm!("rdmsr", in("ecx") msr, out("eax") lo, out("edx") hi, options(nomem, nostack, preserves_flags)) }
    ((hi as u64) << 32) | lo as u64
}

#[inline]
pub fn wrmsr(msr: u32, v: u64) {
    unsafe {
        asm!("wrmsr", in("ecx") msr, in("eax") v as u32, in("edx") (v >> 32) as u32, options(nostack, preserves_flags))
    }
}

#[inline]
pub fn rdtsc() -> u64 {
    unsafe { core::arch::x86_64::_rdtsc() }
}

#[inline]
pub fn halt() {
    unsafe { asm!("hlt", options(nomem, nostack)) }
}

pub fn halt_forever() -> ! {
    loop {
        unsafe { asm!("cli; hlt", options(nomem, nostack)) }
    }
}

#[inline]
pub fn read_cr0() -> u64 {
    let v: u64;
    unsafe { asm!("mov {}, cr0", out(reg) v, options(nomem, nostack, preserves_flags)) }
    v
}

#[inline]
pub fn write_cr0(v: u64) {
    unsafe { asm!("mov cr0, {}", in(reg) v, options(nostack, preserves_flags)) }
}

#[inline]
pub fn read_cr2() -> u64 {
    let v: u64;
    unsafe { asm!("mov {}, cr2", out(reg) v, options(nomem, nostack, preserves_flags)) }
    v
}

#[inline]
pub fn read_cr3() -> u64 {
    let v: u64;
    unsafe { asm!("mov {}, cr3", out(reg) v, options(nomem, nostack, preserves_flags)) }
    v
}

#[inline]
pub fn write_cr3(v: u64) {
    unsafe { asm!("mov cr3, {}", in(reg) v, options(nostack, preserves_flags)) }
}

#[inline]
pub fn read_cr4() -> u64 {
    let v: u64;
    unsafe { asm!("mov {}, cr4", out(reg) v, options(nomem, nostack, preserves_flags)) }
    v
}

#[inline]
pub fn write_cr4(v: u64) {
    unsafe { asm!("mov cr4, {}", in(reg) v, options(nostack, preserves_flags)) }
}

#[inline]
pub fn invlpg(addr: u64) {
    unsafe { asm!("invlpg [{}]", in(reg) addr, options(nostack, preserves_flags)) }
}

#[inline]
pub fn xgetbv(reg: u32) -> u64 {
    let (lo, hi): (u32, u32);
    unsafe { asm!("xgetbv", in("ecx") reg, out("eax") lo, out("edx") hi, options(nomem, nostack, preserves_flags)) }
    ((hi as u64) << 32) | lo as u64
}

#[inline]
pub fn xsetbv(reg: u32, v: u64) {
    unsafe { asm!("xsetbv", in("ecx") reg, in("eax") v as u32, in("edx") (v >> 32) as u32, options(nostack, preserves_flags)) }
}

pub fn read_dr6() -> u64 {
    let v: u64;
    unsafe { asm!("mov {}, dr6", out(reg) v, options(nomem, nostack, preserves_flags)) }
    v
}

pub fn write_dr6(v: u64) {
    unsafe { asm!("mov dr6, {}", in(reg) v, options(nostack, preserves_flags)) }
}

pub fn write_dr7(v: u64) {
    unsafe { asm!("mov dr7, {}", in(reg) v, options(nostack, preserves_flags)) }
}

pub fn write_dr(i: u64, v: u64) {
    unsafe {
        match i {
            0 => asm!("mov dr0, {}", in(reg) v, options(nostack, preserves_flags)),
            1 => asm!("mov dr1, {}", in(reg) v, options(nostack, preserves_flags)),
            2 => asm!("mov dr2, {}", in(reg) v, options(nostack, preserves_flags)),
            _ => asm!("mov dr3, {}", in(reg) v, options(nostack, preserves_flags)),
        }
    }
}

#[inline]
pub fn enable_interrupts_briefly() {
    // Not `nomem`: interrupt handlers run here and touch kernel state.
    unsafe { asm!("sti", "nop", "nop", "cli", options(nostack)) }
}

pub mod msr {
    pub const APIC_BASE: u32 = 0x1b;
    pub const TSC_DEADLINE: u32 = 0x6e0;
    pub const PAT: u32 = 0x277;
    pub const EFER: u32 = 0xc000_0080;
    pub const STAR: u32 = 0xc000_0081;
    pub const LSTAR: u32 = 0xc000_0082;
    pub const CSTAR: u32 = 0xc000_0083;
    pub const FMASK: u32 = 0xc000_0084;
    pub const FS_BASE: u32 = 0xc000_0100;
    pub const GS_BASE: u32 = 0xc000_0101;
    pub const KERNEL_GS_BASE: u32 = 0xc000_0102;
}
