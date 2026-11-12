//! Local APIC, in x2APIC mode when the CPU has it and xAPIC otherwise
//! (detected at boot, DESIGN.md §3). IPIs use physical destinations.
use crate::cpu::{cpuid, rdmsr, wrmsr, msr};
use core::sync::atomic::{AtomicU64, AtomicBool, Ordering};

static X2APIC: AtomicBool = AtomicBool::new(false);
/// Kernel virtual address of the xAPIC MMIO page.
static MMIO: AtomicU64 = AtomicU64::new(0);

pub const REG_ID: u32 = 0x20;
pub const REG_EOI: u32 = 0xb0;
pub const REG_SVR: u32 = 0xf0;
pub const REG_ISR: u32 = 0x100;
pub const REG_IRR: u32 = 0x200;
pub const REG_ICR_LO: u32 = 0x300;
pub const REG_ICR_HI: u32 = 0x310;
pub const REG_LVT_TIMER: u32 = 0x320;
pub const REG_LVT_LINT0: u32 = 0x350;
pub const REG_LVT_LINT1: u32 = 0x360;
pub const REG_LVT_ERROR: u32 = 0x370;
pub const REG_TIMER_INIT: u32 = 0x380;
pub const REG_TIMER_CUR: u32 = 0x390;
pub const REG_TIMER_DIV: u32 = 0x3e0;

pub fn has_x2apic() -> bool {
    cpuid(1, 0).ecx & (1 << 21) != 0
}

pub fn base_paddr() -> u64 {
    rdmsr(msr::APIC_BASE) & 0x000f_ffff_ffff_f000
}

pub fn is_x2apic() -> bool {
    X2APIC.load(Ordering::Relaxed)
}

/// Enable the local APIC. `mmio` is where the xAPIC page is mapped; it is
/// used only when x2APIC is unavailable.
pub fn enable(mmio: u64) {
    let base = rdmsr(msr::APIC_BASE);
    let firmware_x2 = base & (1 << 10) != 0;
    if has_x2apic() || firmware_x2 {
        wrmsr(msr::APIC_BASE, base | (1 << 11) | (1 << 10));
        X2APIC.store(true, Ordering::Relaxed);
    } else {
        wrmsr(msr::APIC_BASE, base | (1 << 11));
        MMIO.store(mmio, Ordering::Relaxed);
    }
}

pub fn read(reg: u32) -> u32 {
    if is_x2apic() {
        rdmsr(0x800 + (reg >> 4)) as u32
    } else {
        unsafe { core::ptr::read_volatile((MMIO.load(Ordering::Relaxed) + reg as u64) as *const u32) }
    }
}

pub fn write(reg: u32, v: u32) {
    if is_x2apic() {
        wrmsr(0x800 + (reg >> 4), v as u64)
    } else {
        unsafe { core::ptr::write_volatile((MMIO.load(Ordering::Relaxed) + reg as u64) as *mut u32, v) }
    }
}

pub fn id() -> u32 {
    if is_x2apic() {
        read(REG_ID)
    } else {
        read(REG_ID) >> 24
    }
}

pub fn eoi() {
    write(REG_EOI, 0);
}

/// Whether any vector in [lo, hi] is requested (IRR).
pub fn irr_pending(lo: u32, hi: u32) -> bool {
    let mut v = lo;
    while v <= hi {
        let w = read(REG_IRR + (v / 32) * 0x10);
        if w & (1 << (v % 32)) != 0 {
            return true;
        }
        v += 1;
    }
    false
}

/// Send an IPI with physical destination mode.
pub fn send_ipi(dest: u32, icr_lo: u32) {
    if is_x2apic() {
        wrmsr(0x830, ((dest as u64) << 32) | icr_lo as u64);
    } else {
        write(REG_ICR_HI, dest << 24);
        write(REG_ICR_LO, icr_lo);
        while read(REG_ICR_LO) & (1 << 12) != 0 {
            core::hint::spin_loop();
        }
    }
}
