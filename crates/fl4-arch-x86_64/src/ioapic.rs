//! IOAPICs found in the ACPI MADT. All pins start masked; user space
//! routes pins to vectors through IRQControl.
use core::sync::atomic::{AtomicU64, Ordering};

pub const MAX_IOAPICS: usize = 8;
const REG_VER: u32 = 1;

static BASE: [AtomicU64; MAX_IOAPICS] = [const { AtomicU64::new(0) }; MAX_IOAPICS];
static PINS: [AtomicU64; MAX_IOAPICS] = [const { AtomicU64::new(0) }; MAX_IOAPICS];
static COUNT: AtomicU64 = AtomicU64::new(0);
/// Low word of each redirection entry as last programmed, per IRQ: bit 63
/// valid, bits 32..39 ioapic, 40..47 pin, 0..31 the entry.
static ROUTE: [AtomicU64; 256] = [const { AtomicU64::new(0) }; 256];

fn read(i: usize, reg: u32) -> u32 {
    let b = BASE[i].load(Ordering::Relaxed);
    unsafe {
        core::ptr::write_volatile(b as *mut u32, reg);
        core::ptr::read_volatile((b + 0x10) as *const u32)
    }
}

fn write(i: usize, reg: u32, v: u32) {
    let b = BASE[i].load(Ordering::Relaxed);
    unsafe {
        core::ptr::write_volatile(b as *mut u32, reg);
        core::ptr::write_volatile((b + 0x10) as *mut u32, v);
    }
}

/// Register an IOAPIC mapped at kernel address `mmio`; masks every pin.
pub fn add(mmio: u64) {
    let i = COUNT.load(Ordering::Relaxed) as usize;
    if i >= MAX_IOAPICS {
        return;
    }
    BASE[i].store(mmio, Ordering::Relaxed);
    let n = ((read(i, REG_VER) >> 16) & 0xff) + 1;
    PINS[i].store(n as u64, Ordering::Relaxed);
    for p in 0..n {
        write(i, 0x10 + 2 * p, 1 << 16);
        write(i, 0x11 + 2 * p, 0);
    }
    COUNT.store(i as u64 + 1, Ordering::Relaxed);
}

pub fn count() -> u64 {
    COUNT.load(Ordering::Relaxed)
}

pub fn pins(i: u64) -> u64 {
    if i < count() {
        PINS[i as usize].load(Ordering::Relaxed)
    } else {
        0
    }
}

/// Route `pin` of `ioapic` to `vector` on the boot CPU (`dest`), masked.
/// A nonzero `high` replaces the destination word and `lo_extra` is ORed
/// into the low word (remappable-format entries, l4h 0025).
#[allow(clippy::too_many_arguments)]
pub fn map(ioapic: u64, pin: u64, level: u64, polarity: u64, vector: u64, dest: u32, high: u32, lo_extra: u32) {
    let i = ioapic as usize;
    let lo = (1u32 << 16) | ((level as u32) << 15) | ((polarity as u32) << 13) | lo_extra | vector as u32;
    write(i, 0x10 + 2 * pin as u32, 1 << 16);
    write(i, 0x11 + 2 * pin as u32, if high != 0 { high } else { dest << 24 });
    write(i, 0x10 + 2 * pin as u32, lo);
    let irq = (vector - 0x20) as usize;
    if irq < 256 {
        ROUTE[irq].store((1 << 63) | (ioapic << 32) | (pin << 40) | lo as u64, Ordering::Relaxed);
    }
}

/// Mask or unmask whatever pin `irq` is routed from.
pub fn mask(irq: u64, masked: bool) {
    if irq >= 256 {
        return;
    }
    let r = ROUTE[irq as usize].load(Ordering::Relaxed);
    if r & (1 << 63) == 0 {
        return;
    }
    let i = ((r >> 32) & 0xff) as usize;
    let pin = ((r >> 40) & 0xff) as u32;
    let mut lo = r as u32;
    if masked {
        lo |= 1 << 16;
    } else {
        lo &= !(1 << 16);
    }
    write(i, 0x10 + 2 * pin, lo);
    ROUTE[irq as usize].store((r & !0xffff_ffff) | lo as u64, Ordering::Relaxed);
}

pub fn forget(irq: u64) {
    if irq < 256 {
        ROUTE[irq as usize].store(0, Ordering::Relaxed);
    }
}
