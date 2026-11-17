//! The console UART: an Arm PL011 (or SBSA generic UART) or a 16550, as
//! ACPI SPCR or the device tree's stdout-path names it.
use core::sync::atomic::{AtomicU64, Ordering};

pub const KIND_NONE: u64 = 0;
pub const KIND_PL011: u64 = 1;
pub const KIND_16550: u64 = 2;

static KIND: AtomicU64 = AtomicU64::new(KIND_NONE);
static BASE: AtomicU64 = AtomicU64::new(0);
/// 16550: register stride shift (0 for bytes, 2 for 32-bit registers).
static SHIFT: AtomicU64 = AtomicU64::new(0);
static WIDE: AtomicU64 = AtomicU64::new(0);

const PL011_DR: u64 = 0x0;
const PL011_FR: u64 = 0x18;
const FR_RXFE: u32 = 1 << 4;
const FR_TXFF: u32 = 1 << 5;

const U_THR: u64 = 0;
const U_LSR: u64 = 5;
const LSR_DR: u32 = 1;
const LSR_THRE: u32 = 1 << 5;

/// `base` is a kernel virtual address.
pub fn init(kind: u64, base: u64, shift: u64, wide: bool) {
    BASE.store(base, Ordering::Relaxed);
    SHIFT.store(shift, Ordering::Relaxed);
    WIDE.store(wide as u64, Ordering::Relaxed);
    KIND.store(kind, Ordering::Release);
}

pub fn release() {
    KIND.store(KIND_NONE, Ordering::Release);
}

fn rd32(a: u64) -> u32 {
    unsafe { core::ptr::read_volatile(a as *const u32) }
}

fn wr32(a: u64, v: u32) {
    unsafe { core::ptr::write_volatile(a as *mut u32, v) }
}

fn ureg(r: u64) -> u64 {
    BASE.load(Ordering::Relaxed) + (r << SHIFT.load(Ordering::Relaxed))
}

fn urd(r: u64) -> u32 {
    if WIDE.load(Ordering::Relaxed) != 0 {
        rd32(ureg(r))
    } else {
        unsafe { core::ptr::read_volatile(ureg(r) as *const u8) as u32 }
    }
}

fn uwr(r: u64, v: u32) {
    if WIDE.load(Ordering::Relaxed) != 0 {
        wr32(ureg(r), v)
    } else {
        unsafe { core::ptr::write_volatile(ureg(r) as *mut u8, v as u8) }
    }
}

pub fn putc(c: u8) {
    let b = BASE.load(Ordering::Relaxed);
    match KIND.load(Ordering::Acquire) {
        KIND_PL011 => {
            let mut n = 0u32;
            while rd32(b + PL011_FR) & FR_TXFF != 0 && n < 1_000_000 {
                core::hint::spin_loop();
                n += 1;
            }
            wr32(b + PL011_DR, c as u32);
        }
        KIND_16550 => {
            let mut n = 0u32;
            while urd(U_LSR) & LSR_THRE == 0 && n < 1_000_000 {
                core::hint::spin_loop();
                n += 1;
            }
            uwr(U_THR, c as u32);
        }
        _ => {}
    }
}

pub fn getc() -> Option<u8> {
    let b = BASE.load(Ordering::Relaxed);
    match KIND.load(Ordering::Acquire) {
        KIND_PL011 => {
            if rd32(b + PL011_FR) & FR_RXFE != 0 {
                None
            } else {
                Some(rd32(b + PL011_DR) as u8)
            }
        }
        KIND_16550 => {
            if urd(U_LSR) & LSR_DR == 0 {
                None
            } else {
                Some(urd(U_THR) as u8)
            }
        }
        _ => None,
    }
}
