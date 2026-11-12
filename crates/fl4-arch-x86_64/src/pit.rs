//! PIT channel 2 as a reference clock for calibrating the TSC and the
//! LAPIC timer at boot.
use crate::cpu::{inb, outb};

pub const HZ: u64 = 1_193_182;

/// Busy-wait `ticks` PIT ticks (at most 65535) using channel 2.
pub fn wait(ticks: u16, mut during: impl FnMut()) {
    let gate = inb(0x61);
    outb(0x61, (gate & !0x02) | 0x01);
    outb(0x43, 0xb0); // channel 2, lobyte/hibyte, mode 0
    outb(0x42, ticks as u8);
    outb(0x42, (ticks >> 8) as u8);
    // Restart the count by toggling the gate.
    let g = inb(0x61);
    outb(0x61, g & !1);
    outb(0x61, g | 1);
    while inb(0x61) & 0x20 == 0 {
        during();
    }
}
