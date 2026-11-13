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

/// Stop channel 0's periodic interrupt (left running by the firmware):
/// mode 0 counts down once and then holds its output, so ISA IRQ 0
/// (IOAPIC pin 2, which an HPET timer may also be routed to) stays quiet.
pub fn quiet_channel0() {
    outb(0x43, 0x30); // channel 0, lobyte/hibyte, mode 0
    outb(0x40, 1);
    outb(0x40, 0);
}
