//! 16550 UART on COM1, the console in every QEMU setup (DESIGN.md §12).
use crate::cpu::{inb, outb};

const COM1: u16 = 0x3f8;

pub fn init() {
    outb(COM1 + 1, 0x00); // no interrupts
    outb(COM1 + 3, 0x80); // DLAB
    outb(COM1, 0x01); // 115200 baud
    outb(COM1 + 1, 0x00);
    outb(COM1 + 3, 0x03); // 8n1
    outb(COM1 + 2, 0xc7); // FIFO on, cleared
    outb(COM1 + 4, 0x0b);
}

pub fn putc(c: u8) {
    if c == b'\n' {
        putc_raw(b'\r');
    }
    putc_raw(c);
}

fn putc_raw(c: u8) {
    let mut n = 0u32;
    while inb(COM1 + 5) & 0x20 == 0 && n < 100_000 {
        n += 1;
        core::hint::spin_loop();
    }
    outb(COM1, c);
}

pub fn getc() -> Option<u8> {
    if inb(COM1 + 5) & 1 != 0 {
        Some(inb(COM1))
    } else {
        None
    }
}
