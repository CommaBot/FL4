//! The legacy 8259 PICs: remapped out of the exception range and masked.
use crate::cpu::outb;

pub fn disable() {
    outb(0x20, 0x11);
    outb(0xa0, 0x11);
    outb(0x21, 0x20);
    outb(0xa1, 0x28);
    outb(0x21, 4);
    outb(0xa1, 2);
    outb(0x21, 1);
    outb(0xa1, 1);
    outb(0x21, 0xff);
    outb(0xa1, 0xff);
}
