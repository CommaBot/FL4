//! FL4's x86_64 hardware backend. Trusted code (DESIGN.md §5): everything
//! here is small, unsafe where it must be, and covered by tests in QEMU.
#![no_std]

pub mod apic;
pub mod cpu;
pub mod ioapic;
pub mod pic;
pub mod pit;
pub mod serial;
