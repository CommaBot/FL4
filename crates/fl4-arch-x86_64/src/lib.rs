//! FL4's x86_64 hardware backend. Trusted code (DESIGN.md §5): everything
//! here is small, unsafe where it must be, and covered by tests in QEMU.
#![no_std]

pub mod apic;
pub mod arch;
pub mod cpu;
pub mod cvm;
pub mod fbcon;
pub mod fpu;
pub mod ioapic;
mod kvm_clock;
pub mod percpu;
pub mod pic;
pub mod pit;
pub mod serial;
pub mod sev;
pub mod smp;
pub mod spec;
pub mod tdx;
pub mod timer;
pub mod tlb;

pub mod vm;
