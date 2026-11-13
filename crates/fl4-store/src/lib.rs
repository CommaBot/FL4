//! FL4's object store over physical memory (trusted, DESIGN.md §5).
//!
//! `PhysStore` implements `fl4_core::machine::Store` by reading and writing
//! kernel virtual addresses. Every address the core uses is in the kernel
//! window or the kernel image, both always mapped. With `tx` set, accesses
//! go through the calling core's transaction (`tx`, DESIGN.md §7).
#![no_std]

pub mod tx;

use fl4_core::machine::Store;

/// Physical memory through the kernel window.
pub struct Phys;

impl tx::Mem for Phys {
    #[inline(always)]
    fn load(&self, addr: u64) -> u64 {
        unsafe { core::ptr::read_volatile(addr as *const u64) }
    }
    #[inline(always)]
    fn store(&self, addr: u64, v: u64) {
        unsafe { core::ptr::write_volatile(addr as *mut u64, v) }
    }
}

pub struct PhysStore {
    pub ks_base: u64,
    pub cpu: u64,
    /// Run inside this core's transaction.
    pub tx: bool,
}

impl Store for PhysStore {
    #[inline(always)]
    fn read(&self, addr: u64) -> u64 {
        debug_assert!(addr & 7 == 0);
        if self.tx {
            tx::read(self.cpu, &Phys, addr)
        } else {
            unsafe { core::ptr::read_volatile(addr as *const u64) }
        }
    }

    #[inline(always)]
    fn write(&mut self, addr: u64, v: u64) {
        debug_assert!(addr & 7 == 0);
        if self.tx {
            tx::write(self.cpu, addr, v)
        } else {
            unsafe { core::ptr::write_volatile(addr as *mut u64, v) }
        }
    }

    fn zero(&mut self, addr: u64, len: u64) {
        if self.tx {
            tx::zero(self.cpu, addr, len)
        } else {
            unsafe { core::ptr::write_bytes(addr as *mut u8, 0, len as usize) }
        }
    }

    #[inline(always)]
    fn ks_base(&self) -> u64 {
        self.ks_base
    }

    #[inline(always)]
    fn cur_cpu(&self) -> u64 {
        self.cpu
    }
}
