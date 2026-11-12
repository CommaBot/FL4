//! FL4 transaction runtime: lock table, serial gate (sim-tested).
//!
//! Until fine-grained locking (DESIGN.md §7, milestone M4) every kernel
//! entry on a multi-core system runs under the serial gate, which then acts
//! like seL4's big kernel lock.
#![no_std]

use core::sync::atomic::{AtomicU32, AtomicU64, Ordering};

/// The serial gate: a ticket lock, fair among cores. Spinning cores keep
/// running `wait`, which services remote calls, as seL4's CLH lock does,
/// so a core holding the gate can wait for another core's acknowledgement.
pub struct SerialGate {
    next: AtomicU32,
    serving: AtomicU32,
    /// Core holding the gate, or u64::MAX.
    owner: AtomicU64,
}

impl SerialGate {
    pub const fn new() -> SerialGate {
        SerialGate { next: AtomicU32::new(0), serving: AtomicU32::new(0), owner: AtomicU64::new(u64::MAX) }
    }

    /// Take the gate for core `cpu`, calling `wait` on every spin while
    /// another core holds it. A caller whose entry was cancelled while it
    /// waited (a remote stall) releases the gate straight away.
    pub fn acquire(&self, cpu: u64, mut wait: impl FnMut()) {
        let ticket = self.next.fetch_add(1, Ordering::Relaxed);
        while self.serving.load(Ordering::Acquire) != ticket {
            wait();
            core::hint::spin_loop();
        }
        self.owner.store(cpu, Ordering::Relaxed);
    }

    pub fn release(&self) {
        self.owner.store(u64::MAX, Ordering::Relaxed);
        let s = self.serving.load(Ordering::Relaxed);
        self.serving.store(s.wrapping_add(1), Ordering::Release);
    }

    pub fn owner(&self) -> u64 {
        self.owner.load(Ordering::Relaxed)
    }
}

impl Default for SerialGate {
    fn default() -> Self {
        Self::new()
    }
}
