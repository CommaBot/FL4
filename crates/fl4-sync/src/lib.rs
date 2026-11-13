//! FL4 transaction runtime: the serial gate (trusted, sim-tested).
//!
//! Kernel entries on a multi-core system run as transactions (fl4-store's
//! `tx`) while the gate is open. An entry that cannot run as a transaction
//! takes the gate: it waits its turn among serial entries, closes the gate
//! to new transactions, waits for running ones to finish, and then runs
//! directly on memory (DESIGN.md §7). Every wait calls a hook that services
//! remote calls, as seL4's CLH lock does, so a core in the gate can wait for
//! another core's acknowledgement.
#![no_std]

use core::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, Ordering};

pub const MAX_CPUS: usize = 64;

pub struct SerialGate {
    next: AtomicU32,
    serving: AtomicU32,
    /// A serial entry holds, or is waiting to hold, the gate.
    closed: AtomicBool,
    /// Cores running a transaction.
    active: [AtomicBool; MAX_CPUS],
    /// Core holding the gate, or u64::MAX.
    owner: AtomicU64,
}

impl SerialGate {
    pub const fn new() -> SerialGate {
        SerialGate {
            next: AtomicU32::new(0),
            serving: AtomicU32::new(0),
            closed: AtomicBool::new(false),
            active: [const { AtomicBool::new(false) }; MAX_CPUS],
            owner: AtomicU64::new(u64::MAX),
        }
    }

    /// Start a transaction on core `cpu`: wait while the gate is closed.
    pub fn enter_tx(&self, cpu: u64, mut wait: impl FnMut()) {
        let a = &self.active[cpu as usize];
        loop {
            while self.closed.load(Ordering::Acquire) {
                wait();
                core::hint::spin_loop();
            }
            a.store(true, Ordering::SeqCst);
            if !self.closed.load(Ordering::SeqCst) {
                return;
            }
            a.store(false, Ordering::Release);
        }
    }

    /// The transaction on `cpu` has committed or given up.
    pub fn leave_tx(&self, cpu: u64) {
        self.active[cpu as usize].store(false, Ordering::Release);
    }

    /// Take the gate for core `cpu`: wait for earlier serial entries, close
    /// the gate, and wait for running transactions to finish.
    pub fn acquire(&self, cpu: u64, mut wait: impl FnMut()) {
        let ticket = self.next.fetch_add(1, Ordering::Relaxed);
        while self.serving.load(Ordering::Acquire) != ticket {
            wait();
            core::hint::spin_loop();
        }
        self.closed.store(true, Ordering::SeqCst);
        for (c, a) in self.active.iter().enumerate() {
            if c as u64 == cpu {
                continue;
            }
            while a.load(Ordering::SeqCst) {
                wait();
                core::hint::spin_loop();
            }
        }
        self.owner.store(cpu, Ordering::Relaxed);
    }

    pub fn release(&self) {
        self.owner.store(u64::MAX, Ordering::Relaxed);
        let s = self.serving.load(Ordering::Relaxed);
        let next = s.wrapping_add(1);
        // Keep the gate closed if another serial entry is waiting.
        if self.next.load(Ordering::Relaxed) == next {
            self.closed.store(false, Ordering::Release);
        }
        self.serving.store(next, Ordering::Release);
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
