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
            // (Mutation test: `mutant-gate-no-wait` does not wait.)
            if c as u64 == cpu || cfg!(feature = "mutant-gate-no-wait") {
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

/// What a kernel entry needs from its environment: the kernel on hardware,
/// or the simulator.
pub trait EntryEnv {
    type S: fl4_core::machine::Store;
    type A: fl4_core::machine::Arch;
    type M: fl4_store::tx::Mem;
    fn cpu(&self) -> u64;
    /// More than one core runs the kernel.
    fn multi(&self) -> bool;
    /// The store, inside this core's transaction or direct.
    fn store(&self, tx: bool) -> Self::S;
    fn arch(&self) -> Self::A;
    fn mem(&self) -> &Self::M;
    /// Service a remote call; true if it stalled this core's thread.
    fn service_remote(&self) -> bool;
    /// Arch operations are queued (inside a transaction) or run directly.
    fn set_tx(&self, on: bool);
    /// Run (`committed`) or drop the queued Arch effects.
    fn finish_effects(&self, committed: bool);
    /// The entry has completed (it will not run again).
    fn entry_done(&self);
    /// This core now holds the serial gate (released when it leaves the
    /// kernel).
    fn holding_gate(&self);
    fn count(&self, _what: Count) {}
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Count {
    Commit,
    Abort,
    Serial,
}

/// Transaction attempts before an entry runs under the serial gate (none
/// with the test-only `serial-gate` feature).
pub const TX_ATTEMPTS: u32 = if cfg!(feature = "serial-gate") { 0 } else { 4 };

/// Run the kernel's part of an entry (DESIGN.md §7): directly on one core;
/// otherwise as a transaction, rerun on conflict, and under the serial gate
/// if it cannot run as one or keeps conflicting. `body` must be repeatable:
/// everything it reads or writes goes through the store and Arch it is
/// given. Returns false when a stall cancelled a non-interrupt entry before
/// it ran.
pub fn run_entry<E: EntryEnv>(
    env: &E,
    gate: &SerialGate,
    irq: bool,
    mut body: impl FnMut(&mut E::S, &mut E::A),
) -> bool {
    use fl4_store::tx;
    let cpu = env.cpu();
    let mut a = env.arch();
    if !env.multi() {
        body(&mut env.store(false), &mut a);
        env.entry_done();
        return true;
    }
    let stalled = core::cell::Cell::new(false);
    let wait = || {
        if env.service_remote() {
            stalled.set(true);
        }
    };
    for _ in 0..TX_ATTEMPTS {
        gate.enter_tx(cpu, wait);
        if stalled.get() && !irq {
            gate.leave_tx(cpu);
            return false;
        }
        tx::begin(cpu);
        env.set_tx(true);
        let mut s = env.store(true);
        body(&mut s, &mut a);
        env.set_tx(false);
        let ok = tx::commit(cpu, env.mem());
        let serial = tx::needs_serial(cpu);
        tx::end(cpu);
        gate.leave_tx(cpu);
        env.finish_effects(ok);
        if ok {
            env.count(Count::Commit);
            env.entry_done();
            return true;
        }
        env.count(Count::Abort);
        if serial {
            break;
        }
    }
    env.count(Count::Serial);
    gate.acquire(cpu, wait);
    env.holding_gate();
    if stalled.get() && !irq {
        return false;
    }
    body(&mut env.store(false), &mut a);
    env.entry_done();
    true
}
