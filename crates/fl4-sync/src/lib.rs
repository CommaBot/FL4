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

use core::sync::atomic::{AtomicU64, Ordering};
use fl4_store::tx::Mem;

pub const MAX_CPUS: usize = 64;

pub struct SerialGate {
    next: AtomicU64,
    serving: AtomicU64,
    /// A serial entry holds, or is waiting to hold, the gate (0 or 1).
    closed: AtomicU64,
    /// Cores running a transaction (0 or 1). Its store and the gate
    /// holder's store of `closed` are SeqCst, followed by a load of the
    /// other: a Dekker handshake, which needs the store-load order that
    /// x86 gives only to locked stores.
    active: [AtomicU64; MAX_CPUS],
    /// Core holding the gate, or u64::MAX.
    owner: AtomicU64,
}

impl SerialGate {
    pub const fn new() -> SerialGate {
        SerialGate {
            next: AtomicU64::new(0),
            serving: AtomicU64::new(0),
            closed: AtomicU64::new(0),
            active: [const { AtomicU64::new(0) }; MAX_CPUS],
            owner: AtomicU64::new(u64::MAX),
        }
    }

    /// Start a transaction on core `cpu`: wait while the gate is closed.
    pub fn enter_tx<M: Mem>(&self, m: &M, cpu: u64, mut wait: impl FnMut()) {
        let a = &self.active[cpu as usize];
        loop {
            while m.a_load(&self.closed, Ordering::Acquire) != 0 {
                wait();
                core::hint::spin_loop();
            }
            // (Mutation test: `mutant-gate-release` drops the store-load
            // order, which only the store-buffer model can show.)
            let o = if cfg!(feature = "mutant-gate-release") { Ordering::Release } else { Ordering::SeqCst };
            m.a_store(a, 1, o);
            if m.a_load(&self.closed, Ordering::SeqCst) == 0 {
                return;
            }
            m.a_store(a, 0, Ordering::Release);
        }
    }

    /// The transaction on `cpu` has committed or given up.
    pub fn leave_tx<M: Mem>(&self, m: &M, cpu: u64) {
        m.a_store(&self.active[cpu as usize], 0, Ordering::Release);
    }

    /// Take the gate for core `cpu`: wait for earlier serial entries, close
    /// the gate, and wait for running transactions to finish.
    pub fn acquire<M: Mem>(&self, m: &M, cpu: u64, mut wait: impl FnMut()) {
        let ticket = m.a_add(&self.next, 1, Ordering::Relaxed);
        while m.a_load(&self.serving, Ordering::Acquire) != ticket {
            wait();
            core::hint::spin_loop();
        }
        m.a_store(&self.closed, 1, Ordering::SeqCst);
        for (c, a) in self.active.iter().enumerate() {
            // (Mutation test: `mutant-gate-no-wait` does not wait.)
            if c as u64 == cpu || cfg!(feature = "mutant-gate-no-wait") {
                continue;
            }
            while m.a_load(a, Ordering::SeqCst) != 0 {
                wait();
                core::hint::spin_loop();
            }
        }
        m.a_store(&self.owner, cpu, Ordering::Relaxed);
    }

    pub fn release<M: Mem>(&self, m: &M) {
        m.a_store(&self.owner, u64::MAX, Ordering::Relaxed);
        let s = m.a_load(&self.serving, Ordering::Relaxed);
        let next = s.wrapping_add(1);
        // Keep the gate closed if another serial entry is waiting.
        if m.a_load(&self.next, Ordering::Relaxed) == next {
            m.a_store(&self.closed, 0, Ordering::Release);
        }
        m.a_store(&self.serving, next, Ordering::Release);
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
    /// An interrupt this entry accepted that the run which took effect did
    /// not handle, now forgotten: an aborted attempt polled it at a
    /// preemption point and the rerun did not reach one, or a stall
    /// cancelled the entry. It is still in service and needs an entry of
    /// its own, or it blocks every interrupt of its priority and below
    /// (GitHub issue #6).
    fn unhandled_irq(&self) -> Option<u64>;
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
/// given. An interrupt the entry accepted but did not handle in the run
/// that took effect gets an entry of its own afterwards (`unhandled_irq`).
/// Returns false when a stall cancelled a non-interrupt entry before
/// it ran.
pub fn run_entry<E: EntryEnv>(
    env: &E,
    gate: &SerialGate,
    irq: bool,
    body: impl FnMut(&mut E::S, &mut E::A),
) -> bool {
    let (ran, mut serial) = attempts(env, gate, irq, body);
    while let Some(v) = env.unhandled_irq() {
        let irq_body = |s: &mut E::S, a: &mut E::A| fl4_core::syscall::handle_interrupt_entry(s, a, v);
        if serial {
            // This core still holds the gate (until it leaves the kernel),
            // so the interrupt's entry runs directly too.
            irq_body(&mut env.store(false), &mut env.arch());
            env.entry_done();
        } else {
            serial = attempts(env, gate, true, irq_body).1;
        }
    }
    ran
}

fn attempts<E: EntryEnv>(
    env: &E,
    gate: &SerialGate,
    irq: bool,
    mut body: impl FnMut(&mut E::S, &mut E::A),
) -> (bool, bool) {
    use fl4_store::tx;
    let cpu = env.cpu();
    let mut a = env.arch();
    if !env.multi() {
        body(&mut env.store(false), &mut a);
        env.entry_done();
        return (true, false);
    }
    let stalled = core::cell::Cell::new(false);
    let wait = || {
        if env.service_remote() {
            stalled.set(true);
        }
    };
    for _ in 0..TX_ATTEMPTS {
        gate.enter_tx(env.mem(), cpu, wait);
        if stalled.get() && !irq {
            gate.leave_tx(env.mem(), cpu);
            return (false, false);
        }
        tx::begin(cpu, env.mem());
        env.set_tx(true);
        let mut s = env.store(true);
        body(&mut s, &mut a);
        env.set_tx(false);
        let ok = tx::commit(cpu, env.mem());
        let serial = tx::needs_serial(cpu);
        tx::end(cpu);
        gate.leave_tx(env.mem(), cpu);
        env.finish_effects(ok);
        if ok {
            env.count(Count::Commit);
            env.entry_done();
            return (true, false);
        }
        env.count(Count::Abort);
        if serial {
            break;
        }
    }
    env.count(Count::Serial);
    gate.acquire(env.mem(), cpu, wait);
    env.holding_gate();
    if stalled.get() && !irq {
        return (false, true);
    }
    body(&mut env.store(false), &mut a);
    env.entry_done();
    (true, true)
}
