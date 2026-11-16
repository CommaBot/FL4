//! FL4 transaction runtime: the serial gate (trusted, sim-tested).
//!
//! A quiet multi-core machine can take the existing serial gate and execute
//! an entry directly. One contender may queue behind an existing serial
//! ticket; more contention backs off these probes and entries run concurrently
//! as transactions (fl4-store's `tx`). An irrevocable entry, or one that
//! exhausts its retries, waits for the gate
//! in ticket order. Both forms close the gate and exclude all transactions
//! before touching memory directly (DESIGN.md §7). Every blocking wait
//! services remote calls, as seL4's CLH lock does.
#![no_std]

use core::sync::atomic::{AtomicU64, Ordering};
use fl4_store::tx::Mem;

pub const MAX_CPUS: usize = 64;
/// Concurrent entries between opportunistic probes after contention.
const PROBE_BACKOFF: u64 = 256;

// Written only by its CPU. Padding keeps backoff updates off other CPUs'
// cache lines. These relaxed atomics are policy, not synchronization, and
// go through Mem so the simulator observes every runtime access.
#[repr(align(64))]
struct Policy {
    seen: AtomicU64,
    retry: AtomicU64,
}

// Read on every SMP entry; keep it off the ticket/owner cache line.
#[repr(align(64))]
struct Contention(AtomicU64);

pub struct SerialGate {
    /// Changed when a probe loses or a transaction waits for the gate.
    contention: Contention,
    policy: [Policy; MAX_CPUS],
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
            contention: Contention(AtomicU64::new(0)),
            policy: [const {
                Policy {
                    seen: AtomicU64::new(0),
                    retry: AtomicU64::new(0),
                }
            }; MAX_CPUS],
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
        let mut notified = false;
        loop {
            while m.a_load(&self.closed, Ordering::Acquire) != 0 {
                // Tell a successful probe to back off at its next entry,
                // so a busy core cannot repeatedly barge ahead of STM.
                if !notified {
                    m.a_add(&self.contention.0, 1, Ordering::Relaxed);
                    notified = true;
                }
                wait();
                core::hint::spin_loop();
            }
            // (Mutation test: `mutant-gate-release` drops the store-load
            // order, which only the store-buffer model can show.)
            let o = if cfg!(feature = "mutant-gate-release") {
                Ordering::Release
            } else {
                Ordering::SeqCst
            };
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

    /// Opportunistically reserve a serial ticket, allowing at most one
    /// queued successor. More contention defers probes for `PROBE_BACKOFF`
    /// entries on each core. A queued successor services IPIs while waiting.
    /// The caller must not have an active transaction, as for `acquire`.
    ///
    /// The CAS reserves the next ticket only if the queue is empty or has
    /// just one ticket. After that ticket is served, closing the gate and
    /// checking every active flag use the same SeqCst handshake as
    /// `acquire`/`enter_tx`:
    /// either the probe sees the transaction or it sees the closed gate.
    /// A failed scan releases its ticket before returning; it never runs
    /// an entry, waits for a transaction, or changes the version clock.
    pub fn opportunistic_acquire<M: Mem>(&self, m: &M, cpu: u64, mut wait: impl FnMut()) -> bool {
        let p = &self.policy[cpu as usize];
        let generation = m.a_load(&self.contention.0, Ordering::Relaxed);
        if m.a_load(&p.seen, Ordering::Relaxed) != generation {
            m.a_store(&p.seen, generation, Ordering::Relaxed);
            m.a_store(&p.retry, PROBE_BACKOFF, Ordering::Relaxed);
            return false;
        }
        let remaining = m.a_load(&p.retry, Ordering::Relaxed);
        if remaining != 0 {
            m.a_store(&p.retry, remaining - 1, Ordering::Relaxed);
            return false;
        }
        let ticket = m.a_load(&self.serving, Ordering::Acquire);
        let next = m.a_load(&self.next, Ordering::Relaxed);
        let queued = next == ticket.wrapping_add(1);
        if (next != ticket && !queued)
            || m.a_cas(
                &self.next,
                next,
                next.wrapping_add(1),
                Ordering::Relaxed,
                Ordering::Relaxed,
            )
            .is_err()
        {
            m.a_add(&self.contention.0, 1, Ordering::Relaxed);
            return false;
        }
        if queued {
            while m.a_load(&self.serving, Ordering::Acquire) != next {
                wait();
                core::hint::spin_loop();
            }
        }
        m.a_store(&self.closed, 1, Ordering::SeqCst);
        for (c, a) in self.active.iter().enumerate() {
            if c as u64 != cpu
                && !cfg!(feature = "mutant-gate-no-wait")
                && m.a_load(a, Ordering::SeqCst) != 0
            {
                m.a_add(&self.contention.0, 1, Ordering::Relaxed);
                self.release(m);
                return false;
            }
        }
        m.a_store(&self.owner, cpu, Ordering::Relaxed);
        true
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
/// otherwise probe for exclusive access with at most one queued successor,
/// then use transactions on contention, rerun on conflict, and wait for the
/// serial gate if an entry cannot run as a transaction or keeps conflicting.
/// `body` must be repeatable:
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
        let irq_body =
            |s: &mut E::S, a: &mut E::A| fl4_core::syscall::handle_interrupt_entry(s, a, v);
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
    if TX_ATTEMPTS != 0 && gate.opportunistic_acquire(env.mem(), cpu, wait) {
        env.count(Count::Serial);
        env.holding_gate();
        if stalled.get() && !irq {
            return (false, true);
        }
        body(&mut env.store(false), &mut a);
        env.entry_done();
        return (true, true);
    }
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

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use std::sync::{Arc, Barrier};
    use std::thread;

    struct Atomics;
    impl Mem for Atomics {
        fn load(&self, _: u64) -> u64 {
            unreachable!()
        }
        fn store(&self, _: u64, _: u64) {
            unreachable!()
        }
    }

    #[test]
    fn active_transaction_rejects_probe_and_contention_yields_to_stm() {
        let gate = SerialGate::new();
        gate.enter_tx(&Atomics, 1, || panic!("open gate"));
        assert!(!gate.opportunistic_acquire(&Atomics, 0, thread::yield_now));
        assert_eq!(gate.owner(), u64::MAX);
        // A failed probe must give its ticket back and reopen the gate.
        gate.enter_tx(&Atomics, 2, || panic!("probe stranded the gate"));
        gate.leave_tx(&Atomics, 1);
        gate.leave_tx(&Atomics, 2);
        // Even now that it is empty, contenders get a window for STM.
        assert!(!gate.opportunistic_acquire(&Atomics, 0, thread::yield_now));
        assert!(!gate.opportunistic_acquire(&Atomics, 1, thread::yield_now));
        let recovered = (0..1024).any(|_| gate.opportunistic_acquire(&Atomics, 0, thread::yield_now));
        assert!(
            recovered,
            "uncontended entries must recover the direct path"
        );
        gate.release(&Atomics);
    }

    #[test]
    fn one_successor_waits_in_order_and_services_remote_calls() {
        let gate = SerialGate::new();
        assert!(gate.opportunistic_acquire(&Atomics, 0, || panic!("empty gate")));
        let mut serviced = false;
        assert!(gate.opportunistic_acquire(&Atomics, 1, || {
            assert!(!serviced);
            serviced = true;
            assert_eq!(gate.owner(), 0);
            assert_eq!(gate.next.load(Ordering::Relaxed), 2);
            // A third contender must use STM instead of extending the queue.
            assert!(!gate.opportunistic_acquire(&Atomics, 2, || panic!("full queue")));
            assert_eq!(gate.next.load(Ordering::Relaxed), 2);
            gate.release(&Atomics);
        }));
        assert!(serviced);
        assert_eq!(gate.owner(), 1);
        gate.release(&Atomics);
        gate.enter_tx(&Atomics, 2, || panic!("successor stranded the gate"));
        gate.leave_tx(&Atomics, 2);
    }

    #[test]
    fn probe_preserves_ticket_order_and_wraparound() {
        let gate = Arc::new(SerialGate::new());
        gate.next.store(u64::MAX - 1, Ordering::Relaxed);
        gate.serving.store(u64::MAX - 1, Ordering::Relaxed);
        assert!(gate.opportunistic_acquire(&Atomics, 0, thread::yield_now));
        let waiter = gate.clone();
        let worker = thread::spawn(move || {
            waiter.acquire(&Atomics, 1, thread::yield_now);
            assert_eq!(waiter.owner(), 1);
            waiter.release(&Atomics);
        });
        while gate.next.load(Ordering::Acquire) != 0 {
            thread::yield_now();
        }
        // The queued mandatory entry owns the next ticket; a probe cannot
        // bypass it or increment the ticket counter after failing.
        assert!(!gate.opportunistic_acquire(&Atomics, 2, thread::yield_now));
        assert_eq!(gate.next.load(Ordering::Relaxed), 0);
        gate.release(&Atomics);
        worker.join().unwrap();
        assert_eq!(gate.serving.load(Ordering::Acquire), 0);
        gate.enter_tx(&Atomics, 0, || panic!("ticket rollover stranded the gate"));
        gate.leave_tx(&Atomics, 0);
    }

    #[test]
    fn direct_entries_and_transactions_remain_mutually_exclusive() {
        let gate = Arc::new(SerialGate::new());
        let started = Arc::new(Barrier::new(6));
        let readers = Arc::new(AtomicU64::new(0));
        let writer = Arc::new(AtomicU64::new(u64::MAX));
        let workers: std::vec::Vec<_> = (0..6)
            .map(|cpu| {
                let (gate, started, readers, writer) = (
                    gate.clone(),
                    started.clone(),
                    readers.clone(),
                    writer.clone(),
                );
                thread::spawn(move || {
                    started.wait();
                    let mut transactional = 0;
                    for i in 0..10_000 {
                        let direct = if i % 127 == 0 {
                            gate.acquire(&Atomics, cpu, thread::yield_now);
                            true
                        } else {
                            gate.opportunistic_acquire(&Atomics, cpu, thread::yield_now)
                        };
                        if direct {
                            assert_eq!(writer.swap(cpu, Ordering::SeqCst), u64::MAX);
                            assert_eq!(readers.load(Ordering::SeqCst), 0);
                            if i % 31 == 0 {
                                thread::yield_now();
                            }
                            assert_eq!(readers.load(Ordering::SeqCst), 0);
                            writer.store(u64::MAX, Ordering::SeqCst);
                            gate.release(&Atomics);
                        } else {
                            gate.enter_tx(&Atomics, cpu, thread::yield_now);
                            readers.fetch_add(1, Ordering::SeqCst);
                            assert_eq!(writer.load(Ordering::SeqCst), u64::MAX);
                            if i % 31 == 0 {
                                thread::yield_now();
                            }
                            assert_eq!(writer.load(Ordering::SeqCst), u64::MAX);
                            readers.fetch_sub(1, Ordering::SeqCst);
                            gate.leave_tx(&Atomics, cpu);
                            transactional += 1;
                        }
                    }
                    transactional
                })
            })
            .collect();
        let transactional: u64 = workers.into_iter().map(|w| w.join().unwrap()).sum();
        assert!(
            transactional > 0,
            "contention must use concurrent transactions"
        );
    }
}
