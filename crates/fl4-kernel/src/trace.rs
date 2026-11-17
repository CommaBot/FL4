//! Best-effort debug entries. Never wait: a panic may interrupt a writer.
use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicBool, Ordering};

pub type Entry = [u64; 8];

struct Entries<const N: usize> {
    ring: [Entry; N],
    next: usize,
}

pub struct Trace<const N: usize> {
    busy: AtomicBool,
    entries: UnsafeCell<Entries<N>>,
}

// Every access to entries holds busy, including panic dumps.
unsafe impl<const N: usize> Sync for Trace<N> {}

struct Unlock<'a>(&'a AtomicBool);
impl Drop for Unlock<'_> {
    fn drop(&mut self) { self.0.store(false, Ordering::Release); }
}

impl<const N: usize> Trace<N> {
    pub const fn new() -> Self {
        assert!(N >= 2);
        Self {
            busy: AtomicBool::new(false),
            entries: UnsafeCell::new(Entries { ring: [[0; 8]; N], next: 0 }),
        }
    }

    fn try_lock(&self) -> Option<Unlock<'_>> {
        self.busy.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .ok().map(|_| Unlock(&self.busy))
    }

    pub fn record(&self, e: Entry) {
        let Some(_lock) = self.try_lock() else { return; };
        let entries = unsafe { &mut *self.entries.get() };
        let n = entries.next;
        // Collapse loops of period 1 and 2.
        if n < 2 || (entries.ring[(n - 1) % N] != e && entries.ring[(n - 2) % N] != e) {
            entries.ring[n % N] = e;
            entries.next = n.wrapping_add(1);
        }
    }

    /// A recursive panic skips the dump instead of waiting on itself.
    /// Visit one entry at a time: panic may run on a 4 KiB IST stack.
    pub fn visit_recent(&self, limit: usize, mut visit: impl FnMut(usize, Entry)) -> bool {
        let Some(_lock) = self.try_lock() else { return false; };
        let entries = unsafe { &*self.entries.get() };
        let count = entries.next.min(N).min(limit);
        let start = entries.next - count;
        for i in start..entries.next {
            visit(i, entries.ring[i % N]);
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wraps_and_collapses_short_loops() {
        let trace = Trace::<4>::new();
        trace.record([1; 8]);
        trace.record([2; 8]);
        trace.record([1; 8]);
        trace.record([2; 8]);
        let mut entries = std::vec::Vec::new();
        assert!(trace.visit_recent(4, |i, e| entries.push((i, e))));
        assert_eq!(entries, [(0, [1; 8]), (1, [2; 8])]);
        for i in 3..=6 { trace.record([i; 8]); }
        entries.clear();
        assert!(trace.visit_recent(4, |i, e| entries.push((i, e))));
        assert_eq!(entries, [(2, [3; 8]), (3, [4; 8]), (4, [5; 8]), (5, [6; 8])]);
    }

    #[test]
    fn busy_trace_and_recursive_panic_dump_never_wait() {
        let trace = Trace::<4>::new();
        trace.record([1; 8]);
        assert!(trace.visit_recent(1, |_, e| {
            trace.record([2; 8]);
            assert!(!trace.visit_recent(1, |_, _| panic!("busy trace was accessed")));
            assert_eq!(e, [1; 8]);
        }));
        assert!(trace.visit_recent(1, |i, e| assert_eq!((i, e), (0, [1; 8]))));
    }
}
