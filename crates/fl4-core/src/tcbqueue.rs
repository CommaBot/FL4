//! TCB queues linked through `sched_next`/`sched_prev` (seL4 tcb_queue_t).
//! Ready queues, the release queue, and (MCS) endpoint and notification
//! queues all use them. Operations take and return the queue by value; the
//! caller stores it back.

use crate::machine::Store;
use crate::obj::Tcb;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Queue {
    pub head: Tcb,
    pub end: Tcb,
}

impl Queue {
    pub fn empty() -> Queue {
        Queue { head: Tcb(0), end: Tcb(0) }
    }
    pub fn is_empty(self) -> bool {
        self.head.is_null()
    }
}

pub fn prepend<S: Store>(s: &mut S, q: Queue, t: Tcb) -> Queue {
    if q.is_empty() {
        t.set_sched_next(s, 0);
        t.set_sched_prev(s, 0);
        Queue { head: t, end: t }
    } else {
        t.set_sched_next(s, q.head.0);
        t.set_sched_prev(s, 0);
        q.head.set_sched_prev(s, t.0);
        Queue { head: t, end: q.end }
    }
}

pub fn append<S: Store>(s: &mut S, q: Queue, t: Tcb) -> Queue {
    if q.is_empty() {
        t.set_sched_next(s, 0);
        t.set_sched_prev(s, 0);
        Queue { head: t, end: t }
    } else {
        q.end.set_sched_next(s, t.0);
        t.set_sched_prev(s, q.end.0);
        t.set_sched_next(s, 0);
        Queue { head: q.head, end: t }
    }
}

pub fn remove<S: Store>(s: &mut S, q: Queue, t: Tcb) -> Queue {
    let before = Tcb(t.sched_prev(s));
    let after = Tcb(t.sched_next(s));
    let r = if q.head == t && q.end == t {
        Queue::empty()
    } else if q.head == t {
        after.set_sched_prev(s, 0);
        Queue { head: after, end: q.end }
    } else if q.end == t {
        before.set_sched_next(s, 0);
        Queue { head: q.head, end: before }
    } else {
        before.set_sched_next(s, after.0);
        after.set_sched_prev(s, before.0);
        q
    };
    t.set_sched_next(s, 0);
    t.set_sched_prev(s, 0);
    r
}

/// `tcb_queue_insert`: put `t` immediately before `after`, which is not the
/// head.
pub fn insert_before<S: Store>(s: &mut S, t: Tcb, after: Tcb) {
    let before = Tcb(after.sched_prev(s));
    after.set_sched_prev(s, t.0);
    t.set_sched_next(s, after.0);
    t.set_sched_prev(s, before.0);
    before.set_sched_next(s, t.0);
}

/// `tcb_queue_insert_after`: put `t` immediately after `before`, which is
/// not the end.
pub fn insert_after<S: Store>(s: &mut S, t: Tcb, before: Tcb) {
    let after = Tcb(before.sched_next(s));
    t.set_sched_prev(s, before.0);
    t.set_sched_next(s, after.0);
    after.set_sched_prev(s, t.0);
    before.set_sched_next(s, t.0);
}

/// seL4 MCS `tcbAppend`: insert in priority order (FIFO among equals).
pub fn append_by_prio<S: Store>(s: &mut S, q: Queue, t: Tcb) -> Queue {
    let p = t.prio(s);
    if q.is_empty() || p > q.head.prio(s) {
        prepend(s, q, t)
    } else if q.end.prio(s) >= p {
        append(s, q, t)
    } else {
        let mut before = q.end;
        while !before.is_null() && p > before.prio(s) {
            before = Tcb(before.sched_prev(s));
        }
        insert_after(s, t, before);
        q
    }
}
