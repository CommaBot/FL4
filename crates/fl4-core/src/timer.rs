//! Per-TCB deadline timers (l4h 0003, 0006; DESIGN.md §4). Armed timers sit
//! in a per-core red-black tree ordered by deadline, with the earliest
//! cached. Insert and remove are O(log n); at most `FIRE_BATCH` timers fire
//! per kernel entry.

use crate::layout::node;
use crate::machine::{Arch, Store};
use crate::obj::{node_get, node_set, Tcb};

pub const FIRE_BATCH: u64 = 32;

const RED: u64 = 1;

fn is_red<S: Store>(s: &S, t: Tcb) -> bool {
    !t.is_null() && t.timer_height(s) & RED != 0
}

fn set_red<S: Store>(s: &mut S, t: Tcb, red: bool) {
    let h = t.timer_height(s) & !RED;
    t.set_timer_height(s, h | if red { RED } else { 0 });
}

fn core_of<S: Store>(s: &S, t: Tcb) -> u64 {
    t.timer_height(s) >> 8
}

fn left<S: Store>(s: &S, t: Tcb) -> Tcb {
    Tcb(t.timer_left(s))
}

fn right<S: Store>(s: &S, t: Tcb) -> Tcb {
    Tcb(t.timer_right(s))
}

fn parent<S: Store>(s: &S, t: Tcb) -> Tcb {
    Tcb(t.timer_parent(s))
}

fn root<S: Store>(s: &S, core: u64) -> Tcb {
    Tcb(node_get(s, core, node::TIMER_ROOT))
}

fn set_root<S: Store>(s: &mut S, core: u64, t: Tcb) {
    node_set(s, core, node::TIMER_ROOT, t.0)
}

fn replace_child<S: Store>(s: &mut S, core: u64, p: Tcb, old: Tcb, new: Tcb) {
    if p.is_null() {
        set_root(s, core, new);
    } else if left(s, p) == old {
        p.set_timer_left(s, new.0);
    } else {
        p.set_timer_right(s, new.0);
    }
}

fn rotate_left<S: Store>(s: &mut S, core: u64, x: Tcb) {
    let y = right(s, x);
    let yl = left(s, y);
    x.set_timer_right(s, yl.0);
    if !yl.is_null() {
        yl.set_timer_parent(s, x.0);
    }
    let xp = parent(s, x);
    y.set_timer_parent(s, xp.0);
    replace_child(s, core, xp, x, y);
    y.set_timer_left(s, x.0);
    x.set_timer_parent(s, y.0);
}

fn rotate_right<S: Store>(s: &mut S, core: u64, x: Tcb) {
    let y = left(s, x);
    let yr = right(s, y);
    x.set_timer_left(s, yr.0);
    if !yr.is_null() {
        yr.set_timer_parent(s, x.0);
    }
    let xp = parent(s, x);
    y.set_timer_parent(s, xp.0);
    replace_child(s, core, xp, x, y);
    y.set_timer_right(s, x.0);
    x.set_timer_parent(s, y.0);
}

fn insert_fixup<S: Store>(s: &mut S, core: u64, z0: Tcb) {
    let mut z = z0;
    // Each round moves z two levels up or ends the loop.
    let mut fuel: u64 = 128;
    loop {
        let p = parent(s, z);
        if p.is_null() || !is_red(s, p) || fuel == 0 {
            break;
        }
        fuel -= 1;
        let g = parent(s, p);
        if p == left(s, g) {
            let u = right(s, g);
            if is_red(s, u) {
                set_red(s, p, false);
                set_red(s, u, false);
                set_red(s, g, true);
                z = g;
                continue;
            }
            let mut pp = p;
            if z == right(s, p) {
                rotate_left(s, core, p);
                z = p;
                pp = parent(s, z);
            }
            set_red(s, pp, false);
            set_red(s, g, true);
            rotate_right(s, core, g);
        } else {
            let u = left(s, g);
            if is_red(s, u) {
                set_red(s, p, false);
                set_red(s, u, false);
                set_red(s, g, true);
                z = g;
                continue;
            }
            let mut pp = p;
            if z == left(s, p) {
                rotate_right(s, core, p);
                z = p;
                pp = parent(s, z);
            }
            set_red(s, pp, false);
            set_red(s, g, true);
            rotate_left(s, core, g);
        }
    }
    let r = root(s, core);
    set_red(s, r, false);
}

fn remove_fixup<S: Store>(s: &mut S, core: u64, x0: Tcb, parent0: Tcb) {
    let mut x = x0;
    let mut p = parent0;
    let mut fuel: u64 = 256;
    while x != root(s, core) && !is_red(s, x) && !p.is_null() && fuel > 0 {
        fuel -= 1;
        if x == left(s, p) {
            let mut w = right(s, p);
            if is_red(s, w) {
                set_red(s, w, false);
                set_red(s, p, true);
                rotate_left(s, core, p);
                w = right(s, p);
            }
            if !is_red(s, left(s, w)) && !is_red(s, right(s, w)) {
                set_red(s, w, true);
                x = p;
                p = parent(s, x);
            } else {
                if !is_red(s, right(s, w)) {
                    let wl = left(s, w);
                    set_red(s, wl, false);
                    set_red(s, w, true);
                    rotate_right(s, core, w);
                    w = right(s, p);
                }
                let pr = is_red(s, p);
                set_red(s, w, pr);
                set_red(s, p, false);
                let wr = right(s, w);
                set_red(s, wr, false);
                rotate_left(s, core, p);
                x = root(s, core);
                p = Tcb(0);
            }
        } else {
            let mut w = left(s, p);
            if is_red(s, w) {
                set_red(s, w, false);
                set_red(s, p, true);
                rotate_right(s, core, p);
                w = left(s, p);
            }
            if !is_red(s, left(s, w)) && !is_red(s, right(s, w)) {
                set_red(s, w, true);
                x = p;
                p = parent(s, x);
            } else {
                if !is_red(s, left(s, w)) {
                    let wr = right(s, w);
                    set_red(s, wr, false);
                    set_red(s, w, true);
                    rotate_left(s, core, w);
                    w = left(s, p);
                }
                let pr = is_red(s, p);
                set_red(s, w, pr);
                set_red(s, p, false);
                let wl = left(s, w);
                set_red(s, wl, false);
                rotate_right(s, core, p);
                x = root(s, core);
                p = Tcb(0);
            }
        }
    }
    if !x.is_null() {
        set_red(s, x, false);
    }
}

/// Disarm `t`'s timer if it is armed (l4h `timerQueueRemove`).
pub fn remove<S: Store>(s: &mut S, t: Tcb) {
    if t.timer_deadline(s) == 0 {
        return;
    }
    let core = core_of(s, t);
    if node_get(s, core, node::TIMER_MIN) == t.0 {
        let mut next = right(s, t);
        if !next.is_null() {
            while !left(s, next).is_null() {
                next = left(s, next);
            }
        } else {
            next = parent(s, t);
        }
        node_set(s, core, node::TIMER_MIN, next.0);
    }
    let x;
    let x_parent;
    let mut removed_red = is_red(s, t);
    let tl = left(s, t);
    let tr = right(s, t);
    if tl.is_null() || tr.is_null() {
        x = if !tl.is_null() { tl } else { tr };
        x_parent = parent(s, t);
        replace_child(s, core, x_parent, t, x);
        if !x.is_null() {
            x.set_timer_parent(s, x_parent.0);
        }
    } else {
        let mut y = tr;
        while !left(s, y).is_null() {
            y = left(s, y);
        }
        removed_red = is_red(s, y);
        x = right(s, y);
        if parent(s, y) == t {
            x_parent = y;
        } else {
            x_parent = parent(s, y);
            x_parent.set_timer_left(s, x.0);
            if !x.is_null() {
                x.set_timer_parent(s, x_parent.0);
            }
            y.set_timer_right(s, tr.0);
            tr.set_timer_parent(s, y.0);
        }
        let tp = parent(s, t);
        replace_child(s, core, tp, t, y);
        y.set_timer_parent(s, tp.0);
        y.set_timer_left(s, tl.0);
        tl.set_timer_parent(s, y.0);
        let tred = is_red(s, t);
        set_red(s, y, tred);
    }
    if !removed_red {
        remove_fixup(s, core, x, x_parent);
    }
    t.set_timer_parent(s, 0);
    t.set_timer_left(s, 0);
    t.set_timer_right(s, 0);
    t.set_timer_height(s, 0);
    t.set_timer_deadline(s, 0);
}

/// Arm `t`'s timer for `deadline` with `badge`, replacing any earlier
/// setting; deadline 0 disarms (l4h `timerQueueInsert`).
pub fn insert<S: Store>(s: &mut S, t: Tcb, deadline: u64, badge: u64) {
    remove(s, t);
    if deadline == 0 {
        return;
    }
    let core = s.cur_cpu();
    let mut p = Tcb(0);
    let mut cur = root(s, core);
    let mut go_left = false;
    let mut first = true;
    while !cur.is_null() {
        p = cur;
        if deadline < cur.timer_deadline(s) {
            go_left = true;
            cur = left(s, cur);
        } else {
            go_left = false;
            first = false;
            cur = right(s, cur);
        }
    }
    if p.is_null() {
        set_root(s, core, t);
    } else if go_left {
        p.set_timer_left(s, t.0);
    } else {
        p.set_timer_right(s, t.0);
    }
    t.set_timer_deadline(s, deadline);
    t.set_timer_badge(s, badge);
    t.set_timer_parent(s, p.0);
    t.set_timer_left(s, 0);
    t.set_timer_right(s, 0);
    t.set_timer_height(s, (core << 8) | RED);
    insert_fixup(s, core, t);
    if first {
        node_set(s, core, node::TIMER_MIN, t.0);
        node_set(s, core, node::REPROGRAM, 1);
    }
}

/// The earliest armed deadline on this core, or 0.
pub fn earliest<S: Store>(s: &S) -> u64 {
    let t = Tcb(node_get(s, s.cur_cpu(), node::TIMER_MIN));
    if t.is_null() {
        0
    } else {
        t.timer_deadline(s)
    }
}

/// Fire due timers, at most `FIRE_BATCH` (l4h `fireTimers`).
pub fn fire<S: Store, A: Arch>(s: &mut S, a: &mut A) {
    let now = node_get(s, s.cur_cpu(), node::CUR_TIME);
    let mut i = 0;
    while i < FIRE_BATCH {
        let t = Tcb(node_get(s, s.cur_cpu(), node::TIMER_MIN));
        if t.is_null() || t.timer_deadline(s) > now {
            return;
        }
        let badge = t.timer_badge(s);
        remove(s, t);
        let n = t.bound_ntfn(s);
        if n != 0 {
            crate::notification::send_signal(s, a, n, badge);
        }
        let c = s.cur_cpu();
        node_set(s, c, node::REPROGRAM, 1);
        i += 1;
    }
}
