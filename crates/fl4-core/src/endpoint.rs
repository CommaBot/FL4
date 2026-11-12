//! Endpoints (seL4 object/endpoint.c, MCS).

use crate::cap::Cap;
use crate::ipc;
use crate::machine::{Arch, Store};
use crate::notification;
use crate::obj::{Ep, Ntfn, Reply, Sc, Tcb, EP_IDLE, EP_RECV, EP_SEND};
use crate::sched;
use crate::schedcontext;
use crate::sporadic;
use crate::tcbqueue::{self, Link, Queue};

const FLAG_GRANT: u64 = 1;
const FLAG_GRANT_REPLY: u64 = 2;
const FLAG_CALL: u64 = 4;

fn get_queue<S: Store>(s: &S, ep: Ep) -> Queue {
    Queue { head: Tcb(ep.head(s)), end: Tcb(ep.tail(s)) }
}

fn set_queue<S: Store>(s: &mut S, ep: Ep, q: Queue, state: u64) {
    ep.set_queue(s, q.head.0, q.end.0, state);
}

/// seL4 `tcbEPAppend`.
fn ep_append<S: Store>(s: &mut S, ep: Ep, t: Tcb, state: u64) {
    let q = get_queue(s, ep);
    let q = tcbqueue::append_by_prio(s, Link::Ep, q, t);
    set_queue(s, ep, q, state);
}

/// seL4 `tcbEPDequeue`.
pub fn ep_dequeue<S: Store>(s: &mut S, ep_ptr: u64, t: Tcb) {
    let ep = Ep(ep_ptr);
    let q = get_queue(s, ep);
    let st = ep.state(s);
    let q = tcbqueue::remove(s, Link::Ep, q, t);
    set_queue(s, ep, q, if q.is_empty() { EP_IDLE } else { st });
}

/// seL4 `reorderEP`.
pub fn reorder_ep<S: Store>(s: &mut S, ep_ptr: u64, t: Tcb) {
    let ep = Ep(ep_ptr);
    let st = ep.state(s);
    let q = get_queue(s, ep);
    let q = tcbqueue::remove(s, Link::Ep, q, t);
    let q = tcbqueue::append_by_prio(s, Link::Ep, q, t);
    set_queue(s, ep, q, st);
}

fn unblock_sporadic<S: Store>(s: &mut S, t: Tcb) {
    let sc = Sc(t.sc(s));
    if sporadic::sc_sporadic(s, sc) && sc != sched::cur_sc(s) {
        sporadic::unblock_check(s, sc);
    }
}

/// seL4 `sendIPC` (MCS).
#[allow(clippy::too_many_arguments)]
pub fn send_ipc<S: Store, A: Arch>(
    s: &mut S,
    a: &mut A,
    blocking: bool,
    do_call: bool,
    badge: u64,
    can_grant: bool,
    can_grant_reply: bool,
    can_donate: bool,
    thread: Tcb,
    ep_ptr: u64,
) {
    let ep = Ep(ep_ptr);
    let st = ep.state(s);
    if st == EP_IDLE || st == EP_SEND {
        if blocking {
            thread.set_state(s, sched::TS_BLOCKED_ON_SEND);
            thread.set_block_obj(s, ep_ptr);
            thread.set_block_badge(s, badge);
            let f = (if can_grant { FLAG_GRANT } else { 0 })
                | (if can_grant_reply { FLAG_GRANT_REPLY } else { 0 })
                | (if do_call { FLAG_CALL } else { 0 });
            thread.set_block_flags(s, f);
            sched::schedule_tcb(s, thread);
            ep_append(s, ep, thread, EP_SEND);
        }
        return;
    }
    // Recv: a receiver is waiting.
    let dest = get_queue(s, ep).head;
    ep_dequeue(s, ep_ptr, dest);
    ipc::do_ipc_transfer(s, a, thread, ep_ptr, badge, can_grant, dest);
    let reply = Reply(dest.reply_obj(s));
    if reply.0 != 0 {
        ipc::reply_unlink(s, reply, dest);
    }
    if do_call || thread.fault_type(s) != fl4_abi::consts::fault::NullFault {
        if reply.0 != 0 && (can_grant || can_grant_reply) {
            ipc::reply_push(s, a, thread, dest, reply, can_donate);
        } else {
            sched::set_thread_state(s, thread, sched::TS_INACTIVE);
        }
    } else if can_donate && dest.sc(s) == 0 {
        let sc = Sc(thread.sc(s));
        schedcontext::donate(s, a, sc, dest);
    }
    sched::set_thread_state(s, dest, sched::TS_RUNNING);
    unblock_sporadic(s, dest);
    sched::possible_switch_to(s, dest);
}

/// seL4 `receiveIPC` (MCS).
pub fn receive_ipc<S: Store, A: Arch>(s: &mut S, a: &mut A, thread: Tcb, cap: Cap, blocking: bool, reply_cap: Cap) {
    let ep_ptr = cap.ptr();
    let ep = Ep(ep_ptr);
    let mut reply = Reply(0);
    if let Cap::Reply { ptr, .. } = reply_cap {
        reply = Reply(ptr);
        let rt = Tcb(reply.tcb(s));
        if !rt.is_null() && rt != thread {
            ipc::cancel_ipc(s, a, rt);
        }
    }
    let ntfn = Ntfn(thread.bound_ntfn(s));
    if ntfn.0 != 0 && ntfn.state(s) == crate::obj::NTFN_ACTIVE {
        notification::complete_signal(s, a, ntfn, thread);
        return;
    }
    if ntfn.0 != 0 && blocking {
        notification::maybe_return_sched_context(s, ntfn, thread);
    }
    let st = ep.state(s);
    if st == EP_IDLE || st == EP_RECV {
        if blocking {
            thread.set_state(s, sched::TS_BLOCKED_ON_RECV);
            thread.set_block_obj(s, ep_ptr);
            thread.set_reply_obj(s, reply.0);
            sched::schedule_tcb(s, thread);
            if reply.0 != 0 {
                reply.set_tcb(s, thread.0);
            }
            ep_append(s, ep, thread, EP_RECV);
        } else {
            thread.set_reg(s, crate::layout::reg::BADGE, 0);
        }
        return;
    }
    // Send: a sender is waiting.
    let sender = get_queue(s, ep).head;
    ep_dequeue(s, ep_ptr, sender);
    let badge = sender.block_badge(s);
    let flags = sender.block_flags(s);
    let can_grant = flags & FLAG_GRANT != 0;
    let can_grant_reply = flags & FLAG_GRANT_REPLY != 0;
    let do_call = flags & FLAG_CALL != 0;
    ipc::do_ipc_transfer(s, a, sender, ep_ptr, badge, can_grant, thread);
    unblock_sporadic(s, sender);
    let ftype = sender.fault_type(s);
    if do_call || ftype != fl4_abi::consts::fault::NullFault {
        if (can_grant || can_grant_reply) && reply.0 != 0 {
            let can_donate = sender.sc(s) != 0 && ftype != fl4_abi::consts::fault::Timeout;
            ipc::reply_push(s, a, sender, thread, reply, can_donate);
        } else {
            sched::set_thread_state(s, sender, sched::TS_INACTIVE);
        }
    } else {
        sched::set_thread_state(s, sender, sched::TS_RUNNING);
        sched::possible_switch_to(s, sender);
    }
}

fn restart_thread_if_no_fault<S: Store>(s: &mut S, t: Tcb) {
    if t.fault_type(s) == fl4_abi::consts::fault::NullFault {
        sched::set_thread_state(s, t, sched::TS_RESTART);
        unblock_sporadic(s, t);
        sched::possible_switch_to(s, t);
    } else {
        sched::set_thread_state(s, t, sched::TS_INACTIVE);
    }
}

/// seL4 `cancelAllIPC`.
pub fn cancel_all_ipc<S: Store>(s: &mut S, ep_ptr: u64) {
    let ep = Ep(ep_ptr);
    if ep.state(s) == EP_IDLE {
        return;
    }
    let mut t = get_queue(s, ep).head;
    while !t.is_null() {
        let next = tcbqueue::next_of(s, Link::Ep, t);
        ep_dequeue(s, ep_ptr, t);
        if t.state(s) == sched::TS_BLOCKED_ON_RECV {
            let r = Reply(t.reply_obj(s));
            if r.0 != 0 {
                ipc::reply_unlink(s, r, t);
            }
        }
        restart_thread_if_no_fault(s, t);
        t = next;
    }
    sched::reschedule_required(s);
}

/// seL4 `cancelBadgedSends`.
pub fn cancel_badged_sends<S: Store>(s: &mut S, ep_ptr: u64, badge: u64) {
    let ep = Ep(ep_ptr);
    if ep.state(s) != EP_SEND {
        return;
    }
    let mut t = get_queue(s, ep).head;
    while !t.is_null() {
        let next = tcbqueue::next_of(s, Link::Ep, t);
        if t.block_badge(s) == badge {
            ep_dequeue(s, ep_ptr, t);
            restart_thread_if_no_fault(s, t);
        }
        t = next;
    }
    sched::reschedule_required(s);
}
