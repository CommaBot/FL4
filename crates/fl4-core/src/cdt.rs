//! The capability derivation tree and slot operations (seL4 object/cnode.c,
//! the part below the invocation decoder).
//!
//! The tree is seL4's doubly linked list in derivation order: a slot's
//! children follow it, and `is_mdb_parent_of` decides where its subtree
//! ends.

use crate::layout::WALK_FUEL;
use crate::capability::Cap;
use crate::error::{Exc, KResult, SysError};
use crate::machine::{Arch, Store};
use crate::objects;
use crate::obj::Slot;
use crate::sched;

fn set_untyped_cap_as_full<S: Store>(s: &mut S, src_cap: Cap, new_cap: Cap, src: Slot) {
    if let (Cap::Untyped { ptr: p1, size_bits: b1, is_device, .. }, Cap::Untyped { ptr: p2, size_bits: b2, .. }) =
        (src_cap, new_cap)
    {
        if p1 == p2 && b1 == b2 {
            src.set_cap(s, Cap::Untyped { ptr: p1, size_bits: b1, free_index: 1u64 << (b1 & 63), is_device });
        }
    }
}

/// seL4 `cteInsert`: put `new_cap`, derived from the cap in `src`, into the
/// empty slot `dest` as `src`'s next sibling or child.
pub fn insert<S: Store>(s: &mut S, new_cap: Cap, src: Slot, dest: Slot) {
    let src_cap = src.cap(s);
    insert_with_cap(s, new_cap, src_cap, src, dest);
}

/// Insert using the source cap already read by this entry. The caller must
/// not have changed it or crossed a preemption point since that read.
pub(crate) fn insert_with_cap<S: Store>(s: &mut S, new_cap: Cap, src_cap: Cap, src: Slot, dest: Slot) {
    let revocable = objects::is_cap_revocable(new_cap, src_cap);
    let next = src.next(s);
    set_untyped_cap_as_full(s, src_cap, new_cap, src);
    dest.set_cap(s, new_cap);
    dest.set_prev(s, src);
    dest.set_next_flags(s, next, revocable, revocable);
    src.set_next(s, dest);
    if !next.is_null() {
        next.set_prev(s, dest);
    }
}

/// seL4 `cteMove`.
pub fn move_cap<S: Store>(s: &mut S, new_cap: Cap, src: Slot, dest: Slot) {
    let prev = src.prev(s);
    let next = src.next(s);
    let revocable = src.revocable(s);
    let first_badged = src.first_badged(s);
    dest.set_cap(s, new_cap);
    dest.set_prev(s, prev);
    dest.set_next_flags(s, next, revocable, first_badged);
    src.clear(s);
    if !prev.is_null() {
        prev.set_next(s, dest);
    }
    if !next.is_null() {
        next.set_prev(s, dest);
    }
}

/// seL4 `cteSwap`.
pub fn swap<S: Store>(s: &mut S, cap1: Cap, slot1: Slot, cap2: Cap, slot2: Slot) {
    slot1.set_cap(s, cap2);
    slot2.set_cap(s, cap1);
    let p1 = slot1.prev(s);
    let n1 = slot1.next(s);
    let r1 = slot1.revocable(s);
    let f1 = slot1.first_badged(s);
    if !p1.is_null() {
        p1.set_next(s, slot2);
    }
    if !n1.is_null() {
        n1.set_prev(s, slot2);
    }
    let p2 = slot2.prev(s);
    let n2 = slot2.next(s);
    let r2 = slot2.revocable(s);
    let f2 = slot2.first_badged(s);
    slot1.set_prev(s, p2);
    slot1.set_next_flags(s, n2, r2, f2);
    slot2.set_prev(s, p1);
    slot2.set_next_flags(s, n1, r1, f1);
    if !p2.is_null() {
        p2.set_next(s, slot1);
    }
    if !n2.is_null() {
        n2.set_prev(s, slot1);
    }
}

fn cap_swap_for_delete<S: Store>(s: &mut S, slot1: Slot, slot2: Slot) {
    if slot1 == slot2 {
        return;
    }
    let c1 = slot1.cap(s);
    let c2 = slot2.cap(s);
    swap(s, c1, slot1, c2, slot2);
}

/// seL4 `isMDBParentOf`.
pub fn is_mdb_parent_of<S: Store>(s: &S, a: Slot, b: Slot) -> bool {
    if !a.revocable(s) {
        return false;
    }
    let ca = a.cap(s);
    let cb = b.cap(s);
    if !objects::same_region_as(ca, cb) {
        return false;
    }
    match ca {
        Cap::Endpoint { badge, .. } => {
            if badge == 0 {
                return true;
            }
            let bb = match cb {
                Cap::Endpoint { badge, .. } => badge,
                _ => 0,
            };
            badge == bb && !b.first_badged(s)
        }
        Cap::Notification { badge, .. } => {
            if badge == 0 {
                return true;
            }
            let bb = match cb {
                Cap::Notification { badge, .. } => badge,
                _ => 0,
            };
            badge == bb && !b.first_badged(s)
        }
        _ => true,
    }
}

/// seL4 `ensureNoChildren`.
pub fn ensure_no_children<S: Store>(s: &S, slot: Slot) -> KResult<()> {
    let next = slot.next(s);
    if !next.is_null() && is_mdb_parent_of(s, slot, next) {
        return Err(Exc::Sys(SysError::RevokeFirst));
    }
    Ok(())
}

/// seL4 `ensureEmptySlot`.
pub fn ensure_empty_slot<S: Store>(s: &S, slot: Slot) -> KResult<()> {
    if !slot.cap(s).is_null() {
        return Err(Exc::Sys(SysError::DeleteFirst));
    }
    Ok(())
}

/// seL4 `isFinalCapability`.
pub fn is_final_capability<S: Store>(s: &S, slot: Slot) -> bool {
    let cap = slot.cap(s);
    is_final_capability_with_cap(s, slot, cap)
}

fn is_final_capability_with_cap<S: Store>(s: &S, slot: Slot, cap: Cap) -> bool {
    let prev = slot.prev(s);
    let prev_same = !prev.is_null() && objects::same_object_as(prev.cap(s), cap);
    if prev_same {
        return false;
    }
    let next = slot.next(s);
    if next.is_null() {
        true
    } else {
        !objects::same_object_as(cap, next.cap(s))
    }
}

/// seL4 `slotCapLongRunningDelete`.
pub fn slot_cap_long_running_delete<S: Store>(s: &S, slot: Slot) -> bool {
    let cap = slot.cap(s);
    if cap.is_null() || !is_final_capability_with_cap(s, slot, cap) {
        return false;
    }
    matches!(cap, Cap::Thread { .. } | Cap::Zombie { .. } | Cap::CNode { .. })
}

/// seL4 `insertNewCap`: a new object's cap, as a child of `parent`.
pub fn insert_new_cap<S: Store>(s: &mut S, parent: Slot, slot: Slot, cap: Cap) {
    let next = parent.next(s);
    slot.set_cap(s, cap);
    slot.set_prev(s, parent);
    slot.set_next_flags(s, next, true, true);
    if !next.is_null() {
        next.set_prev(s, slot);
    }
    parent.set_next(s, slot);
}

fn empty_slot<S: Store, A: Arch>(s: &mut S, a: &mut A, slot: Slot, cleanup: Cap) {
    if slot.cap(s).is_null() {
        return;
    }
    let prev = slot.prev(s);
    let next = slot.next(s);
    let fb = slot.first_badged(s);
    if !prev.is_null() {
        prev.set_next(s, next);
    }
    if !next.is_null() {
        next.set_prev(s, prev);
        let nfb = next.first_badged(s);
        next.set_first_badged(s, nfb || fb);
    }
    slot.clear(s);
    objects::post_cap_deletion(s, a, cleanup);
}

fn cap_removable(cap: Cap, slot: Slot) -> bool {
    match cap {
        Cap::Null => true,
        Cap::Zombie { ptr, number, .. } => number == 0 || (number == 1 && slot.0 == ptr),
        _ => false,
    }
}

fn cap_cyclic_zombie(cap: Cap, slot: Slot) -> bool {
    match cap {
        Cap::Zombie { ptr, .. } => ptr == slot.0,
        _ => false,
    }
}

/// Outcome of `finaliseSlot`.
struct Finalised {
    success: bool,
    cleanup: Cap,
}

/// seL4 `finaliseSlot(slot, false)`, for a cap inside a zombie being
/// deleted: it never deletes, it reduces a zombie by swapping it into the
/// first slot of what it covers, so it needs no recursion. The fuel never
/// runs out on a well-formed CDT; if it did, the caller would restart the
/// operation, as after any preemption.
fn finalise_slot_deferred<S: Store, A: Arch>(s: &mut S, a: &mut A, slot: Slot) -> KResult<Finalised> {
    let mut fuel: u64 = WALK_FUEL;
    while fuel > 0 {
        fuel -= 1;
        let cap = slot.cap(s);
        if cap.is_null() {
            return Ok(Finalised { success: true, cleanup: Cap::Null });
        }
        let fin = is_final_capability_with_cap(s, slot, cap);
        let (remainder, cleanup) = objects::finalise_cap(s, a, cap, fin, false);
        if cap_removable(remainder, slot) {
            return Ok(Finalised { success: true, cleanup });
        }
        slot.set_cap(s, remainder);
        if cap_cyclic_zombie(remainder, slot) {
            return Ok(Finalised { success: false, cleanup });
        }
        // seL4 `reduceZombie(slot, false)`.
        if let Cap::Zombie { ptr, .. } = remainder {
            cap_swap_for_delete(s, Slot(ptr), slot);
        }
        sched::preemption_point(s, a)?;
    }
    Err(Exc::Preempted)
}

/// seL4 `finaliseSlot(slot, true)`: each round finishes or deletes the
/// last cap a zombie covers (seL4 `reduceZombie(slot, true)`).
fn finalise_slot_immediate<S: Store, A: Arch>(s: &mut S, a: &mut A, slot: Slot) -> KResult<Finalised> {
    let mut fuel: u64 = WALK_FUEL;
    while fuel > 0 {
        fuel -= 1;
        let cap = slot.cap(s);
        if cap.is_null() {
            return Ok(Finalised { success: true, cleanup: Cap::Null });
        }
        let fin = is_final_capability_with_cap(s, slot, cap);
        let (remainder, cleanup) = objects::finalise_cap(s, a, cap, fin, false);
        if cap_removable(remainder, slot) {
            return Ok(Finalised { success: true, cleanup });
        }
        slot.set_cap(s, remainder);
        if let Cap::Zombie { ptr, ztype, number: n } = remainder {
            let end = Slot::index(ptr, n.wrapping_sub(1));
            delete_deferred(s, a, end)?;
            if let Cap::Zombie { ptr: p2, ztype: t2, number: n2 } = slot.cap(s) {
                if p2 == ptr && n2 == n && t2 == ztype {
                    slot.set_cap(s, Cap::Zombie { ptr, ztype, number: n.wrapping_sub(1) });
                }
            }
        }
        sched::preemption_point(s, a)?;
    }
    Err(Exc::Preempted)
}

/// seL4 `cteDelete(slot, false)`.
fn delete_deferred<S: Store, A: Arch>(s: &mut S, a: &mut A, slot: Slot) -> KResult<()> {
    let f = finalise_slot_deferred(s, a, slot)?;
    if f.success {
        empty_slot(s, a, slot, f.cleanup);
    }
    Ok(())
}

/// seL4 `cteDelete`.
pub fn delete<S: Store, A: Arch>(s: &mut S, a: &mut A, slot: Slot, exposed: bool) -> KResult<()> {
    if !exposed {
        return delete_deferred(s, a, slot);
    }
    let f = finalise_slot_immediate(s, a, slot)?;
    empty_slot(s, a, slot, f.cleanup);
    Ok(())
}

/// seL4 `cteDeleteOne`, for the caps it is used on (an IRQ slot's
/// notification cap): they finalise immediately.
pub fn delete_one<S: Store, A: Arch>(s: &mut S, a: &mut A, slot: Slot) {
    let cap = slot.cap(s);
    if !cap.is_null() {
        let fin = is_final_capability_with_cap(s, slot, cap);
        let _ = objects::finalise_cap_object(s, a, cap, fin);
        empty_slot(s, a, slot, Cap::Null);
    }
}

/// seL4 `cteRevoke`.
pub fn revoke<S: Store, A: Arch>(s: &mut S, a: &mut A, slot: Slot) -> KResult<()> {
    // The fuel never runs out on a well-formed CDT; if it did, the caller
    // would restart the revoke, as after any preemption.
    let mut fuel: u64 = WALK_FUEL;
    while fuel > 0 {
        fuel -= 1;
        let next = slot.next(s);
        if next.is_null() || !is_mdb_parent_of(s, slot, next) {
            return Ok(());
        }
        delete(s, a, next, true)?;
        sched::preemption_point(s, a)?;
    }
    Err(Exc::Preempted)
}
