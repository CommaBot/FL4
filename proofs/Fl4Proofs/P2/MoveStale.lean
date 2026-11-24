/-
# P2 (line p2sl): `PathObl.move` against the ReplyRecv fast path's write order

**Finding** (for the ownership map of `P2/OwnMap.lean`, v4: a thread's
`STATE`, `BLOCK_OBJ` and `REPLY_OBJ` are its home core's; only its queue links
`EP_NEXT` / `EP_PREV` are `lock <BLOCK_OBJ>`'s while `STATE` is 3 or 6).
`fastpath.reply_recv_found` (and `reply_recv_vm_found`) as extracted at
0d242948 block the current thread `t` by writing `STATE := TS_BLOCKED_ON_RECV`
*before* `BLOCK_OBJ := ep`. `BLOCK_OBJ` is never cleared when a thread resumes,
so between the two writes it holds an earlier object (0 for a thread that
never blocked), which fl4-sync's `local_syscall` has not locked. That one
write moves `t`'s queue links from `core (home)` to `lock <stale object>`, so
`PathObl.OwnMove`, checked at every write (`PathObl.move`), fails. Writing
`BLOCK_OBJ` first (kernel change 5f480380 / e53e2eda, "write the
owner-deciding word last when publishing") moves them to `lock ep`, which the
glue holds.

The fault fast path's `STATE := TS_BLOCKED_ON_REPLY` (5) before `REPLY_OBJ`
is no longer an issue: state 5 is not queued and `REPLY_OBJ` decides no owner.

* `block_stale_not_move`: the memory-level statement, over `OwnMap.own`;
* `set_state_stale_mguard_fails`: the extracted `obj.Tcb.set_state` on the
  checking store of `PathObl.move` fails there.

Premise: `OwnMap.LayP` [J] (P1's placement, `P2/OwnLayout.lean`).
-/
import Fl4Proofs.P2.OwnLayout
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.MoveStale
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap
open Classical

/-- The owner of a thread's `EP_NEXT`: the lock of `BLOCK_OBJ` while queued,
else the home core. -/
theorem own_ep_next {K : KLayout} (hL : LayP K) {t : U64} (ht : K.heap t = some .tcb) (m : U64 → U64) :
    own K m (fld t oEP_NEXT) =
      if QueuedState (m (fld t oSTATE)) then .lock (m (fld t oBLOCK_OBJ)) else .core (m (fld t oAFFINITY)) := by
  have hv := hL.tcb_fld ht (off := oEP_NEXT) (by simp [oEP_NEXT])
  have e : (fld t oEP_NEXT).val = t.val + 3496 := by rw [hv]; simp [oEP_NEXT]
  have hr : region K (fld t oEP_NEXT) = .tcb t :=
    hL.region_tcb ht ⟨by omega, by rw [e]; norm_num⟩ (by omega)
  have ho : (fld t oEP_NEXT).val - t.val = 3496 := by omega
  have h1 : ¬ GateField 3496 := by unfold GateField; decide
  have h2 : ¬ TimerField 3496 := by unfold TimerField; decide
  have h3 : GField 3496 := by unfold GField; decide
  simp only [own, hr, ho, tcbOwner, if_neg h1, if_neg h2, if_pos h3, gOwner]

/-- **Queueing a running thread through a stale `BLOCK_OBJ` is no owner move**:
from a memory where `t` is not queued to one where its `STATE` is queued and
its `BLOCK_OBJ` names an object the path has not locked. -/
theorem block_stale_not_move {K : KLayout} (hL : LayP K) {t : U64} (ht : K.heap t = some .tcb)
    {m m' : U64 → U64} {c : U64} {lk : U64 → Prop}
    (hq : ¬ QueuedState (m (fld t oSTATE))) (hs : QueuedState (m' (fld t oSTATE)))
    (hl : ¬ lk (m' (fld t oBLOCK_OBJ))) :
    ¬ PathObl.OwnMove (own K) c lk m m' := by
  intro hM
  have e0 := own_ep_next hL ht m
  have e1 := own_ep_next hL ht m'
  rw [if_neg hq] at e0; rw [if_pos hs] at e1
  have := (hM (fld t oEP_NEXT) (by rw [e0, e1]; simp)).2
  rw [e1] at this; exact hl this

/-- **The extracted write on `PathObl.move`'s checking store fails**: `t` not
queued, the state written `TS_BLOCKED_ON_RECV` (3), its `BLOCK_OBJ` not
locked. -/
theorem set_state_stale_mguard_fails {S : Type} {st : machine.Store S} [L : LawfulStore st]
    {K : KLayout} (hL : LayP K) {t : U64} (ht : K.heap t = some .tcb) {s : S}
    {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64} {User : U64 → Prop} {c : U64} {lk : U64 → Prop}
    (hq : ¬ QueuedState (L.mem s (fld t oSTATE)))
    (ha : Aligned (fld t oSTATE)) (hb : Aligned (fld t oBLOCK_OBJ))
    (hl : ¬ lk (L.mem s (fld t oBLOCK_OBJ))) :
    obj.Tcb.set_state (PathObl.mguard st
      (fun x y => PathObl.StepOK (own K) cls ko User c lk (L.mem x) (L.mem y))) t s 3#u64 = fail .panic := by
  have vS := hL.tcb_fld ht (off := oSTATE) (by simp [oSTATE])
  have vB := hL.tcb_fld ht (off := oBLOCK_OBJ) (by simp [oBLOCK_OBJ])
  rw [oSTATE_val] at vS; rw [oBOBJ_val] at vB
  have hs : L.mem (L.wr s (fld t oSTATE) 3#u64) (fld t oSTATE) = 3#u64 := L.mem_wr_same ha
  have hbo : L.mem (L.wr s (fld t oSTATE) 3#u64) (fld t oBLOCK_OBJ) = L.mem s (fld t oBLOCK_OBJ) :=
    L.mem_wr_ne ha hb (by omega)
  have hn : ¬ PathObl.StepOK (own K) cls ko User c lk (L.mem s) (L.mem (L.wr s (fld t oSTATE) 3#u64)) :=
    fun hst => block_stale_not_move hL ht hq (by rw [hs]; simp [QueuedState]) (by rw [hbo]; exact hl) hst.1
  unfold obj.Tcb.set_state
  simp only [lift, bind_ok]
  have e : core.num.U64.wrapping_add t layout.tcb.STATE = fld t oSTATE := by
    have : layout.tcb.STATE = oSTATE := UScalar.eq_of_val_eq (by rw [oSTATE_val]; exact P0.Consts.layout.tcb.STATE.val_eq)
    rw [this]; rfl
  rw [e]
  show (do let s' ← st.write s (fld t oSTATE) 3#u64
           if PathObl.StepOK (own K) cls ko User c lk (L.mem s) (L.mem s') then ok s' else fail .panic) = _
  rw [L.write_eq, bind_tc_ok, if_neg hn]

end Fl4Proofs.P2.MoveStale
