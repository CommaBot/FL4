/-
# P2 (line p2sl): `PathObl.move` against the fast paths' write order

**Finding.** The fast paths block the current thread `t` by writing `STATE`
*before* the object word that names the lock `STATE` then selects:

* `fastpath.fault`: `t.set_state(TS_BLOCKED_ON_REPLY)`, then
  `t.set_reply_obj(r)`;
* `fastpath.reply_recv_found`: `t.set_state(TS_BLOCKED_ON_RECV)`, then
  `t.set_block_obj(ep)`, `t.set_reply_obj(r)`.

(`fastpath_vm.rs` has the same two orders.) `BLOCK_OBJ` and `REPLY_OBJ` are
never cleared when a thread resumes, so between the two writes they hold an
earlier object (0 for a thread that never blocked), which fl4-sync's
`local_syscall` has not locked: it locks only the new endpoint and reply
object. In `OwnMap.own` that one write moves `t`'s `STATE` group from
`core (home)` to `lock <stale object>`, so `PathObl.OwnMove`, checked at every
write (`PathObl.move`), fails.

* `block_stale_not_move`: the memory-level statement, over `OwnMap.own`;
* `set_state_stale_mguard_fails`: the extracted `obj.Tcb.set_state` on the
  checking store of `PathObl.move` fails there.

These are statements about the single write. That an accepted run reaches it
with a stale object is read off the extracted bodies (not proved here). `t` is
then the current thread and in no queue, and no reply object names it through
the stale word, so this is about the ownership map and the write order; no
other core can reach `t` through the stale object.

Premise: `OwnMap.RegionOK` [J] (layout facts, `P2/OwnMap.lean`).
-/
import Fl4Proofs.P2.OwnMap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.MoveStale
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap
open Classical

/-- A running thread's `STATE` is its home core's. -/
theorem own_state_home {K : KLayout} (hK : RegionOK K) {t : U64} (ht : K.heap t = some .tcb) {m : U64 → U64}
    (hq : ¬ QueuedState (m (fld t oSTATE))) (hr : ¬ ReplyState (m (fld t oSTATE))) :
    own K m (fld t oSTATE) = .core (m (fld t oAFFINITY)) := by
  rw [own_tcb_at hK ht (Or.inr (Or.inl rfl)), oSTATE_val]
  simp [tcbOwner, GateField, TimerField, GField, gOwner, hq, hr]

/-- Queued: the lock of `BLOCK_OBJ`. -/
theorem own_state_queued {K : KLayout} (hK : RegionOK K) {t : U64} (ht : K.heap t = some .tcb) {m : U64 → U64}
    (hq : QueuedState (m (fld t oSTATE))) :
    own K m (fld t oSTATE) = .lock (m (fld t oBLOCK_OBJ)) := by
  rw [own_tcb_at hK ht (Or.inr (Or.inl rfl)), oSTATE_val]
  simp [tcbOwner, GateField, TimerField, GField, gOwner, hq]

/-- Blocked on reply: the lock of `REPLY_OBJ`. -/
theorem own_state_reply {K : KLayout} (hK : RegionOK K) {t : U64} (ht : K.heap t = some .tcb) {m : U64 → U64}
    (hr : ReplyState (m (fld t oSTATE))) :
    own K m (fld t oSTATE) = .lock (m (fld t oREPLY_OBJ)) := by
  have hq : ¬ QueuedState (m (fld t oSTATE)) := by
    unfold ReplyState at hr; unfold QueuedState; omega
  rw [own_tcb_at hK ht (Or.inr (Or.inl rfl)), oSTATE_val]
  simp [tcbOwner, GateField, TimerField, GField, gOwner, hq, hr]

/-- **Blocking a running thread through a stale object word is no owner
move**: from a memory where `t` runs to one where its `STATE` is blocked
(3: receive; 5: reply) and its `BLOCK_OBJ` / `REPLY_OBJ` is an object the path
has not locked. -/
theorem block_stale_not_move {K : KLayout} (hK : RegionOK K) {t : U64} (ht : K.heap t = some .tcb)
    {m m' : U64 → U64} {c : U64} {lk : U64 → Prop}
    (hq : ¬ QueuedState (m (fld t oSTATE))) (hr : ¬ ReplyState (m (fld t oSTATE)))
    (h : (QueuedState (m' (fld t oSTATE)) ∧ ¬ lk (m' (fld t oBLOCK_OBJ))) ∨
      (ReplyState (m' (fld t oSTATE)) ∧ ¬ lk (m' (fld t oREPLY_OBJ)))) :
    ¬ PathObl.OwnMove (own K) c lk m m' := by
  intro hM
  have e0 := own_state_home hK ht hq hr
  rcases h with ⟨hs, hl⟩ | ⟨hs, hl⟩
  · have e1 := own_state_queued hK ht hs
    have := (hM (fld t oSTATE) (by rw [e0, e1]; simp)).2
    rw [e1] at this; exact hl this
  · have e1 := own_state_reply hK ht hs
    have := (hM (fld t oSTATE) (by rw [e0, e1]; simp)).2
    rw [e1] at this; exact hl this

/-- **The extracted write on `PathObl.move`'s checking store fails**: `t`
running, the state written `TS_BLOCKED_ON_RECV` (3) or `TS_BLOCKED_ON_REPLY`
(5), the object word it selects not locked. -/
theorem set_state_stale_mguard_fails {S : Type} {st : machine.Store S} [L : LawfulStore st]
    {K : KLayout} (hK : RegionOK K) {t v : U64} (ht : K.heap t = some .tcb) {s : S}
    {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64} {User : U64 → Prop} {c : U64} {lk : U64 → Prop}
    (hq : ¬ QueuedState (L.mem s (fld t oSTATE))) (hr : ¬ ReplyState (L.mem s (fld t oSTATE)))
    (ha : ∀ off, off = oSTATE ∨ off = oBLOCK_OBJ ∨ off = oREPLY_OBJ → Aligned (fld t off))
    (h : (v = 3#u64 ∧ ¬ lk (L.mem s (fld t oBLOCK_OBJ))) ∨
      (v = 5#u64 ∧ ¬ lk (L.mem s (fld t oREPLY_OBJ)))) :
    obj.Tcb.set_state (PathObl.mguard st
      (fun x y => PathObl.StepOK (own K) cls ko User c lk (L.mem x) (L.mem y))) t s v = fail .panic := by
  have vS := (hK.tcb t ht oSTATE (Or.inr (Or.inl rfl))).2
  have vB := (hK.tcb t ht oBLOCK_OBJ (Or.inr (Or.inr (Or.inl rfl)))).2
  have vR := (hK.tcb t ht oREPLY_OBJ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).2
  rw [oSTATE_val] at vS; rw [oBOBJ_val] at vB; rw [oROBJ_val] at vR
  have aS := ha _ (Or.inl rfl)
  have hs : L.mem (L.wr s (fld t oSTATE) v) (fld t oSTATE) = v := L.mem_wr_same aS
  have hb : L.mem (L.wr s (fld t oSTATE) v) (fld t oBLOCK_OBJ) = L.mem s (fld t oBLOCK_OBJ) :=
    L.mem_wr_ne aS (ha _ (Or.inr (Or.inl rfl))) (by omega)
  have hro : L.mem (L.wr s (fld t oSTATE) v) (fld t oREPLY_OBJ) = L.mem s (fld t oREPLY_OBJ) :=
    L.mem_wr_ne aS (ha _ (Or.inr (Or.inr rfl))) (by omega)
  have hn : ¬ PathObl.StepOK (own K) cls ko User c lk (L.mem s) (L.mem (L.wr s (fld t oSTATE) v)) :=
    fun hst => by
      refine block_stale_not_move hK ht hq hr ?_ hst.1
      rcases h with ⟨rfl, hl⟩ | ⟨rfl, hl⟩
      · exact Or.inl ⟨by rw [hs]; simp [QueuedState], by rw [hb]; exact hl⟩
      · exact Or.inr ⟨by rw [hs]; simp [ReplyState], by rw [hro]; exact hl⟩
  unfold obj.Tcb.set_state
  simp only [lift, bind_ok]
  have e : core.num.U64.wrapping_add t layout.tcb.STATE = fld t oSTATE := by
    have : layout.tcb.STATE = oSTATE := UScalar.eq_of_val_eq (by rw [oSTATE_val]; exact P0.Consts.layout.tcb.STATE.val_eq)
    rw [this]; rfl
  rw [e]
  show (do let s' ← st.write s (fld t oSTATE) v
           if PathObl.StepOK (own K) cls ko User c lk (L.mem s) (L.mem s') then ok s' else fail .panic) = _
  rw [L.write_eq, bind_tc_ok, if_neg hn]

end Fl4Proofs.P2.MoveStale
