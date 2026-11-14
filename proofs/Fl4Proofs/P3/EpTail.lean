/-
P3 (DESIGN.md §9), endpoints: unlinking a reply, and the scheduler tails of
the transfers.

* `reply_unlink_rel`: FL4's `reply_unlink r t` (the reply's TCB word to 0,
  then `set_thread_state t Inactive`) refines l4v `reply_unlink_tcb t r` for
  a thread blocked on a receive with reply `r`, given l4v's back pointer
  `reply_tcb r = Some t` (an l4v invariant, `sym_refs`; a hypothesis here).
* `EpTailHyps`: the scheduler parts of the transfers, as hypotheses (scheduler
  and scheduling-context subsystems): `wakeTail` (after the receiver of a
  send is set running: `unblock_sporadic` + `possible_switch_to` ↔
  `if_sporadic_cur_sc_test_refill_unblock_check` + `possible_switch_to`),
  `sporadicAssert` (the receive's `unblock_sporadic` of the sender ↔
  `if_sporadic_cur_sc_assert_refill_unblock_check`, assumed deterministic: a
  single spec outcome) and `switchTo` (`possible_switch_to` ↔
  `possible_switch_to`); `wakeTail` and `switchTo` with `TailPost`:
  the spec does not fail, FL4's outcome is matched by one of the spec's, FL4
  keeps the footprint, the spec `KView`, and `SR` holds after.
-/
import Fl4Proofs.P3.EpDeq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Defs
open Fl4Spec

/-- The spec's tail of a send to a waiting receiver (Ipc_A `send_ipc`, after
`set_thread_state dest Running`). -/
def specWakeTailE (d : ObjRef) : SMonad Unit Unit := do
  let destSc ← getTcbObjRef Tcb.tcbSchedContext d
  ifSporadicCurScTestRefillUnblockCheck destSc
  possibleSwitchTo d

/-- The spec's sporadic check of the sender in `receive_ipc`. -/
def specSporadicAssert (t : ObjRef) : SMonad Unit Unit := do
  let scPtr ← getTcbObjRef Tcb.tcbSchedContext t
  ifSporadicCurScAssertRefillUnblockCheck scPtr

end Defs

section Hyps
variable {S A : Type} (st : machine.Store S) [L : LawfulStore st]

/-- The post-condition of a tail: from FL4 state `s` and spec state `σ`,
the spec computation `m` does not fail, FL4's final state `s'` is matched by
one of its outcomes, FL4 keeps the footprint, the spec `KView`, and `SR`
holds after. -/
def TailPost (T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (SR : S → Fl4Spec.State Unit → Prop)
    (s : S) (σ : Fl4Spec.State Unit) (m : Fl4Spec.SMonad Unit Unit) (s' : S) : Prop :=
  ¬ (m σ).2 ∧ ∃ σ', ((), σ') ∈ (m σ).1 ∧ FootEq T E R B (L.mem s) (L.mem s') ∧ KView σ σ' ∧ SR s' σ'

/-- The scheduler tails of the transfers (see the module docstring). -/
structure EpTailHyps (A : Type) (T E R : Set U64) (B : Set (U64 × Fl4Spec.Word))
    (SR : S → Fl4Spec.State Unit → Prop) : Prop where
  wakeTail : ∀ s (a : A) σ (t : U64), EpStateRel T E R B (L.mem s) σ → SR s σ → t ∈ T →
    (do
      let s1 ← endpoint.unblock_sporadic st s t
      let s2 ← sched.possible_switch_to st s1 t
      ok (s2, a)) ⦃ r => r.2 = a ∧ TailPost st T E R B SR s σ (specWakeTailE t.bv) r.1 ⦄
  sporadicAssert : ∀ s σ (t : U64), EpStateRel T E R B (L.mem s) σ → SR s σ → t ∈ T →
    endpoint.unblock_sporadic st s t ⦃ s' => ∃ σ', specSporadicAssert t.bv σ = ({((), σ')}, False) ∧
      FootEq T E R B (L.mem s) (L.mem s') ∧ KView σ σ' ∧ SR s' σ' ⦄
  switchTo : ∀ s (a : A) σ (t : U64), EpStateRel T E R B (L.mem s) σ → SR s σ → t ∈ T →
    (do
      let s1 ← sched.possible_switch_to st s t
      ok (s1, a)) ⦃ r => r.2 = a ∧ TailPost st T E R B SR s σ (Fl4Spec.possibleSwitchTo t.bv) r.1 ⦄

end Hyps

/-! ## Unlinking a reply -/

section
variable {S A : Type} {st : machine.Store S} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- Writing the TCB word of the reply object `r`. -/
theorem reply_write_rel (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ) {r : U64} (hr : r ∈ R) {xr : Fl4Spec.Reply}
    (hkr : σ.kheap r.bv = some (.reply xr)) (v : U64) :
    Fl4Spec.setReplyObjRef (Z := Unit) Fl4Spec.replyTcbUpdate r.bv (optRef v) σ =
      ({((), updK σ r.bv (.reply { xr with replyTcb := optRef v }))}, False) ∧
    EpStateRel T E R B (L.mem (L.wr s (rTcbA r) v)) (updK σ r.bv (.reply { xr with replyTcb := optRef v })) ∧
    SR (L.wr s (rTcbA r) v) (updK σ r.bv (.reply { xr with replyTcb := optRef v })) ∧
    Agree (L.mem s) (L.mem (L.wr s (rTcbA r) v)) (fun b => b.val ≠ r.val) := by
  have ha := a_rtcb hP hr
  have hag := agree_wr (L := L) (s := s) (v := v) ha.1
  have hag' : Agree (L.mem s) (L.mem (L.wr s (rTcbA r) v)) (fun b => b.val ≠ r.val) :=
    hag.mono fun b hb => by rw [rTcbA_val]; exact hb
  refine ⟨setReplyTcb_eq _ hkr, hR.upd_reply hP hr _ (hag'.mono fun b hb => hb.2) ?_, ?_, hag'⟩
  · show optRef v = optRef _
    rw [rd_wr_eq ha.1]
  · refine hH.stable _ _ _ _ hSR ((writesIn_wr ha.1).mono fun b hb => ?_) (EpStep.reply hkr _)
    subst hb
    exact Or.inr (Or.inl ⟨r, hr, rTcbA_val r⟩)

/-- **`reply_unlink`** of a thread blocked on a receive with reply `r`. -/
theorem reply_unlink_rel (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) {e' : Fl4Spec.ObjRef} {dd : Fl4Spec.ReceiverPayload} {r : U64}
    (hst : x.tcbState = .blockedOnReceive e' (some r.bv) dd) (hr : r ∈ R) {xr : Fl4Spec.Reply}
    (hkr : σ.kheap r.bv = some (.reply xr)) (hback : xr.replyTcb = some t.bv)
    (hq : ∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) :
    ipc.reply_unlink st s r t ⦃ s' =>
      Fl4Spec.replyUnlinkTcb (Z := Unit) t.bv r.bv σ =
        ({((), stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := none })) t.bv
          (.tcb { x with tcbState := .inactive })) t.bv)}, False) ∧
      EpStateRel T E R B (L.mem s') (stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := none })) t.bv
          (.tcb { x with tcbState := .inactive })) t.bv) ∧
      SR s' (stsAct (updK (updK σ r.bv (.reply { xr with replyTcb := none })) t.bv
          (.tcb { x with tcbState := .inactive })) t.bv) ⦄ := by
  obtain ⟨e1, hR1, hS1, -⟩ := reply_write_rel hH hP s σ hR hSR hr hkr 0#u64
  rw [optRef_zero] at e1 hR1 hS1
  have hrt : r.bv ≠ t.bv := kheap_ne hkr hk (fun _ h1 h2 => by subst h1; cases h2)
  have hk1 : (updK σ r.bv (.reply { xr with replyTcb := none })).kheap t.bv = some (.tcb x) := by
    simp [Ne.symm hrt, hk]
  have hq1 : ∀ e ∈ E, ∀ z, (updK σ r.bv (.reply { xr with replyTcb := none })).kheap e.bv = some (.endpoint z) →
      t.bv ∉ z.epQueue := by
    intro e he z hz
    have hre : r.bv ≠ e.bv := by
      intro h; rw [← h] at hz; simp at hz
    exact hq e he z (by simpa [Ne.symm hre] using hz)
  unfold ipc.reply_unlink
  step as ⟨s1, hs1⟩
  subst hs1
  refine WP.spec_mono (set_thread_state_rel hH hP _ _ hR1 hS1 ht hk1 hq1 .inactive (by simp [tsCode])
    sched.TS_INACTIVE (by unfold sched.TS_INACTIVE; rfl)) ?_
  rintro s2 ⟨hR2, hS2⟩
  refine ⟨?_, hR2, hS2⟩
  unfold Fl4Spec.replyUnlinkTcb
  rw [nd_bind_one (getReply_eq hkr), nd_bind_one (assert_true hback σ), nd_bind_one (getThreadState_eq hk),
    nd_bind_one (assert_true (Or.inr ⟨e', dd, hst⟩) σ), nd_bind_one e1, setThreadState_eq _ hk1]

end

end

end Fl4Proofs.P3.Endp
