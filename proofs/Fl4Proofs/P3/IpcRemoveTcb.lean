/-
P3 (DESIGN.md §9), IPC: **`reply_remove_tcb` on `IRel`** (`cancel_ipc` of a
thread blocked on its reply), discharging IpcCancelAll's `RemoveTcbHyp`.

FL4's side splits as `reply_obj; rrtCut; reply_unlink` (ScRemoveTcb's
`reply_remove_tcb_eq`), the spec's as `assert; replyRemoveTcbSc;
reply_unlink_tcb` (`replyRemoveTcb_split`). The call-stack part is the Sc
proofs' `reply_remove_tcb_sc_refines`, lifted to `IRel` by `tk_liftCW` (the
spec's step `ScTKw` by `nkt_replyRemoveTcbSc`); then `reply_unlink_irel`.

* `reply_remove_tcb_irel`: at a state, given the call-stack relation and
  invariants there (`CallRel`, `RFree`, `RPlaced`, `NSC`, `Inv`, the SCs
  nonzero) and l4v `valid_sched`/`valid_objs` (`SchedValid`, `ObjCover`): the
  reply is `r`'s ghost (TCB's reply word, `ObjCover.reply`) and linked back
  (`SchedValid.onReply`).
* `RemoveTcbOK`, `removeTcbHyp_of`: `RemoveTcbHyp` from those facts at every
  related state (re-scoped to `JAtZ` by the fold, whose fields give each).
-/
import Fl4Proofs.P3.IpcCancelAll
import Fl4Proofs.P3.ScRemoveTcb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec

noncomputable section

theorem nkt_replyRemoveTcbSc (r : ObjRef) : NKT (replyRemoveTcbSc r) := by
  unfold replyRemoveTcbSc getReplyObjRef getSkObjRef getSimpleKo setReplyObjRef
  repeat' (first | nkt_step | (unfold NonDet.when; split) | split)

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

/-- The spec's `reply_remove_tcb`: the state assertion, its call-stack part
(`replyRemoveTcbSc`), then `reply_unlink_tcb`. -/
theorem replyRemoveTcb_split {σ σ5 : Fl4Spec.State Unit} {t r : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hst : x.tcbState = .blockedOnReply r)
    (hsp : replyRemoveTcbSc r σ = ({((), σ5)}, False)) {X : Set (Unit × Fl4Spec.State Unit) × Prop}
    (hul : Fl4Spec.replyUnlinkTcb (Z := Unit) t r σ5 = X) :
    Fl4Spec.replyRemoveTcb (Z := Unit) t r σ = X := by
  unfold replyRemoveTcbSc at hsp
  rw [nd_gets_bind] at hsp
  unfold Fl4Spec.replyRemoveTcb
  rw [nd_bind_one (getThreadState_eq hk), nd_bind_one (assert_true hst σ), nd_gets_bind]
  cases hw : Fl4Spec.scWithReply r σ with
  | none =>
    rw [hw] at hsp
    have e := (nd_pure_one hsp).1
    subst e
    exact hul
  | some p =>
    rw [hw] at hsp
    dsimp only at hsp ⊢
    refine Eq.trans ?_ ((nd_bind_one hsp fun _ => Fl4Spec.replyUnlinkTcb (Z := Unit) t r).trans hul)
    simp only [nd_assoc_f]

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 4000000 in
/-- **`reply_remove_tcb` on `IRel`** (module docstring). -/
theorem reply_remove_tcb_irel (hP0 : IPlaced N T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hX : IRel st th cr N T C E R B c s σ) (hSV : Sched.SchedValid σ) (hOC : Sched.ObjCover N T E R C σ)
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRF : RFree (L.mem s) R C σ Lst)
    (hRP : RPlaced st N T C R c s σ) (hN : NSC N C σ) (hI : Inv σ) (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) {r : Fl4Spec.ObjRef}
    (hst : x.tcbState = .blockedOnReply r) :
    ipc.reply_remove_tcb st s t ⦃ s' => ∃ σ' x', Fl4Spec.replyRemoveTcb (Z := Unit) t.bv r σ = ({((), σ')}, False) ∧
      IRel st th cr N T C E R B c s' σ' ∧ σ'.kheap t.bv = some (.tcb x') ∧ x'.tcbState = .inactive ⦄ := by
  obtain ⟨xr, hkr, hback⟩ := hSV.onReply _ x r hk hst
  obtain ⟨i, hiR, hir⟩ := hOC.reply r xr hkr
  subst hir
  obtain ⟨x0, hk0, hTR⟩ := hX.1.tcb t ht
  rw [hk] at hk0; cases hk0
  have hiw : L.mem s (tReplyA t) = i := Sched.bv_inj (hTR.reply _ hst)
  rw [reply_remove_tcb_eq]
  step with Fl4Proofs.P1.obj.Tcb.reply_obj.spec as ⟨i', hi'⟩
  have hii : i' = i := by rw [hi']; exact hiw
  subst hii
  refine WP.spec_bind (reply_remove_tcb_sc_refines s σ hX.2.2.1 hX.1.toN hN hI hCR hRP hRF hC0 hOC.sc hiR) ?_
  rintro s4 ⟨σ5, Lst5, hsp, h1, h2, -, -, -, -, -, -, huf, -, -, hw5⟩
  have hK : ScTKw (fun p => p = σ.curThread) σ σ5 :=
    ScTKw.ofFalse (NKT.of_eq (nkt_replyRemoveTcbSc i'.bv) hsp)
  have hX5 := tk_liftCW hP0 hX (hw5.mono fun b hb => hb.elim (fun h => Or.inl (Or.inl h)) Or.inr) hK h1 h2
  obtain ⟨xr5, hkr5, er5⟩ := huf.1 _ xr hkr
  obtain ⟨xt5, hkt5, et5⟩ := huf.2 _ x hk
  refine WP.spec_mono (reply_unlink_irel hP0 s4 σ5 hX5 ht hkt5 (by rw [et5]; exact hst) hiR hkr5
    (er5.trans hback)) ?_
  rintro s6 ⟨hul, hX6⟩
  exact ⟨_, { xt5 with tcbState := .inactive }, replyRemoveTcb_split hk hst hsp hul, hX6,
    by simp [unlinkSt, stsAct_kheap, updK], rfl⟩

/-- **What `reply_remove_tcb` needs beyond `IRel`** at a state: the call
stacks (`CallRel`, `RFree`), `RPlaced`, `NSC`, `Inv`, the SCs nonzero, and
l4v `valid_sched`/`valid_objs` (`SchedValid`, `ObjCover`). Every one is a
`JAtZ` field. -/
def RemoveTcbOK (st : machine.Store S) [L : LawfulStore st] (N T C E R : Set U64) (c : U64) (s : S)
    (σ : Fl4Spec.State Unit) : Prop :=
  ∃ Lst : U64 → List U64, CallRel (L.mem s) R C σ Lst ∧ RFree (L.mem s) R C σ Lst ∧ RPlaced st N T C R c s σ ∧
    NSC N C σ ∧ Inv σ ∧ (∀ q ∈ C, q ≠ 0#u64) ∧ Sched.SchedValid σ ∧ Sched.ObjCover N T E R C σ

/-- **`RemoveTcbHyp` from `RemoveTcbOK`** at every related state. -/
theorem removeTcbHyp_of (hP0 : IPlaced N T E R B)
    (hD : ∀ s σ, IRel st th cr N T C E R B c s σ → RemoveTcbOK st N T C E R c s σ) :
    RemoveTcbHyp st th cr N T C E R B c := by
  intro s σ t x r hX ht hk hst
  obtain ⟨Lst, hCR, hRF, hRP, hN, hI, hC0, hSV, hOC⟩ := hD s σ hX
  exact reply_remove_tcb_irel hP0 s σ hX hSV hOC hCR hRF hRP hN hI hC0 ht hk hst

end

end

end Fl4Proofs.P3.Ipc
