/-
P3 (DESIGN.md §9), scheduling contexts: l4v's `cur_sc_offset_ready` /
`cur_sc_offset_sufficient` (`OffOK`), under which `commit_time` keeps the
full `Inv` (`commit_time_inv`).
-/
import Fl4Proofs.P3.ScUpdate
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`commit_time` keeps the full `Inv`** under `OffOK`, if the current
SC's owner is bound back to it (l4v `sym_refs`) and not released. -/
theorem commit_time_inv {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hscC : nodeW st s c layout.node.CUR_SC ∈ C)
    {u0 : Fl4Spec.ObjRef} (hown0 : ∀ x n, σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) →
      x.scTcb = some u0 ∨ x.scTcb = none)
    (hback : ∀ xt, σ.kheap u0 = some (.tcb xt) → xt.tcbSchedContext = some σ.curSc)
    (hidle : (nodeW st s c layout.node.IDLE_SC).bv = Fl4Spec.idleScPtr)
    (hnr : 0 < σ.consumedTime → u0 ∉ σ.releaseQueue) (hoff : OffOK σ)
    (hmrt : sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    sched.commit_time st ar s a ⦃ s' => ∃ σ', Fl4Spec.commitTime (Z := Unit) σ = ({((), σ')}, False) ∧
      SchedRel st N T C c s' σ' ∧ NtfnStateRel N T (L.mem s') σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      HeadKeeps σ σ' (nodeW st s c layout.node.CUR_SC).bv ⦄ := by
  have hcs : σ.curSc = (nodeW st s c layout.node.CUR_SC).bv := hS.lists.choose_spec.choose_spec.2.curSc
  refine WP.spec_mono (commit_time_refines s a σ hS hR hN hI hscC hown0 hidle hnr hoff hmrt hmb) ?_
  rintro s' ⟨σ', h1, h2, h3, h4, hI', hK, hH, -⟩
  refine ⟨σ', h1, h2, h3, h4, ?_, hK⟩
  obtain ⟨e1, e2, e3, -, e5, -, -, hfr, hsc⟩ := hK
  refine hI'.inv fun xt hxt hcl => ?_
  intro x' scp y m h1' h2' h3' h4' h5'
  rw [hxt] at h1'; cases h1'
  -- `u0` is a TCB, not the SC
  have hu0 : u0 ≠ (nodeW st s c layout.node.CUR_SC).bv := by
    rintro e; rw [e] at hxt
    obtain ⟨y0, m0, hy0⟩ : ∃ y0 m0, σ'.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext y0 m0) := by
      obtain ⟨Q, R, -, hs⟩ := h2.lists
      obtain ⟨y0, m0, hk0, -⟩ := hs.scs _ hscC
      exact ⟨y0, m0, hk0⟩
    rw [hxt] at hy0; cases hy0
  have hxt0 : σ.kheap u0 = some (.tcb xt) := by rw [← hfr _ hu0]; exact hxt
  have hscp : scp = (nodeW st s c layout.node.CUR_SC).bv := by
    have := hback xt hxt0; rw [h2', hcs] at this; cases this; rfl
  subst hscp
  obtain ⟨x0, hx0, hHF⟩ := hH y m h3'
  have ht' : σ'.curTime = σ.curTime := e5
  -- the released head
  by_cases hc : 0 < σ.consumedTime
  · obtain ⟨hsuf, hr', hr0⟩ := hoff hc x0 m (by rw [hcs]; exact hx0)
    obtain ⟨hmin, htm⟩ := hHF.1 hc hsuf
    refine ⟨?_, ?_⟩
    · show Fl4Spec.refillReady' 0 σ'.curTime (Fl4Spec.refillHd y) = true
      rw [ht']
      simp only [Fl4Spec.refillReady', decide_eq_true_eq] at hr' hr0 ⊢
      rcases htm with htm | htm <;> rw [htm]
      · simpa using hr0
      · simpa using hr'
    · unfold Fl4Spec.refillSufficient Fl4Spec.refillCapacity
      have : ¬ (Fl4Spec.refillHd y).rAmount < 0 := by simp
      simp only [this, ↓reduceIte, decide_eq_true_eq]
      have e0 : (Fl4Spec.refillHd y).rAmount - 0 = (Fl4Spec.refillHd y).rAmount := by simp
      rw [e0]; exact hmin
  · have hr := hHF.2 hc
    have hhd : Fl4Spec.refillHd y = Fl4Spec.refillHd x0 := by unfold Fl4Spec.refillHd; rw [hr]
    obtain ⟨y1, hy1, -, hm1⟩ := hsc x0 m hx0
    rw [h3'] at hy1; cases hy1
    have hrel := hI.rd u0 xt hxt0 hcl xt _ x0 m hxt0 (by rw [hback xt hxt0, hcs]) hx0
      (by unfold Fl4Spec.scActive Fl4Spec.activeSc at h4' ⊢; rw [← hm1]; exact h4') (by rw [← e3]; exact h5')
    unfold released at hrel ⊢
    rw [hhd, ht']; exact hrel

end

end

end Fl4Proofs.P3.Sched
