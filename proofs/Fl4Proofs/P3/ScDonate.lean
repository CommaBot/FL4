/-
P3 (DESIGN.md §9), scheduling contexts: the refill tests and the
no-donation cases of `maybe_donate_sched_context`.

* `ready_refines`: `sporadic::ready` computes l4v `refill_ready (cur_time)
  (refill_hd sc)` (`get_sc_refill_ready`).
* `sufficient_refines`: `sporadic::sufficient` computes l4v
  `refill_sufficient usage (refill_hd sc)` (`get_sc_refill_sufficient`),
  given that the architecture's `MIN_BUDGET` (`2 * kernel_wcet_ticks`) is
  the spec's (`Fl4Spec.MIN_BUDGET`, built from the unspecified `timeConsts`):
  hypothesis `hmb`.
* `maybe_donate_nodonate`: when the thread has an SC, the notification has
  none, or the notification's SC is bound to a TCB, FL4 and the spec change
  nothing.
-/
import Fl4Proofs.P3.ScReturnRef
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`ready` refines `refill_ready`.** -/
theorem ready_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) {sc : obj.Sc} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext x n)) (ha : Fl4Spec.scActive x = true) :
    sporadic.ready st s sc ⦃ b => Fl4Spec.getScRefillReady (Z := Unit) sc.bv σ = ({(b, σ)}, False) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  replace hx := hx.strong ha
  have hW := hx.wf
  have hne : x.scRefills ≠ [] := by rw [hx.refills]; exact refills_ne hW
  step
  rw [getScRefillReady_eq hk hne, b_post, refillHd_eq hW hx.refills, ← rf0_eq hW, curTime_eq hc, hs.curTime]
  congr 3
  unfold Fl4Spec.refillReady Fl4Spec.refillReady'
  simp only [toRefill]
  refine decide_eq_decide.2 ?_
  rw [u64_le_bv]
  exact iff_of_eq (congrArg (· ≤ _) (BitVec.add_zero _))

/-- **`sufficient` refines `refill_sufficient`**, given the platform's
minimum budget is the spec's. -/
theorem sufficient_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) {sc : obj.Sc} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext x n)) (ha : Fl4Spec.scActive x = true) (usage : U64)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    sporadic.sufficient st ar s a sc usage ⦃ b =>
      Fl4Spec.getScRefillSufficient (Z := Unit) sc.bv usage.bv σ = ({(b, σ)}, False) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  replace hx := hx.strong ha
  have hW := hx.wf
  have hne : x.scRefills ≠ [] := by rw [hx.refills]; exact refills_ne hW
  have hd : Fl4Spec.refillHd x = toRefill (L.refill s sc (L.rhead s sc)) := by
    rw [refillHd_eq hW hx.refills, rf0_eq hW]
  unfold sporadic.sufficient sporadic.capacity
  step as ⟨r, r_post⟩
  rw [getScRefillSufficient_eq hk hne, hd, ← r_post]
  by_cases hu : usage > r.amount
  · simp only [hu, ↓reduceIte, bind_ok]
    refine WP.spec_bind hmb ?_
    intro mb hmb'
    simp only [WP.spec_ok]
    have hlt : r.amount.bv < usage.bv := by
      have := (gt_iff_val).1 hu; rw [BitVec.lt_def]; exact this
    unfold Fl4Spec.refillSufficient Fl4Spec.refillCapacity
    simp only [toRefill, hlt, ↓reduceIte]
    congr 3
    refine decide_eq_decide.2 ?_
    rw [← hmb', GE.ge, UScalar.le_equiv, BitVec.le_def]; rfl
  · simp only [hu, ↓reduceIte]
    have hle : usage.val ≤ r.amount.val := by have := (gt_iff_val).not.1 hu; omega
    have hsub : (r.amount - usage) ⦃ d => d.val = r.amount.val - usage.val ⦄ := by step*
    refine WP.spec_bind hsub ?_
    intro d hd'
    refine WP.spec_bind hmb ?_
    intro mb hmb'
    simp only [WP.spec_ok]
    have hnlt : ¬ r.amount.bv < usage.bv := by rw [BitVec.lt_def]; exact Nat.not_lt.2 hle
    unfold Fl4Spec.refillSufficient Fl4Spec.refillCapacity
    simp only [toRefill, hnlt, ↓reduceIte]
    congr 3
    refine decide_eq_decide.2 ?_
    have hdb : d.bv = r.amount.bv - usage.bv := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hle)]
      exact hd'
    rw [← hmb', ← hdb, GE.ge, UScalar.le_equiv, BitVec.le_def]; rfl

/-- **No donation**: the thread has an SC, or the notification has none, or
the notification's SC is bound to a TCB. -/
theorem maybe_donate_nodonate {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ) (t n : U64) (ht : t ∈ T) (hn : n ∈ N)
    (hno : L.mem s (scA t) ≠ 0#u64 ∨ L.mem s (nScA n) = 0#u64 ∨
      (L.mem s (nScA n) ∈ C ∧ L.mem s (scW (L.mem s (nScA n)) 24#u64) ≠ 0#u64)) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ r =>
      r = (s, a) ∧ Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σ = ({((), σ)}, False) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xn, hkn, hxn⟩ := hR.ntfn n hn
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  have hspec : Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σ =
      Fl4Spec.NonDet.when (optRef (L.mem s (scA t)) = none) (Fl4Spec.NonDet.maybeM (fun scPtr => do
        let scTcb ← Fl4Spec.getScObjRef Fl4Spec.SchedContext.scTcb scPtr
        Fl4Spec.NonDet.when (scTcb = none) <| do
          Fl4Spec.schedContextDonate scPtr t.bv
          Fl4Spec.schedContextResume scPtr) (optRef (L.mem s (nScA n)))) σ := by
    unfold Fl4Spec.maybeDonateSc Fl4Spec.getTcbObjRef
    rw [nd_bind_one (threadGet_eq _ hkt), hsct]
    simp only [Fl4Spec.NonDet.when]
    split_ifs
    · rw [nd_bind_one' (getNtfnSc_eq hkn), hxn.sc]
    · rfl
  unfold notification.maybe_donate_sched_context
  step
  rw [i_post]
  rcases hno with h1 | h2 | ⟨hC, h3⟩
  · simp only [h1, ↓reduceIte, WP.spec_ok]
    refine ⟨by trivial, ?_⟩
    rw [hspec, Fl4Spec.NonDet.when, ite_f (by rw [optRef_ne h1]; simp)]; rfl
  · by_cases h0 : L.mem s (scA t) = 0#u64
    · simp only [h0, ↓reduceIte]
      step
      step
      simp only [b_post, i1_post, h2, decide_true, ↓reduceIte, WP.spec_ok]
      refine ⟨by trivial, ?_⟩
      rw [hspec, Fl4Spec.NonDet.when, ite_t (by rw [h0, optRef_zero]), h2, optRef_zero]; rfl
    · simp only [h0, ↓reduceIte, WP.spec_ok]
      refine ⟨by trivial, ?_⟩
      rw [hspec, Fl4Spec.NonDet.when, ite_f (by rw [optRef_ne h0]; simp)]; rfl
  · by_cases h0 : L.mem s (scA t) = 0#u64
    · simp only [h0, ↓reduceIte]
      step
      step
      by_cases hne0 : L.mem s (nScA n) = 0#u64
      · simp only [b_post, i1_post, hne0, decide_true, ↓reduceIte, WP.spec_ok]
        refine ⟨by trivial, ?_⟩
        rw [hspec, Fl4Spec.NonDet.when, ite_t (by rw [h0, optRef_zero]), hne0, optRef_zero]; rfl
      simp only [b_post, i1_post, hne0, decide_false, Bool.false_eq_true, ↓reduceIte]
      step
      have e3 : i2 ≠ 0#u64 := by rw [i2_post]; simpa [scTcbA, scW, layout.sc.TCB] using h3
      simp only [e3, ↓reduceIte, WP.spec_ok]
      refine ⟨by trivial, ?_⟩
      obtain ⟨xs, ns, hks, hxs⟩ := hs.scs _ hC
      rw [hspec, Fl4Spec.NonDet.when, ite_t (by rw [h0, optRef_zero]), optRef_ne hne0]
      simp only [Fl4Spec.NonDet.maybeM]
      rw [nd_bind_one (show Fl4Spec.getScObjRef (Z := Unit) Fl4Spec.SchedContext.scTcb _ σ = ({(xs.scTcb, σ)}, False) by
        unfold Fl4Spec.getScObjRef; rw [nd_bind_one (getSchedContext_eq hks)]; rfl)]
      simp only [Fl4Spec.NonDet.when, hxs.tcb, optRef_ne h3]
      rfl
    · simp only [h0, ↓reduceIte, WP.spec_ok]
      refine ⟨by trivial, ?_⟩
      rw [hspec, Fl4Spec.NonDet.when, ite_f (by rw [optRef_ne h0]; simp)]; rfl

end

end

end Fl4Proofs.P3.Sched
