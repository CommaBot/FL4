/-
P3 (DESIGN.md §9), scheduling contexts: **what charging a sufficient budget
leaves at the head** (`refillBudgetCheck_head`, `rrChargeL_head`).

If the current SC's head refill can pay the consumed time `c` and keep
`MIN_BUDGET` (`refill_sufficient c`), `refill_budget_check c` does not
overrun: the head moves `c` later (or stays, if `c = 0` or the head is at
`MAX_RELEASE_TIME`) and keeps at least `MIN_BUDGET`; the round-robin charge
keeps the head's time.
-/
import Fl4Proofs.P3.ScCharge7
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

theorem min_budget_pos : (0 : Ticks) < MIN_BUDGET := MIN_BUDGET_pos'

/-- A sufficient refill pays the usage and keeps `MIN_BUDGET`. -/
theorem suff_nat {u : Ticks} {r : Refill} (h : refillSufficient u r = true) :
    u.toNat < r.rAmount.toNat ∧ MIN_BUDGET.toNat ≤ r.rAmount.toNat - u.toNat := by
  unfold refillSufficient refillCapacity at h
  simp only [decide_eq_true_eq] at h
  have hm : 0 < MIN_BUDGET.toNat := by have := min_budget_pos; rw [BitVec.lt_def] at this; simpa using this
  by_cases hlt : r.rAmount < u
  · rw [if_pos hlt] at h; rw [BitVec.le_def] at h; simp at h; omega
  · rw [if_neg hlt] at h
    have hle : u ≤ r.rAmount := by rw [BitVec.not_lt] at hlt; exact hlt
    rw [BitVec.le_def] at h hle
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hle)] at h
    omega

end Spec

/-- `schedule_used` keeps the head's time; it keeps its amount, or (for a
single refill) adds the new amount. -/
theorem schedUsedL_head {m : Nat} (h2 : 2 ≤ m) (a : sporadic.Refill) (tl : List sporadic.Refill)
    (nw : sporadic.Refill) : ((schedUsedL m (a :: tl) nw).headD zR).time = a.time ∧
      (((schedUsedL m (a :: tl) nw).headD zR).amount = a.amount ∨
        ((schedUsedL m (a :: tl) nw).headD zR).amount = core.num.U64.wrapping_add a.amount nw.amount) := by
  unfold schedUsedL
  cases tl with
  | nil =>
    simp only [List.getLastD_cons, List.getLastD_nil, List.dropLast_singleton, List.nil_append,
      List.length_singleton]
    by_cases h3 : nw.time ≤ core.num.U64.wrapping_add a.time a.amount
    · rw [if_pos h3]; exact ⟨rfl, Or.inr rfl⟩
    · rw [if_neg h3, if_neg (by omega)]; exact ⟨rfl, Or.inl rfl⟩
  | cons b l =>
    simp only [List.dropLast_cons_of_ne_nil (List.cons_ne_nil b l)]
    split_ifs <;> exact ⟨rfl, Or.inl rfl⟩

theorem the_headD {rs : List sporadic.Refill} (hne : rs ≠ []) : Fl4Spec.the (rs.map toRefill).head? = toRefill (rs.headD zR) := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne; rfl

/-- **The head after a sufficient `refill_budget_check`.** -/
theorem refillBudgetCheck_head {σ σ' : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.SchedContext} {n : Nat}
    (hcur : σ.curSc = p) (hk : σ.kheap p = some (.schedContext x n)) {rs : List sporadic.Refill}
    (hx : x.scRefills = rs.map toRefill) (hne : rs ≠ []) {per : U64} (hper : x.scPeriod = per.bv)
    (hp0 : x.scPeriod ≠ 0) (hm2 : 2 ≤ x.scRefillMax) (u : U64)
    (hsuf : Fl4Spec.refillSufficient u.bv (Fl4Spec.refillHd x) = true)
    (h : Fl4Spec.refillBudgetCheck (Z := Unit) u.bv σ = ({((), σ')}, False)) :
    ∀ y m, σ'.kheap p = some (.schedContext y m) → Fl4Spec.MIN_BUDGET ≤ (Fl4Spec.refillHd y).rAmount ∧
      ((Fl4Spec.refillHd y).rTime = (Fl4Spec.refillHd x).rTime ∨
        (Fl4Spec.refillHd y).rTime = (Fl4Spec.refillHd x).rTime + u.bv) := by
  obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hH : Fl4Spec.refillHd x = toRefill hd := refillHd_map hx hne
  have hne' : x.scRefills ≠ [] := by rw [hx]; simp
  obtain ⟨hlt, hmin⟩ := suff_nat hsuf
  rw [hH] at hlt hmin
  simp only [toRefill] at hlt hmin
  have hav : hd.amount.bv.toNat = hd.amount.val := rfl
  have huv : u.bv.toNat = u.val := rfl
  rw [hav, huv] at hlt hmin
  rw [refillBudgetCheck_eq hcur hk hp0] at h
  have hov : ¬ Fl4Spec.the (Fl4Spec.headRefillOverrun (Z := Unit) p u.bv σ) = true := by
    simp only [headRefillOverrun_eq hk hne', hH, Fl4Spec.the, toRefill, decide_eq_true_eq, not_and, BitVec.le_def]
    intro h1; rw [hav, huv] at h1; omega
  unfold Fl4Spec.handleOverrun at h
  rw [nd_bind_one (wl_done (C := fun usage s => Fl4Spec.the (Fl4Spec.headRefillOverrun p usage s) = true)
    (B := fun usage => Fl4Spec.chargeEntireHeadRefill p usage) hov)] at h
  unfold specTail at h
  rw [nd_bind_one (getRefillHead_eq hk hne'), hH, Fl4Spec.NonDet.when] at h
  have hmin' : ¬ (toRefill hd).rAmount < Fl4Spec.MIN_BUDGET := by
    simp only [toRefill]; rw [BitVec.lt_def, hav]; omega
  split_ifs at h with hc
  · rw [nd_bind_one (postBody_eq hk (hd := hd) (tl := tl) hx hper (toRefill hd) rfl u)] at h
    set l := schedUsedL x.scRefillMax (⟨core.num.U64.wrapping_add hd.time u, core.num.U64.wrapping_sub hd.amount u⟩ :: tl)
      ⟨core.num.U64.wrapping_add hd.time per, u⟩ with hl
    have hk1 : (updSc σ p { x with scRefills := l.map toRefill } n).kheap p =
        some (.schedContext { x with scRefills := l.map toRefill } n) := by simp [updK]
    have hlne : l ≠ [] := by rw [hl]; exact schedUsedL_ne
    obtain ⟨ht, ha⟩ := schedUsedL_head hm2 ⟨core.num.U64.wrapping_add hd.time u, core.num.U64.wrapping_sub hd.amount u⟩
      tl ⟨core.num.U64.wrapping_add hd.time per, u⟩
    rw [← hl] at ht ha
    have hlam : Fl4Spec.MIN_BUDGET.toNat ≤ (l.headD zR).amount.val := by
      rcases ha with ha | ha <;> rw [ha]
      · rw [wsub_val (by omega)]; omega
      · have hb : hd.amount.val < 2 ^ 64 := by scalar_tac
        dsimp only
        rw [wadd_val (by rw [wsub_val (by omega)]; omega), wsub_val (by omega)]; omega
    have hinsuf : ¬ Fl4Spec.the (Fl4Spec.refillHeadInsufficient (Z := Unit) p
        (updSc σ p { x with scRefills := l.map toRefill } n)) = true := by
      simp only [refillHeadInsufficient_eq hk1 (by simpa using hlne),
        refillHd_map (x := { x with scRefills := l.map toRefill }) rfl hlne, Fl4Spec.the, toRefill,
        decide_eq_true_eq, BitVec.lt_def]
      have e : (l.headD zR).amount.bv.toNat = (l.headD zR).amount.val := rfl
      rw [e]; omega
    unfold Fl4Spec.headInsufficientLoop at h
    rw [wl_done (C := fun _ s => Fl4Spec.the (Fl4Spec.refillHeadInsufficient p s) = true)
      (B := fun _ => Fl4Spec.mergeNonoverlappingHeadRefill p) hinsuf] at h
    rw [pair_eq h]
    intro y m hy
    rw [hk1] at hy; cases hy
    rw [refillHd_map (x := { x with scRefills := l.map toRefill }) rfl hlne]
    refine ⟨by rw [BitVec.le_def]; exact hlam, Or.inr ?_⟩
    rw [hH]; simp only [toRefill]; rw [ht, core.num.U64.wrapping_add_bv_eq]
  · rw [nd_bind_one (show Fl4Spec.NonDet.pure (σ := Fl4Spec.State Unit) () σ = ({((), σ)}, False) from rfl)] at h
    have hinsuf : ¬ Fl4Spec.the (Fl4Spec.refillHeadInsufficient (Z := Unit) p σ) = true := by
      simp only [refillHeadInsufficient_eq hk hne', hH, Fl4Spec.the, decide_eq_true_eq]; exact hmin'
    unfold Fl4Spec.headInsufficientLoop at h
    rw [wl_done (C := fun _ s => Fl4Spec.the (Fl4Spec.refillHeadInsufficient p s) = true)
      (B := fun _ => Fl4Spec.mergeNonoverlappingHeadRefill p) hinsuf] at h
    rw [pair_eq h]
    intro y m hy
    rw [hk] at hy; cases hy
    refine ⟨?_, Or.inl rfl⟩
    rw [hH]; simp only [toRefill]; rw [BitVec.le_def, hav]; omega

/-- The round-robin charge keeps the head's time; its amount is the old one
less `c`, or (single refill) the old one. -/
theorem rrChargeL_head {rs : List sporadic.Refill} (hne : rs ≠ []) (c : U64) :
    ((rrChargeL rs c).headD zR).time = (rs.headD zR).time ∧
      (((rrChargeL rs c).headD zR).amount = core.num.U64.wrapping_sub (rs.headD zR).amount c ∨
        ((rrChargeL rs c).headD zR).amount =
          core.num.U64.wrapping_add (core.num.U64.wrapping_sub (rs.headD zR).amount c) c) := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
  unfold rrChargeL
  cases l with
  | nil => exact ⟨rfl, Or.inr rfl⟩
  | cons b l =>
    simp only [List.tail_cons, List.headD_cons]
    rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil b l)]
    exact ⟨rfl, Or.inl rfl⟩

end

end Fl4Proofs.P3.Sched
