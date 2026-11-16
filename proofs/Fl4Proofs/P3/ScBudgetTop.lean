/-
P3 (DESIGN.md §9), scheduling contexts: **`sporadic::budget_check` refines
l4v `refill_budget_check`** (`budget_check_refines`).

Hypotheses beyond `SchedRel`:
* the current SC is one of `C`, and not round-robin (seL4 asserts it);
* its refill amounts are positive, sum to less than `2 ^ 64` and to at least
  `MIN_BUDGET` (l4v `valid_refills`: `MIN_BUDGET ≤` the budget, which is the
  sum);
* the platform's `MAX_RELEASE_TIME` and `MIN_BUDGET` are the spec's (`hmrt`,
  `hmb`).
-/
import Fl4Proofs.P3.ScBudget
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

/-- The spec's `refill_budget_check` after `handle_overrun`. -/
def specTail (scPtr : Fl4Spec.ObjRef) (usage' : Fl4Spec.Ticks) : Fl4Spec.SMonad Unit Unit := do
  let head ← Fl4Spec.getRefillHead scPtr
  Fl4Spec.NonDet.when (usage' > 0 ∧ head.rTime < Fl4Spec.MAX_RELEASE_TIME) <| do
    let sc ← Fl4Spec.getSchedContext scPtr
    let used ← pure { rTime := head.rTime + sc.scPeriod, rAmount := usage' : Fl4Spec.Refill }
    Fl4Spec.updateRefillHd scPtr fun r => { r with rAmount := head.rAmount - usage' }
    Fl4Spec.updateRefillHd scPtr fun r => { r with rTime := head.rTime + usage' }
    Fl4Spec.scheduleUsed scPtr used
  Fl4Spec.headInsufficientLoop scPtr

theorem nd_bind_assoc' {σ α β γ : Type} (m : Fl4Spec.NonDet σ α) (f : α → Fl4Spec.NonDet σ β)
    (g : β → Fl4Spec.NonDet σ γ) (s : σ) : ((m >>= f) >>= g) s = (m >>= fun a => f a >>= g) s := by
  simp only [nd_bind_apply']
  refine Prod.ext (Set.ext fun r => ?_) (propext ?_)
  · simp only [Set.mem_setOf_eq]; constructor
    · rintro ⟨x, ⟨y, hy, hx⟩, hr⟩; exact ⟨y, hy, x, hx, hr⟩
    · rintro ⟨y, hy, x, hx, hr⟩; exact ⟨x, ⟨y, hy, hx⟩, hr⟩
  · simp only [Set.mem_setOf_eq]; constructor
    · rintro ((h | ⟨y, hy, h⟩) | ⟨x, ⟨y, hy, hx⟩, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨y, hy, Or.inl h⟩
      · exact Or.inr ⟨y, hy, Or.inr ⟨x, hx, h⟩⟩
    · rintro (h | ⟨y, hy, h | ⟨x, hx, h⟩⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨y, hy, h⟩)
      · exact Or.inr ⟨x, ⟨y, hy, hx⟩, h⟩

theorem refillBudgetCheck_eq {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.SchedContext} {n : Nat}
    (hcur : σ.curSc = p) (hk : σ.kheap p = some (.schedContext x n)) (hrr : x.scPeriod ≠ 0) (u : Fl4Spec.Ticks) :
    Fl4Spec.refillBudgetCheck (Z := Unit) u σ = (Fl4Spec.handleOverrun p u >>= fun u' => specTail p u') σ := by
  unfold Fl4Spec.refillBudgetCheck
  rw [nd_gets_bind, hcur, nd_bind_one (isRoundRobin_eq hk), nd_bind_one (assert_true (by simpa using hrr) σ)]
  rfl

/-- The charge after the overrun loop, on the lists. -/
theorem postBody_eq {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) {hd : sporadic.Refill} {tl : List sporadic.Refill}
    (hx : y.scRefills = (hd :: tl).map toRefill) {per : U64} (hper : y.scPeriod = per.bv)
    (head : Fl4Spec.Refill) (hh : head = toRefill hd) (u : U64) :
    (do
      let sc ← Fl4Spec.getSchedContext p
      let used ← pure { rTime := head.rTime + sc.scPeriod, rAmount := u.bv : Fl4Spec.Refill }
      Fl4Spec.updateRefillHd p fun r => { r with rAmount := head.rAmount - u.bv }
      Fl4Spec.updateRefillHd p fun r => { r with rTime := head.rTime + u.bv }
      Fl4Spec.scheduleUsed (Z := Unit) p used) σ =
      ({((), updSc σ p { y with scRefills := (schedUsedL y.scRefillMax
        (⟨core.num.U64.wrapping_add hd.time u, core.num.U64.wrapping_sub hd.amount u⟩ :: tl)
        ⟨core.num.U64.wrapping_add hd.time per, u⟩).map toRefill } n)}, False) := by
  rw [nd_bind_one (getSchedContext_eq hk), nd_pure_bind', nd_bind_one (updateRefillHd_eq hk _)]
  have hk2 : ∀ z : Fl4Spec.SchedContext, (updSc σ p z n).kheap p = some (.schedContext z n) :=
    fun z => by simp [updK]
  rw [nd_bind_one (updateRefillHd_eq (hk2 _) _), updSc_updSc]
  have hused : ({ rTime := head.rTime + y.scPeriod, rAmount := u.bv } : Fl4Spec.Refill) =
      toRefill ⟨core.num.U64.wrapping_add hd.time per, u⟩ := by
    rw [hh, hper]; simp [toRefill, core.num.U64.wrapping_add_bv_eq]
  rw [hused, scheduleUsed_eq (hk2 _) (rs := ⟨core.num.U64.wrapping_add hd.time u, core.num.U64.wrapping_sub hd.amount u⟩ :: tl)
    (by simp [hx, hh, toRefill, Fl4Spec.the, core.num.U64.wrapping_add_bv_eq, core.num.U64.wrapping_sub_bv_eq])
    (by simp), updSc_updSc]

/-- What `refill_budget_check` leaves: the SC at `p` with new refills,
non-empty, positive, summing below `2 ^ 64`, the head holding at least
`MIN_BUDGET`. -/
def BudgetPost (σ σ' : Fl4Spec.State Unit) (p : Fl4Spec.ObjRef) : Prop :=
  ∀ y m, σ.kheap p = some (.schedContext y m) → ∃ y', σ' = updSc σ p y' m ∧
    y' = { y with scRefills := y'.scRefills } ∧ y'.scRefills ≠ [] ∧
    (∀ r ∈ y'.scRefills, 0 < r.rAmount.toNat) ∧ (y'.scRefills.map fun r => r.rAmount.toNat).sum < 2 ^ 64 ∧
    Fl4Spec.MIN_BUDGET ≤ (Fl4Spec.refillHd y').rAmount

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`budget_check` refines `refill_budget_check`.** -/
theorem budget_check_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hcC : nodeW st s c layout.node.CUR_SC ∈ C)
    (hca : (L.rmax s (nodeW st s c layout.node.CUR_SC)).val ≠ 0)
    (hmrt : sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hrr : L.rperiod s (nodeW st s c layout.node.CUR_SC) ≠ 0#u64)
    (hpos : Pos (L.refills s (nodeW st s c layout.node.CUR_SC)))
    (hsum : lsum (L.refills s (nodeW st s c layout.node.CUR_SC)) < 2 ^ 64)
    (hmin : Fl4Spec.MIN_BUDGET.toNat ≤ lsum (L.refills s (nodeW st s c layout.node.CUR_SC))) (usage : U64) :
    sporadic.budget_check st ar s a usage ⦃ s' => ∃ σ', Fl4Spec.refillBudgetCheck (Z := Unit) usage.bv σ =
      ({((), σ')}, False) ∧ FootEq N T (L.mem s) (L.mem s') ∧ KView σ σ' ∧ SchedRel st N T C c s' σ' ∧
      BudgetPost σ σ' (nodeW st s c layout.node.CUR_SC).bv ∧ WritesIn st s s' (KFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  set sc := nodeW st s c layout.node.CUR_SC with hscdef
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hcC
  replace hx := hx.act hca
  have hrr' : x.scPeriod ≠ 0 := by
    rw [hx.period]; intro e; exact hrr (eq_of_bv (by rw [e]; rfl))
  have hkk : ∀ s' : S, (specAt (st := st) σ sc x n s').kheap sc.bv =
      some (.schedContext { x with scRefills := (L.refills s' sc).map toRefill } n) := fun s' => by
    simp only [specAt, updK_kheap, Function.update_self] <;> rfl
  have hspec := refillBudgetCheck_eq (σ := σ) hs.curSc hk hrr' usage.bv
  unfold sporadic.budget_check
  step with LawfulStore.cur_cpu_spec as ⟨i, i_post⟩
  step with obj.node_get.spec as ⟨i1, i1_post⟩
  have hi1 : i1 = sc := by rw [i1_post, i_post, hc.cur]; rfl
  subst hi1
  refine WP.spec_bind hmrt ?_
  intro mrt hmrt'
  step with obj.Sc.period.spec as ⟨period, period_post⟩
  have hu : usage.val ≤ layout.WALK_FUEL.val := by
    have := usage.hBounds; rw [walk_fuel_val]; simp [U64.size] at this ⊢; omega
  refine WP.spec_bind (loop0_refines hk hx mrt period hmrt' period_post.symm hpos hsum usage _ hu) ?_
  rintro ⟨s1, u1⟩ ⟨hR1, hP1, hS1, hex, hov⟩
  have hW1 := hR1.wf
  have hne1 := refills_ne' hW1
  have hper1 : L.rperiod s1 sc = period := by rw [hR1.period hx, period_post]
  step as ⟨h, h_post⟩
  rw [head_eq' hW1] at h_post
  subst h_post
  have hne1' : ((L.refills s1 sc).map toRefill) ≠ [] := by simpa using hne1
  obtain ⟨q, l, e⟩ := List.exists_cons_of_ne_nil hne1
  generalize hhd : (L.refills s1 sc).headD zR = hd at *
  have hq : hd = q := by rw [← hhd, e]; rfl
  have hdm : hd ∈ L.refills s1 sc := by rw [hq, e]; exact List.mem_cons_self
  have hcond : (u1.bv > 0 ∧ (toRefill hd).rTime < Fl4Spec.MAX_RELEASE_TIME) ↔ (u1 > 0#u64 ∧ hd.time < mrt) := by
    simp only [toRefill, ← hmrt', ← u64_lt_bv, GT.gt]
    rw [u64_lt_bv]; rfl
  -- the charge after the overrun loop
  refine WP.spec_bind (Pₘ := fun s2 => RingAt st s s2 sc n ∧ Pos (L.refills s2 sc) ∧
      lsum (L.refills s2 sc) = lsum (L.refills s sc) ∧
      specTail sc.bv u1.bv (specAt (st := st) σ sc x n s1) =
        Fl4Spec.headInsufficientLoop (Z := Unit) sc.bv (specAt (st := st) σ sc x n s2)) ?_ ?_
  · by_cases hc1 : u1 > 0#u64 ∧ hd.time < mrt
    · have hgt : hd.amount > u1 := by
        by_contra hle
        refine hex ⟨?_, hc1.2⟩
        rw [GT.gt, UScalar.lt_equiv] at hle; rw [UScalar.le_equiv]; omega
      simp only [hc1.1, hc1.2, hgt, ↓reduceIte]
      step as ⟨i2, i2_post⟩
      step as ⟨i3, i3_post⟩
      step as ⟨i4, i4_post⟩
      refine WP.spec_bind (set_head_ring hR1 _) ?_
      rintro s3 ⟨hR3, hl3⟩
      refine WP.spec_mono (schedule_used_ring hR3 _) ?_
      rintro s4 ⟨hR4, hl4⟩
      have hgt' : u1.val < hd.amount.val := by rw [GT.gt, UScalar.lt_equiv] at hgt; exact hgt
      have hu0 : 0 < u1.val := by have := hc1.1; rw [GT.gt, UScalar.lt_equiv] at this; simpa using this
      have hi4 : i4.val = hd.amount.val - u1.val := by rw [i4_post]; exact wsub_val (by omega)
      have hl3' : L.refills s3 sc = ⟨i3, i4⟩ :: l := by rw [hl3, e]; rfl
      have hS1' : lsum (L.refills s1 sc) = hd.amount.val + lsum l := by rw [e, lsum_cons, hq]
      have hno : ((⟨i3, i4⟩ :: l : List sporadic.Refill).getLastD zR).amount.val + u1.val < 2 ^ 64 := by
        by_cases hl : l = []
        · subst hl; simp only [List.getLastD_cons, List.getLastD_nil]
          rw [hi4]; have := le_lsum hdm; rw [hS1] at this; omega
        · rw [getLastD_eq (by simp), List.getLast_cons hl]
          have := le_lsum (rs := l) (List.getLast_mem hl)
          rw [hS1] at hS1'; omega
      refine ⟨hR4, ?_, ?_, ?_⟩
      · rw [hl4, hl3']
        refine pos_schedUsedL (fun r hr => ?_) (by simp) hno hu0
        rcases List.mem_cons.1 hr with rfl | hr
        · show 0 < i4.val; omega
        · exact hP1 r (by rw [e]; exact List.mem_cons_of_mem _ hr)
      · rw [hl4, hl3', lsum_schedUsedL (by simp) hno, lsum_cons, ← hS1, hS1']
        simp only; omega
      · unfold specTail
        rw [nd_bind_one (getRefillHead_eq (hkk s1) hne1'), refillHd_map rfl hne1, hhd, Fl4Spec.NonDet.when,
          ite_t (hcond.2 hc1), nd_bind_one (postBody_eq (hkk s1) (hd := q) (tl := l) (by rw [e])
            (per := period) (by rw [hx.period, period_post]) (toRefill hd) (by rw [hq]) u1), updSc_updSc]
        show Fl4Spec.headInsufficientLoop sc.bv (updSc σ sc.bv { x with scRefills := _ } n) =
          Fl4Spec.headInsufficientLoop sc.bv (updSc σ sc.bv { x with scRefills := (L.refills s4 sc).map toRefill } n)
        rw [hl4, hl3', hR3.mx, hx.max, i2_post, i3_post, i4_post, hq]
    · have hfin : specTail sc.bv u1.bv (specAt (st := st) σ sc x n s1) =
          Fl4Spec.headInsufficientLoop (Z := Unit) sc.bv (specAt (st := st) σ sc x n s1) := by
        unfold specTail
        rw [nd_bind_one (getRefillHead_eq (hkk s1) hne1'), refillHd_map rfl hne1, hhd, Fl4Spec.NonDet.when,
          ite_f (fun h => hc1 (hcond.1 h))]
        exact nd_pure_bind' _ _ _
      by_cases hu0 : u1 > 0#u64
      · have ht' : ¬ hd.time < mrt := fun h => hc1 ⟨hu0, h⟩
        rw [if_pos hu0, if_neg ht']
        exact (WP.spec_ok _).2 ⟨hR1, hP1, hS1, hfin⟩
      · rw [if_neg hu0]
        exact (WP.spec_ok _).2 ⟨hR1, hP1, hS1, hfin⟩
  · rintro s2 ⟨hR2, hP2, hS2, ht2⟩
    refine WP.spec_bind hmb ?_
    intro mb hmb'
    step with obj.Sc.refill_max.spec as ⟨i2, i2_post⟩
    step as ⟨fuel2, fuel2_post⟩
    have hf2 : (L.refills s2 sc).length ≤ fuel2.val := by
      have h1 := hR2.wf.size_le; have h2 := hR2.wf.le_abs; have h3 := absMax_lt (n + Fl4Spec.minSchedContextBits)
      rw [fuel2_post, refills_length, wadd_val (by rw [i2_post]; simp; omega), i2_post]; simp; omega
    have hmbv : mb.val = Fl4Spec.MIN_BUDGET.toNat := by rw [← hmb']; rfl
    refine WP.spec_mono (loop1_refines (σ0 := σ) (x := x) hR2 hP2 (by rw [hS2]; exact hsum) mb hmb' (by rw [hS2, hmbv]; exact hmin)
      fuel2 hf2) ?_
    rintro s3 ⟨hR3, hp3, hs3, hm3, hl⟩
    obtain ⟨hS3, hf3, hv3⟩ := hS.ringAt hcC hk hR3
    refine ⟨_, by rw [hspec, nd_bind_one hov, ht2, hl], hf3, hv3, hS3, fun y m hy => ?_, RingAt.kfoot hS hcC hR3⟩
    rw [hk] at hy; cases hy
    have hne3 := refills_ne' hR3.wf
    refine ⟨_, rfl, rfl, by simpa using hne3, fun r hr => ?_, ?_, ?_⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
      simpa [toRefill] using hp3 q hq
    · rw [← lsum_eq_map, hs3, hS2]; exact hsum
    · obtain ⟨q, l, e⟩ := List.exists_cons_of_ne_nil hne3
      have hh : Fl4Spec.refillHd { x with scRefills := (L.refills s3 sc).map toRefill } = toRefill q := by
        unfold Fl4Spec.refillHd; simp [e]; rfl
      rw [hh, ← hmb']
      rw [e] at hm3; simp only [List.headD_cons] at hm3
      rw [u64_lt_bv] at hm3
      show mb.bv ≤ q.amount.bv
      rw [BitVec.le_def]; rw [BitVec.lt_def] at hm3; omega

end

end

end Fl4Proofs.P3.Sched
