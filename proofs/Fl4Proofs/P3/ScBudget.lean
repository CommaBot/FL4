/-
P3 (DESIGN.md §9), scheduling contexts: **`refill_budget_check`**, the
overrun loop (`handle_overrun`, `loop0_refines`).

Only the refill amounts matter for the simulation (times use the same
wrapping arithmetic on both sides): the amounts are positive (`Pos`, so each
round consumes at least one tick of usage and FL4's fuel, `U64::MAX`, never
runs out) and their sum (`lsum`) is fixed and below `2 ^ 64` (so merging two
refills does not wrap).
-/
import Fl4Proofs.P3.ScBudgetSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

/-! ## Amounts -/

/-- The sum of the amounts. -/
def lsum (rs : List sporadic.Refill) : Nat := (rs.map fun r => r.amount.val).sum

/-- All amounts are positive. -/
def Pos (rs : List sporadic.Refill) : Prop := ∀ r ∈ rs, 0 < r.amount.val

theorem lsum_eq_map (rs : List sporadic.Refill) :
    lsum rs = ((rs.map toRefill).map fun r => r.rAmount.toNat).sum := by
  simp [lsum, toRefill, Function.comp]; rfl

theorem lsum_append (a b : List sporadic.Refill) : lsum (a ++ b) = lsum a + lsum b := by
  simp [lsum]

theorem lsum_cons (r : sporadic.Refill) (a : List sporadic.Refill) : lsum (r :: a) = r.amount.val + lsum a := by
  simp [lsum]

theorem lsum_single (r : sporadic.Refill) : lsum [r] = r.amount.val := by simp [lsum]

theorem le_lsum {rs : List sporadic.Refill} {r : sporadic.Refill} (h : r ∈ rs) : r.amount.val ≤ lsum rs := by
  induction rs with
  | nil => cases h
  | cons a l ih =>
    rw [lsum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem getLastD_eq {rs : List sporadic.Refill} (hne : rs ≠ []) : rs.getLastD zR = rs.getLast hne := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast hne]; rfl

theorem split_last {rs : List sporadic.Refill} (hne : rs ≠ []) : rs = rs.dropLast ++ [rs.getLastD zR] := by
  rw [getLastD_eq hne, List.dropLast_concat_getLast]

theorem wadd_val' {x y : U64} (h : x.val + y.val < 2 ^ 64) : (core.num.U64.wrapping_add x y).val = x.val + y.val :=
  wadd_val h

theorem lsum_schedUsedL {m : Nat} {rs : List sporadic.Refill} (hne : rs ≠ []) {nw : sporadic.Refill}
    (hno : (rs.getLastD zR).amount.val + nw.amount.val < 2 ^ 64) :
    lsum (schedUsedL m rs nw) = lsum rs + nw.amount.val := by
  have e := split_last hne
  have hl : lsum rs = lsum rs.dropLast + (rs.getLastD zR).amount.val := by
    conv_lhs => rw [e]
    rw [lsum_append, lsum_single]
  unfold schedUsedL
  dsimp only
  split_ifs
  · rw [lsum_append, lsum_single]; simp only; rw [wadd_val' hno]; omega
  · rw [lsum_append, lsum_single]; simp only; rw [wadd_val' hno]; omega
  · rw [lsum_append, lsum_single]

theorem pos_schedUsedL {m : Nat} {rs : List sporadic.Refill} (hP : Pos rs) (hne : rs ≠ []) {nw : sporadic.Refill}
    (hno : (rs.getLastD zR).amount.val + nw.amount.val < 2 ^ 64) (hn : 0 < nw.amount.val) :
    Pos (schedUsedL m rs nw) := by
  have hd : ∀ r ∈ rs.dropLast, 0 < r.amount.val := fun r hr => hP r (List.dropLast_subset _ hr)
  unfold schedUsedL
  dsimp only
  split_ifs
  · intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hd r hr
    · simp only [List.mem_singleton] at hr; subst hr; simp only; rw [wadd_val' hno]; omega
  · intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hd r hr
    · simp only [List.mem_singleton] at hr; subst hr; simp only; rw [wadd_val' hno]; omega
  · intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hP r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact hn

theorem schedUsedL_ne {m : Nat} {rs : List sporadic.Refill} {nw : sporadic.Refill} : schedUsedL m rs nw ≠ [] := by
  unfold schedUsedL; dsimp only; split_ifs <;> simp

theorem u64_lt_bv (a b : U64) : a < b ↔ a.bv < b.bv := by
  rw [UScalar.lt_equiv, BitVec.lt_def]; rfl

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem refills_ne' {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) : L.refills s sc ≠ [] := by
  rw [refills_cons hW]; simp

theorem head_eq' {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) :
    L.refill s sc (L.rhead s sc) = (L.refills s sc).headD zR := by
  rw [refills_cons hW, ← rf0_eq hW]; rfl

theorem RingAt.period {s0 s : S} {sc : U64} {n : Nat} (h : RingAt st s0 s sc n) {x : Fl4Spec.SchedContext} {n' : Nat}
    (hx : ScRel1 st s0 sc x n') : L.rperiod s sc = L.rperiod s0 sc := by
  simp only [LawfulStore.rperiod, periodA_eq]
  exact h.hdr (by simp) (by simp) (hx.hdr (by simp) (by simp)).1

theorem single_iff' {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) :
    L.rhead s sc = L.rtail s sc ↔ (L.refills s sc).length = 1 := by
  rw [hW.single_iff, refills_length]

/-- The spec state with `sc`'s refills replaced by FL4's. -/
abbrev specAt (σ : Fl4Spec.State Unit) (sc : U64) (x : Fl4Spec.SchedContext) (n : Nat) (s : S) : Fl4Spec.State Unit :=
  updSc σ sc.bv { x with scRefills := (L.refills s sc).map toRefill } n

/-- **The overrun loop refines `handle_overrun`.** -/
theorem loop0_refines {s0 : S} {σ0 : Fl4Spec.State Unit} {sc : U64} {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ0.kheap sc.bv = some (.schedContext x n)) (hx : ScRel1 st s0 sc x n)
    (mrt period : U64) (hmrt : mrt.bv = Fl4Spec.MAX_RELEASE_TIME) (hper : L.rperiod s0 sc = period)
    (hpos : Pos (L.refills s0 sc)) (hsum : lsum (L.refills s0 sc) < 2 ^ 64)
    (usage fuel : U64) (hu : usage.val ≤ fuel.val) :
    sporadic.budget_check_loop0 st s0 sc mrt period usage fuel ⦃ s1 u1 =>
      RingAt st s0 s1 sc n ∧ Pos (LawfulStore.refills (st := st) s1 sc) ∧
      lsum (LawfulStore.refills (st := st) s1 sc) = lsum (L.refills s0 sc) ∧
      ¬ (((LawfulStore.refills (st := st) s1 sc).headD zR).amount ≤ u1 ∧
        ((LawfulStore.refills (st := st) s1 sc).headD zR).time < mrt) ∧
      Fl4Spec.handleOverrun (Z := Unit) sc.bv usage.bv σ0 = ({(u1.bv, specAt (st := st) σ0 sc x n s1)}, False) ⦄ := by
  have hkk : ∀ s : S, (specAt (st := st) σ0 sc x n s).kheap sc.bv =
      some (.schedContext { x with scRefills := (L.refills s sc).map toRefill } n) := fun s => by
    simp only [specAt, updK_kheap, Function.update_self] <;> rfl
  have hper' : x.scPeriod = period.bv := by rw [hx.period, hper]
  have hmax : x.scRefillMax = (L.rmax s0 sc).val := hx.max.symm
  have h00 : specAt (st := st) σ0 sc x n s0 = σ0 := by
    show updSc σ0 sc.bv { x with scRefills := (L.refills s0 sc).map toRefill } n = σ0
    rw [← hx.refills]; exact updSc_self hk
  unfold sporadic.budget_check_loop0
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => RingAt st s0 y.1 sc n ∧ Pos (L.refills y.1 sc) ∧
      lsum (L.refills y.1 sc) = lsum (L.refills s0 sc) ∧ y.2.1.val ≤ y.2.2.val ∧
      Fl4Spec.handleOverrun (Z := Unit) sc.bv usage.bv σ0 =
        Fl4Spec.handleOverrun (Z := Unit) sc.bv y.2.1.bv (specAt (st := st) σ0 sc x n y.1))
  · rintro ⟨x0, x1, x2⟩ ⟨hR, hP, hS, hle, hsp⟩
    dsimp only at hR hP hS hle hsp
    have hW := hR.wf
    have hne := refills_ne' hW
    have hne' : ((L.refills x0 sc).map toRefill) ≠ [] := by simpa using hne
    set hd := (L.refills x0 sc).headD zR with hhd
    have hdm : hd ∈ L.refills x0 sc := by
      obtain ⟨a, l, e⟩ := List.exists_cons_of_ne_nil hne; rw [hhd, e]; exact List.mem_cons_self
    have hpos0 := hP hd hdm
    have hC : Fl4Spec.the (Fl4Spec.headRefillOverrun (Z := Unit) sc.bv x1.bv (specAt (st := st) σ0 sc x n x0)) = true ↔
        (hd.amount ≤ x1 ∧ hd.time < mrt) := by
      rw [headRefillOverrun_eq (hkk x0) hne', refillHd_map rfl hne, the_some, decide_eq_true_iff, ← hhd]
      simp only [toRefill, ← u64_le_bv, ← hmrt, ← u64_lt_bv]
    have fin : ¬ (hd.amount ≤ x1 ∧ hd.time < mrt) →
        RingAt st s0 x0 sc n ∧ Pos (L.refills x0 sc) ∧ lsum (L.refills x0 sc) = lsum (L.refills s0 sc) ∧
        ¬ (((L.refills x0 sc).headD zR).amount ≤ x1 ∧ ((L.refills x0 sc).headD zR).time < mrt) ∧
        Fl4Spec.handleOverrun (Z := Unit) sc.bv usage.bv σ0 = ({(x1.bv, specAt (st := st) σ0 sc x n x0)}, False) :=
      fun hnc => ⟨hR, hP, hS, hnc, by
        rw [hsp]; unfold Fl4Spec.handleOverrun
        exact wl_done (C := fun usage s => Fl4Spec.the (Fl4Spec.headRefillOverrun (Z := Unit) sc.bv usage s) = true)
          (B := fun usage => Fl4Spec.chargeEntireHeadRefill sc.bv usage) (fun h => hnc (hC.1 h))⟩
    unfold sporadic.budget_check_loop0.body
    step as ⟨h, h_post⟩
    rw [head_eq' hW, ← hhd] at h_post
    subst h_post
    split
    · rename_i hA
      split
      · rename_i hT
        split
        · -- a head with no budget: ruled out, refill amounts are positive
          rename_i hz
          exfalso
          rw [hz] at hpos0; simp at hpos0
        · split
          · rename_i hf
            exfalso
            have : x1.val = 0 := by rw [hf] at hle; simpa using hle
            rw [UScalar.le_equiv] at hA; omega
          · rename_i hf
            have hf' : fuel.val = fuel.val := rfl
            step as ⟨fuel1, fuel1_post⟩
            step as ⟨b, b_post⟩
            have hA' : hd.amount.val ≤ x1.val := by rw [UScalar.le_equiv] at hA; exact hA
            have hu1 : (core.num.U64.wrapping_sub x1 hd.amount).val = x1.val - hd.amount.val := wsub_val hA'
            have hspc := chargeEntire_eq (hkk x0) rfl hne (per := period) hper' x1.bv
            have hstep : Fl4Spec.handleOverrun (Z := Unit) sc.bv x1.bv (specAt (st := st) σ0 sc x n x0) =
                Fl4Spec.handleOverrun (Z := Unit) sc.bv (x1.bv - (toRefill hd).rAmount)
                  (updSc σ0 sc.bv { x with scRefills := (chargeL x.scRefillMax period (L.refills x0 sc)).map toRefill } n) := by
              unfold Fl4Spec.handleOverrun
              rw [wl_step (C := fun usage s => Fl4Spec.the (Fl4Spec.headRefillOverrun (Z := Unit) sc.bv usage s) = true)
                (B := fun usage => Fl4Spec.chargeEntireHeadRefill sc.bv usage) (hC.2 ⟨hA, hT⟩) hspc, updSc_updSc]
            have hcont : ∀ s1 : S, RingAt st s0 s1 sc n →
                L.refills s1 sc = chargeL x.scRefillMax period (L.refills x0 sc) →
                Pos (L.refills s1 sc) → lsum (L.refills s1 sc) = lsum (L.refills s0 sc) →
                RingAt st s0 s1 sc n ∧ Pos (L.refills s1 sc) ∧ lsum (L.refills s1 sc) = lsum (L.refills s0 sc) ∧
                  (core.num.U64.wrapping_sub x1 hd.amount).val ≤ fuel1.val ∧
                  Fl4Spec.handleOverrun (Z := Unit) sc.bv usage.bv σ0 = Fl4Spec.handleOverrun (Z := Unit) sc.bv
                    (core.num.U64.wrapping_sub x1 hd.amount).bv (specAt (st := st) σ0 sc x n s1) ∧ fuel1.val < x2.val := by
              intro s1 h1 hl1 hp1 hs1
              refine ⟨h1, hp1, hs1, ?_, ?_, ?_⟩
              · rw [hu1, fuel1_post]; omega
              · rw [hsp, hstep, core.num.U64.wrapping_sub_bv_eq]
                show _ = Fl4Spec.handleOverrun (Z := Unit) sc.bv _
                  (updSc σ0 sc.bv { x with scRefills := (L.refills s1 sc).map toRefill } n)
                rw [hl1]; rfl
              · rw [fuel1_post]
                have : x2.val ≠ 0 := fun e => hf (UScalar.eq_of_val_eq (by simpa using e))
                omega
            split
            · -- a single refill: a period later
              rename_i hb
              have h1 : (L.refills x0 sc).length = 1 := (single_iff' hW).1 (by rw [b_post] at hb; simpa using hb)
              step as ⟨i1, i1_post⟩
              refine WP.spec_bind (set_head_ring hR _) ?_
              rintro s1 ⟨hR1, hl1⟩
              obtain ⟨a, l, e⟩ := List.exists_cons_of_ne_nil hne
              have hl : l = [] := by rw [e] at h1; simpa using h1
              subst hl
              have hl1' : L.refills s1 sc = chargeL x.scRefillMax period (L.refills x0 sc) := by
                rw [hl1, e]; unfold chargeL; simp only [List.length_cons, List.length_nil, ↓reduceIte,
                  List.headD_cons, List.tail_cons, i1_post]
                rw [e] at hhd; simp only [List.headD_cons] at hhd; rw [hhd]
              simp only [lift, bind_ok, WP.spec_ok]
              refine hcont s1 hR1 hl1' ?_ ?_
              · rw [hl1, e]; intro r hr
                simp only [List.tail_cons, List.mem_singleton] at hr; subst hr
                simpa using hpos0
              · have ha : hd = a := by rw [hhd, e]; rfl
                rw [hl1, ← hS, e]; simp [lsum, ha]
            · -- pop the head and schedule it a period later
              rename_i hb
              have hneq : L.rhead x0 sc ≠ L.rtail x0 sc := by rw [b_post] at hb; simpa using hb
              have h2 : (L.refills x0 sc).length ≠ 1 := fun e => hneq ((single_iff' hW).2 e)
              obtain ⟨a, l, e⟩ := List.exists_cons_of_ne_nil hne
              have hlne : l ≠ [] := by rintro rfl; exact h2 (by rw [e]; rfl)
              have ha : hd = a := by rw [hhd, e]; rfl
              have hno : (l.getLastD zR).amount.val + a.amount.val < 2 ^ 64 := by
                have hS' := hS
                rw [e, lsum_cons] at hS'
                have h3 := le_lsum (rs := l) (r := l.getLastD zR) (by rw [getLastD_eq hlne]; exact List.getLast_mem hlne)
                omega
              refine WP.spec_bind (Pₘ := fun s3 => RingAt st s0 s3 sc n ∧
                L.refills s3 sc = chargeL x.scRefillMax period (L.refills x0 sc) ∧ Pos (L.refills s3 sc) ∧
                lsum (L.refills s3 sc) = lsum (L.refills s0 sc)) ?_ ?_
              · refine WP.spec_bind (pop_head_ring hR hneq) ?_
                rintro ⟨old, s2⟩ ⟨hold, hR2, hl2⟩
                rw [← hhd] at hold
                subst hold
                step as ⟨i1, i1_post⟩
                refine WP.spec_mono (schedule_used_ring hR2 _) ?_
                rintro s3 ⟨hR3, hl3⟩
                have htl : L.refills s2 sc = l := by rw [hl2, e]; rfl
                refine ⟨hR3, ?_, ?_, ?_⟩
                · rw [hl3, htl, hR2.mx, ← hmax, e]
                  unfold chargeL
                  simp only [List.headD_cons, List.tail_cons, i1_post, ← ha]
                  rw [if_neg (by simpa using hlne)]
                · rw [hl3, htl]
                  exact pos_schedUsedL (fun r hr => hP r (by rw [e]; exact List.mem_cons_of_mem _ hr)) hlne
                    (by rw [ha]; simpa using hno) (by simpa using hpos0)
                · rw [hl3, htl, lsum_schedUsedL hlne (by rw [ha]; simpa using hno), ← hS, e, lsum_cons, ← ha]
                  simp only; omega
              · rintro s3 ⟨hR3, hl3', hp3, hs3⟩
                simp only [lift, bind_ok, WP.spec_ok]
                exact hcont s3 hR3 hl3' hp3 hs3
      · rename_i hT
        simp only [WP.spec_ok]
        exact fin fun h => hT h.2
    · rename_i hA
      simp only [WP.spec_ok]
      exact fin fun h => hA h.1
  · exact ⟨RingAt.refl hx.wf, hpos, rfl, hu, by rw [h00]⟩

/-! ## The insufficient-head loop -/

theorem refillHeadInsufficient_eq {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.SchedContext}
    {n : Nat} (hk : σ.kheap p = some (.schedContext x n)) (hne : x.scRefills ≠ []) :
    Fl4Spec.refillHeadInsufficient (Z := Unit) p σ =
      some (decide ((Fl4Spec.refillHd x).rAmount < Fl4Spec.MIN_BUDGET)) := by
  show Option.bind (Fl4Spec.readRefillHead p σ) (fun h => Fl4Spec.Lookup.oreturn _ σ) = _
  rw [readRefillHead_eq hk hne]; rfl

/-- `merge_nonoverlapping_head_refill` on the list. -/
def mergeL (rs : List sporadic.Refill) : List sporadic.Refill :=
  ⟨core.num.U64.wrapping_sub (rs.tail.headD zR).time (rs.headD zR).amount,
    core.num.U64.wrapping_add (rs.tail.headD zR).amount (rs.headD zR).amount⟩ :: rs.tail.tail

theorem mergeNH_eq {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) {rs : List sporadic.Refill} (hx : x.scRefills = rs.map toRefill)
    (h2 : 2 ≤ rs.length) :
    Fl4Spec.mergeNonoverlappingHeadRefill (Z := Unit) p σ =
      ({((), updSc σ p { x with scRefills := (mergeL rs).map toRefill } n)}, False) := by
  obtain ⟨a, b, l, rfl⟩ : ∃ a b l, rs = a :: b :: l := by
    match rs, h2 with
    | a :: b :: l, _ => exact ⟨a, b, l, rfl⟩
  have hne' : x.scRefills ≠ [] := by rw [hx]; simp
  unfold Fl4Spec.mergeNonoverlappingHeadRefill
  rw [nd_bind_one (refillPopHead_eq hk hne')]
  have hk1 : (updSc σ p { x with scRefills := x.scRefills.tail } n).kheap p =
      some (.schedContext { x with scRefills := x.scRefills.tail } n) := by simp [updK]
  rw [nd_bind_one (updateRefillHd_eq hk1 _)]
  have hk2 : ∀ y : Fl4Spec.SchedContext, (updSc (updSc σ p { x with scRefills := x.scRefills.tail } n) p y n).kheap p =
      some (.schedContext y n) := fun y => by simp [updK]
  rw [updateRefillHd_eq (hk2 _), updSc_updSc, updSc_updSc]
  congr 4
  simp [hx, mergeL, Fl4Spec.refillHd, Fl4Spec.the, toRefill, core.num.U64.wrapping_add_bv_eq,
    core.num.U64.wrapping_sub_bv_eq]

/-- **The insufficient-head loop refines `head_insufficient_loop`**, for
positive amounts whose sum is at least the minimum budget. -/
theorem loop1_refines {s0 s1 : S} {σ0 : Fl4Spec.State Unit} {sc : U64} {x : Fl4Spec.SchedContext} {n : Nat}
    (h1 : RingAt st s0 s1 sc n) (hpos : Pos (L.refills s1 sc)) (hsum : lsum (L.refills s1 sc) < 2 ^ 64)
    (mb : U64) (hmb : mb.bv = Fl4Spec.MIN_BUDGET) (hmin : mb.val ≤ lsum (L.refills s1 sc))
    (fuel2 : U64) (hf : (L.refills s1 sc).length ≤ fuel2.val) :
    sporadic.budget_check_loop1 st s1 sc mb fuel2 ⦃ s2 => RingAt st s0 s2 sc n ∧
      Pos (LawfulStore.refills (st := st) s2 sc) ∧
      lsum (LawfulStore.refills (st := st) s2 sc) = lsum (L.refills s1 sc) ∧
      ¬ ((LawfulStore.refills (st := st) s2 sc).headD zR).amount < mb ∧
      Fl4Spec.headInsufficientLoop (Z := Unit) sc.bv (specAt (st := st) σ0 sc x n s1) =
        ({((), specAt (st := st) σ0 sc x n s2)}, False) ⦄ := by
  have hkk : ∀ s : S, (specAt (st := st) σ0 sc x n s).kheap sc.bv =
      some (.schedContext { x with scRefills := (L.refills s sc).map toRefill } n) := fun s => by
    simp only [specAt, updK_kheap, Function.update_self] <;> rfl
  unfold sporadic.budget_check_loop1
  apply loop.spec_decr_nat (measure := fun y => y.2.val)
    (inv := fun y => RingAt st s0 y.1 sc n ∧ Pos (L.refills y.1 sc) ∧
      lsum (L.refills y.1 sc) = lsum (L.refills s1 sc) ∧ (L.refills y.1 sc).length ≤ y.2.val ∧
      Fl4Spec.headInsufficientLoop (Z := Unit) sc.bv (specAt (st := st) σ0 sc x n s1) =
        Fl4Spec.headInsufficientLoop (Z := Unit) sc.bv (specAt (st := st) σ0 sc x n y.1))
  · rintro ⟨x0, x1⟩ ⟨hR, hP, hS, hle, hsp⟩
    dsimp only at hR hP hS hle hsp
    have hW := hR.wf
    have hne := refills_ne' hW
    have hne' : ((L.refills x0 sc).map toRefill) ≠ [] := by simpa using hne
    set hd := (L.refills x0 sc).headD zR with hhd
    have hC : Fl4Spec.the (Fl4Spec.refillHeadInsufficient (Z := Unit) sc.bv (specAt (st := st) σ0 sc x n x0)) = true ↔
        hd.amount < mb := by
      rw [refillHeadInsufficient_eq (hkk x0) hne', refillHd_map rfl hne, the_some, decide_eq_true_iff, ← hhd]
      simp only [toRefill, ← hmb, ← u64_lt_bv]
    have fin : ¬ hd.amount < mb → RingAt st s0 x0 sc n ∧ Pos (L.refills x0 sc) ∧
        lsum (L.refills x0 sc) = lsum (L.refills s1 sc) ∧ ¬ ((L.refills x0 sc).headD zR).amount < mb ∧
        Fl4Spec.headInsufficientLoop (Z := Unit) sc.bv (specAt (st := st) σ0 sc x n s1) =
          ({((), specAt (st := st) σ0 sc x n x0)}, False) := fun hnc => ⟨hR, hP, hS, by rw [← hhd]; exact hnc, by
      rw [hsp]; unfold Fl4Spec.headInsufficientLoop
      exact wl_done (C := fun _ s => Fl4Spec.the (Fl4Spec.refillHeadInsufficient (Z := Unit) sc.bv s) = true)
        (B := fun _ => Fl4Spec.mergeNonoverlappingHeadRefill sc.bv) (fun h => hnc (hC.1 h))⟩
    unfold sporadic.budget_check_loop1.body
    step as ⟨r, r_post⟩
    rw [head_eq' hW, ← hhd] at r_post
    subst r_post
    split
    · rename_i hlt
      step as ⟨b, b_post⟩
      split
      · rename_i hb
        exfalso
        have h1' : (L.refills x0 sc).length = 1 := (single_iff' hW).1 (by rw [b_post] at hb; simpa using hb)
        obtain ⟨a, l, e⟩ := List.exists_cons_of_ne_nil hne
        have hl : l = [] := by rw [e] at h1'; simpa using h1'
        subst hl
        have ha : hd = a := by rw [hhd, e]; rfl
        have : lsum (L.refills x0 sc) = a.amount.val := by rw [e]; simp [lsum]
        rw [UScalar.lt_equiv] at hlt
        rw [ha] at hlt; omega
      · rename_i hb
        have hneq : L.rhead x0 sc ≠ L.rtail x0 sc := by rw [b_post] at hb; simpa using hb
        have h2 : (L.refills x0 sc).length ≠ 1 := fun e => hneq ((single_iff' hW).2 e)
        split
        · rename_i hfp
          step as ⟨fuel21, fuel21_post⟩
          have hx1 : 0 < x1.val := by have := hfp; rw [GT.gt, UScalar.lt_equiv] at this; simpa using this
          obtain ⟨a, c, l, e⟩ : ∃ a c l, L.refills x0 sc = a :: c :: l := by
            match h : L.refills x0 sc with
            | [] => exact absurd h hne
            | [a] => exact absurd (by rw [h]; rfl) h2
            | a :: c :: l => exact ⟨a, c, l, rfl⟩
          have ha : hd = a := by rw [hhd, e]; rfl
          have hno : c.amount.val + a.amount.val < 2 ^ 64 := by
            have := hS; rw [e, lsum_cons, lsum_cons] at this; omega
          refine WP.spec_bind (pop_head_ring hR hneq) ?_
          rintro ⟨old, s2⟩ ⟨hold, hR2, hl2⟩
          rw [← hhd] at hold
          subst hold
          have htl : L.refills s2 sc = c :: l := by rw [hl2, e]; rfl
          step as ⟨h, h_post⟩
          rw [head_eq' hR2.wf, htl] at h_post
          simp only [List.headD_cons] at h_post
          subst h
          step as ⟨i1, i1_post⟩
          step as ⟨i2, i2_post⟩
          refine WP.spec_bind (set_head_ring hR2 _) ?_
          rintro s3 ⟨hR3, hl3⟩
          have hl3' : L.refills s3 sc = mergeL (L.refills x0 sc) := by
            rw [hl3, htl, e]; simp only [mergeL, List.tail_cons, List.headD_cons, i1_post, i2_post, ← ha]
          simp only [WP.spec_ok]
          refine ⟨hR3, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hl3']; intro q hq
            rw [e] at hq; simp only [mergeL, List.tail_cons, List.headD_cons, List.mem_cons] at hq
            rcases hq with rfl | hq
            · simp only; rw [wadd_val' hno]; have := hP c (by rw [e]; simp); omega
            · exact hP q (by rw [e]; simp [hq])
          · rw [hl3', ← hS, e]; simp only [mergeL, List.tail_cons, List.headD_cons, lsum_cons]
            rw [wadd_val' hno]; omega
          · rw [hl3', e, fuel21_post]; rw [e] at hle
            simp only [mergeL, List.tail_cons, List.length_cons] at hle ⊢
            omega
          · rw [hsp]; unfold Fl4Spec.headInsufficientLoop
            rw [wl_step (C := fun _ s => Fl4Spec.the (Fl4Spec.refillHeadInsufficient (Z := Unit) sc.bv s) = true)
              (B := fun _ => Fl4Spec.mergeNonoverlappingHeadRefill sc.bv) (hC.2 hlt)
              (mergeNH_eq (hkk x0) rfl (by rw [e]; simp)), updSc_updSc]
            show _ = Fl4Spec.NonDet.whileLoop _ _ () (updSc σ0 sc.bv { x with scRefills := (L.refills s3 sc).map toRefill } n)
            rw [hl3']
          · rw [fuel21_post]; omega
        · rename_i hfp
          exfalso
          have : x1.val = 0 := by
            rw [GT.gt, UScalar.lt_equiv] at hfp; simp at hfp; omega
          have := hW.size_pos; rw [← refills_length] at this; omega
    · rename_i hlt
      simp only [WP.spec_ok]
      exact fin hlt
  · exact ⟨h1, hpos, rfl, hf, rfl⟩

end

end

end Fl4Proofs.P3.Sched
