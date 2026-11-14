/-
P3 (DESIGN.md §9), scheduling contexts: the spec's refill-list operations on
a related SC, as the list operations of ScRing.lean (`toRefill` images):
`update_refill_tl`, `refill_add_tail`, `get_refill_tail`, `refill_single`,
`refill_full`, and `schedule_used` (`scheduleUsed_eq`, FL4's `schedUsedL`).
-/
import Fl4Proofs.P3.ScRing
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec
variable {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}

theorem getRefills_eq (hk : σ.kheap p = some (.schedContext x n)) :
    getRefills (Z := Unit) p σ = ({(x.scRefills, σ)}, False) := by
  unfold getRefills; rw [nd_bind_one (getSchedContext_eq hk)]; rfl

theorem getRefillTail_eq (hk : σ.kheap p = some (.schedContext x n)) (hne : x.scRefills ≠ []) :
    getRefillTail (Z := Unit) p σ = ({(refillTl x, σ)}, False) := by
  have : readRefillTail (Z := Unit) p σ = some (refillTl x) := by
    show Option.bind (readSchedContext p σ) (fun sc => Option.bind (Lookup.oassert (sc.scRefills ≠ []) σ)
      (fun _ => Lookup.oreturn (refillTl sc) σ)) = _
    rw [readSchedContext_eq hk]
    simp [Lookup.oassert, hne, Lookup.oreturn]
  simp [getRefillTail, NonDet.getsThe, this, NonDet.assertOpt]; rfl

theorem refillSingle_eq (hk : σ.kheap p = some (.schedContext x n)) :
    refillSingle (Z := Unit) p σ = ({(decide (x.scRefills.length = 1), σ)}, False) := by
  unfold refillSingle refillSize
  rw [nd_bind_one (nd_bind_one (getRefills_eq hk) _)]; rfl

theorem refillFull_eq (hk : σ.kheap p = some (.schedContext x n)) :
    refillFull (Z := Unit) p σ = ({(decide (x.scRefills.length = x.scRefillMax), σ)}, False) := by
  unfold refillFull
  rw [nd_bind_one (getSchedContext_eq hk)]; rfl

theorem updateRefillTl_eq (hk : σ.kheap p = some (.schedContext x n)) (f : Refill → Refill) :
    updateRefillTl (Z := Unit) p f σ =
      ({((), updSc σ p { x with scRefills := x.scRefills.dropLast ++ [f (the x.scRefills.getLast?)] } n)}, False) :=
  updateSchedContext_eq hk _

theorem refillAddTail_eq (hk : σ.kheap p = some (.schedContext x n)) (r : Refill) :
    refillAddTail (Z := Unit) p r σ = ({((), updSc σ p { x with scRefills := x.scRefills ++ [r] } n)}, False) :=
  updateSchedContext_eq hk _

end Spec

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem the_getLast_map {rs : List sporadic.Refill} (hne : rs ≠ []) :
    Fl4Spec.the (rs.map toRefill).getLast? = toRefill (rs.getLastD zR) := by
  rw [List.getLast?_map, List.getLast?_eq_getLast hne]
  simp [List.getLastD_eq_getLast?, List.getLast?_eq_getLast hne]; rfl

/-- **`schedule_used` refines `schedule_used`** on the lists. -/
theorem scheduleUsed_eq {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) {rs : List sporadic.Refill} (hx : x.scRefills = rs.map toRefill)
    (hne : rs ≠ []) (nw : sporadic.Refill) :
    Fl4Spec.scheduleUsed (Z := Unit) p (toRefill nw) σ =
      ({((), updSc σ p { x with scRefills := (schedUsedL x.scRefillMax rs nw).map toRefill } n)}, False) := by
  have hne' : x.scRefills ≠ [] := by rw [hx]; simpa using hne
  have htl : Fl4Spec.refillTl x = toRefill (rs.getLastD zR) := by
    unfold Fl4Spec.refillTl; rw [hx]; exact the_getLast_map hne
  unfold Fl4Spec.scheduleUsed
  rw [nd_bind_one (getRefills_eq hk), nd_bind_one (assert_true hne' σ), nd_bind_one (getRefillTail_eq hk hne'), htl]
  set t := rs.getLastD zR with ht
  have hmerge : Fl4Spec.canMergeRefill (toRefill t) (toRefill nw) ↔
      nw.time ≤ core.num.U64.wrapping_add t.time t.amount := by
    unfold Fl4Spec.canMergeRefill toRefill
    rw [u64_le_bv, core.num.U64.wrapping_add_bv_eq]
  have hd : (x.scRefills.dropLast) = (rs.dropLast).map toRefill := by rw [hx, List.map_dropLast]
  have hlast : Fl4Spec.the x.scRefills.getLast? = toRefill t := by rw [hx]; exact the_getLast_map hne
  unfold schedUsedL
  simp only [← ht]
  by_cases hc : nw.time ≤ core.num.U64.wrapping_add t.time t.amount
  · rw [ite_t (hmerge.2 hc), ite_t hc, updateRefillTl_eq hk]
    congr 4
    rw [hd, hlast, List.map_append, List.map_singleton]
    simp [toRefill, core.num.U64.wrapping_add_bv_eq]
  · rw [ite_f (fun h => hc (hmerge.1 h)), ite_f hc, nd_bind_one (refillFull_eq hk)]
    by_cases hf : rs.length = x.scRefillMax
    · have hf' : x.scRefills.length = x.scRefillMax := by rw [hx, List.length_map]; exact hf
      simp only [hf', decide_true, not_true_eq_false, ↓reduceIte, hf]
      rw [nd_bind_one (updateRefillTl_eq hk _)]
      have hk1 : (updSc σ p { x with scRefills := x.scRefills.dropLast ++
          [{ Fl4Spec.the x.scRefills.getLast? with rTime := (toRefill nw).rTime - (toRefill t).rAmount }] } n).kheap p =
          some (.schedContext { x with scRefills := x.scRefills.dropLast ++
            [{ Fl4Spec.the x.scRefills.getLast? with rTime := (toRefill nw).rTime - (toRefill t).rAmount }] } n) := by
        simp [updK]
      rw [updateRefillTl_eq hk1, updSc_updSc]
      congr 4
      simp only [List.dropLast_concat, List.getLast?_append, List.getLast?_singleton, Option.some_or]
      rw [hd, hlast, List.map_append, List.map_singleton]
      simp [Fl4Spec.the, toRefill, core.num.U64.wrapping_add_bv_eq, core.num.U64.wrapping_sub_bv_eq]
    · have hf' : ¬ x.scRefills.length = x.scRefillMax := by rw [hx, List.length_map]; exact hf
      simp only [hf', decide_false, not_false_eq_true, ↓reduceIte, hf, Bool.false_eq_true]
      rw [refillAddTail_eq hk, hx, List.map_append, List.map_singleton]

theorem updSc_self {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) : updSc σ p x n = σ := by
  show updK σ p _ = σ
  unfold updK
  have : Function.update σ.kheap p (some (.schedContext x n)) = σ.kheap := by
    funext q; by_cases e : q = p
    · subst e; simp [hk]
    · simp [e]
  rw [this]

theorem refillHd_map {x : Fl4Spec.SchedContext} {rs : List sporadic.Refill} (hx : x.scRefills = rs.map toRefill)
    (hne : rs ≠ []) : Fl4Spec.refillHd x = toRefill (rs.headD zR) := by
  unfold Fl4Spec.refillHd; rw [hx]
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne; rfl

theorem headRefillOverrun_eq {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (hne : x.scRefills ≠ []) (u : Fl4Spec.Ticks) :
    Fl4Spec.headRefillOverrun (Z := Unit) p u σ = some (decide ((Fl4Spec.refillHd x).rAmount ≤ u ∧
      (Fl4Spec.refillHd x).rTime < Fl4Spec.MAX_RELEASE_TIME)) := by
  show Option.bind (Fl4Spec.readRefillHead p σ) (fun h => Fl4Spec.Lookup.oreturn _ σ) = _
  rw [readRefillHead_eq hk hne]; rfl

/-- `charge_entire_head_refill` on the list. -/
def chargeL (m : Nat) (per : U64) (rs : List sporadic.Refill) : List sporadic.Refill :=
  if rs.length = 1 then [⟨core.num.U64.wrapping_add (rs.headD zR).time per, (rs.headD zR).amount⟩]
  else schedUsedL m rs.tail ⟨core.num.U64.wrapping_add (rs.headD zR).time per, (rs.headD zR).amount⟩

theorem chargeEntire_eq {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) {rs : List sporadic.Refill} (hx : x.scRefills = rs.map toRefill)
    (hne : rs ≠ []) {per : U64} (hper : x.scPeriod = per.bv) (u : Fl4Spec.Ticks) :
    Fl4Spec.chargeEntireHeadRefill (Z := Unit) p u σ =
      ({(u - (toRefill (rs.headD zR)).rAmount,
        updSc σ p { x with scRefills := (chargeL x.scRefillMax per rs).map toRefill } n)}, False) := by
  have hne' : x.scRefills ≠ [] := by rw [hx]; simpa using hne
  have hhd := refillHd_map hx hne
  unfold Fl4Spec.chargeEntireHeadRefill
  rw [nd_bind_one (getRefillHead_eq hk hne'), nd_bind_one (getSchedContext_eq hk),
    nd_bind_one (refillSingle_eq hk), hhd, hper]
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
  unfold chargeL
  by_cases h1 : (a :: l).length = 1
  · have hl : l = [] := by simpa using h1
    subst hl
    have h1' : (x.scRefills.length = 1) := by rw [hx]; rfl
    simp only [h1', decide_true, ↓reduceIte, h1]
    rw [nd_bind_one (updateRefillHd_eq hk _)]
    show ({(_, _)}, False) = _
    congr 4
    rw [hx]
    simp [toRefill, Fl4Spec.the, core.num.U64.wrapping_add_bv_eq, hper]
  · have h1' : ¬ (x.scRefills.length = 1) := by rw [hx, List.length_map]; exact h1
    simp only [h1', decide_false, Bool.false_eq_true, ↓reduceIte, h1]
    rw [nd_bind_one (refillPopHead_eq hk hne'), hhd]
    have hl : l ≠ [] := by rintro rfl; exact h1 rfl
    have hk1 : (updSc σ p { x with scRefills := x.scRefills.tail } n).kheap p =
        some (.schedContext { x with scRefills := x.scRefills.tail } n) := by simp [updK]
    have hx1 : ({ x with scRefills := x.scRefills.tail } : Fl4Spec.SchedContext).scRefills = l.map toRefill := by
      rw [hx]; rfl
    have e := scheduleUsed_eq hk1 hx1 hl ⟨core.num.U64.wrapping_add a.time per, a.amount⟩
    have et : toRefill ⟨core.num.U64.wrapping_add a.time per, a.amount⟩ =
        { rTime := (toRefill a).rTime + per.bv, rAmount := (toRefill a).rAmount } := by
      simp [toRefill, core.num.U64.wrapping_add_bv_eq]
    simp only [List.headD_cons]
    rw [← et, nd_bind_one e, updSc_updSc]
    simp only [h1, ↓reduceIte, List.headD_cons, List.tail_cons]
    rw [hper]; rfl

end

end

end Fl4Proofs.P3.Sched
