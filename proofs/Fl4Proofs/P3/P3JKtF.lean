/-
P3 (line p3J, gen 21): **the heap-type frame** (spec side only; outside the `JAtZ` cone), a scripted copy of
SpecInvDomF (`scratch/p3J/genKt.py`: `DL` ↦ `KQ`, `dlV` ↦ `ktV`).

* `ktV σ := fun o => (σ.kheap o).map aType`: the type of every heap object (UtRetResetJ's `khT`). `KQ m := FK ktV m`.
* `set_object` asserts that the new object has the old one's `a_type` (`kq_setObject`), so every spec function that
  writes the heap only through `set_object` keeps `ktV`; the only other heap writers are `retype_region` and
  `detype` (`delete_objects`), reached only from untyped invocations (P3JKtG leaves them out).

Named premises: none. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.VsDom
import Fl4Spec.Ext.Entry
open Classical

namespace Fl4Proofs.P3.SInvKt
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

/-- The type of every heap object (UtRetResetJ's `khT`). -/
def ktV (σ : State Unit) : ObjRef → Option AType := fun o => (σ.kheap o).map aType

/-- Every outcome of `m` keeps the type of every heap object. -/
abbrev KQ {α : Type} (m : NonDet (State Unit) α) : Prop := FK ktV m

/-- `KQ` for the exception monad. -/
abbrev KQE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := FKE ktV m

open Lean Meta Elab Tactic in
/-- Unfold the spec function at the head of an `FK`/`FKE` goal (sch12's
`fv_unfold`). -/
elab "kq_sf_unfold" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let args := t.getAppArgs
  if args.size == 0 then throwError "kq_sf_unfold: no arguments"
  let m := args.back!
  let m := if m.isAppOf ``ExceptT.run then m.getAppArgs.back! else m
  match m.getAppFn with
  | .const n _ =>
    if (`Fl4Spec).isPrefixOf n && !(`Fl4Spec.NonDet).isPrefixOf n && !(`Fl4Spec.NonDetE).isPrefixOf n then
      evalTactic (← `(tactic| unfold $(mkIdent n):ident))
    else throwError "kq_sf_unfold: {n} is not a spec function"
  | _ => throwError "kq_sf_unfold: no head constant"

/-- A `KQ` lemma of a spec function (extended below, one rule per lemma). -/
syntax "kq_leaf" : tactic
macro_rules | `(tactic| kq_leaf) => `(tactic| fail "no kq_leaf")

macro "kq_auto" : tactic => `(tactic| repeat' (first | kq_leaf | dk_step0 | kq_sf_unfold))

/-- `kq_auto` without unfolding (for the scripted copies of the `DK` lemmas). -/
macro "kq_auto0" : tactic => `(tactic| repeat' (first | kq_leaf | dk_step0))

/-! ## Leaves -/

theorem kq_doMachineOp {α : Type} (mop : NonDet MachineState α) : KQ (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_doMachineOp _)

theorem kq_doExtendedOp (eop : DetExtMonad Unit) : KQ (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_doExtendedOp _)

theorem kq_getCap (sl : CslotPtr) : KQ (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; dsimp only
  repeat' dk_step0
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getCap _)

theorem kqe_rab (p : Cap × CapRef) : KQE (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact dke_liftE (dk_fail)
    · refine dke_bind (dke_whenE _ (dke_throw _)) fun _ => dke_bind (dke_whenE _ (dke_throw _)) fun _ =>
        dke_bind (dke_returnOk _) fun _ => ?_
      dsimp only
      split
      · exact dke_returnOk _
      · refine dke_bind (dke_liftE (kq_getCap _)) fun nc => ?_
        split
        · exact kqe_rab _
        · exact dke_returnOk _
  · exact dke_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_rab _)

theorem kq_zipWithMx {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, KQ (g a b)) :
    ∀ l1 l2, KQ (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => dk_bind (h a b) (fun _ => kq_zipWithMx h l1 l2)
  | [], _ => dk_pure' _
  | _ :: _, [] => dk_pure' _
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible refine kq_zipWithMx (fun _ _ => ?_) _ _)

set_option maxRecDepth 20000

theorem kq_setObject (p : ObjRef) (o : KernelObject) : KQ (setObject (Z := Unit) p o) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨k, hk⟩ : ∃ k, σ.kheap p = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap p with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  obtain ⟨hk, rfl⟩ := hk
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨hty, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  funext o'
  unfold ktV
  by_cases e : o' = p
  · subst e; simp only [Function.update_self, hk, Option.map_some]; exact congrArg some hty.symm
  · simp only [Function.update_of_ne e]
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setObject _ _)

/-- A bind on a returned value (so that the continuation sees the value). -/
theorem kqe_returnOk_bind {ε α β : Type} {v : α} {g : α → NonDetE (State Unit) ε β} (h : KQE (g v)) :
    KQE (NonDetE.returnOk v >>= g) := by
  show FK ktV (ExceptT.run (NonDetE.returnOk v >>= g))
  rw [ExceptT.run_bind]
  intro σ x ⟨y, hy, hx⟩
  obtain rfl := Set.mem_singleton_iff.1 hy
  exact h σ x hx
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible refine kqe_returnOk_bind ?_)

end

end Fl4Proofs.P3.SInvKt
