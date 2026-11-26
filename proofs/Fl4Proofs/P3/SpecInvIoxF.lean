/-
P3 (line p3J, gen 4): **the IOAPIC-count frame, kit** (spec side only, outside the JAtZ cone): `SpecInvDomF` with the projection
`dlV` (the domain list) replaced by `ioxV` (`x64_num_ioapics`, `x64_ioapic_nirqs`), a scripted renaming
(`scratch/p3J/genIox.py`; VsDom's `FK` combinators are generic in the projection). No sorry.
-/
import Fl4Proofs.P3.VsDom
import Fl4Spec.Ext.Entry
open Classical

namespace Fl4Proofs.P3.SInvIox
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

/-- The IOAPIC count and the pin counts of the spec's arch state (`x64_num_ioapics`,
`x64_ioapic_nirqs`; written by no spec step). -/
def ioxV (σ : State Unit) : Word64 × (Word → BitVec 8) :=
  (σ.archState.x64NumIoapics, σ.archState.x64IoapicNirqs)

/-- Every outcome of `m` keeps the domain list, its start and its index. -/
abbrev IOX {α : Type} (m : NonDet (State Unit) α) : Prop := FK ioxV m

/-- `IOX` for the exception monad. -/
abbrev IOXE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := FKE ioxV m

open Lean Meta Elab Tactic in
/-- Unfold the spec function at the head of an `FK`/`FKE` goal (sch12's
`fv_unfold`). -/
elab "iox_unfold" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let args := t.getAppArgs
  if args.size == 0 then throwError "iox_unfold: no arguments"
  let m := args.back!
  let m := if m.isAppOf ``ExceptT.run then m.getAppArgs.back! else m
  match m.getAppFn with
  | .const n _ =>
    if (`Fl4Spec).isPrefixOf n && !(`Fl4Spec.NonDet).isPrefixOf n && !(`Fl4Spec.NonDetE).isPrefixOf n then
      evalTactic (← `(tactic| unfold $(mkIdent n):ident))
    else throwError "iox_unfold: {n} is not a spec function"
  | _ => throwError "iox_unfold: no head constant"

/-- A `IOX` lemma of a spec function (extended below, one rule per lemma). -/
syntax "iox_leaf" : tactic
macro_rules | `(tactic| iox_leaf) => `(tactic| fail "no iox_leaf")

macro "iox_auto" : tactic => `(tactic| repeat' (first | iox_leaf | dk_step0 | iox_unfold))

/-- `iox_auto` without unfolding (for the scripted copies of the `DK` lemmas). -/
macro "iox_auto0" : tactic => `(tactic| repeat' (first | iox_leaf | dk_step0))

/-! ## Leaves -/

theorem iox_doMachineOp {α : Type} (mop : NonDet MachineState α) : IOX (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_doMachineOp _)

theorem iox_doExtendedOp (eop : DetExtMonad Unit) : IOX (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_doExtendedOp _)

theorem iox_getCap (sl : CslotPtr) : IOX (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; dsimp only
  repeat' dk_step0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getCap _)

theorem ioxe_rab (p : Cap × CapRef) : IOXE (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact dke_liftE (dk_fail)
    · refine dke_bind (dke_whenE _ (dke_throw _)) fun _ => dke_bind (dke_whenE _ (dke_throw _)) fun _ =>
        dke_bind (dke_returnOk _) fun _ => ?_
      dsimp only
      split
      · exact dke_returnOk _
      · refine dke_bind (dke_liftE (iox_getCap _)) fun nc => ?_
        split
        · exact ioxe_rab _
        · exact dke_returnOk _
  · exact dke_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_rab _)

theorem iox_zipWithMx {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, IOX (g a b)) :
    ∀ l1 l2, IOX (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => dk_bind (h a b) (fun _ => iox_zipWithMx h l1 l2)
  | [], _ => dk_pure' _
  | _ :: _, [] => dk_pure' _
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible refine iox_zipWithMx (fun _ _ => ?_) _ _)

set_option maxRecDepth 20000

theorem iox_setObject (p : ObjRef) (o : KernelObject) : IOX (setObject (Z := Unit) p o) := by
  unfold setObject; dk_auto0
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setObject _ _)

/-- A bind on a returned value (so that the continuation sees the value). -/
theorem ioxe_returnOk_bind {ε α β : Type} {v : α} {g : α → NonDetE (State Unit) ε β} (h : IOXE (g v)) :
    IOXE (NonDetE.returnOk v >>= g) := by
  show FK ioxV (ExceptT.run (NonDetE.returnOk v >>= g))
  rw [ExceptT.run_bind]
  intro σ x ⟨y, hy, hx⟩
  obtain rfl := Set.mem_singleton_iff.1 hy
  exact h σ x hx
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible refine ioxe_returnOk_bind ?_)

end

end Fl4Proofs.P3.SInvIox
