/-
P3 (DESIGN.md §9), CSpace: the spec's `cap_insert` (CSpace_A), evaluated on
a state where both slots are CNode slots, for the nondeterministic spec
(`Z = Unit`, where `do_extended_op` does nothing).
-/
import Fl4Proofs.P3.SetCap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3

noncomputable section

section
open Fl4Spec Classical

/-- Bind after a computation with one outcome. -/
theorem nd_bind_one {σ α β : Type} {m : NonDet σ α} {s s' : σ} {a : α} (h : m s = ({(a, s')}, False))
    (f : α → NonDet σ β) : (m >>= f) s = f a s' := by
  simp only [nd_bind_apply, h, Set.mem_singleton_iff, exists_eq_left, false_or]
  ext <;> simp

theorem nd_single_ext {σ α : Type} {m : NonDet σ α} {s : σ} {a : α} (h1 : (m s).1 = {(a, s)}) (h2 : ¬ (m s).2) :
    m s = ({(a, s)}, False) := by
  ext1
  · exact h1
  · exact propext ⟨h2, False.elim⟩

theorem doExtendedOp_unit (eop : DetExtMonad Unit) (σ : State Unit) :
    doExtendedOp (Z := Unit) eop σ = ({((), σ)}, False) := by
  unfold doExtendedOp
  show (NonDet.get >>= _) σ = _
  rw [nd_bind_single (show (NonDet.get : NonDet (State Unit) (State Unit)) σ = ({(σ, σ)}, False) from rfl)]
  have hsel : NonDet.selectF (σ := State Unit) (NonDet.mkEf (StateExt.wrapExtOp eop σ)) σ =
      ({(((), σ), σ)}, False) := by
    apply nd_single_ext
    · ext x; simp [NonDet.selectF, NonDet.mkEf, StateExt.wrapExtOp, NonDet.pure]
      constructor
      · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
      · rintro rfl; simp
    · simp [NonDet.selectF, NonDet.mkEf, StateExt.wrapExtOp, NonDet.pure]
  show (NonDet.selectF _ >>= _) σ = _
  rw [nd_bind_single hsel]
  rfl

theorem updateCdt_eq {Z : Type} (f : Cdt → Cdt) (σ : State Z) :
    updateCdt (Z := Z) f σ = ({((), { σ with cdt := f σ.cdt })}, False) := by
  unfold updateCdt setCdt
  show (NonDet.gets _ >>= _) σ = _
  rw [nd_bind_single (show (NonDet.gets (fun s : State Z => s.cdt)) σ = ({(σ.cdt, σ)}, False) from rfl)]
  show (NonDet.get >>= _) σ = _
  rw [nd_bind_single (show (NonDet.get : NonDet (State Z) (State Z)) σ = ({(σ, σ)}, False) from rfl)]
  rfl

theorem setOriginal_eq {Z : Type} (sl : CslotPtr) (v : Bool) (σ : State Z) :
    setOriginal (Z := Z) sl v σ =
      ({((), { σ with isOriginalCap := Function.update σ.isOriginalCap sl v })}, False) := by
  unfold setOriginal
  show (NonDet.gets _ >>= _) σ = _
  rw [nd_bind_single (show (NonDet.gets (fun s : State Z => s.isOriginalCap)) σ = ({(σ.isOriginalCap, σ)}, False) from rfl)]
  rfl

theorem gets_eq {Z α : Type} (f : State Z → α) (σ : State Z) :
    NonDet.gets f σ = ({(f σ, σ)}, False) := rfl

/-- The state after `cap_insert`, from the state `σ2` after its two `set_cap`s. -/
def capInsertState (σ σ2 : State Unit) (a srcA : Cap) (src dest : CslotPtr) : State Unit :=
  { σ2 with
    cdt := Function.update σ.cdt dest
      (if decide (shouldBeParentOf srcA (σ.isOriginalCap src) a (decide (isCapRevocable a srcA))) = true
       then some src else σ.cdt src),
    isOriginalCap := Function.update σ.isOriginalCap dest (decide (isCapRevocable a srcA)) }

theorem capInsert_eq {σ σ1 σ2 : State Unit} {a srcA : Cap} {src dest : CslotPtr}
    (hsrc : getCap (Z := Unit) src σ = ({(srcA, σ)}, False))
    (hdst : getCap (Z := Unit) dest σ = ({(.nullCap, σ)}, False))
    (h1 : setUntypedCapAsFull (Z := Unit) srcA a src σ = ({((), σ1)}, False))
    (h2 : setCap (Z := Unit) a dest σ1 = ({((), σ2)}, False))
    (hio : σ2.isOriginalCap = σ.isOriginalCap) (hcdt : σ2.cdt = σ.cdt) :
    capInsert (Z := Unit) a src dest σ = ({((), capInsertState σ σ2 a srcA src dest)}, False) := by
  unfold capInsert
  show (getCap src >>= _) σ = _
  rw [nd_bind_single hsrc]
  show ((pure _ : NonDet (State Unit) Bool) >>= _) σ = _
  rw [nd_pure_bind]
  show (getCap dest >>= _) σ = _
  rw [nd_bind_single hdst]
  show (NonDet.assert _ >>= _) σ = _
  rw [nd_bind_single (show NonDet.assert (σ := State Unit) (Cap.nullCap = Cap.nullCap) σ = ({((), σ)}, False) by
    simp [NonDet.assert])]
  show (setUntypedCapAsFull _ _ _ >>= _) σ = _
  rw [nd_bind_one h1]
  show (setCap _ _ >>= _) σ1 = _
  rw [nd_bind_one h2]
  show (NonDet.gets _ >>= _) σ2 = _
  rw [nd_bind_single (gets_eq _ σ2)]
  show ((pure _ : NonDet (State Unit) Bool) >>= _) σ2 = _
  rw [nd_pure_bind]
  show (NonDet.gets _ >>= _) σ2 = _
  rw [nd_bind_single (gets_eq _ σ2)]
  show (NonDet.gets _ >>= _) σ2 = _
  rw [nd_bind_single (gets_eq _ σ2)]
  show (updateCdt _ >>= _) σ2 = _
  rw [nd_bind_one (updateCdt_eq _ σ2)]
  show (doExtendedOp _ >>= _) _ = _
  rw [nd_bind_single (doExtendedOp_unit _ _)]
  rw [setOriginal_eq]
  simp only [hio, hcdt, capInsertState]

theorem setUntyped_full {Z : Type} {srcA newA : Cap} {src : CslotPtr} {σ : State Z}
    (h : isUntypedCap srcA = true ∧ isUntypedCap newA = true ∧ objRefOf srcA = objRefOf newA ∧
      capBitsUntyped srcA = capBitsUntyped newA) :
    setUntypedCapAsFull (Z := Z) srcA newA src σ = setCap (maxFreeIndexUpdate srcA) src σ := by
  unfold setUntypedCapAsFull; rw [if_pos h]

theorem setUntyped_skip {Z : Type} {srcA newA : Cap} {src : CslotPtr} {σ : State Z}
    (h : ¬ (isUntypedCap srcA = true ∧ isUntypedCap newA = true ∧ objRefOf srcA = objRefOf newA ∧
      capBitsUntyped srcA = capBitsUntyped newA)) :
    setUntypedCapAsFull (Z := Z) srcA newA src σ = ({((), σ)}, False) := by
  unfold setUntypedCapAsFull; rw [if_neg h]; rfl

theorem setCdt_eq {Z : Type} (t : Cdt) (σ : State Z) :
    setCdt (Z := Z) t σ = ({((), { σ with cdt := t })}, False) := by
  unfold setCdt
  show (NonDet.get >>= _) σ = _
  rw [nd_bind_single (show (NonDet.get : NonDet (State Z) (State Z)) σ = ({(σ, σ)}, False) from rfl)]
  rfl

/-- The state after `cap_move`, from the state `σ2` after its two `set_cap`s. -/
def capMoveState (σ σ2 : State Unit) (src dest : CslotPtr) : State Unit :=
  { σ2 with
    cdt := fun r =>
      if Function.update (Function.update σ.cdt dest (σ.cdt src)) src none r = some src then some dest
      else Function.update (Function.update σ.cdt dest (σ.cdt src)) src none r,
    isOriginalCap := Function.update (Function.update σ.isOriginalCap dest (σ.isOriginalCap src)) src false }

theorem capMove_eq {σ σ1 σ2 : State Unit} {a : Cap} {src dest : CslotPtr}
    (h1 : setCap (Z := Unit) a dest σ = ({((), σ1)}, False))
    (h2 : setCap (Z := Unit) .nullCap src σ1 = ({((), σ2)}, False))
    (hio : σ2.isOriginalCap = σ.isOriginalCap) (hcdt : σ2.cdt = σ.cdt) :
    capMove (Z := Unit) a src dest σ = ({((), capMoveState σ σ2 src dest)}, False) := by
  unfold capMove
  show (setCap _ _ >>= _) σ = _
  rw [nd_bind_one h1]
  show (setCap _ _ >>= _) σ1 = _
  rw [nd_bind_one h2]
  show (NonDet.gets _ >>= _) σ2 = _
  rw [nd_bind_single (gets_eq _ σ2)]
  show (NonDet.gets _ >>= _) σ2 = _
  rw [nd_bind_single (gets_eq _ σ2)]
  show (NonDet.gets _ >>= _) σ2 = _
  rw [nd_bind_single (gets_eq _ σ2)]
  show ((pure _ : NonDet (State Unit) _) >>= _) σ2 = _
  rw [nd_pure_bind]
  show ((pure _ : NonDet (State Unit) _) >>= _) σ2 = _
  rw [nd_pure_bind]
  show (setCdt _ >>= _) σ2 = _
  rw [nd_bind_one (setCdt_eq _ σ2)]
  show (doExtendedOp _ >>= _) _ = _
  rw [nd_bind_single (doExtendedOp_unit _ _)]
  show (NonDet.gets _ >>= _) _ = _
  rw [nd_bind_single (gets_eq _ _)]
  show (setOriginal _ _ >>= _) _ = _
  rw [nd_bind_one (setOriginal_eq _ _ _), setOriginal_eq]
  simp only [hio, hcdt, capMoveState]

/-- The state after `empty_slot`'s CDT and original-flag updates (before its
`set_cap`). -/
def emptySlotCdtState (σ : State Unit) (slot : CslotPtr) : State Unit :=
  { σ with
    cdt := Function.update (fun p => if σ.cdt p = some slot then σ.cdt slot else σ.cdt p) slot none,
    isOriginalCap := Function.update σ.isOriginalCap slot false }

theorem emptySlot_eq {σ σ2 : State Unit} {slot : CslotPtr} {c : Cap}
    (hget : getCap (Z := Unit) slot σ = ({(c, σ)}, False)) (hcn : c ≠ .nullCap)
    (h2 : setCap (Z := Unit) .nullCap slot (emptySlotCdtState σ slot) = ({((), σ2)}, False)) :
    emptySlot (Z := Unit) slot .nullCap σ = ({((), σ2)}, False) := by
  unfold emptySlot
  show (getCap slot >>= _) σ = _
  rw [nd_bind_single hget]
  simp only [hcn, ↓reduceIte]
  show (NonDet.gets _ >>= _) σ = _
  rw [nd_bind_single (gets_eq _ σ)]
  show (NonDet.gets _ >>= _) σ = _
  rw [nd_bind_single (gets_eq _ σ)]
  show ((pure _ : NonDet (State Unit) _) >>= _) σ = _
  rw [nd_pure_bind]
  show (setCdt _ >>= _) σ = _
  rw [nd_bind_one (setCdt_eq _ σ)]
  show (doExtendedOp _ >>= _) _ = _
  rw [nd_bind_single (doExtendedOp_unit _ _)]
  show (setOriginal _ _ >>= _) _ = _
  rw [nd_bind_one (setOriginal_eq _ _ _)]
  show (setCap _ _ >>= _) (emptySlotCdtState σ slot) = _
  rw [nd_bind_one h2]
  rfl

end

end

end Fl4Proofs.P3
