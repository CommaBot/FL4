/-
P3 (DESIGN.md §9), CSpace: **the spec's `cap_insert` sets one original
bit** (`capInsert_orig`): every other slot's `is_original_cap` is kept (an
`NK`-style frame over the monad, `NO`).
-/
import Fl4Proofs.P3.IntFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
open Fl4Spec

/-- The original bits off the slot `d` are kept. -/
def OKeep (d : CslotPtr) (σ σ' : State Unit) : Prop := ∀ sl, sl ≠ d → σ'.isOriginalCap sl = σ.isOriginalCap sl

theorem OKeep.refl (d : CslotPtr) (σ : State Unit) : OKeep d σ σ := fun _ _ => rfl
theorem OKeep.trans {d : CslotPtr} {σ1 σ2 σ3 : State Unit} (h1 : OKeep d σ1 σ2) (h2 : OKeep d σ2 σ3) :
    OKeep d σ1 σ3 := fun sl h => (h2 sl h).trans (h1 sl h)

/-- Every outcome keeps `OKeep d`. -/
def NO {α : Type} (d : CslotPtr) (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → OKeep d σ x.2

variable {d : CslotPtr}

theorem no_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : NO d m)
    (hf : ∀ a, NO d (f a)) : NO d (m >>= f) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hf y.1 y.2 x hx)

theorem no_pure {α : Type} (a : α) : NO d (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact OKeep.refl d σ

theorem no_pure' {α : Type} (a : α) : NO d (NonDet.pure a : NonDet (State Unit) α) := no_pure a

theorem no_gets {α : Type} (f : State Unit → α) : NO d (NonDet.gets f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact OKeep.refl d σ

theorem no_get : NO d (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact OKeep.refl d σ

theorem no_modify {f : State Unit → State Unit} (hf : ∀ σ, OKeep d σ (f σ)) : NO d (NonDet.modify f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hf σ

theorem no_assert (P : Prop) : NO d (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact OKeep.refl d σ

theorem no_fail {α : Type} : NO d (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem no_assertOpt {α : Type} (o : Option α) : NO d (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact no_fail
  · exact no_pure' _

theorem no_getsThe {α : Type} (f : State Unit → Option α) : NO d (NonDet.getsThe f) := by
  intro σ x hx
  exact no_assertOpt (f σ) σ x hx

theorem no_selectF {α : Type} (S : Set α × Prop) : NO d (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact OKeep.refl d σ

theorem no_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : NO d m1) (h2 : NO d m2) :
    NO d (if P then m1 else m2) := by
  split <;> assumption

theorem no_getObject (p : ObjRef) : NO d (getObject (Z := Unit) p) := no_getsThe _

theorem no_get_put {f : State Unit → State Unit} (hf : ∀ σ, OKeep d σ (f σ)) :
    NO d (NonDet.get >>= fun s => NonDet.put (f s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hf σ

theorem no_setObject (p : ObjRef) (o : KernelObject) : NO d (setObject (Z := Unit) p o) := by
  unfold setObject
  refine no_bind (no_getObject p) (fun _ => no_bind (no_assert _) (fun _ => ?_))
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact OKeep.refl d σ

/-- `set_original` at `d` keeps the other slots' bits. -/
theorem no_setOriginal (v : Bool) : NO d (setOriginal (Z := Unit) d v) := by
  unfold setOriginal
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  intro sl h
  exact Function.update_of_ne h _ _

macro "no_step" : tactic => `(tactic| first
  | exact no_pure _ | exact no_pure' _ | exact no_fail | exact no_gets _ | exact no_get
  | exact no_assert _ | exact no_assertOpt _ | exact no_getObject _ | exact no_setObject _ _
  | exact no_get_put (fun σ => OKeep.refl _ σ)
  | exact no_modify (fun σ => OKeep.refl _ σ)
  | (refine no_bind ?_ (fun _ => ?_))
  | (apply no_ite)
  | split)

theorem no_getCap (sl : CslotPtr) : NO d (getCap (Z := Unit) sl) := by
  obtain ⟨o, c⟩ := sl
  unfold getCap
  refine no_bind (no_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> repeat no_step

theorem no_setCap (cap : Cap) (sl : CslotPtr) : NO d (setCap (Z := Unit) cap sl) := by
  obtain ⟨o, c⟩ := sl
  unfold setCap
  refine no_bind (no_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> repeat no_step

theorem no_doExtendedOp (eop : DetExtMonad Unit) : NO d (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine no_bind no_get (fun _ => no_bind (no_selectF _) (fun _ => ?_))
  split
  exact no_modify (fun σ => OKeep.refl _ σ)

/-- **The spec's `cap_insert` keeps every original bit but the
destination's.** -/
theorem capInsert_orig (c : Cap) (src dest : CslotPtr) : NO dest (capInsert (Z := Unit) c src dest) := by
  unfold capInsert setUntypedCapAsFull updateCdt setCdt
  repeat (first | exact no_setOriginal _ | exact no_getCap _ | exact no_setCap _ _ | exact no_doExtendedOp _ |
    no_step)

end

end

end Fl4Proofs.P3
