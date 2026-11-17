/-
P3 (DESIGN.md §9), CSpace: **the spec's `cap_insert` changes the CDT at the
destination only** (`capInsert_cdt`): every other slot's parent is kept (an
`NK`-style frame over the monad, `NCd`, as SlotOrig's `NO`).
-/
import Fl4Proofs.P3.SlotOrig
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
open Fl4Spec

/-- The CDT off the slots `d` is kept. -/
def CdtKeepOff (d : CslotPtr → Prop) (σ σ' : State Unit) : Prop :=
  ∀ sl, ¬ d sl → σ'.cdt sl = σ.cdt sl

theorem CdtKeepOff.refl (d : CslotPtr → Prop) (σ : State Unit) : CdtKeepOff d σ σ := fun _ _ => rfl
theorem CdtKeepOff.trans {d : CslotPtr → Prop} {σ1 σ2 σ3 : State Unit} (h1 : CdtKeepOff d σ1 σ2)
    (h2 : CdtKeepOff d σ2 σ3) : CdtKeepOff d σ1 σ3 := fun sl h => (h2 sl h).trans (h1 sl h)

/-- Every outcome keeps `CdtKeepOff d`. -/
def NCd {α : Type} (d : CslotPtr → Prop) (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, x ∈ (m σ).1 → CdtKeepOff d σ x.2

variable {d : CslotPtr → Prop}

theorem ncd_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : NCd d m)
    (hf : ∀ a, NCd d (f a)) : NCd d (m >>= f) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hf y.1 y.2 x hx)

theorem ncd_pure {α : Type} (a : α) : NCd d (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact CdtKeepOff.refl d σ

theorem ncd_pure' {α : Type} (a : α) : NCd d (NonDet.pure a : NonDet (State Unit) α) := ncd_pure a

theorem ncd_gets {α : Type} (f : State Unit → α) : NCd d (NonDet.gets f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact CdtKeepOff.refl d σ

theorem ncd_get : NCd d (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact CdtKeepOff.refl d σ

theorem ncd_modify {f : State Unit → State Unit} (hf : ∀ σ, CdtKeepOff d σ (f σ)) : NCd d (NonDet.modify f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hf σ

theorem ncd_assert (P : Prop) : NCd d (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact CdtKeepOff.refl d σ

theorem ncd_fail {α : Type} : NCd d (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem ncd_assertOpt {α : Type} (o : Option α) : NCd d (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact ncd_fail
  · exact ncd_pure' _

theorem ncd_getsThe {α : Type} (f : State Unit → Option α) : NCd d (NonDet.getsThe f) := by
  intro σ x hx
  exact ncd_assertOpt (f σ) σ x hx

theorem ncd_selectF {α : Type} (S : Set α × Prop) : NCd d (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact CdtKeepOff.refl d σ

theorem ncd_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : NCd d m1)
    (h2 : NCd d m2) : NCd d (if P then m1 else m2) := by
  split <;> assumption

theorem ncd_getObject (p : ObjRef) : NCd d (getObject (Z := Unit) p) := ncd_getsThe _

theorem ncd_get_put {f : State Unit → State Unit} (hf : ∀ σ, CdtKeepOff d σ (f σ)) :
    NCd d (NonDet.get >>= fun s => NonDet.put (f s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hf σ

theorem ncd_setObject (p : ObjRef) (o : KernelObject) : NCd d (setObject (Z := Unit) p o) := by
  unfold setObject
  refine ncd_bind (ncd_getObject p) (fun _ => ncd_bind (ncd_assert _) (fun _ => ?_))
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact CdtKeepOff.refl d σ

/-- Updating the CDT at a slot of `d` keeps the other slots' parents. -/
theorem ncd_updateCdt {sl0 : CslotPtr} (hd : d sl0) (v : Cdt → Option CslotPtr) :
    NCd d (updateCdt (Z := Unit) fun cdt => Function.update cdt sl0 (v cdt)) := by
  unfold updateCdt setCdt
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  obtain ⟨z, hz, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hz] at hx
  rw [Set.mem_singleton_iff.1 hx]
  intro sl h
  exact Function.update_of_ne (fun e => h (by subst e; exact hd)) _ _

macro "ncd_step" : tactic => `(tactic| first
  | exact ncd_pure _ | exact ncd_pure' _ | exact ncd_fail | exact ncd_gets _ | exact ncd_get
  | exact ncd_assert _ | exact ncd_assertOpt _ | exact ncd_getObject _ | exact ncd_setObject _ _
  | exact ncd_get_put (fun σ => CdtKeepOff.refl _ σ)
  | exact ncd_modify (fun σ => CdtKeepOff.refl _ σ)
  | (refine ncd_bind ?_ (fun _ => ?_))
  | (apply ncd_ite)
  | split)

theorem ncd_getCap (sl : CslotPtr) : NCd d (getCap (Z := Unit) sl) := by
  obtain ⟨o, c⟩ := sl
  unfold getCap
  refine ncd_bind (ncd_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> repeat ncd_step

theorem ncd_setCap (cap : Cap) (sl : CslotPtr) : NCd d (setCap (Z := Unit) cap sl) := by
  obtain ⟨o, c⟩ := sl
  unfold setCap
  refine ncd_bind (ncd_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> repeat ncd_step

theorem ncd_doExtendedOp (eop : DetExtMonad Unit) : NCd d (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine ncd_bind ncd_get (fun _ => ncd_bind (ncd_selectF _) (fun _ => ?_))
  split
  exact ncd_modify (fun σ => CdtKeepOff.refl _ σ)

theorem ncd_setOriginal (sl : CslotPtr) (v : Bool) : NCd d (setOriginal (Z := Unit) sl v) := by
  unfold setOriginal
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact CdtKeepOff.refl d σ

/-- **The spec's `cap_insert` keeps every slot's parent but the
destination's.** -/
theorem capInsert_cdt (c : Cap) (src dest : CslotPtr) : NCd (· = dest) (capInsert (Z := Unit) c src dest) := by
  unfold capInsert setUntypedCapAsFull
  repeat (first | exact ncd_updateCdt (by rfl) _ | exact ncd_setOriginal _ _ | exact ncd_getCap _ |
    exact ncd_setCap _ _ | exact ncd_doExtendedOp _ | ncd_step)

end

end

end Fl4Proofs.P3
