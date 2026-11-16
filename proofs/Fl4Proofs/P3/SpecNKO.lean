/-
P3 (DESIGN.md §9): **where the spec's heap changes** (`NKO`, `nko_*`,
`capInsert_nko`: `cap_insert` changes the heap at the source's and the
destination's objects only) and **CNode-only heap changes** (`KeepC`,
`keepC_of`), moved from IpcGrant.lean so the CSpace decodes can use them.
-/
import Fl4Proofs.P3.SpecCnK
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc

noncomputable section

section CnK
open Fl4Spec

/-! ### Where the heap changes -/

/-- Every outcome keeps the heap outside `Ps`. -/
def NKO {α : Type} (Ps : Set ObjRef) (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, x ∈ (m σ).1 → ∀ p ∉ Ps, x.2.kheap p = σ.kheap p

section NKO
variable {Ps : Set ObjRef}

theorem nko_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : NKO Ps m)
    (hf : ∀ a, NKO Ps (f a)) : NKO Ps (m >>= f) := by
  intro σ x ⟨y, hy, hx⟩ p hp
  exact (hf y.1 y.2 x hx p hp).trans (hm σ y hy p hp)

theorem nko_pure {α : Type} (a : α) : NKO Ps (pure a : NonDet (State Unit) α) := by
  intro σ x hx p _; rw [Set.mem_singleton_iff.1 hx]

theorem nko_pure' {α : Type} (a : α) : NKO Ps (NonDet.pure a : NonDet (State Unit) α) := nko_pure a

theorem nko_gets {α : Type} (f : State Unit → α) : NKO Ps (NonDet.gets f) := by
  intro σ x hx p _; rw [Set.mem_singleton_iff.1 hx]

theorem nko_get : NKO Ps (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx p _; rw [Set.mem_singleton_iff.1 hx]

theorem nko_assert (P : Prop) : NKO Ps (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx p _; obtain ⟨-, rfl⟩ := hx; rfl

theorem nko_fail {α : Type} : NKO Ps (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem nko_assertOpt {α : Type} (o : Option α) : NKO Ps (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact nko_fail
  · exact nko_pure' _

theorem nko_getsThe {α : Type} (f : State Unit → Option α) : NKO Ps (NonDet.getsThe f) := by
  intro σ x hx
  exact nko_assertOpt (f σ) σ x hx

theorem nko_selectF {α : Type} (S : Set α × Prop) : NKO Ps (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx p _; obtain ⟨-, h⟩ := hx; rw [h]

theorem nko_getObject (p : ObjRef) : NKO Ps (getObject (Z := Unit) p) := nko_getsThe _

theorem nko_get_put {f : State Unit → State Unit} (hf : ∀ σ, (f σ).kheap = σ.kheap) :
    NKO Ps (NonDet.get >>= fun s => NonDet.put (f s)) := by
  intro σ x ⟨y, hy, hx⟩ p _
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact congrFun (hf σ) p

theorem nko_modify {f : State Unit → State Unit} (hf : ∀ σ, (f σ).kheap = σ.kheap) : NKO Ps (NonDet.modify f) := by
  intro σ x hx p _; rw [Set.mem_singleton_iff.1 hx]; exact congrFun (hf σ) p

theorem nko_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : NKO Ps m1)
    (h2 : NKO Ps m2) : NKO Ps (if P then m1 else m2) := by
  split <;> assumption

theorem nko_getCap (sl : CslotPtr) : NKO Ps (getCap (Z := Unit) sl) := by
  obtain ⟨o, c⟩ := sl
  unfold getCap
  refine nko_bind (nko_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;>
    repeat (first | exact nko_pure _ | exact nko_fail | exact nko_assert _ | exact nko_assertOpt _ |
      (refine nko_bind ?_ (fun _ => ?_)))

/-- `set_cap` changes the heap at the slot's object only. -/
theorem nko_setCap (cap : Cap) (sl : CslotPtr) (hs : sl.1 ∈ Ps) : NKO Ps (setCap (Z := Unit) cap sl) := by
  obtain ⟨o, c⟩ := sl
  unfold setCap
  intro σ x hx p hp
  dsimp only at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨k, hk, rfl⟩ : ∃ k, σ.kheap o = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap o with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  have hpo : p ≠ o := fun e => hp (e ▸ hs)
  have fin : ∀ o', x ∈ (setObject (Z := Unit) o o' σ).1 → x.2.kheap p = σ.kheap p :=
    fun o' hx' => by rw [setObject_out hx']; simp [Function.update_of_ne hpo]
  have pb : ∀ o', x ∈ ((pure o' >>= fun obj' => setObject (Z := Unit) o obj') σ).1 →
      x ∈ (setObject (Z := Unit) o o' σ).1 := by
    intro o' hx'; obtain ⟨z, hz, hx'⟩ := hx'; rw [Set.mem_singleton_iff.1 hz] at hx'; exact hx'
  have fb : ∀ (f : KernelObject → NonDet (State Unit) Unit), x ∈ ((NonDet.fail >>= f) σ).1 → False := by
    intro f hx'; obtain ⟨z, hz, -⟩ := hx'; exact hz
  cases k with
  | cnode r cs =>
    dsimp only at hx
    split at hx
    · exact fin _ (pb _ hx)
    · exact (fb _ hx).elim
  | tcb t =>
    dsimp only at hx
    repeat' split at hx
    all_goals first
      | exact (fb _ hx).elim
      | exact fin _ (pb _ hx)
  | _ => dsimp only at hx; exact (fb _ hx).elim

theorem nko_doExtendedOp (eop : DetExtMonad Unit) : NKO Ps (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine nko_bind nko_get (fun _ => nko_bind (nko_selectF _) (fun _ => ?_))
  split
  exact nko_modify (fun σ => rfl)

end NKO

/-- **`cap_insert` changes the heap at the source's and the destination's
objects only.** -/
theorem capInsert_nko (c : Cap) (src dest : CslotPtr) :
    NKO {src.1, dest.1} (capInsert (Z := Unit) c src dest) := by
  unfold capInsert setUntypedCapAsFull updateCdt setCdt setOriginal
  repeat (first | exact nko_getCap _ | exact nko_setCap _ _ (by simp) | exact nko_doExtendedOp _ |
    exact nko_pure _ | exact nko_pure' _ | exact nko_fail | exact nko_gets _ | exact nko_get |
    exact nko_assert _ | exact nko_get_put (fun σ => rfl) |
    exact nko_modify (fun σ => rfl) | (refine nko_bind ?_ (fun _ => ?_)) |
    (apply nko_ite) | split)

/-- **The spec's heap changed in CNodes only** (keeping their sizes). -/
def KeepC (σ σ' : State Unit) : Prop :=
  ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ r cs cs', σ.kheap p = some (.cnode r cs) ∧ σ'.kheap p = some (.cnode r cs')

theorem KeepC.refl (σ : State Unit) : KeepC σ σ := fun _ => Or.inl rfl

theorem KeepC.trans {σ1 σ2 σ3 : State Unit} (h1 : KeepC σ1 σ2) (h2 : KeepC σ2 σ3) : KeepC σ1 σ3 := by
  intro p
  rcases h1 p with e1 | ⟨r, cs, cs', a1, b1⟩ <;> rcases h2 p with e2 | ⟨r', ds, ds', a2, b2⟩
  · exact Or.inl (e2.trans e1)
  · rw [e1] at a2; exact Or.inr ⟨r', ds, ds', a2, b2⟩
  · rw [e2, b1]; exact Or.inr ⟨r, cs, cs', a1, rfl⟩
  · rw [b1] at a2; cases a2; exact Or.inr ⟨r, cs, ds', a1, b2⟩

/-- `CnK` with the heap changed at CNodes only. -/
theorem keepC_of {σ σ' : State Unit} {Ps : Set ObjRef} (hK : CnK σ σ') (hO : ∀ p ∉ Ps, σ'.kheap p = σ.kheap p)
    (hc : ∀ p ∈ Ps, ∃ r cs, σ.kheap p = some (.cnode r cs)) : KeepC σ σ' := by
  intro p
  by_cases hp : p ∈ Ps
  · obtain ⟨r, cs, hk⟩ := hc p hp
    rcases hK.2 p with e | ⟨r', cs1, cs', h1, h2⟩ | ⟨x, y, h1, -, -⟩
    · exact Or.inl e
    · rw [hk] at h1; cases h1; exact Or.inr ⟨r, cs, cs', hk, h2⟩
    · rw [hk] at h1; cases h1
  · exact Or.inl (hO p hp)

end CnK

end

end Fl4Proofs.P3.Ipc
