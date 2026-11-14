/-
P3 (DESIGN.md §9), interrupts and IO ports: **frames**. The spec's
`cap_insert` keeps the interrupt state, the IRQ node and the arch state
(`capInsert_keeps`); FL4's `cdt::insert` writes only slot words, so keeps
the words outside the objects and the kernel-state base (`insert_frame`).
-/
import Fl4Proofs.P3.CtlIns
import Fl4Proofs.P3.StateFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
open Fl4Spec

/-- The interrupt state, the IRQ node and the arch state are kept. -/
def IKeep (σ σ' : State Unit) : Prop :=
  σ'.interruptStates = σ.interruptStates ∧ σ'.interruptIrqNode = σ.interruptIrqNode ∧ σ'.archState = σ.archState

theorem IKeep.refl (σ : State Unit) : IKeep σ σ := ⟨rfl, rfl, rfl⟩
theorem IKeep.trans {σ1 σ2 σ3 : State Unit} (h1 : IKeep σ1 σ2) (h2 : IKeep σ2 σ3) : IKeep σ1 σ3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

/-- Every outcome keeps `IKeep`. -/
def NK {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → IKeep σ x.2

theorem nk_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : NK m)
    (hf : ∀ a, NK (f a)) : NK (m >>= f) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hf y.1 y.2 x hx)

theorem nk_bind' {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : NK m)
    (hf : ∀ a, NK (f a)) : NK (NonDet.bind m f) := nk_bind hm hf

theorem nk_pure {α : Type} (a : α) : NK (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact IKeep.refl σ

theorem nk_pure' {α : Type} (a : α) : NK (NonDet.pure a : NonDet (State Unit) α) := nk_pure a

theorem nk_gets {α : Type} (f : State Unit → α) : NK (NonDet.gets f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact IKeep.refl σ

theorem nk_get : NK (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact IKeep.refl σ

theorem nk_modify {f : State Unit → State Unit} (hf : ∀ σ, IKeep σ (f σ)) : NK (NonDet.modify f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hf σ

theorem nk_assert (P : Prop) : NK (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact IKeep.refl σ

theorem nk_fail {α : Type} : NK (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem nk_assertOpt {α : Type} (o : Option α) : NK (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact nk_fail
  · exact nk_pure' _

theorem nk_getsThe {α : Type} (f : State Unit → Option α) : NK (NonDet.getsThe f) := by
  intro σ x hx
  exact nk_assertOpt (f σ) σ x hx

theorem nk_selectF {α : Type} (S : Set α × Prop) : NK (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact IKeep.refl σ

theorem nk_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : NK m1) (h2 : NK m2) :
    NK (if P then m1 else m2) := by
  split <;> assumption

theorem nk_getObject (p : ObjRef) : NK (getObject (Z := Unit) p) := nk_getsThe _

theorem nk_setObject (p : ObjRef) (o : KernelObject) : NK (setObject (Z := Unit) p o) := by
  unfold setObject
  refine nk_bind (nk_getObject p) (fun _ => nk_bind (nk_assert _) (fun _ => ?_))
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact IKeep.refl σ

theorem nk_get_put {f : State Unit → State Unit} (hf : ∀ σ, IKeep σ (f σ)) :
    NK (NonDet.get >>= fun s => NonDet.put (f s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hf σ

macro "nk_step" : tactic => `(tactic| first
  | exact nk_pure _ | exact nk_pure' _ | exact nk_fail | exact nk_gets _ | exact nk_get
  | exact nk_assert _ | exact nk_assertOpt _ | exact nk_getObject _ | exact nk_setObject _ _
  | exact nk_get_put (fun σ => IKeep.refl σ)
  | exact nk_modify (fun σ => IKeep.refl σ)
  | (refine nk_bind ?_ (fun _ => ?_))
  | (apply nk_ite)
  | split)

theorem nk_getCap (sl : CslotPtr) : NK (getCap (Z := Unit) sl) := by
  obtain ⟨o, c⟩ := sl
  unfold getCap
  refine nk_bind (nk_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> repeat nk_step

theorem nk_setCap (cap : Cap) (sl : CslotPtr) : NK (setCap (Z := Unit) cap sl) := by
  obtain ⟨o, c⟩ := sl
  unfold setCap
  refine nk_bind (nk_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> repeat nk_step

theorem nk_doExtendedOp (eop : DetExtMonad Unit) : NK (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine nk_bind nk_get (fun _ => nk_bind (nk_selectF _) (fun _ => ?_))
  split
  exact nk_modify (fun σ => IKeep.refl σ)

/-- **The spec's `cap_insert` keeps the interrupt and arch state.** -/
theorem capInsert_keeps (c : Cap) (src dest : CslotPtr) : NK (capInsert (Z := Unit) c src dest) := by
  unfold capInsert setUntypedCapAsFull updateCdt setCdt setOriginal
  repeat (first | exact nk_getCap _ | exact nk_setCap _ _ | exact nk_doExtendedOp _ | nk_step)

end

/-! ## FL4: slot writes keep the words outside the objects -/

section
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- `s'` agrees with `s` outside the objects, with the same kernel-state
base. -/
def SlotFrame (th : TypedHeap) (s s' : S) : Prop :=
  L.ksb s' = L.ksb s ∧ ∀ b, OutsideObjects th b → L.mem s' b = L.mem s b

theorem SlotFrame.refl (s : S) : SlotFrame (L := L) th s s := ⟨rfl, fun _ _ => rfl⟩

theorem SlotFrame.wr' (hP : Placed th) {s s1 : S} (h : SlotFrame (L := L) th s s1) {a k : U64} (ha : IsSlot th a)
    (hk : Off k) (v : U64) : SlotFrame (L := L) th s (L.wr s1 (wordOf a k) v) := by
  refine ⟨by rw [L.ksb_wr]; exact h.1, fun b hb => ?_⟩
  rw [L.mem_wr _ _ _ _ (slot_word_aligned hP ha hk) hb.1, if_neg, h.2 b hb]
  intro e
  obtain ⟨p, kd, hkd, h1, h2, -⟩ := slot_in_object hP ha
  have := hb.2 p kd hkd
  have hv := slot_word_val hP ha hk
  have := hk.lt
  rw [e] at hv
  omega

theorem SlotFrame.out {s s' : S} (h : SlotFrame (L := L) th s s') {b : U64} (hb : OutsideObjects th b) :
    L.mem s' b = L.mem s b := h.2 b hb

attribute [local step] set_cap_spec set_untyped_spec

/-- **`cdt::insert` writes only slot words.** -/
theorem insert_frame (hP : Placed th) (s : S) (c : capability.Cap) (src dest : U64)
    (hs : IsSlot th src) (hd : IsSlot th dest)
    (srcC : capability.Cap) (hsrcC : capAt (L.mem s) src = ok srcC)
    (hnx : nextOf (L.mem s) src = 0#u64 ∨ IsSlot th (nextOf (L.mem s) src)) :
    cdt.insert st s c src dest ⦃ s' => SlotFrame (L := L) th s s' ⦄ := by
  unfold cdt.insert
  rw [slot_cap_eq, hsrcC]
  simp only [bind_ok, is_cap_revocable_eq]
  step*
  all_goals
    have e2 : ∀ s1 : S, L.wr (L.wr s1 dest ⟨(encodeF c).1⟩) (core.num.U64.wrapping_add dest 8#u64) ⟨(encodeF c).2⟩ =
        wrCap (L := L) s1 dest c := fun _ => rfl
    subst_vars
    rw [e2]
  · cases hf : fullF srcC c <;> simp only [hf, wrCap_eq] <;>
      repeat (first
        | exact SlotFrame.refl s
        | refine SlotFrame.wr' hP ?_ (by assumption) (by first | exact off0 | exact off8 | exact off16 | exact off24) _)
  · have hz : nextOf (L.mem s) src ≠ 0#u64 := by
      intro h; simp_all only [decide_true, not_true_eq_false]
    have hn := hnx.resolve_left hz
    cases hf : fullF srcC c <;> simp only [hf, wrCap_eq] <;>
      repeat (first
        | exact SlotFrame.refl s
        | refine SlotFrame.wr' hP ?_ (by assumption) (by first | exact off0 | exact off8 | exact off16 | exact off24) _)

end

end

end Fl4Proofs.P3
