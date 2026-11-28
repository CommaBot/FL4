/-
P3 (line mmuAD, gen 42b16, goals 2-3): **every EPT-related arm of `finalise_cap` at `VmEptState`** — FL4's
`objects::finalise_cap … c fin false` (objects.rs l. 263-273, `finalise_cap_object`) against the extended spec's
`finaliseCapV` (Fl4Spec/Ext/VirtFinalise), for
* an `Ept p l m asid va` cap that is unmapped or not final (`m = false ∨ fin = false`): FL4 does nothing (the first
  match `ok (s, a)`; `finalise_cap_object`'s `Ept` arm runs `ept::finalise` only when `fin`, and `ept::finalise`
  only when the cap is mapped), and so does the spec (the `eptCap` hook's `else finaliseCap cap final`, an unmapped
  `eptCap _ _ none` falls through to `finaliseCap`; `archFinaliseCap`'s last arm `_, _ => return (nullCap, nullCap)`):
  **`fl4_finEptNop`**, **`finCapV_eptNop`**, **`VmEptState.finEptNop`**;
* an unmapped frame cap `Frame p sz r d false e asid va` (any `e`, any `fin`): FL4 unmaps nothing and, for a final
  device frame, runs `retire_dma_frame` (arch state only, `AR` kept by `MRKeepD` [P]); the spec's cap is a
  `.vmNoMap` page cap with no mapping, `archFinaliseCap`'s last arm: **`finCapV_frameOff`**,
  **`VmEptState.finFrameOff`**;
* **the EPT arm** (`EptFinShape c`: an `Ept` cap, an EPT-mapped frame cap, an unmapped frame cap; any finality):
  **`VmEptState.finEptArm`**, from `finEptNop`, P3/EptFinUnmap's `VmEptState.finEptTbl` (final mapped `l ≠ 0`) and
  `VmEptState.finEptFrameG` (EPT-mapped frame, device or not), P3/EptFinRoot's `VmEptState.finEptRoot` (final
  mapped root, `finaliseCap = finaliseCapV` there: `finaliseCapV_eptRoot`), and `finFrameOff`. Its post: `(Null,
  Null)`, the pair `(nullCap, nullCap)` with some `σ'` an outcome of `finaliseCapV (absCap c) fin σ`, `VmEptState` at
  FL4's state and `σ'`, the slots kept. **`finaliseCapVF_eptShape`**: on these caps the report-extended
  `finaliseCapVF` (Ext/VirtKernelF, used by `recDelVF`) is `finaliseCapV`.

Not here: the deletion around it (the finalise loop and slot clearing at `VmEptState`), after the post-#115
retype/deletion dedup.

Premises: `ArchRefines arI AR` [P] (as P3/EptUnmapRel); `MRKeepD arI AR` [P] (P3/MachKeepD, the arch operations of
the finalisation keep `AR`; already a premise of the U44 / `_sysLzz` tops), with `P0.StoreTotal st` /
`P0.ArchTotal arI`, asked for only at a final device frame (`hD`). No new named premise. New file; root import after
`P3.EptFinUnmap`. No existing statement changed.
-/
import Fl4Proofs.P3.EptFinUnmap
import Fl4Proofs.P3.EptDelRoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Spec side -/

section Spec
open Fl4Spec

/-- The spec's finalisation of an unmapped or non-final `Ept` cap does nothing. -/
theorem finCapV_eptNop (σ : State Unit) {p l asid va : U64} {m fin : Bool} (h : m = false ∨ fin = false) :
    finaliseCapV (Z := Unit) (absCap (.Ept p l m asid va)) fin σ = ({((.nullCap, .nullCap), σ)}, False) := by
  rcases h with rfl | rfl
  · cases fin <;> rfl
  · cases m <;> rfl

/-- The spec's finalisation of an unmapped frame cap does nothing. -/
theorem finCapV_frameOff (σ : State Unit) {p r asid va : U64} {sz : capability.FrameSize} {d e : Bool}
    (fin : Bool) :
    finaliseCapV (Z := Unit) (absCap (.Frame p sz r d false e asid va)) fin σ =
      ({((.nullCap, .nullCap), σ)}, False) := by
  cases fin <;> rfl

/-- A mapped EPT root cap's `finaliseCapV` is the ported `finaliseCap`. -/
theorem finaliseCapV_eptRoot (p asid va : U64) (b : Bool) :
    finaliseCapV (Z := Unit) (absCap (.Ept p 0#u64 true asid va)) b =
      finaliseCap (absCap (.Ept p 0#u64 true asid va)) b := by
  have h0 : (0#u64 : U64).val = 0 := rfl
  show (if b = true ∧ (0#u64 : U64).val ≠ 0 then _ else _) = _
  rw [if_neg (by rw [h0]; simp)]

end Spec

/-- **The EPT-related caps of `finalise_cap`**: an `Ept` cap, an EPT-mapped frame cap, an unmapped frame cap. -/
inductive EptFinShape : capability.Cap → Prop
  | ept (p l : U64) (m : Bool) (asid va : U64) : EptFinShape (.Ept p l m asid va)
  | frameEpt (p : U64) (sz : capability.FrameSize) (r : U64) (d : Bool) (asid va : U64) :
      EptFinShape (.Frame p sz r d true true asid va)
  | frameOff (p : U64) (sz : capability.FrameSize) (r : U64) (d e : Bool) (asid va : U64) :
      EptFinShape (.Frame p sz r d false e asid va)

/-- On the EPT-related caps the report-extended `finaliseCapVF` is `finaliseCapV`. -/
theorem finaliseCapVF_eptShape {c : capability.Cap} (hE : EptFinShape c) (b : Bool) :
    Fl4Spec.finaliseCapVF (Z := Unit) (absCap c) b = Fl4Spec.finaliseCapV (absCap c) b := by
  cases hE with
  | ept p l m asid va => cases m <;> rfl
  | frameEpt => rfl
  | frameOff => rfl

/-! ## FL4 side -/

section
variable {S : Type} {st : machine.Store S} {A : Type} {arI : machine.Arch A}

/-- FL4's finalisation of an unmapped or non-final `Ept` cap does nothing. -/
theorem fl4_finEptNop (s : S) (a : A) {p l asid va : U64} {m fin : Bool} (h : m = false ∨ fin = false) :
    objects.finalise_cap st arI s a (.Ept p l m asid va) fin false = ok ((.Null, .Null), s, a) := by
  rcases h with rfl | rfl
  · cases fin <;> simp [objects.finalise_cap, objects.finalise_cap_object, ept.finalise]
  · simp [objects.finalise_cap, objects.finalise_cap_object]

end

/-! ## `VmEptState` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64} {XL : U64 → Nat}

open Fl4Proofs.P3.Vs

/-- **The finalisation of an unmapped or non-final `Ept` cap at `VmEptState`** (module docstring). -/
theorem VmEptState.finEptNop (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ)
    {p l asid va : U64} {m fin : Bool} (h : m = false ∨ fin = false) :
    objects.finalise_cap st arI s a (.Ept p l m asid va) fin false ⦃ r =>
      r.1 = (.Null, .Null) ∧ ∃ σ' : Fl4Spec.State Unit,
        Fl4Spec.finaliseCapV (Z := Unit) (absCap (.Ept p l m asid va)) fin σ =
          ({((.nullCap, .nullCap), σ')}, False) ∧
        VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D r.2.1 r.2.2 σ' ∧
        SlotsSame Z.th (L.mem s) (L.mem r.2.1) ⦄ := by
  rw [fl4_finEptNop s a h]
  exact (WP.spec_ok _).2 ⟨rfl, σ, finCapV_eptNop σ h, J, SlotsSame.refl _ _⟩

set_option maxHeartbeats 4000000 in
/-- **The finalisation of an unmapped frame cap at `VmEptState`** (module docstring): a final device frame's
`retire_dma_frame` keeps `AR` by `MRKeepD` [P] (`hD`). -/
theorem VmEptState.finFrameOff (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ)
    {p r asid va : U64} {sz : capability.FrameSize} {d e : Bool} (fin : Bool)
    (hD : d = true → fin = true → P0.StoreTotal st ∧ P0.ArchTotal arI ∧ MRKeepD arI AR) :
    objects.finalise_cap st arI s a (.Frame p sz r d false e asid va) fin false ⦃ res =>
      res.1 = (.Null, .Null) ∧ ∃ σ' : Fl4Spec.State Unit,
        Fl4Spec.finaliseCapV (Z := Unit) (absCap (.Frame p sz r d false e asid va)) fin σ =
          ({((.nullCap, .nullCap), σ')}, False) ∧
        VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D res.2.1 res.2.2 σ' ∧
        SlotsSame Z.th (L.mem s) (L.mem res.2.1) ⦄ := by
  have hAR : AR a σ.archState.x64CurrentCr3 := J.1.1.xtop.fin.1.1.2.2.2.2.2.2
  unfold objects.finalise_cap objects.finalise_cap_object
  simp only [bind_ok, ↓reduceIte, Bool.false_eq_true]
  cases fin with
  | false =>
    simp only [↓reduceIte, Bool.false_eq_true, eq_self_iff_true, if_true]
    exact (WP.spec_ok _).2 ⟨rfl, σ, finCapV_frameOff σ false, J, SlotsSame.refl _ _⟩
  | true =>
    cases d with
    | false =>
      simp only [↓reduceIte, Bool.false_eq_true, eq_self_iff_true, if_true]
      exact (WP.spec_ok _).2 ⟨rfl, σ, finCapV_frameOff σ true, J, SlotsSame.refl _ _⟩
    | true =>
      obtain ⟨hS, hT, hK⟩ := hD rfl rfl
      simp only [↓reduceIte, eq_self_iff_true, if_true]
      exact WP.spec_bind (MKD.objects_retire_dma_frame hS hT hK hAR)
        (fun a2 h => (WP.spec_ok _).2 ⟨rfl, σ, finCapV_frameOff σ true, J.archV h, SlotsSame.refl _ _⟩)

/-- An equation post as a membership post. -/
private theorem finPost_mem {F : Set ((Fl4Spec.Cap × Fl4Spec.Cap) × Fl4Spec.State Unit) × Prop}
    {Q : Fl4Spec.State Unit → Prop} {x : capability.Cap × capability.Cap}
    (h : x = (.Null, .Null) ∧ ∃ σ' : Fl4Spec.State Unit, F = ({((Fl4Spec.Cap.nullCap, Fl4Spec.Cap.nullCap), σ')}, False) ∧ Q σ') :
    x = (.Null, .Null) ∧ ∃ σ' : Fl4Spec.State Unit, ((Fl4Spec.Cap.nullCap, Fl4Spec.Cap.nullCap), σ') ∈ F.1 ∧ Q σ' := by
  obtain ⟨h1, σ', hF, hQ⟩ := h
  exact ⟨h1, σ', by rw [hF]; exact Set.mem_singleton _, hQ⟩

open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1 in
set_option maxHeartbeats 4000000 in
/-- **The EPT arm of `finalise_cap` at `VmEptState`** (module docstring): every EPT-related cap of a slot, any
finality. From `ArchRefines` [P]; `MRKeepD` [P] (with `P0.StoreTotal` / `P0.ArchTotal`) only at a final device
frame (`hD`). -/
theorem VmEptState.finEptArm [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR)
    (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr} (hAs : AbsSlot Z.th sl)
    {c : capability.Cap} (hE : EptFinShape c) (hc : capAt (L.mem s) (cslotAddr sl) = ok c) (fin : Bool)
    (hD : ∀ p sz r m e asid va, c = .Frame p sz r true m e asid va → fin = true →
      P0.StoreTotal st ∧ P0.ArchTotal arI ∧ MRKeepD arI AR) :
    objects.finalise_cap st arI s a c fin false ⦃ res =>
      res.1 = (.Null, .Null) ∧ ∃ σ' : Fl4Spec.State Unit,
        ((.nullCap, .nullCap), σ') ∈ (Fl4Spec.finaliseCapV (Z := Unit) (absCap c) fin σ).1 ∧
        VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D res.2.1 res.2.2 σ' ∧
        SlotsSame Z.th (L.mem s) (L.mem res.2.1) ⦄ := by
  cases hE with
  | ept p l m asid va =>
    cases m with
    | false => exact WP.spec_mono (J.finEptNop (Or.inl rfl)) (fun _ h => finPost_mem h)
    | true =>
      cases fin with
      | false => exact WP.spec_mono (J.finEptNop (Or.inr rfl)) (fun _ h => finPost_mem h)
      | true =>
        by_cases hl : l = 0#u64
        · subst hl
          have B := J.1.1
          have hDS : DState (L := L) Z.th s σ Z.G := ⟨B.xtop.rel.2.1, B.del, B.xtop.rel.2.2.1⟩
          rw [finaliseCapV_eptRoot]
          refine WP.spec_mono (J.finEptRoot hA hDS hAs hc) ?_
          rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨h1, h2, h3, σ1, hm, J1, hSS, -⟩
          simp only at h1 h2 h3 hm J1 hSS ⊢
          have hn := ept_finRoot_null hm
          simp only [Prod.mk.injEq] at hn
          have hcl : cl = .Null := (absCap_eq_null h3).1 hn.2
          have hrm : rem = .Null := h1
          subst hcl hrm
          exact ⟨rfl, σ1, hm, J1, hSS⟩
        · exact WP.spec_mono (J.finEptTbl hA hAs hc hl) (fun _ h => finPost_mem h)
  | frameEpt p sz r d asid va =>
    exact WP.spec_mono (J.finEptFrameG hA hAs hc fin
      (fun hd hf => hD p sz r true true asid va (by rw [hd]) hf)) (fun _ h => finPost_mem h)
  | frameOff p sz r d e asid va =>
    exact WP.spec_mono (J.finFrameOff fin (fun hd hf => hD p sz r false e asid va (by rw [hd]) hf))
      (fun _ h => finPost_mem h)

end

end

end Fl4Proofs.P3
