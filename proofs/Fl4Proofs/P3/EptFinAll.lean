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

Gen 42b19 (the Architect's goal 2, and goal 3's deletion step for `Ept` caps): **`VmEptState.delEpt`**, the delete
of a slot holding any `Ept` cap at `VmEptState` (FL4 `cdt::delete(slot, true)` against `capDeleteVF`): the mapped
root by P3/EptDelRoot's `delEptRoot`; an unmapped or non-final cap with both finalisations a no-op; a final mapped
non-root cap by P3/EptFinUnmap's `finEptTblU`; each then P3/EptDelRoot's `delEptStep`, whose emptying runs through
the one `EptCore.ofEmpty`. Its `hxl`: **`ept_nonfinal_twin`** (FL4's `is_final_capability` false: an MDB neighbour
holds an `Ept` cap to the same table, `soB_ept` / `shape_eq_ept`), **`ept_final_uq`** (the spec's finality, P3/DelFin's
`final_other`: no other slot cap names the table) with `finEptTblU`'s unreachability. **`VmEptState.vsPendFrame`**:
`VsPend` at a frame slot (no VSpace key), so after `finEptFrameG` (VmEptState after, slots kept) an EPT-mapped
frame's slot is pending. No new premise.

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


/-! ## The delete of an `Ept` slot cap (gen 42b19) -/

/-- A cap of an `Ept` cap's shape is an `Ept` cap to the same table. -/
theorem shape_eq_ept {u : capability.Cap} {p l a v : U64} {m : Bool} (h : shape u = shape (.Ept p l m a v)) :
    ∃ (lv' : U64) (m' : Bool) (a' v' : U64), u = .Ept p lv' m' a' v' := by
  cases u <;> simp only [shape, reduceCtorEq] at h
  rename_i q l' m' a' v'
  obtain ⟨rfl, -⟩ := capability.Cap.Ept.inj h
  exact ⟨_, _, _, _, rfl⟩

/-- `same_object_as` of an `Ept` cap, either side: an `Ept` cap to the same table (objects.rs l. 124, 137-152). -/
theorem soB_ept {u : capability.Cap} {p l a v : U64} {m : Bool}
    (h : soB u (.Ept p l m a v) = true ∨ soB (.Ept p l m a v) u = true) :
    ∃ (lv' : U64) (m' : Bool) (a' v' : U64), u = .Ept p lv' m' a' v' := by
  rcases h with h | h
  · have hs : isUt u = false ∧ srB u (.Ept p l m a v) = true := by
      cases u <;> simp_all [soB, isUt]
    exact shape_eq_ept (srB_ept_right hs.1 hs.2).symm
  · have hs : srB (.Ept p l m a v) u = true := by cases u <;> simpa [soB] using h
    exact shape_eq_ept (srB_ept_left hs)

/-- **A non-final `Ept` cap has another slot naming its table** (FL4's `is_final_capability`, cdt.rs l. 163-175: an
MDB neighbour holds a `same_object_as` cap, here an `Ept` cap to the same table, `soB_ept`; the neighbour is another
slot, `mdb_prev_slot` / `mdb_next_slot`). The non-final half of `EptCore.ofEmpty`'s `hxl`. -/
theorem ept_nonfinal_twin {th : TypedHeap} {m : U64 → U64} {G : MdbGhost} (hP : Placed th) (hM : MdbLinks th m G)
    {x p l a v : U64} {mm : Bool} (hxs : IsSlot th x) (hc : capAt m x = ok (.Ept p l mm a v))
    (hf : finF m x = false) :
    ∃ y, IsSlot th y ∧ y ≠ x ∧ ∃ (lv' : U64) (mm' : Bool) (a' v' : U64), capV m y = .Ept p lv' mm' a' v' := by
  have hcv := capV_of_capAt hc
  have hxm : x ∈ G.chains.flatten := (hM.members x).2 ⟨hxs, _, hc, by intro h; cases h⟩
  unfold finF at hf
  by_cases hp : prevOf m x ≠ 0#u64 ∧ soB (capV m (prevOf m x)) (capV m x) = true
  · obtain ⟨g1, g2⟩ := VirtVCappedDel.mdb_prev_slot hP hM hxm hxs hp.1
    rw [hcv] at hp
    exact ⟨_, g1, g2, soB_ept (Or.inl hp.2)⟩
  · rw [if_neg hp] at hf
    by_cases hn : nextOf m x = 0#u64
    · rw [if_pos hn] at hf; cases hf
    · rw [if_neg hn, hcv] at hf
      obtain ⟨g1, g2⟩ := VirtVCappedDel.mdb_next_slot hM hxm hn
      exact ⟨_, g1, g2, soB_ept (Or.inr (by simpa using hf))⟩

/-- **A final `Ept` cap is the only slot cap to its table** (the spec's finality, P3/DelFin's `final_other`: no
other slot's cap references the table). What P3/EptFinUnmap's `finEptTblU` asks for the table's unreachability. -/
theorem ept_final_uq {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} (hR : StateRel th (L.mem s) σ)
    (hP : Placed th) {xsl : Fl4Spec.CslotPtr} (hxs : AbsSlot th xsl) {p l a v : U64} {mm : Bool}
    (hcx : capAt (L.mem s) (cslotAddr xsl) = ok (.Ept p l mm a v))
    (hfin : Fl4Spec.isFinalCap' (absCap (.Ept p l mm a v)) σ) :
    ∀ y, IsSlot th y → y ≠ cslotAddr xsl → ∀ l' (mm' : Bool) a' v', capV (L.mem s) y ≠ .Ept p l' mm' a' v' := by
  intro y hy hne l' mm' a' v' h
  have hr : ∀ (l0 : U64) (m0 : Bool) (a0 v0 : U64), p.bv ∈ Fl4Spec.objRefs (absCap (.Ept p l0 m0 a0 v0)) := by
    intro l0 m0 a0 v0; cases m0 <;> simp [absCap, Fl4Spec.objRefs, Fl4Spec.aobjRef]
  exact final_other hR hP hxs hcx hfin (hr l mm a v) hy hne (by rw [h]; exact hr l' mm' a' v')

/-- **`VsPend` at a frame slot of `VmEptState`** (the Architect's goal-2 note for EPT-mapped frames): a frame cap has
no VSpace key (`VKey`), so the slot is pending from `VsNamed` alone (`VsPend.of_nokey`). With `finEptFrameG`'s
post (`VmEptState` after, slots kept) it holds after the finalisation of an EPT-mapped frame. -/
theorem VmEptState.vsPendFrame (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) {x p r asid va : U64}
    {sz : capability.FrameSize} {d mp e : Bool} (hx : capV (L.mem s) x = .Frame p sz r d mp e asid va) :
    Z.vx = ∅ → VsPend Z.th (L.mem s) (L.ksb s) x :=
  fun h => VsPend.of_nokey (J.1.1.carry.vsNamed h) (by rw [hx]; rfl)

open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1 in
set_option maxHeartbeats 4000000 in
/-- **The delete of a slot holding any `Ept` cap at `VmEptState`** (gen 42b19, the Architect's goal 2: root level 0,
unmapped, non-final and final non-root caps through one `EptCore.ofEmpty`): FL4's `cdt::delete(slot, true)` of a
slot holding `Ept p l m asid va` ends in `Ok ()` with an outcome of the spec's `capDeleteVF`, `VmEptState V X XL` at
the new ghost, the slot null, every other slot's cap and `ksb` kept. Cases on FL4's finality (`finalHyp_full`):
* mapped root (`l = 0`, `m`): `delEptRoot`;
* unmapped, or not final: both finalisations do nothing (`fl4_finEptNop`, `finCapV_eptNop`); `ofEmpty`'s `hxl` from
  `ept_nonfinal_twin` (only asked of a mapped non-root cap, which is then not final);
* final mapped non-root: P3/EptFinUnmap's `finEptTblU`, `hxl` from its unreachability with `ept_final_uq`.
Then P3/EptDelRoot's `delEptStep`. From `ArchRefines` [P] only. -/
theorem VmEptState.delEpt [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR)
    (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ)
    {sl : Fl4Spec.CslotPtr} {p l asid va : U64} {m : Bool} (hAs : AbsSlot Z.th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Ept p l m asid va)) :
    cdt.delete st arI s a (cslotAddr sl) true ⦃ r => r.1 = .Ok () ∧
      ∃ (σ' : Fl4Spec.State Unit) (G' : MdbGhost) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        (.ok (), σ') ∈ ((Fl4Spec.capDeleteVF (Z := Unit) sl).run σ).1 ∧
        VmEptState (L := L) arI V X XL AR (Z.mv G' Z.vs) H Cs Ac' Lst' D' r.2.1 r.2.2 σ' ∧
        capV (L.mem r.2.1) (cslotAddr sl) = .Null ∧
        (∀ y, IsSlot Z.th y → y ≠ cslotAddr sl → capV (L.mem r.2.1) y = capV (L.mem s) y) ∧
        L.ksb r.2.1 = L.ksb s ⦄ := by
  have B := J.1.1
  have hP := B.xtop.rel.1
  have hR := B.xtop.rel.2.1.1
  have hDS : DState (L := L) Z.th s σ Z.G := ⟨B.xtop.rel.2.1, B.del, B.xtop.rel.2.2.1⟩
  by_cases hroot : m = true ∧ l = 0#u64
  · obtain ⟨rfl, rfl⟩ := hroot
    exact J.delEptRoot arI hA hAs hc
  obtain ⟨fin, hfin, hNF, -⟩ := finalHyp_full Z.th hP s σ Z.G sl _ hDS hAs hc (fun h => by cases h)
  have hfe : fin = decide (Fl4Spec.isFinalCap' (absCap (.Ept p l m asid va)) σ) := hNF (Or.inl ⟨trivial, rfl⟩)
  have hfF : finF (L.mem s) (cslotAddr sl) = fin := by
    have e := (is_final_eq (L := L) s (cslotAddr sl)).symm.trans hfin
    exact eq_of_ok_eq e
  by_cases hnop : m = false ∨ fin = false
  · -- nothing to finalise
    refine VmEptState.delEptStep arI hAs hc hR hfin (fl4_finEptNop s a hnop) ?_ J (SlotsSame.refl _ _) rfl ?_
    · rw [finaliseCapVF_eptShape (.ept p l m asid va), ← hfe, finCapV_eptNop σ hnop]
      exact Set.mem_singleton _
    · intro hm _
      have hf0 : fin = false := hnop.resolve_left (by rw [hm]; decide)
      exact Or.inr (ept_nonfinal_twin hP B.xtop.rel.2.1.2.2.1 hAs.isSlot hc (by rw [hfF, hf0]))
  · -- final, mapped, not the root
    have hm : m = true := by
      cases m
      · exact absurd (Or.inl rfl) hnop
      · rfl
    have hf1 : fin = true := by
      cases fin
      · exact absurd (Or.inr rfl) hnop
      · rfl
    subst hm hf1
    have hl0 : l ≠ 0#u64 := fun h => hroot ⟨rfl, h⟩
    obtain ⟨⟨rc, s1, a1⟩, hr, h1, σ1, hF, J1, hSS, hks, hU⟩ := spec_exists (J.finEptTblU hA hAs hc hl0)
    simp only at h1 hF J1 hSS hks hU
    subst h1
    have hfin' : Fl4Spec.isFinalCap' (absCap (.Ept p l true asid va)) σ := of_decide_eq_true hfe.symm
    refine VmEptState.delEptStep arI hAs hc hR hfin hr ?_ J1 hSS hks
      (fun _ _ => Or.inl (hU (ept_final_uq hR hP hAs hc hfin')))
    rw [finaliseCapVF_eptShape (.ept p l true asid va), ← hfe, hF]
    exact Set.mem_singleton _
end

end

end Fl4Proofs.P3
