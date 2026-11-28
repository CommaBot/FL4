/-
P3 (line mmuAD, gen 42b15, goal 2): **the finalisation of a final mapped non-root EPT cap at `VmEptState`** —
FL4's `objects::finalise_cap … c true false` (objects.rs l. 263-273) at
* a mapped `Ept p l true asid va` cap with `l ≠ 0` (l. 266 → `ept::finalise`, ept.rs l. 228-233:
  `ept::unmap(asid, vaddr, ptr, level, true)`), against the extended spec's `finaliseCapV` of
  `.eptCap p l (some (asid, va))` (Fl4Spec/Ext/VirtFinalise: `final ∧ level ≠ 0` → `guestUnmap … true`, then
  `(nullCap, nullCap)`);
* an EPT-mapped non-device `Frame p sz r false true true asid va` cap (l. 267-272: when `asid ≠ 0`
  `ept::unmap(asid, vaddr, ptr, size.bits(), false)`; no DMA retire for a non-device frame), against `finaliseCapV`
  of `.pageCap false p R .vmEptMap sz (some (asid, va))` (`when (asid ≠ 0) guestUnmap … false`, then
  `(nullCap, nullCap)`).

Both through P3/EptUnmapRel's `EptCore.unmapRel` (the guest address bound from `JExtEpt.vtop`, gen 42b15 for frames)
and, on a hit, P3/EptTableUnmapV's `VmEptState.unmapEntry`.

* Spec: **`finCapV_eptTbl`**, **`finCapV_eptFrame`** (single outcomes).
* FL4: **`EptCore.finTblF`**, **`EptCore.finFrameF`** (the finalise ⦃ `(Null, Null)`, the arch relation kept,
  `UnmapOut` ⦄).
* Tops: **`VmEptState.finEptTbl`**, **`VmEptState.finEptFrame`**: from `VmEptState` and the slot's cap, FL4's
  `finalise_cap … true false` ⦃ `(Null, Null)`, the spec's `finaliseCapV … true` has the single outcome
  `((nullCap, nullCap), σ')`, `VmEptState` at FL4's state and `σ'`, the slots kept (`SlotsSame`) ⦄.

Gen 42b16: an EPT-mapped **device** frame too: **`EptCore.finFrameFG`**, **`VmEptState.finEptFrameG`** (any device
bit; a final device frame's `retire_dma_frame`, objects.rs l. 270, keeps `AR` by `MRKeepD` [P] through MachKeepD's
`MKD.objects_retire_dma_frame`, with `P0.StoreTotal st` / `P0.ArchTotal arI`, all asked for only when
`d = true → fin = true`); `EptCore.finFrameF` / `VmEptState.finEptFrame` are their non-device corollaries
(statements unchanged).

Not here: the deletion around it (the finalise loop and slot clearing at `VmEptState`, after the post-#115
retype/deletion dedup); a non-final or unmapped cap and the combined EPT arm are P3/EptFinAll's.

Premises: `ArchRefines arI AR` [P] (as P3/EptUnmapRel); `MRKeepD arI AR` [P] (P3/MachKeepD; already a premise of the
U44 / `_sysLzz` tops), only at a final device frame. No new named premise. Root import after `P3.EptFrameUnmap`.
-/
import Fl4Proofs.P3.EptTableUnmapV
import Fl4Proofs.P3.MachKeepD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Spec side -/

section Spec
open Fl4Spec

/-- The spec's finalisation of a final mapped non-root EPT table cap. -/
theorem finCapV_eptTbl {σ σ2 : State Unit} {p asid gpa : Word} {l : Nat} (hl : l ≠ 0)
    (hG : guestUnmap (Z := Unit) asid gpa p l true σ = ({((), σ2)}, False)) :
    finaliseCapV (Z := Unit) (.archObjectCap (.eptCap p l (some (asid, gpa)))) true σ =
      ({((.nullCap, .nullCap), σ2)}, False) := by
  unfold finaliseCapV
  dsimp only
  rw [if_pos ⟨rfl, hl⟩, Notif.nd_bind_one hG]
  rfl

/-- The spec's finalisation of an EPT-mapped frame cap (any finality). -/
theorem finCapV_eptFrame {σ σ2 : State Unit} {dev : Bool} {p : ObjRef} {R : CapRights} {sz : VMPageSize}
    {asid gpa : Word}
    (hG : NonDet.when (asid ≠ 0) (guestUnmap (Z := Unit) asid gpa p (pageBitsForSize sz) false) σ =
      ({((), σ2)}, False)) (b : Bool) :
    finaliseCapV (Z := Unit) (.archObjectCap (.pageCap dev p R .vmEptMap sz (some (asid, gpa)))) b σ =
      ({((.nullCap, .nullCap), σ2)}, False) := by
  unfold finaliseCapV
  dsimp only
  rw [Notif.nd_bind_one hG]
  rfl

end Spec

/-! ## FL4 side -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}
variable {X : Set U64} {XL : U64 → Nat} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}

open Fl4Proofs.P3.Vs

set_option maxHeartbeats 4000000 in
/-- FL4's finalisation of a final mapped non-root `Ept` cap (module docstring). -/
theorem EptCore.finTblF (C : EptCore (L := L) X XL th s σ) {P : Set U64} (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hA : ArchRefines arI AR) (a : A) {c : Fl4Spec.Cr3} (hAR : AR a c) {p l asid va : U64} (hl0 : l ≠ 0#u64)
    (hlv : l.val = 39 ∨ l.val = 30 ∨ l.val = 21) (hva : va.val < 2 ^ 47) :
    objects.finalise_cap st arI s a (.Ept p l true asid va) true false ⦃ r =>
      r.1 = (.Null, .Null) ∧ AR r.2.2 c ∧
      UnmapOut (L := L) X XL σ s asid va p l true r.2.1
        (Fl4Spec.guestUnmap (Z := Unit) asid.bv va.bv p.bv l.val true σ) ⦄ := by
  unfold objects.finalise_cap objects.finalise_cap_object ept.finalise
  simp only [bind_ok, ↓reduceIte, hl0, eq_self_iff_true, if_true]
  refine WP.spec_bind (C.unmapRel hR hA a hAR asid va p l true hva (by omega)) ?_
  rintro ⟨s1, a1⟩ ⟨h1, h2⟩
  exact (WP.spec_ok _).2 ⟨rfl, h1, h2⟩

set_option maxHeartbeats 4000000 in
/-- FL4's finalisation of an EPT-mapped frame cap, device or not (module docstring; gen 42b16). A final device
frame's `retire_dma_frame` keeps `AR` by `MRKeepD` [P] (`MKD.objects_retire_dma_frame`, with `P0.StoreTotal` /
`P0.ArchTotal`), asked for only then (`hD`). -/
theorem EptCore.finFrameFG (C : EptCore (L := L) X XL th s σ) {P : Set U64} (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hA : ArchRefines arI AR) (a : A) {c : Fl4Spec.Cr3} (hAR : AR a c) {p r asid va : U64}
    {sz : capability.FrameSize} {d : Bool} (hva : va.val < 2 ^ 47) (fin : Bool)
    (hD : d = true → fin = true → P0.StoreTotal st ∧ P0.ArchTotal arI ∧ MRKeepD arI AR) :
    objects.finalise_cap st arI s a (.Frame p sz r d true true asid va) fin false ⦃ res =>
      res.1 = (.Null, .Null) ∧ AR res.2.2 c ∧
      ((asid = 0#u64 ∧ res.2.1 = s) ∨
        (asid ≠ 0#u64 ∧ UnmapOut (L := L) X XL σ s asid va p (fbits sz) false res.2.1
          (Fl4Spec.guestUnmap (Z := Unit) asid.bv va.bv p.bv (fbits sz).val false σ))) ⦄ := by
  unfold objects.finalise_cap objects.finalise_cap_object
  simp only [bind_ok, ↓reduceIte, Bool.false_eq_true]
  refine WP.spec_bind (Pₘ := fun x : S × A => AR x.2 c ∧
      ((asid = 0#u64 ∧ x.1 = s) ∨
        (asid ≠ 0#u64 ∧ UnmapOut (L := L) X XL σ s asid va p (fbits sz) false x.1
          (Fl4Spec.guestUnmap (Z := Unit) asid.bv va.bv p.bv (fbits sz).val false σ)))) ?_ ?_
  · by_cases h0 : asid = 0#u64
    · rw [if_neg (by simp [h0])]
      exact (WP.spec_ok _).2 ⟨hAR, Or.inl ⟨h0, rfl⟩⟩
    · rw [if_pos (by simpa using h0), bits_eq, bind_ok]
      refine WP.spec_mono (C.unmapRel hR hA a hAR asid va p (fbits sz) false hva (by cases sz <;> simp [fbits])) ?_
      rintro ⟨s3, a2⟩ ⟨h1, h2⟩
      exact ⟨h1, Or.inr ⟨h0, h2⟩⟩
  · rintro ⟨s1, a1⟩ ⟨h1, h2⟩
    cases fin with
    | false =>
      simp only [↓reduceIte, Bool.false_eq_true, eq_self_iff_true, if_true]
      exact (WP.spec_ok _).2 ⟨rfl, h1, h2⟩
    | true =>
      cases d with
      | false =>
        simp only [↓reduceIte, Bool.false_eq_true, eq_self_iff_true, if_true]
        exact (WP.spec_ok _).2 ⟨rfl, h1, h2⟩
      | true =>
        obtain ⟨hS, hT, hK⟩ := hD rfl rfl
        simp only [↓reduceIte, eq_self_iff_true, if_true]
        exact WP.spec_bind (MKD.objects_retire_dma_frame hS hT hK h1) (fun a2 h => (WP.spec_ok _).2 ⟨rfl, h, h2⟩)

/-- FL4's finalisation of an EPT-mapped non-device frame cap (module docstring). -/
theorem EptCore.finFrameF (C : EptCore (L := L) X XL th s σ) {P : Set U64} (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (hA : ArchRefines arI AR) (a : A) {c : Fl4Spec.Cr3} (hAR : AR a c) {p r asid va : U64}
    {sz : capability.FrameSize} (hva : va.val < 2 ^ 47) (fin : Bool) :
    objects.finalise_cap st arI s a (.Frame p sz r false true true asid va) fin false ⦃ res =>
      res.1 = (.Null, .Null) ∧ AR res.2.2 c ∧
      ((asid = 0#u64 ∧ res.2.1 = s) ∨
        (asid ≠ 0#u64 ∧ UnmapOut (L := L) X XL σ s asid va p (fbits sz) false res.2.1
          (Fl4Spec.guestUnmap (Z := Unit) asid.bv va.bv p.bv (fbits sz).val false σ))) ⦄ :=
  C.finFrameFG hR hA a hAR hva fin (fun h => by cases h)

end

/-! ## `VmEptState` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64} {XL : U64 → Nat}

open Fl4Proofs.P3.Vs

set_option maxHeartbeats 4000000 in
/-- **The finalisation of a final mapped non-root EPT table cap at `VmEptState`** (module docstring). -/
theorem VmEptState.finEptTbl (hA : ArchRefines arI AR) (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ)
    {sl : Fl4Spec.CslotPtr} (hAs : AbsSlot Z.th sl) {p l asid va : U64}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Ept p l true asid va)) (hl0 : l ≠ 0#u64) :
    objects.finalise_cap st arI s a (.Ept p l true asid va) true false ⦃ r =>
      r.1 = (.Null, .Null) ∧ ∃ σ' : Fl4Spec.State Unit,
        Fl4Spec.finaliseCapV (Z := Unit) (absCap (.Ept p l true asid va)) true σ =
          ({((.nullCap, .nullCap), σ')}, False) ∧
        VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D r.2.1 r.2.2 σ' ∧
        SlotsSame Z.th (L.mem s) (L.mem r.2.1) ⦄ := by
  have B := J.1.1
  have C := J.2
  have hxs : IsSlot Z.th (cslotAddr sl) := hAs.isSlot
  have hcv : capV (L.mem s) (cslotAddr sl) = .Ept p l true asid va := capV_of_capAt hc
  obtain ⟨-, hlv4, -⟩ := C.capTbl hxs hcv
  have hlv : l.val = 39 ∨ l.val = 30 ∨ l.val = 21 := by
    rcases hlv4 with h | h
    · exact absurd (UScalar.eq_of_val_eq (by rw [h]; rfl) : l = 0#u64) hl0
    · exact h
  have hl0' : l.val ≠ 0 := by omega
  have hva : va.val < 2 ^ 47 := C.exte.vtop.1 _ hxs _ _ _ _ hcv
  have hAR : AR a σ.archState.x64CurrentCr3 := B.xtop.fin.1.1.2.2.2.2.2.2
  refine WP.spec_mono (C.finTblF B.xtop.fin.2.1 hA a hAR hl0 hlv hva) ?_
  rintro ⟨rc, s3, a3⟩ ⟨h1, hAR2, hU⟩
  refine ⟨h1, ?_⟩
  have habs : absCap (.Ept p l true asid va) = .archObjectCap (.eptCap p.bv l.val (some (asid.bv, va.bv))) := rfl
  rw [habs]
  rcases hU with ⟨e3, hG⟩ | ⟨t, ht, es, hXt, hPt, hk, -, e3, hG⟩
  · simp only at e3
    subst e3
    exact ⟨σ, finCapV_eptTbl hl0' hG, J.archV hAR2, SlotsSame.refl _ _⟩
  · simp only at e3
    subst e3
    obtain ⟨J3, hSS3⟩ := J.unmapEntry ht (g := va.bv) hva (by rw [hXt]; exact hPt) hk _
    exact ⟨_, finCapV_eptTbl hl0' (hG.trans (storeGuestEntry_eq hk _ _)), J3.archV hAR2, hSS3⟩

set_option maxHeartbeats 4000000 in
/-- **The finalisation of an EPT-mapped frame cap at `VmEptState`, device or not** (module docstring; gen 42b16:
`hD` as `EptCore.finFrameFG`). -/
theorem VmEptState.finEptFrameG (hA : ArchRefines arI AR)
    (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr} (hAs : AbsSlot Z.th sl)
    {p r asid va : U64} {sz : capability.FrameSize} {d : Bool}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Frame p sz r d true true asid va)) (fin : Bool)
    (hD : d = true → fin = true → P0.StoreTotal st ∧ P0.ArchTotal arI ∧ MRKeepD arI AR) :
    objects.finalise_cap st arI s a (.Frame p sz r d true true asid va) fin false ⦃ res =>
      res.1 = (.Null, .Null) ∧ ∃ σ' : Fl4Spec.State Unit,
        Fl4Spec.finaliseCapV (Z := Unit) (absCap (.Frame p sz r d true true asid va)) fin σ =
          ({((.nullCap, .nullCap), σ')}, False) ∧
        VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D res.2.1 res.2.2 σ' ∧
        SlotsSame Z.th (L.mem s) (L.mem res.2.1) ⦄ := by
  have B := J.1.1
  have C := J.2
  have hxs : IsSlot Z.th (cslotAddr sl) := hAs.isSlot
  have hcv : capV (L.mem s) (cslotAddr sl) = .Frame p sz r d true true asid va := capV_of_capAt hc
  have hva : va.val < 2 ^ 47 := C.exte.vtop.2 _ hxs _ _ _ _ _ _ hcv
  have hAR : AR a σ.archState.x64CurrentCr3 := B.xtop.fin.1.1.2.2.2.2.2.2
  refine WP.spec_mono (C.finFrameFG B.xtop.fin.2.1 hA a hAR hva fin hD) ?_
  rintro ⟨rc, s3, a3⟩ ⟨h1, hAR2, hcase⟩
  refine ⟨h1, ?_⟩
  have habs : absCap (.Frame p sz r d true true asid va) =
      .archObjectCap (.pageCap d p.bv (vmRightsOf r) .vmEptMap (frameSizeOf sz) (some (asid.bv, va.bv))) := rfl
  rw [habs]
  rcases hcase with ⟨h0, e3⟩ | ⟨h0, hU⟩
  · simp only at e3
    subst e3
    have hb : ¬ asid.bv ≠ 0 := by rw [h0]; exact fun h => h rfl
    refine ⟨σ, finCapV_eptFrame ?_ fin, J.archV hAR2, SlotsSame.refl _ _⟩
    unfold Fl4Spec.NonDet.when; rw [if_neg hb]; rfl
  · have hb : asid.bv ≠ 0 := fun h => h0 (P1.eq_of_bv (by rw [h]; rfl))
    rcases hU with ⟨e3, hG⟩ | ⟨t, ht, es, hXt, hPt, hk, -, e3, hG⟩
    · simp only at e3
      subst e3
      refine ⟨σ, finCapV_eptFrame ?_ fin, J.archV hAR2, SlotsSame.refl _ _⟩
      unfold Fl4Spec.NonDet.when; rw [if_pos hb, ← fbits_val]; exact hG
    · simp only at e3
      subst e3
      obtain ⟨J3, hSS3⟩ := J.unmapEntry ht (g := va.bv) hva (by rw [hXt]; exact hPt) hk _
      refine ⟨_, finCapV_eptFrame ?_ fin, J3.archV hAR2, hSS3⟩
      unfold Fl4Spec.NonDet.when; rw [if_pos hb, ← fbits_val, hG, storeGuestEntry_eq hk]

/-- **The finalisation of an EPT-mapped non-device frame cap at `VmEptState`** (module docstring). -/
theorem VmEptState.finEptFrame (hA : ArchRefines arI AR)
    (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr} (hAs : AbsSlot Z.th sl)
    {p r asid va : U64} {sz : capability.FrameSize}
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Frame p sz r false true true asid va)) (fin : Bool) :
    objects.finalise_cap st arI s a (.Frame p sz r false true true asid va) fin false ⦃ res =>
      res.1 = (.Null, .Null) ∧ ∃ σ' : Fl4Spec.State Unit,
        Fl4Spec.finaliseCapV (Z := Unit) (absCap (.Frame p sz r false true true asid va)) fin σ =
          ({((.nullCap, .nullCap), σ')}, False) ∧
        VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D res.2.1 res.2.2 σ' ∧
        SlotsSame Z.th (L.mem s) (L.mem res.2.1) ⦄ :=
  J.finEptFrameG hA hAs hc fin (fun h => by cases h)

end

end

end Fl4Proofs.P3
