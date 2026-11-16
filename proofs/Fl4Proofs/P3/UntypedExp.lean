/-
P3 (DESIGN.md §9), untyped: **what a retype did, exposed** (`RetExp`), for
the joint invariants after it (ScPlaceRet):

* the MDB's non-untyped caps are kept; the new caps `cj j` sit in the new
  slots `dslot j`, physical, over `[A + j k, A + j k + k)`;
* every untyped cap after lies inside one before (`ut`);
* the new objects lie in an untyped cap's free part, or its whole region when
  it has no children (`src`);
* the typed heap after: the old objects, or new ones at the new caps
  (`NewQ`) of size at most `k` (`th`).

`RetypeDelta.toExp` derives it from the retype's `RetypeDelta`;
`RetExp.same_left` moves its start across writes keeping the slots.  `ksb`
(the kernel-state base) is kept by the cap writes and the non-TCB object
loop (`set_cap_ksb`, `insert_new_cap_ksb`, `create_new_objects_ksb`).
-/
import Fl4Proofs.P3.UntypedUtInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section
set_option linter.unusedSimpArgs false

/-- `q` is a new object's address: the `j`-th of the window, with a
non-untyped cap. -/
def NewQ (A k w : Nat) (cj : Nat → capability.Cap) (q : U64) : Prop :=
  ∃ j, j < w ∧ q.val = A + j * k ∧ isUt (cj j) = false

/-- **What a retype did** (module docstring), from the memory and ghost
tree `m`, `G` to `m'`, `G'`, with the typed heaps `th`, `th'`. -/
structure RetExp (th th' : TypedHeap) (m m' : U64 → U64) (G G' : MdbGhost) (A k w : Nat)
    (dslot : Nat → U64) (cj : Nat → capability.Cap) : Prop where
  k1 : 1 ≤ k
  keep : ∀ y ∈ G.chains.flatten, isUt (capV m y) = false → y ∈ G'.chains.flatten ∧ capV m' y = capV m y
  newm : ∀ j, j < w → dslot j ∈ G'.chains.flatten
  newc : ∀ j, j < w → capV m' (dslot j) = cj j
  cphys : ∀ j, j < w → physF (cj j) = true
  cbase : ∀ j, j < w → baseF (cj j) = A + j * k
  ctop : ∀ j, j < w → topF (cj j) = A + j * k + k - 1
  ut : ∀ x ∈ G'.chains.flatten, ∀ p sb fi d, capV m' x = .Untyped p sb fi d →
    ∃ x0 ∈ G.chains.flatten, ∃ p0 sb0 fi0 d0, capV m x0 = .Untyped p0 sb0 fi0 d0 ∧
      p0.val ≤ p.val ∧ p.val + 2 ^ sb.val ≤ p0.val + 2 ^ sb0.val
  src : ∃ x0 ∈ G.chains.flatten, ∃ p0 sb0 fi0 d0, capV m x0 = .Untyped p0 sb0 fi0 d0 ∧
    p0.val ≤ A ∧ A + w * k ≤ p0.val + 2 ^ sb0.val ∧ (p0.val + fi0.val ≤ A ∨ ∀ y, ¬ Mdb.Desc G.par y x0)
  th : ∀ q kd, th' q = some kd → (th q = some kd ∧ (NewQ A k w cj q → objSize kd = 0)) ∨
    (NewQ A k w cj q ∧ objSize kd ≤ k)

theorem isUt_untyped (p sb fi : U64) (d : Bool) : isUt (.Untyped p sb fi d) = true := rfl

section
variable {th th' : TypedHeap} {G0 Gf : MdbGhost} {m0 m1 mf : U64 → U64} {src p sb fi nfi : U64} {dev : Bool}
  {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap}

/-- **`RetExp` from the retype's `RetypeDelta`**, the MDB links after it, and
the shape of the typed heap after. -/
theorem RetypeDelta.toExp (h : RetypeDelta th m0 m1 mf G0 Gf src p sb fi nfi dev A k w dslot cj)
    (hU : UtInv m0 G0) (hMf : MdbLinks th' mf Gf)
    (hth : ∀ q kd, th' q = some kd → (th q = some kd ∧ (NewQ A k w cj q → objSize kd = 0)) ∨
      (NewQ A k w cj q ∧ objSize kd ≤ k)) :
    RetExp th th' m0 mf G0 Gf A k w dslot cj := by
  have hsb := capV_ut_sb h.hcs
  have hreg := hU.reg src h.hsrc (by rw [h.hcs]; exact ok_inj (phys_eq _).symm)
  rw [h.hcs] at hreg
  obtain ⟨-, -, hfit⟩ := ut_range hsb hreg
  have hsrcU : isUt (capV m0 src) = true := by rw [h.hcs]; rfl
  refine ⟨h.hk, fun y hy hu => ?_, fun j hj => ?_, fun j hj => h.F2a j hj, h.cphys, h.cbase, h.ctop,
    fun x hx p' sb' fi' d' hcx => ?_, ⟨src, h.hsrc, p, sb, fi, dev, h.hcs, by have := h.hA; omega, h.hAw, Or.inl h.hA⟩, hth⟩
  · have hys : y ≠ src := by rintro rfl; rw [hsrcU] at hu; cases hu
    exact ⟨h.F1b y hy, by rw [h.F2b y hy, h.hc1 y hy hys]⟩
  · exact (desc_mem hMf ((h.F3 _ src).2 (Or.inr ⟨j, hj, rfl, Or.inl rfl⟩))).1
  · rcases h.F1 x hx with hx0 | ⟨j, hj, rfl⟩
    · by_cases hxs : x = src
      · subst hxs
        rw [h.F2b _ hx0, h.hcs1] at hcx
        cases hcx
        exact ⟨_, h.hsrc, p, sb, fi, dev, h.hcs, le_refl _, le_refl _⟩
      · rw [h.F2b _ hx0, h.hc1 x hx0 hxs] at hcx
        exact ⟨x, hx0, p', sb', fi', d', hcx, le_refl _, le_refl _⟩
    · rw [h.F2a j hj] at hcx
      obtain ⟨us, d, he, hk⟩ := h.cut j hj (by rw [hcx]; rfl)
      rw [hcx] at he
      cases he
      have h1 : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
      rw [Nat.add_mul, Nat.one_mul] at h1
      have hlt : A + j * k < 2 ^ 64 := by have := h.hk; have := h.hAw; omega
      have hv : (⟨BitVec.ofNat 64 (A + j * k)⟩ : U64).val = A + j * k := by
        show (BitVec.ofNat 64 (A + j * k)).toNat = _; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      refine ⟨src, h.hsrc, p, sb, fi, dev, h.hcs, ?_, ?_⟩
      · rw [hv]; have := h.hA; omega
      · rw [hv, hk]; have := h.hAw; omega

end

/-- An old object at a new address, in a free window, is empty. -/
theorem newQ_free {th : TypedHeap} {A k w : Nat} {cj : Nat → capability.Cap} (hk : 1 ≤ k)
    (hrf : RegionFree th A (A + w * k)) : ∀ q kd, th q = some kd → NewQ A k w cj q → objSize kd = 0 := by
  rintro q kd hq ⟨j, hj, hv, -⟩
  have h1 : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at h1
  rcases hrf q kd hq with h | h <;> omega

/-- The typed heap kept, over a free window. -/
theorem th_same_shape {th : TypedHeap} {A k w : Nat} {cj : Nat → capability.Cap} (hk : 1 ≤ k)
    (hrf : RegionFree th A (A + w * k)) : ∀ q kd, th q = some kd →
      (th q = some kd ∧ (NewQ A k w cj q → objSize kd = 0)) ∨ (NewQ A k w cj q ∧ objSize kd ≤ k) :=
  fun q kd hq => Or.inl ⟨hq, newQ_free hk hrf q kd hq⟩

/-- The typed heap grown by `w` objects of kind `kd` over a free window,
with non-untyped new caps. -/
theorem extendTh_shape {th : TypedHeap} {A k w : Nat} {kd : ObjKind} {cj : Nat → capability.Cap} (hk : 1 ≤ k)
    (hrf : RegionFree th A (A + w * k)) (hsz : objSize kd ≤ k) (hcj : ∀ j, j < w → isUt (cj j) = false) :
    ∀ q kd', extendTh th A k w kd q = some kd' →
      (th q = some kd' ∧ (NewQ A k w cj q → objSize kd' = 0)) ∨ (NewQ A k w cj q ∧ objSize kd' ≤ k) := by
  intro q kd' hq
  by_cases hnew : ∃ i, i < w ∧ q.val = A + i * k
  · rw [extendTh_new hnew] at hq
    cases hq
    obtain ⟨i, hi, hv⟩ := hnew
    exact Or.inr ⟨⟨i, hi, hv, hcj i hi⟩, hsz⟩
  · rw [extendTh_old hnew] at hq
    exact Or.inl ⟨hq, newQ_free hk hrf q kd' hq⟩

/-- **`RetExp` moved back across writes keeping the slots.** -/
theorem RetExp.same_left {th th' : TypedHeap} {m m0 m' : U64 → U64} {G G' : MdbGhost} {A k w : Nat}
    {dslot : Nat → U64} {cj : Nat → capability.Cap} (hM : MdbLinks th m G) (hS : SlotsSame th m m0)
    (h : RetExp th th' m0 m' G G' A k w dslot cj) : RetExp th th' m m' G G' A k w dslot cj := by
  have hc : ∀ x ∈ G.chains.flatten, capV m0 x = capV m x := fun x hx => hS.capV ((hM.members x).1 hx).1
  refine ⟨h.k1, fun y hy hu => ?_, h.newm, h.newc, h.cphys, h.cbase, h.ctop, fun x hx p sb fi d hcx => ?_, ?_, h.th⟩
  · rw [← hc y hy] at hu ⊢; exact h.keep y hy hu
  · obtain ⟨x0, hx0, p0, sb0, fi0, d0, e, h1, h2⟩ := h.ut x hx p sb fi d hcx
    exact ⟨x0, hx0, p0, sb0, fi0, d0, by rw [← hc x0 hx0]; exact e, h1, h2⟩
  · obtain ⟨x0, hx0, p0, sb0, fi0, d0, e, h1, h2, h3⟩ := h.src
    exact ⟨x0, hx0, p0, sb0, fi0, d0, by rw [← hc x0 hx0]; exact e, h1, h2, h3⟩

/-! ## `ksb` kept -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem set_cap_ksb (sl : obj.Slot) (s : S) (c : capability.Cap) :
    obj.Slot.set_cap st sl s c ⦃ s' => L.ksb s' = L.ksb s ⦄ :=
  WP.spec_mono (set_cap_spec (L := L) sl s c) (by rintro _ rfl; simp)

theorem insert_new_cap_ksb (s : S) (src dest : U64) (c : capability.Cap) :
    cdt.insert_new_cap st s src dest c ⦃ s' => L.ksb s' = L.ksb s ⦄ := by
  unfold cdt.insert_new_cap
  step
  obtain ⟨s1, h1, k1⟩ := spec_exists (set_cap_ksb (L := L) dest s c)
  rw [h1]; simp only [bind_ok]
  step; step; step; step
  simp only [obj.Slot.is_null, bind_ok]
  by_cases hz0 : next = 0#u64
  · simp only [hz0, decide_true, ↓reduceIte, bind_ok]
    step*
    subst_vars; simp_all
  · simp only [hz0, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
    step*
    subst_vars; simp_all

/-- **The object loop of a non-TCB, non-PML4 retype keeps `ksb`** (its
objects need no initialisation; only the cap inserts write). -/
theorem create_new_objects_ksb {A' : Type} (arI : machine.Arch A') (ar : A') (s : S) (nt us parent dest off win base : U64)
    (dev : Bool) (hn : nt.val = 0 ∨ (2 ≤ nt.val ∧ nt.val ≤ 13 ∧ nt.val ≠ 8)) (hus : us.val < 64)
    (hz : zOf nt.val us.val < 64) :
    objects.create_new_objects st arI s ar nt parent dest off win base us dev ⦃ res => L.ksb res.1 = L.ksb s ⦄ := by
  have hn14 : nt.val < 14 := by omega
  unfold objects.create_new_objects
  rw [object_size_eq nt us hn14 hus]
  simp only [bind_ok]
  unfold objects.create_new_objects_loop
  have h63 : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val = zOf nt.val us.val := by
    have : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val =
        (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val % 64 := by
      simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
    rw [this]
    show (BitVec.ofNat 64 (zOf nt.val us.val)).toNat % 64 = _
    simp; omega
  refine loop.spec_decr_nat (measure := fun x => win.val - x.2.2.val)
    (inv := fun x => x.2.2.val ≤ win.val ∧ L.ksb x.1 = L.ksb s) _ _ _ ?_ ?_
  · rintro ⟨s1, a1, i⟩ ⟨hiw, hk⟩
    simp only at hiw hk ⊢
    unfold objects.create_new_objects_loop.body
    by_cases hit : i < win
    · rw [if_pos hit]
      have hit' : i.val < win.val := hit
      simp only [lift, bind_ok]
      obtain ⟨i2, hi2, -, -⟩ := spec_exists (UScalar.ShiftLeft_spec i
        ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64) _
        (by rw [h63]; simp [UScalarTy.U64_numBits_eq]; omega) rfl)
      rw [hi2]; simp only [bind_ok]
      rw [create_object_eq arI s1 a1 nt _ us dev hn]
      simp only [bind_ok, uncurry_apply_pair]
      rw [spec_eq_ok (slot_index_spec dest _)]
      simp only [bind_ok]
      obtain ⟨s3, h3, k3⟩ := spec_exists (insert_new_cap_ksb (L := L) s1 parent
        (slotAddr dest.bv (core.num.U64.wrapping_add off i).bv) (newCapOf nt.val (core.num.U64.wrapping_add base i2) us dev))
      rw [h3]; simp only [bind_ok]
      step as ⟨i5, hi5⟩
      refine ⟨by omega, by rw [k3, hk], by omega⟩
    · rw [if_neg hit, WP.spec_ok]
      exact hk
  · exact ⟨by simp, rfl⟩

end

end
end Fl4Proofs.P3
