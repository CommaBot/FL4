/-
P3 (DESIGN.md §9), untyped: **`untyped::retype` with a reset** against l4v
`invoke_untyped` with `reset = True`: `reset_untyped_cap`, then the retype
from the reset state. The spec is nondeterministic (preemption), so the
result is: no failure (`NSat`), and an outcome of FL4's kind (`NHas`).

For the no-failure of the retype after the spec's reset when FL4 was
preempted, the retype is run (`retype_full`) from an FL4 state built for
the purpose: the region zeroed and the free index 0, related to the spec's
only CSpace state after a complete reset (`reset_nsat_ok`).
-/
import Fl4Proofs.P3.UntypedResetRefine
import Fl4Proofs.P3.UntypedRetypeAll
import Fl4Proofs.P3.ResetFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A' : Type} (arI : machine.Arch A')

theorem retype_true_eq (s : S) (a : A') (slot base nt us dest off win : U64) (dev : Bool) :
    untyped.retype st arI s a slot true base nt us dest off win dev =
      (do let (r, s1, a1) ← untyped.reset_untyped st arI s a slot
          match r with
          | .Ok () => untyped.retype st arI s1 a1 slot false base nt us dest off win dev
          | .Err e => ok (.Err e, s1, a1)) := by
  unfold untyped.retype
  simp only [↓reduceIte, Bool.false_eq_true]
  congr 1; funext ⟨r, s1, a1⟩
  rcases r with ⟨⟩ | e <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]

theorem invoke_true_eq (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (sl : Fl4Spec.CslotPtr) (b rb : Fl4Spec.ObjRef)
    (t : Fl4Spec.ApiObjectType) (us : Nat) (slots : List Fl4Spec.CslotPtr) (dev : Bool) :
    Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype sl true b rb t us slots dev) =
      (Fl4Spec.resetUntypedCap sl >>= fun _ =>
        Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype sl false b rb t us slots dev)) := by
  simp only [Fl4Spec.invokeUntypedWith, Fl4Spec.NonDetE.whenE, ↓reduceIte, Bool.false_eq_true, ndE_pure_bind]

/-- **`untyped::retype` with a reset, generic in the retype after it**: given
that the retype from any state the reset can end in (the relations for the
heap without the region, free index 0, the region zero, the other slots
unchanged, the original bits of `σ`, `E`) refines the spec's retype without
reset, the whole refines `invoke_untyped` with `reset = True`: the spec does
not fail, and has an outcome of FL4's kind, related to FL4's result (for the
heap without the region if preempted, the grown heap if done). -/
theorem isSlot_abs' {th : TypedHeap} {y : U64} (h : IsSlot th y) : ∃ sl, AbsSlot th sl ∧ cslotAddr sl = y := by
  obtain ⟨p, i, hi, rfl⟩ := h
  rcases hi with ⟨r, hp, hir⟩ | ⟨ht, hit⟩
  · refine ⟨(p.bv, bitsOf i r), ⟨p, rfl, Or.inl (by simpa using hp)⟩, ?_⟩
    show slotAddr p.bv (Fl4Spec.ofBl _) = _
    rw [slotAddr_ofBl, blVal_bitsOf, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hir]
  · refine ⟨(p.bv, Fl4Spec.tcbCnodeIndex i), ⟨p, rfl, Or.inr ⟨ht, i, hit, rfl⟩⟩, ?_⟩
    show slotAddr p.bv (Fl4Spec.ofBl _) = _
    rw [slotAddr_ofBl, tcbCnodeIndex_blVal i hit]

/-! ## What the retype did, across the reset (`RetExp`) -/

section
variable {th th'' : TypedHeap} {m m1 mf : U64 → U64} {G G' : MdbGhost} {x p sb fi f : U64} {dev : Bool}
  {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap}

/-- **`RetExp` across the reset before it**: the reset restricts the typed
heap to off the region, lowers the (childless) untyped cap's free index and
keeps every other cap. -/
theorem RetExp.of_reset (hM : MdbLinks th m G) (hP : Placed th) (hN : NoStraddle th p.val (p.val + 2 ^ sb.val))
    (hns : ∀ a ∈ G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val)
    (hcv : capV m x = .Untyped p sb fi dev) (hcv1 : capV m1 x = .Untyped p sb f dev)
    (hnd : ∀ y, ¬ Mdb.Desc G.par y x)
    (hF : ∀ y, IsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) y → y ≠ x → capV m1 y = capV m y)
    (hE : RetExp (restrictTh th p.val (p.val + 2 ^ sb.val)) th'' m1 mf G G' A k w dslot cj x) :
    RetExp th th'' m mf G G' A k w dslot cj x := by
  have hsl : ∀ z ∈ G.chains.flatten, IsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) z := fun z hz =>
    ((hM.members z).1 hz).1.restrict hP hN (hns z hz)
  have hc : ∀ z ∈ G.chains.flatten, z ≠ x → capV m1 z = capV m z := fun z hz hzx => hF z (hsl z hz) hzx
  refine ⟨hE.k1, fun y hy hu => ?_, hE.newm, hE.newc, hE.cphys, hE.cbase, hE.ctop, fun z hz p' sb' fi' d' hcz => ?_,
    ?_, fun q kd hq => ?_, hE.gmem, fun y hy hu => ?_, ?_⟩
  · have hyx : y ≠ x := by rintro rfl; rw [hcv] at hu; cases hu
    rw [← hc y hy hyx] at hu ⊢; exact hE.keep y hy hu
  · obtain ⟨x0, hx0, p0, sb0, fi0, d0, e, h1, h2⟩ := hE.ut z hz p' sb' fi' d' hcz
    by_cases hx0x : x0 = x
    · subst hx0x; rw [hcv1] at e; cases e
      exact ⟨_, hx0, p, sb, fi, dev, hcv, h1, h2⟩
    · exact ⟨x0, hx0, p0, sb0, fi0, d0, by rw [← hc x0 hx0 hx0x]; exact e, h1, h2⟩
  · obtain ⟨x0, hx0, p0, sb0, fi0, d0, e, h1, h2, h3⟩ := hE.src
    by_cases hx0x : x0 = x
    · subst hx0x; rw [hcv1] at e; cases e
      exact ⟨_, hx0, p, sb, fi, dev, hcv, h1, h2, Or.inr hnd⟩
    · exact ⟨x0, hx0, p0, sb0, fi0, d0, by rw [← hc x0 hx0 hx0x]; exact e, h1, h2, h3⟩
  · rcases hE.th q kd hq with ⟨ho, h0⟩ | hn
    · exact Or.inl ⟨(restrictTh_some ho).1, h0⟩
    · exact Or.inr hn
  · by_cases hyx : y = x
    · subst hyx; exact hE.utk y hy (by rw [hcv1]; rfl)
    · exact hE.utk y hy (by rw [hc y hy hyx]; exact hu)
  · obtain ⟨hx0, p0, sb0, fi0, fi1, d0, e0, e1, h1, h2, h3, -, h5⟩ := hE.usrc
    rw [hcv1] at e0; cases e0
    refine ⟨hx0, p, sb, fi, fi1, dev, hcv, e1, h1, h2, h3, Or.inr hnd, fun y hy hu hyx => ?_⟩
    rw [← hc y hy hyx] at hu ⊢; exact h5 y hy hu hyx

/-- **A reset alone** (preempted, no retype yet) as a `RetExp` with no new
objects: the typed heap restricted to off the region. -/
theorem RetExp.reset_only (hM : MdbLinks th m G) (hP : Placed th) (hN : NoStraddle th p.val (p.val + 2 ^ sb.val))
    (hns : ∀ a ∈ G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val) (hx : x ∈ G.chains.flatten)
    (hcv : capV m x = .Untyped p sb fi dev) (hcv1 : capV m1 x = .Untyped p sb f dev)
    (hnd : ∀ y, ¬ Mdb.Desc G.par y x)
    (hF : ∀ y, IsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) y → y ≠ x → capV m1 y = capV m y) :
    RetExp th (restrictTh th p.val (p.val + 2 ^ sb.val)) m m1 G G p.val 1 0 dslot cj x := by
  have hsl : ∀ z ∈ G.chains.flatten, IsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) z := fun z hz =>
    ((hM.members z).1 hz).1.restrict hP hN (hns z hz)
  have hc : ∀ z ∈ G.chains.flatten, z ≠ x → capV m1 z = capV m z := fun z hz hzx => hF z (hsl z hz) hzx
  refine ⟨le_refl _, fun y hy hu => ?_, fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
    fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
    fun z hz p' sb' fi' d' hcz => ?_, ⟨x, hx, p, sb, fi, dev, hcv, le_refl _, by simp, Or.inr hnd⟩,
    fun q kd hq => Or.inl ⟨(restrictTh_some hq).1, fun ⟨j, hj, _⟩ => absurd hj (by omega)⟩,
    fun z hz => Or.inl hz, fun y hy hu => ?_,
    ⟨hx, p, sb, fi, f, dev, hcv, hcv1, le_refl _, by simp, by simp, Or.inr hnd, fun y hy _ hyx => hc y hy hyx⟩⟩
  · have hyx : y ≠ x := by rintro rfl; rw [hcv] at hu; cases hu
    exact ⟨hy, hc y hy hyx⟩
  · by_cases hzx : z = x
    · subst hzx; rw [hcv1] at hcz; cases hcz
      exact ⟨_, hz, p, sb, fi, dev, hcv, le_refl _, le_refl _⟩
    · exact ⟨z, hz, p', sb', fi', d', by rw [← hc z hz hzx]; exact hcz, le_refl _, le_refl _⟩
  · by_cases hyx : y = x
    · subst hyx; rw [hcv1]; rfl
    · rw [hc y hy hyx]; exact hu

end

theorem retype_reset_gen (ar : A') (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev)) (hfi0 : fi.val ≠ 0)
    (hnd : ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (pp.bv, idx)))
    (hpal : p.val % 2 ^ sb.val = 0) (hsb4 : 4 ≤ sb.val)
    (hN : NoStraddle th p.val (p.val + 2 ^ sb.val))
    (hns : ∀ a ∈ G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val)
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hrcb : Fl4Spec.resetChunkBits = 16) (hppS : PPFrame) {E : S → Prop} (hPP : PPHyp (L := L) arI th p sb E)
    (hEk : EKept (L := L) E p sb (cslotAddr (pp.bv, idx))) (hE : E s)
    (base nt us dest off win : U64) (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (rb : Fl4Spec.ObjRef)
    (t : Fl4Spec.ApiObjectType) (usv : Nat) (slots : List Fl4Spec.CslotPtr)
    (X : TypedHeap → S → core.result.Result Unit error.Exc × S × A' → Prop) (Y : TypedHeap → Nat → Nat → Nat → (Nat → U64) → (Nat → capability.Cap) → Prop)
    (hRT : ∀ (t1 : S) (a1 : A') (σt : Fl4Spec.State Unit),
      ResetRel (restrictTh th p.val (p.val + 2 ^ sb.val)) G (cslotAddr (pp.bv, idx)) p sb dev (L.mem t1) σt 0#u64 →
      (dev = false → ZeroRegion (L.mem t1) (p.val + (0#u64 : U64).val) (p.val + 2 ^ sb.val)) →
      (∀ y, IsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) y → y ≠ cslotAddr (pp.bv, idx) →
        capV (L.mem t1) y = capV (L.mem s) y) →
      σt.isOriginalCap = σ.isOriginalCap → σt.archState = σ.archState →
      (∀ x, x ∉ regionSet p.bv sb.val → x ≠ pp.bv → σt.kheap x = σ.kheap x) → E t1 →
      untyped.retype st arI t1 a1 (cslotAddr (pp.bv, idx)) false base nt us dest off win dev ⦃ res =>
        res.1 = .Ok () ∧ ∃ σ' G' th'',
          (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) false p.bv rb t usv slots dev)).run σt =
            ({(.ok (), σ')}, False) ∧
          Placed th'' ∧ StateRel th'' (L.mem res.2.1) σ' ∧ SlotsValid th'' (L.mem res.2.1) ∧
          MdbLinks th'' (L.mem res.2.1) G' ∧ CdtRel th'' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
          (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem t1) G (L.mem res.2.1) G') ∧
          (FinInv (restrictTh th p.val (p.val + 2 ^ sb.val)) (L.mem t1) σt G → FinInv th'' (L.mem res.2.1) σ' G') ∧
          L.ksb res.2.1 = L.ksb t1 ∧ X th'' t1 res ∧
          ∃ A k w dslot cj, RetExp (restrictTh th p.val (p.val + 2 ^ sb.val)) th'' (L.mem t1) (L.mem res.2.1) G G'
            A k w dslot cj (cslotAddr (pp.bv, idx)) ∧ Y th'' A k w dslot cj ⦄)
    (hEksb : ∀ t, E t → L.ksb t = L.ksb s) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) true base nt us dest off win dev ⦃ res =>
      NSat (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv rb t usv slots dev)).run σ
        (fun _ => True) ∧
      ((res.1 = .Err .Preempted ∧ ∃ σ' f,
          NHas (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv rb t usv slots dev)).run σ
            (TopP (.error ()) σ') ∧
          ResetRel (restrictTh th p.val (p.val + 2 ^ sb.val)) G (cslotAddr (pp.bv, idx)) p sb dev
            (L.mem res.2.1) σ' f ∧ MdbStep (L.mem s) G (L.mem res.2.1) G ∧
          (FinInv th (L.mem s) σ G → FinInv (restrictTh th p.val (p.val + 2 ^ sb.val)) (L.mem res.2.1) σ' G) ∧
          L.ksb res.2.1 = L.ksb s ∧ untyped.reset_untyped st arI s ar (cslotAddr (pp.bv, idx)) = ok res ∧
          ∀ dslot cj, RetExp th (restrictTh th p.val (p.val + 2 ^ sb.val)) (L.mem s)
            (L.mem res.2.1) G G p.val 1 0 dslot cj (cslotAddr (pp.bv, idx))) ∨
       (res.1 = .Ok () ∧ ∃ σ' G' th'',
          NHas (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv rb t usv slots dev)).run σ
            (fun y => y.1 = .ok () ∧ KSame σ' y.2) ∧
          Placed th'' ∧ StateRel th'' (L.mem res.2.1) σ' ∧ SlotsValid th'' (L.mem res.2.1) ∧
          MdbLinks th'' (L.mem res.2.1) G' ∧ CdtRel th'' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
          (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s) G (L.mem res.2.1) G') ∧
          (FinInv th (L.mem s) σ G → FinInv th'' (L.mem res.2.1) σ' G') ∧ L.ksb res.2.1 = L.ksb s ∧
          (∃ t1 a1, untyped.reset_untyped st arI s ar (cslotAddr (pp.bv, idx)) = ok (.Ok (), t1, a1) ∧ X th'' t1 res) ∧
          ∃ A k w dslot cj, RetExp th th'' (L.mem s) (L.mem res.2.1) G G' A k w dslot cj (cslotAddr (pp.bv, idx)) ∧ Y th'' A k w dslot cj)) ⦄ := by
  set th' := restrictTh th p.val (p.val + 2 ^ sb.val) with hth'
  set x := cslotAddr (pp.bv, idx) with hxdef
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hcv := capV_of_capAt hcap
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hxs : IsSlot th x := hAs.isSlot
  have hxm : x ∈ G.chains.flatten := (hM.members x).2 ⟨hxs, _, hcap, by simp⟩
  have hrx := hU.reg x hxm (by rw [hcv]; exact physF_ut _ _ _ _)
  rw [hcv] at hrx
  obtain ⟨-, -, hfit⟩ := ut_range hsb hrx
  have hxout := hns x hxm
  have hxs' : IsSlot th' x := hxs.restrict hP hN hxout
  have hppout : ¬ (p.val ≤ pp.val ∧ pp.val < p.val + 2 ^ sb.val) := by
    obtain ⟨q, j, hj, hq, he⟩ := hAs.at
    have : pp = q := bv_inj hq
    subst this
    exact hj.obj_out hP hN (by rw [← he]; exact hxout)
  have hpp' : th' pp = some (.cnode rs) := by
    show restrictTh th _ _ pp = _; rw [restrictTh_out hppout]; exact hpp
  have hpb : pp.bv ∉ regionSet p.bv sb.val := by rw [regionSet_iff _ _ _ hsb hfit]; exact hppout
  obtain ⟨cs, hk, hwf, -⟩ := hR.cnode pp rs hpp
  have hg : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ = ({(.untypedCap dev p.bv sb.val fi.val, σ)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := hR.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl (by simpa [hidx] using hpp)
    rw [hcap] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  have h16 : 16 ∣ 2 ^ sb.val := by
    have := Nat.pow_dvd_pow 2 hsb4; simpa using this
  have hmod : ∀ d, d ∣ 2 ^ sb.val → p.val % d = 0 := by
    intro d hd; have := Nat.mod_mod_of_dvd p.val hd; rw [hpal, Nat.zero_mod] at this; exact this.symm
  have hp8 : p.bv.toNat % 8 = 0 := hmod 8 (dvd_trans (by norm_num) h16)
  have hfib : fi.val ≤ 2 ^ sb.val := hU.fib x hxm _ _ _ _ hcv
  have hP' : Placed th' := hP.restrict
  -- a state of FL4 for the spec's state after a complete reset
  have hpow : (⟨BitVec.ofNat 64 (2 ^ sb.val)⟩ : U64).val = 2 ^ sb.val := by
    show (BitVec.ofNat 64 (2 ^ sb.val)).toNat = _
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hsb)
  have hrel0 : ResetRel th' G x p sb dev (L.mem s) (Fl4Spec.detype (regionSet p.bv sb.val) σ) fi := by
    obtain ⟨h1, h2, h3, h4⟩ := detype_rel (σd := Fl4Spec.detype (regionSet p.bv sb.val) σ) hR hV hP hM hC
      hI hU hxm hcv hnd hN hns
      (fun q hq => by simp only [Fl4Spec.detype]; rw [if_neg (by rw [regionSet_iff _ _ _ hsb hfit]; exact hq)]) rfl rfl
    exact ⟨h1, h2, h3, h4, hI, hU, hcv⟩
  have hcsD : (Fl4Spec.detype (regionSet p.bv sb.val) σ).kheap pp.bv = some (.cnode rs cs) :=
    detype_hasCN hk hpb (KSame.refl _)
  have hW : ∃ sc : S, ResetRel th' G x p sb dev (L.mem sc)
        (setCnodeSlot (Fl4Spec.detype (regionSet p.bv sb.val) σ) pp.bv rs cs idx
          (.untypedCap dev p.bv sb.val (0#u64 : U64).val)) 0#u64 ∧
      (dev = false → ZeroRegion (L.mem sc) (p.val + (0#u64 : U64).val) (p.val + 2 ^ sb.val)) ∧
      (∀ y, IsSlot th' y → y ≠ x → capV (L.mem sc) y = capV (L.mem s) y) ∧ E sc := by
    cases dev with
    | false =>
      obtain ⟨hRz, hzz⟩ := reset_zero_step hP hN hrel0 hxs' p ⟨BitVec.ofNat 64 (2 ^ sb.val)⟩ hp8
        (by rw [hpow]; omega) (le_refl _) (by rw [hpow]) hfit
      obtain ⟨sc, hsc, cs', hk', hwf', hRc, hfrc, hcoc⟩ := spec_exists
        (reset_set_step (L := L) hP hpp' hidx hRz hnd 0#u64 (by simp))
      obtain ⟨sc', hsc', hEc⟩ := spec_exists (hEk.2 _ (.Untyped p sb 0#u64 false)
        (hEk.1 s p ⟨BitVec.ofNat 64 (2 ^ sb.val)⟩ hp8 (by rw [hpow]; omega) (le_refl _) (by rw [hpow]) hE))
      rw [hsc] at hsc'; cases eq_of_ok_eq hsc'
      rw [← hxdef] at hfrc hcoc
      have e : cs' = cs := by rw [hcsD] at hk'; cases hk'; rfl
      subst e
      have hZc : ZeroRegion (L.mem sc) (p.val + (0#u64 : U64).val) (p.val + 2 ^ sb.val) := by
        intro w hw h1 h2
        have h1' : p.val ≤ w.val := by simpa using h1
        have hxw := hxs'.restrict_words hP hN
        rw [hfrc w hw (by omega) (by omega), hzz w hw, if_pos (by rw [hpow]; omega)]
      have hS0 : SlotsSame th' (L.mem s) (L.mem (L.zr s p ⟨BitVec.ofNat 64 (2 ^ sb.val)⟩)) :=
        slotsSame_out hP' (fun b hb => hb.restrict_words hP hN) (fun w hw ho => by
          rw [hzz w hw, if_neg (by rw [hpow]; omega)])
      have hFc : ∀ y, IsSlot th' y → y ≠ x → capV (L.mem sc) y = capV (L.mem s) y := fun y hy hyx => by
        rw [hcoc y hy hyx, hS0.capV hy]
      exact ⟨sc, hRc, fun _ => hZc, hFc, hEc⟩
    | true =>
      obtain ⟨sc, hsc, cs', hk', hwf', hRc, hfrc, hcoc⟩ := spec_exists
        (reset_set_step (L := L) hP hpp' hidx hrel0 hnd 0#u64 (by simp))
      obtain ⟨sc', hsc', hEc⟩ := spec_exists (hEk.2 _ (.Untyped p sb 0#u64 true) hE)
      rw [hsc] at hsc'; cases eq_of_ok_eq hsc'
      rw [← hxdef] at hcoc
      have e : cs' = cs := by rw [hcsD] at hk'; cases hk'; rfl
      subst e
      exact ⟨sc, hRc, fun h => absurd h (by decide), hcoc, hEc⟩
  obtain ⟨sc, hRc, hZc, hFc, hEc⟩ := hW
  -- the spec: no failure
  have hNS : NSat (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv rb t usv slots
      dev)).run σ (fun _ => True) := by
    rw [invoke_true_eq]
    apply nsatE_bind
    refine (reset_nsat_ok hk hwf hidx hg hfi0 hp8 hpb hrcb hppS hfib).mono (fun y hy => ?_)
    rcases y with ⟨e | u, s1⟩
    · trivial
    · have hK := hy rfl
      obtain ⟨⟨r1, t2, a2⟩, -, hpost⟩ := spec_exists (hRT sc ar s1 (hRc.of_same (SlotsSame.refl _ _) hxs' hK)
        hZc hFc (by rw [hK.2.2.1]; rfl) (by rw [hK.2.2.2]; rfl)
        (fun x hx hx2 => by
          rw [hK.1]; simp only [setCnodeSlot, Function.update_of_ne hx2, Fl4Spec.detype]; rw [if_neg hx]) hEc)
      obtain ⟨-, σ', G', th'', hrun, -⟩ := hpost
      exact nsat_det hrun trivial
  -- the reset as an MDB step: the untyped cap's free index lowered, nothing else
  have hstep : ∀ (m1 : U64 → U64) (σ' : Fl4Spec.State Unit) (f : U64),
      ResetRel th' G x p sb dev m1 σ' f → σ'.isOriginalCap = σ.isOriginalCap →
      (∀ y, IsSlot th' y → y ≠ x → capV m1 y = capV (L.mem s) y) → MdbStep (L.mem s) G m1 G := by
    intro m1 σ' f hRR ho hF
    have hns' : ∀ z ∈ G.chains.flatten, IsSlot th' z := fun z hz =>
      ((hM.members z).1 hz).1.restrict hP hN (hns z hz)
    refine MdbStep.setFi hM hI hxm hcv hRR.cap (hRR.U.fib x ((hRR.M.members x).2
      ⟨hxs', _, capAt_capV _ _, by rw [hRR.cap]; simp⟩) _ _ _ _ hRR.cap) (Or.inr hnd)
      (fun z hz hzx => hF z (hns' z hz) hzx) (fun z hz => ?_)
    obtain ⟨sl, hA, rfl⟩ := isSlot_abs' ((hM.members _).1 hz).1
    rw [← hRR.C.orig sl (hA.restrict hP hN (hns _ hz)), ← hC.orig sl hA, ho]
  have hNO := reset_nsatO hk hwf hidx hg hfi0 hp8 hpb hrcb hppS
  have hio : ∀ e σ', NHas (Fl4Spec.resetUntypedCap (Z := Unit) (pp.bv, idx)).run σ (TopP e σ') →
      σ'.isOriginalCap = σ.isOriginalCap := by
    rintro e σ' ⟨y, hy, -, hK⟩
    rw [← hK.2.2.1]; exact hNO.2 y hy
  -- FL4: the reset, then the retype
  rw [retype_true_eq]
  obtain ⟨⟨r1, s1, a1⟩, hres, hNSr, σ', f, hcase, hRR, hZ, hF, hE1⟩ := spec_exists
    (reset_untyped_refines (L := L) arI th s ar σ G hR hV hP hM hC hI hU hpp hidx hcap hfi0 hnd hpal hsb4 hN hns hzero
      hrcb hppS hPP hEk hE)
  rw [hres]
  simp only [bind_ok, uncurry_apply_pair]
  rcases hcase with ⟨h1, hf0, hhas⟩ | ⟨h1, hhas⟩
  · simp only at h1; subst h1 hf0
    simp only
    obtain ⟨y, hy, hy1, hy2⟩ := hhas
    have hKy := (reset_nsat_ok hk hwf hidx hg hfi0 hp8 hpb hrcb hppS hfib).2 y hy hy1
    refine WP.spec_mono (hRT s1 a1 y.2 (hRR.of_same (SlotsSame.refl _ _) hxs' hy2) (fun hd => hZ (by rw [hd]; rfl)) hF
      (by rw [hKy.2.2.1]; rfl) (by rw [hKy.2.2.2]; rfl)
      (fun x hx hx2 => by
        rw [hKy.1]; simp only [setCnodeSlot, Function.update_of_ne hx2, Fl4Spec.detype]; rw [if_neg hx]) hE1) ?_
    · rintro res ⟨hr1, σf, G', th'', hrun, hP'', hR'', hV'', hM'', hC'', hI'', ⟨hU'', hSt''⟩, hFin, hks, hX, A, k, w,
        dslot, cj, hEx, hY⟩
      refine ⟨hNS, Or.inr ⟨hr1, σf, G', th'', ?_, hP'', hR'', hV'', hM'', hC'', hI'',
        ⟨hU'', (hstep _ _ _ hRR (hio _ _ ⟨y, hy, hy1, hy2⟩) hF).trans hSt''⟩,
        fun hFI => hFin (reset_fin_of hFI hM.tree.nodup hsb hfit hg hfi0 ⟨y, hy, rfl⟩ x
          (by rw [hRR.cap, hcv]; exact CapSim.of_shape rfl rfl) (fun z hz hzx => hF z ((hRR.M.members z).1 hz).1 hzx)),
        by rw [hks, hEksb _ hE1], ⟨s1, a1, rfl, hX⟩, A, k, w, dslot, cj, hEx.of_reset hM hP hN hns hcv hRR.cap hnd hF, hY⟩⟩
      rw [invoke_true_eq]
      apply nhasE_bind
      refine ⟨y, hy, ?_⟩
      rcases y with ⟨e1, s2⟩
      simp only at hy1; subst hy1
      exact nhas_det hrun ⟨rfl, KSame.refl _⟩
  · simp only at h1; subst h1
    simp only
    obtain ⟨y, hy, hy1, hy2⟩ := hhas
    refine (WP.spec_ok _).2 ⟨hNS, Or.inl ⟨rfl, σ', f, ?_, hRR,
      hstep _ _ _ hRR (hio _ _ ⟨y, hy, hy1, hy2⟩) hF,
      fun hFI => reset_fin_of hFI hM.tree.nodup hsb hfit hg hfi0 ⟨y, hy, hy2.1⟩ x
        (by rw [hRR.cap, hcv]; exact CapSim.of_shape rfl rfl) (fun z hz hzx => hF z ((hRR.M.members z).1 hz).1 hzx),
      hEksb _ hE1, rfl, fun dslot cj => RetExp.reset_only hM hP hN hns hxm hcv hRR.cap hnd hF⟩⟩
    rw [invoke_true_eq]
    apply nhasE_bind
    refine ⟨y, hy, ?_⟩
    rcases y with ⟨e1, s2⟩
    simp only at hy1; subst hy1
    exact ⟨rfl, hy2⟩


/-- The hypotheses of the retype after the reset, from the window of the
destination CNode (outside the region) being empty before it. -/
theorem reset_window {th : TypedHeap} (hP : Placed th) {p sb : U64} {x dest : U64} {r : Nat}
    (hdest : th dest = some (.cnode r)) (hdout : ¬ (p.val ≤ dest.val ∧ dest.val < p.val + 2 ^ sb.val))
    {m m1 : U64 → U64} (hx : capAt m x ≠ ok .Null) (off win : U64) (hwin : off.val + win.val ≤ 2 ^ r)
    (hempty : ∀ i : Nat, off.val ≤ i → i < off.val + win.val → capAt m (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null)
    (hF : ∀ y, IsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) y → y ≠ x → capV m1 y = capV m y) :
    restrictTh th p.val (p.val + 2 ^ sb.val) dest = some (.cnode r) ∧
    ∀ i : Nat, off.val ≤ i → i < off.val + win.val → capAt m1 (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null := by
  have hdest' : restrictTh th p.val (p.val + 2 ^ sb.val) dest = some (.cnode r) := by
    rw [restrictTh_out hdout]; exact hdest
  refine ⟨hdest', fun i h1 h2 => ?_⟩
  have hs : IsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) (slotAddr dest.bv (BitVec.ofNat 64 i)) :=
    ⟨dest, i, Or.inl ⟨r, hdest', by omega⟩, rfl⟩
  have hne : slotAddr dest.bv (BitVec.ofNat 64 i) ≠ x := fun e => hx (by rw [← e]; exact hempty i h1 h2)
  rw [capAt_capV, hF _ hs hne, ← capAt_capV]; exact hempty i h1 h2

/-- **`untyped::retype` with a reset refines `invoke_untyped` with
`reset = True`**, for the types 0, 2..7 and 9..13 (no CNodes from a device
region) from an untyped cap `Untyped p sb fi dev` (`fi ≠ 0`) without descendants (`retype_reset_gen`
with `retype_full`). -/
theorem retype_reset_full (ar : A') (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev)) (hfi0 : fi.val ≠ 0)
    (hnd : ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (pp.bv, idx)))
    (hpal : p.val % 2 ^ sb.val = 0) (hsb4 : 4 ≤ sb.val) (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (hN : NoStraddle th p.val (p.val + 2 ^ sb.val))
    (hns : ∀ a ∈ G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val)
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hrcb : Fl4Spec.resetChunkBits = 16) (hppS : PPFrame) {E : S → Prop} (hPP : PPHyp (L := L) arI th p sb E)
    (hEk : EKept (L := L) E p sb (cslotAddr (pp.bv, idx))) (hE : E s) (hEksb : ∀ t, E t → L.ksb t = L.ksb s)
    (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) sl)
    (nt us : U64) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hn : nt.val = 0 ∨ (2 ≤ nt.val ∧ nt.val ≤ 13 ∧ nt.val ≠ 8)) (hus : us.val < 64) (hz47 : zOf nt.val us.val ≤ 47)
    (hsc : nt.val = 5 → 7 ≤ us.val) (hct0 : nt.val = 4 → us.val ≠ 0)
    {dest : U64} {r : Nat} (hdest : th dest = some (.cnode r))
    (hdout : ¬ (p.val ≤ dest.val ∧ dest.val < p.val + 2 ^ sb.val)) (hr : r < 64)
    (off win : U64) (hwin : off.val + win.val ≤ 2 ^ r) (hw1 : 1 ≤ win.val)
    (hmem : win.val ≤ ((1#64 <<< sb.val : BitVec 64) - (0 : BitVec 64)).toNat >>> zOf nt.val us.val)
    (hempty : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null)
    (hdevT : dev = true → nt.val ≠ 4)
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (hb : bitsApi t us.val = zOf nt.val us.val) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) true
      ⟨Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)⟩ nt us dest off win dev ⦃ res =>
      NSat (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv
          (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev)).run σ (fun _ => True) ∧
      ((res.1 = .Err .Preempted ∧ ∃ σ' f,
          NHas (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv
            (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)) t us.val
            (windowSlots dest r off.val win.val) dev)).run σ (TopP (.error ()) σ') ∧
          ResetRel (restrictTh th p.val (p.val + 2 ^ sb.val)) G (cslotAddr (pp.bv, idx)) p sb dev
            (L.mem res.2.1) σ' f ∧ MdbStep (L.mem s) G (L.mem res.2.1) G ∧
          (FinInv th (L.mem s) σ G → FinInv (restrictTh th p.val (p.val + 2 ^ sb.val)) (L.mem res.2.1) σ' G) ∧
          L.ksb res.2.1 = L.ksb s ∧ untyped.reset_untyped st arI s ar (cslotAddr (pp.bv, idx)) = ok res ∧
          ∀ dslot cj, RetExp th (restrictTh th p.val (p.val + 2 ^ sb.val)) (L.mem s)
            (L.mem res.2.1) G G p.val 1 0 dslot cj (cslotAddr (pp.bv, idx))) ∨
       (res.1 = .Ok () ∧ ∃ σ' G' th'',
          NHas (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv
            (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)) t us.val
            (windowSlots dest r off.val win.val) dev)).run σ (fun y => y.1 = .ok () ∧ KSame σ' y.2) ∧
          Placed th'' ∧ StateRel th'' (L.mem res.2.1) σ' ∧ SlotsValid th'' (L.mem res.2.1) ∧
          MdbLinks th'' (L.mem res.2.1) G' ∧ CdtRel th'' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
          (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s) G (L.mem res.2.1) G') ∧
          (FinInv th (L.mem s) σ G → FinInv th'' (L.mem res.2.1) σ' G') ∧ L.ksb res.2.1 = L.ksb s ∧
          (∃ t1 a1, untyped.reset_untyped st arI s ar (cslotAddr (pp.bv, idx)) = ok (.Ok (), t1, a1) ∧
            WFrame (L := L) t1 res.2.1 (SlotSpan (restrictTh th p.val (p.val + 2 ^ sb.val))) ∧
            (dev = false → WinZero (L.mem res.2.1) (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat
              (2 ^ zOf nt.val us.val) win.val (t = .tcbObject))) ∧
          ∃ A k w dslot cj, RetExp th th'' (L.mem s) (L.mem res.2.1) G G' A k w dslot cj (cslotAddr (pp.bv, idx)) ∧
            A = (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat ∧ k = 2 ^ zOf nt.val us.val ∧ w = win.val ∧ (∀ j, j < w → isUt (cj j) = true → nt.val = 0) ∧ ThX (restrictTh th p.val (p.val + 2 ^ sb.val)) th'' A k w nt.val us.val ∧ cj = cjOf nt.val us dev A k ∧ DslotC (restrictTh th p.val (p.val + 2 ^ sb.val)) dslot w)) ⦄ := by
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hcv := capV_of_capAt hcap
  have hxm : cslotAddr (pp.bv, idx) ∈ G.chains.flatten :=
    (hM.members _).2 ⟨AbsSlot.isSlot ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩, _, hcap, by simp⟩
  have hrx := hU.reg _ hxm (by rw [hcv]; exact physF_ut _ _ _ _)
  rw [hcv] at hrx
  obtain ⟨-, -, hfit⟩ := ut_range hsb hrx
  refine retype_reset_gen arI ar th s σ G hR hV hP hM hC hI hU hpp hidx hcap hfi0 hnd hpal hsb4 hN hns hzero hrcb hppS
    hPP hEk hE _ nt us dest off win bitsApi _ t us.val _ (fun th'' t1 res => WFrame (L := L) t1 res.2.1 (SlotSpan (restrictTh th p.val (p.val + 2 ^ sb.val))) ∧
      (dev = false → WinZero (L.mem res.2.1) (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat
              (2 ^ zOf nt.val us.val) win.val (t = .tcbObject)))
    (fun th'' A k w dslot cj => A = (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat ∧ k = 2 ^ zOf nt.val us.val ∧ w = win.val ∧ (∀ j, j < w → isUt (cj j) = true → nt.val = 0) ∧ ThX (restrictTh th p.val (p.val + 2 ^ sb.val)) th'' A k w nt.val us.val ∧ cj = cjOf nt.val us dev A k ∧ DslotC (restrictTh th p.val (p.val + 2 ^ sb.val)) dslot w) ?_ hEksb
  intro t1 a1 σt hRR hZ hF hio _ _ _
  obtain ⟨hdest', he1⟩ := reset_window hP hdest hdout (by rw [hcap]; simp) off win hwin hempty hF
  have hcap1 : capAt (L.mem t1) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb 0#u64 dev) := by
    rw [capAt_capV, hRR.cap]
  have hpp' : restrictTh th p.val (p.val + 2 ^ sb.val) pp = some (.cnode rs) := by
    obtain ⟨q, j, hj, hq, he⟩ := (show AbsSlot th (pp.bv, idx) from ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩).at
    have : pp = q := bv_inj hq
    subst this
    rw [restrictTh_out (hj.obj_out hP hN (by rw [← he]; exact hns _ hxm))]; exact hpp
  refine WP.spec_mono (retype_full (L := L) arI a1 _ t1 σt G hRR.R hRR.V hP.restrict hRR.M hRR.C hRR.I hRR.U
    (fun sl h => horig sl (by rw [← hio]; exact h)) hpp' hidx hcap1 hpal hfit (by simp) hhigh nt us t ht hn hus hz47
    hsc hct0 hdest' hr off win hwin hw1 hmem he1 (by simpa using RegionFree.restrict hN) hZ hdevT bitsApi hb) ?_
  have hreg : p.val + (0#u64 : U64).val ≤ (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat ∧ (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat % 2 ^ zOf nt.val us.val = 0 ∧
      (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val ≤ p.val + 2 ^ sb.val ∧ _ :=
    retype_region p 0#u64 sb.val (zOf nt.val us.val) win.val hsb (by omega) hpal hfit (by simp) hw1 hmem
  have hsl : ∀ a, IsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) a → a.val + 32 ≤ (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat ∨
      (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val ≤ a.val := by
    intro a ha
    rcases ha.restrict_words hP hN with h | h
    · left; have := hreg.1; simp at this; omega
    · right; have := hreg.2.2.1; omega
  rintro res ⟨h1, -, σ', G', th'', hrun, hP'', hR'', hV'', hM'', hC'', hI'', hUS, -, hFin, hks, hWf, hEx⟩
  refine ⟨h1, σ', G', th'', hrun, hP'', hR'', hV'', hM'', hC'', hI'', hUS, hFin, hks, ⟨hWf, fun hd =>
    winZero_of_slots hWf (fun w hw e1 e2 => hZ hd w hw ?_ ?_) hsl _⟩, hEx⟩
  · have := hreg.1; simp at this ⊢; omega
  · have := hreg.2.2.1; omega


/-- `ksb` and a word outside the region and the untyped cap's slot are kept
by zeroing in the region and writing the slot. -/
theorem ekept_dw {th : TypedHeap} (hP : Placed th) {p sb x : U64} (hx : IsSlot th x) (dw : U64)
    (hdA : P1.Aligned dw) (hdR : ¬ (p.val ≤ dw.val ∧ dw.val < p.val + 2 ^ sb.val))
    (hdX : ¬ (x.val ≤ dw.val ∧ dw.val < x.val + 32)) (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (k0 v0 : U64) :
    EKept (L := L) (fun t => L.ksb t = k0 ∧ L.mem t dw = v0) p sb x := by
  refine ⟨fun s1 a n ha hn h1 h2 ⟨hk, hm⟩ => ⟨by simp [hk], ?_⟩, fun s1 c ⟨hk, hm⟩ => ?_⟩
  · rw [L.mem_zr s1 a n dw ha hn (by omega) hdA, if_neg (by omega)]; exact hm
  · apply WP.spec_mono (set_cap_spec x s1 c)
    rintro s' rfl
    refine ⟨by simp [hk], ?_⟩
    have hf := hx.fit hP
    have hal := hx.align hP
    rw [mem_wr2 _ _ _ _ _ dw (by unfold P1.Aligned; omega) (by unfold P1.Aligned; rw [wa8_val (by omega)]; omega) hdA,
      wa8_val (by omega), if_neg (by omega), if_neg (by omega)]
    exact hm

/-- **`untyped::retype` with a reset refines `invoke_untyped` with
`reset = True`** for TCBs (`retype_reset_gen` with `retype_full_tcb`), the
preemption point keeping `ksb` and the core-0 debug-list head word, which is
outside the region and the slots, and whose TCB (if any) is outside the
region. -/
theorem retype_reset_tcb (ar : A') (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false)) (hfi0 : fi.val ≠ 0)
    (hnd : ∀ y, ¬ Mdb.Desc G.par y (cslotAddr (pp.bv, idx)))
    (hpal : p.val % 2 ^ sb.val = 0) (hsb4 : 4 ≤ sb.val) (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (hN : NoStraddle th p.val (p.val + 2 ^ sb.val))
    (hns : ∀ a ∈ G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val)
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hrcb : Fl4Spec.resetChunkBits = 16) (hppS : PPFrame)
    (hPP : PPHyp (L := L) arI th p sb (fun t => L.ksb t = L.ksb s ∧
      L.mem t (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)))
    (hDWal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hDWobj : ∀ a, IsSlot th a → ¬ (a.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < a.val + 32))
    (hDWreg : ¬ (p.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < p.val + 2 ^ sb.val))
    (hhead : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      (th (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
        TcbOk (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))))
    (hheadR : ¬ (p.val ≤ (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val ∧
      (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val < p.val + 2 ^ sb.val))
    (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) sl)
    (nt us : U64) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hnt : nt.val = 1) (hus : us.val < 64)
    {dest : U64} {r : Nat} (hdest : th dest = some (.cnode r))
    (hdout : ¬ (p.val ≤ dest.val ∧ dest.val < p.val + 2 ^ sb.val)) (hr : r < 64)
    (off win : U64) (hwin : off.val + win.val ≤ 2 ^ r) (hw1 : 1 ≤ win.val)
    (hmem : win.val ≤ ((1#64 <<< sb.val : BitVec 64) - (0 : BitVec 64)).toNat >>> zOf nt.val us.val)
    (hempty : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null)
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (hb : bitsApi t us.val = zOf nt.val us.val) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) true
      ⟨Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)⟩ nt us dest off win false ⦃ res =>
      NSat (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv
          (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) false)).run σ (fun _ => True) ∧
      ((res.1 = .Err .Preempted ∧ ∃ σ' f,
          NHas (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv
            (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)) t us.val
            (windowSlots dest r off.val win.val) false)).run σ (TopP (.error ()) σ') ∧
          ResetRel (restrictTh th p.val (p.val + 2 ^ sb.val)) G (cslotAddr (pp.bv, idx)) p sb false
            (L.mem res.2.1) σ' f ∧ MdbStep (L.mem s) G (L.mem res.2.1) G ∧
          (FinInv th (L.mem s) σ G → FinInv (restrictTh th p.val (p.val + 2 ^ sb.val)) (L.mem res.2.1) σ' G) ∧
          L.ksb res.2.1 = L.ksb s ∧ untyped.reset_untyped st arI s ar (cslotAddr (pp.bv, idx)) = ok res ∧
          ∀ dslot cj, RetExp th (restrictTh th p.val (p.val + 2 ^ sb.val)) (L.mem s)
            (L.mem res.2.1) G G p.val 1 0 dslot cj (cslotAddr (pp.bv, idx))) ∨
       (res.1 = .Ok () ∧ ∃ σ' G' th'',
          NHas (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) true p.bv
            (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)) t us.val
            (windowSlots dest r off.val win.val) false)).run σ (fun y => y.1 = .ok () ∧ KSame σ' y.2) ∧
          Placed th'' ∧ StateRel th'' (L.mem res.2.1) σ' ∧ SlotsValid th'' (L.mem res.2.1) ∧
          MdbLinks th'' (L.mem res.2.1) G' ∧ CdtRel th'' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
          (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s) G (L.mem res.2.1) G') ∧
          (FinInv th (L.mem s) σ G → FinInv th'' (L.mem res.2.1) σ' G') ∧ L.ksb res.2.1 = L.ksb s ∧
          (∃ t1 a1, untyped.reset_untyped st arI s ar (cslotAddr (pp.bv, idx)) = ok (.Ok (), t1, a1) ∧
            WFrame (L := L) t1 res.2.1 (TcbLoopW (restrictTh th p.val (p.val + 2 ^ sb.val)) (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat win.val
              (L.nodeAt t1 0#u64 layout.node.DEBUG_TCBS) (L.mem t1 (L.nodeAt t1 0#u64 layout.node.DEBUG_TCBS))) ∧
            WinZero (L.mem res.2.1) (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat
              (2 ^ zOf nt.val us.val) win.val (t = .tcbObject) ∧
              (L.mem t1 (L.nodeAt t1 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨ th (L.mem t1 (L.nodeAt t1 0#u64 layout.node.DEBUG_TCBS)) = some .tcb)) ∧
          ∃ A k w dslot cj, RetExp th th'' (L.mem s) (L.mem res.2.1) G G' A k w dslot cj (cslotAddr (pp.bv, idx)) ∧
            A = (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat ∧ k = 2 ^ zOf nt.val us.val ∧ w = win.val ∧ (∀ j, j < w → isUt (cj j) = true → nt.val = 0) ∧ ThX (restrictTh th p.val (p.val + 2 ^ sb.val)) th'' A k w nt.val us.val ∧ cj = cjOf nt.val us false A k ∧ DslotC (restrictTh th p.val (p.val + 2 ^ sb.val)) dslot w)) ⦄ := by
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hcv := capV_of_capAt hcap
  have hxm : cslotAddr (pp.bv, idx) ∈ G.chains.flatten :=
    (hM.members _).2 ⟨AbsSlot.isSlot ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩, _, hcap, by simp⟩
  have hrx := hU.reg _ hxm (by rw [hcv]; exact physF_ut _ _ _ _)
  rw [hcv] at hrx
  obtain ⟨-, -, hfit⟩ := ut_range hsb hrx
  have hxs : IsSlot th (cslotAddr (pp.bv, idx)) := AbsSlot.isSlot ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  refine retype_reset_gen arI ar th s σ G hR hV hP hM hC hI hU hpp hidx hcap hfi0 hnd hpal hsb4 hN hns hzero hrcb hppS
    hPP (ekept_dw hP hxs _ hDWal hDWreg (hDWobj _ hxs) hfit _ _) ⟨rfl, rfl⟩ _ nt us dest off win bitsApi _ t us.val _ (fun th'' t1 res => WFrame (L := L) t1 res.2.1 (TcbLoopW (restrictTh th p.val (p.val + 2 ^ sb.val)) (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat win.val
              (L.nodeAt t1 0#u64 layout.node.DEBUG_TCBS) (L.mem t1 (L.nodeAt t1 0#u64 layout.node.DEBUG_TCBS))) ∧
      WinZero (L.mem res.2.1) (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat
              (2 ^ zOf nt.val us.val) win.val (t = .tcbObject) ∧
              (L.mem t1 (L.nodeAt t1 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨ th (L.mem t1 (L.nodeAt t1 0#u64 layout.node.DEBUG_TCBS)) = some .tcb))
    (fun th'' A k w dslot cj => A = (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat ∧ k = 2 ^ zOf nt.val us.val ∧ w = win.val ∧ (∀ j, j < w → isUt (cj j) = true → nt.val = 0) ∧ ThX (restrictTh th p.val (p.val + 2 ^ sb.val)) th'' A k w nt.val us.val ∧ cj = cjOf nt.val us false A k ∧ DslotC (restrictTh th p.val (p.val + 2 ^ sb.val)) dslot w) ?_
    (fun _ h => h.1)
  intro t1 a1 σt hRR hZ hF hio _ _ ⟨hk1, hm1⟩
  have hn1 := nodeAt_ksb (L := L) hk1 0#u64 layout.node.DEBUG_TCBS
  obtain ⟨hdest', he1⟩ := reset_window hP hdest hdout (by rw [hcap]; simp) off win hwin hempty hF
  have hcap1 : capAt (L.mem t1) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb 0#u64 false) := by
    rw [capAt_capV, hRR.cap]
  have hpp' : restrictTh th p.val (p.val + 2 ^ sb.val) pp = some (.cnode rs) := by
    obtain ⟨q, j, hj, hq, he⟩ := (show AbsSlot th (pp.bv, idx) from ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩).at
    have : pp = q := bv_inj hq
    subst this
    rw [restrictTh_out (hj.obj_out hP hN (by rw [← he]; exact hns _ hxm))]; exact hpp
  refine WP.spec_mono (retype_full_tcb (L := L) arI a1 _ t1 σt G hRR.R hRR.V hP.restrict hRR.M hRR.C hRR.I hRR.U
    (fun sl h => horig sl (by rw [← hio]; exact h)) hpp' hidx hcap1 hpal hfit (by simp) hhigh nt us t ht hnt hus
    hdest' hr off win hwin hw1 hmem he1 (by simpa using RegionFree.restrict hN) (hZ rfl)
    (by rw [hn1]; exact hDWal) (by rw [hn1]; intro a ha; exact hDWobj a ha.of_restrict)
    (by rw [hn1]; simpa using hDWreg)
    (by
      rw [hn1, hm1]
      rcases hhead with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨by rw [restrictTh_out hheadR]; exact h1, h2⟩) bitsApi hb) ?_
  have htT : t = .tcbObject := by rw [hnt] at ht; simpa [objTypeOf] using ht.symm
  have hreg : p.val + (0#u64 : U64).val ≤ (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat ∧ (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat % 2 ^ zOf nt.val us.val = 0 ∧
      (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val ≤ p.val + 2 ^ sb.val ∧ _ :=
    retype_region p 0#u64 sb.val (zOf nt.val us.val) win.val hsb (by simp [zOf, hnt]) hpal hfit (by simp) hw1 hmem
  have hr1 : p.val ≤ (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat := by
    have := hreg.1; rwa [show (0#u64 : U64).val = 0 from rfl, Nat.add_zero] at this
  have hr2 := hreg.2.2.1
  have hsl : ∀ a, IsSlot (restrictTh th p.val (p.val + 2 ^ sb.val)) a → a.val + 32 ≤ (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat ∨
      (Fl4Spec.alignUp (p.bv + (0 : BitVec 64)) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val ≤ a.val := by
    intro a ha
    rcases ha.restrict_words hP hN with h | h
    · left; omega
    · right; omega
  rintro res ⟨h1, -, σ', G', th'', hrun, hP'', hR'', hV'', hM'', hC'', hI'', hUS, -, hFin, hks, hWf, hEx⟩
  have e0 : U64.bv 0#u64 = (0 : BitVec 64) := rfl
  rw [e0] at hWf
  refine ⟨h1, σ', G', th'', hrun, hP'', hR'', hV'', hM'', hC'', hI'', hUS, hFin, hks, ⟨hWf, fun w hw e1 e2 =>
    ((winZero_of_frame hWf (fun w hw e1 e2 => hZ rfl w hw (by rw [show (0#u64 : U64).val = 0 from rfl]; omega) (by omega)) hsl ?_ ?_) w hw e1 e2).imp id
      (fun ⟨_, hj⟩ => ⟨htT, hj⟩), by rw [hn1, hm1]; exact hhead.imp id (fun h => h.1)⟩, hEx⟩
  · rw [hn1]; intro h; exact hDWreg ⟨by omega, by omega⟩
  · rw [hn1, hm1]; intro hne h
    rcases hhead with e | ⟨hq, -⟩
    · exact hne e
    · have e4 : objSize ObjKind.tcb = 4096 := rfl
      rcases hN _ _ hq with h' | h' | h'
      · exact hheadR ⟨h'.1, by omega⟩
      · omega
      · omega

end

end

end Fl4Proofs.P3
