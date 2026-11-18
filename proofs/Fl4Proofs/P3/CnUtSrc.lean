/-
P3 (DESIGN.md §9), CSpace: **where the untyped caps after a CNode copy, move
or rotate come from** (`UtSrc`, SlotLive), from FL4's slot changes and the
MDB ghost after (`insG`, `renG`), through the CDT relations before and after
(`CdtRel.has_child_iff`):

* `utSrc_ins`: an insertion (`cdt::insert`): the destination's untyped cap
  is the source's, which had no child; the source's, set full, has the
  destination as a child; every other slot's children kept.
* `utSrc_swap`: a renaming of two slots (`cdt::move_cap`, `cdt::swap`):
  each slot's untyped cap is the other's before, with its children.
-/
import Fl4Proofs.P3.FinOps
import Fl4Proofs.P3.SlotLive
import Fl4Proofs.P3.SlotCover
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

variable {th : TypedHeap} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {G G' : MdbGhost}

/-- One single outcome equal to another names the same state. -/
theorem nd_single_inj {α τ : Type} {a a' : α} {x y : τ}
    (h : (({(a, x)} : Set (α × τ)), False) = ({(a', y)}, False)) : x = y := by
  have h1 := congrArg Prod.fst h
  simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq] at h1
  exact h1.2

/-- **An untyped cap of the MDB is a parent of its copy** (`isPF`: it is
revocable, `utrev`, and of its own region, `self`). -/
theorem isPF_ut {mem : U64 → U64} (hI : MdbInv mem G) {x : U64} (hx : x ∈ G.chains.flatten) {srcC : capability.Cap}
    (hsc : capV mem x = srcC) (hu : isUt srcC = true) (fb : Bool) : isPF (revOf mem x) srcC srcC fb = true := by
  have hzb : isZb srcC = false := by cases srcC <;> simp_all [isUt, isZb]
  have hr := hI.utrev x hx (by rw [hsc]; exact hu)
  have hs := hI.self x hx (by rw [hsc]; exact hzb)
  unfold srM at hs; rw [hsc] at hs
  have hb : isBadged srcC = false := by cases srcC <;> simp_all [isUt, isBadged]
  simp [isPF, hr, hs, hb]

/-- **An insertion's untyped caps** (`cdt::insert`, `insG`). -/
theorem utSrc_ins (hP : Placed th) (hM : MdbLinks th m G) (hC : CdtRel th m σ G) (hC' : CdtRel th m' σ' G')
    {ss ds : Fl4Spec.CslotPtr} (hsA : AbsSlot th ss)
    {srcC c : capability.Cap} (hsc : capV m (cslotAddr ss) = srcC) (hdn : capV m (cslotAddr ds) = .Null)
    (hc' : capV m' (cslotAddr ds) = c) (hs' : capV m' (cslotAddr ss) = (fullF srcC c).getD srcC)
    (ho : ∀ y, IsSlot th y → y ≠ cslotAddr ss → y ≠ cslotAddr ds → capV m' y = capV m y)
    (hsh : shape c = shape srcC) (hutc : isUt srcC = true → c = srcC)
    (hnc : isUt srcC = true → ∀ y, ¬ Mdb.Desc G.par y (cslotAddr ss))
    (hsb : ∀ p sb fi d, srcC = .Untyped p sb fi d → sb.val < 64)
    {b : Bool} (hG' : G' = insG G (cslotAddr ss) (cslotAddr ds) b) (hb : isUt srcC = true → b = true) :
    UtSrc th m m' σ σ' := by
  intro sl p sb fi d hsl hc
  have hdm : cslotAddr ds ∉ G.chains.flatten := fun h => by
    obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h
    rw [capAt_capV, hdn] at h0
    exact hn (eq_of_ok_eq h0).symm
  have hpar' : ∀ a, G'.par a = Function.update G.par (cslotAddr ds)
      (if b then some (cslotAddr ss) else G.par (cslotAddr ss)) a := by
    intro a; rw [hG']; rfl
  -- a child before stays one
  have keep : ∀ sl1, AbsSlot th sl1 → (¬ ∃ x, σ'.cdt x = some sl1) → ¬ ∃ x, σ.cdt x = some sl1 := by
    intro sl1 hs1 h0 h1
    apply h0
    obtain ⟨a, ha⟩ := (hC.has_child_iff hP hs1).1 h1
    have ham : a ∈ G.chains.flatten := (hM.tree.par_mem _ _ ha).1
    have had : a ≠ cslotAddr ds := fun e => hdm (e ▸ ham)
    exact (hC'.has_child_iff hP hs1).2 ⟨a, by rw [hpar', Function.update_of_ne had]; exact ha⟩
  by_cases ed : cslotAddr sl = cslotAddr ds
  · rw [ed, hc'] at hc
    have hu : isUt srcC = true := by rw [← isUt_of_shape hsh, hc]; rfl
    refine ⟨ss, fi, hsA, by rw [hsc, ← hutc hu, hc], Or.inl ⟨rfl, fun _ h1 => ?_⟩⟩
    obtain ⟨a, ha⟩ := (hC.has_child_iff hP hsA).1 h1
    exact hnc hu a (Relation.TransGen.single ha)
  by_cases es : cslotAddr sl = cslotAddr ss
  · rw [es, hs'] at hc
    cases hf : fullF srcC c with
    | none =>
      rw [hf, Option.getD_none] at hc
      exact ⟨sl, fi, hsl, by rw [es, hsc, hc], Or.inl ⟨rfl, keep sl hsl⟩⟩
    | some v =>
      rw [hf, Option.getD_some] at hc
      subst hc
      obtain ⟨p1, b1, f1, d1, rfl⟩ : ∃ p1 b1 f1 d1, srcC = .Untyped p1 b1 f1 d1 := by
        cases srcC <;> simp [fullF] at hf; exact ⟨_, _, _, _, rfl⟩
      obtain ⟨p2, b2, f2, d2, rfl⟩ : ∃ p2 b2 f2 d2, c = .Untyped p2 b2 f2 d2 := by
        cases c <;> simp [fullF] at hf; exact ⟨_, _, _, _, rfl⟩
      simp only [fullF] at hf
      split_ifs at hf with hpb
      simp only [Option.some.injEq, capability.Cap.Untyped.injEq] at hf
      obtain ⟨rfl, rfl, hfi, rfl⟩ := hf
      have hu : isUt (capability.Cap.Untyped p1 b1 f1 d1) = true := rfl
      refine ⟨sl, f1, hsl, by rw [es, hsc], Or.inr ⟨?_, ?_⟩⟩
      · rw [← hfi]; exact shl_one_val (hsb _ _ _ _ rfl)
      · refine (hC'.has_child_iff hP hsl).2 ⟨cslotAddr ds, ?_⟩
        rw [hpar', Function.update_self, hb hu, if_pos rfl, es]
  · exact ⟨sl, fi, hsl, by rw [← ho _ hsl.isSlot es ed]; exact hc, Or.inl ⟨rfl, keep sl hsl⟩⟩

/-- **A renaming's untyped caps** (`cdt::move_cap`, `cdt::swap`, `renG` by
the swap of the two slots): each slot's untyped cap after is the other's
before, whose children it takes. -/
theorem utSrc_swap (hP : Placed th) (hC : CdtRel th m σ G) (hC' : CdtRel th m' σ' G')
    {s1 s2 : Fl4Spec.CslotPtr} (h1A : AbsSlot th s1) (h2A : AbsSlot th s2)
    (hG' : G' = renG G (Equiv.swap (cslotAddr s1) (cslotAddr s2)))
    (hc1 : ∀ p sb fi d, capV m' (cslotAddr s1) = .Untyped p sb fi d → capV m (cslotAddr s2) = .Untyped p sb fi d)
    (hc2 : ∀ p sb fi d, capV m' (cslotAddr s2) = .Untyped p sb fi d → capV m (cslotAddr s1) = .Untyped p sb fi d)
    (ho : ∀ y, IsSlot th y → y ≠ cslotAddr s1 → y ≠ cslotAddr s2 → capV m' y = capV m y) :
    UtSrc th m m' σ σ' := by
  intro sl p sb fi d hsl hc
  set e := Equiv.swap (cslotAddr s1) (cslotAddr s2) with he
  have hpar : ∀ a z, G.par a = some z → G'.par (e a) = some (e z) := by
    intro a z h
    rw [hG']
    show (G.par (e.symm (e a))).map e = some (e z)
    rw [Equiv.symm_apply_apply, h]; rfl
  -- a child of `z` before makes one of `e z` after
  have keep : ∀ sl0 sl1, AbsSlot th sl0 → AbsSlot th sl1 → cslotAddr sl1 = e (cslotAddr sl0) →
      (¬ ∃ x, σ'.cdt x = some sl1) → ¬ ∃ x, σ.cdt x = some sl0 := by
    intro sl0 sl1 hs0 hs1 he1 h0 h1
    apply h0
    obtain ⟨a, ha⟩ := (hC.has_child_iff hP hs0).1 h1
    exact (hC'.has_child_iff hP hs1).2 ⟨e a, by rw [hpar a _ ha, he1]⟩
  by_cases e1 : cslotAddr sl = cslotAddr s1
  · rw [e1] at hc
    exact ⟨s2, fi, h2A, hc1 _ _ _ _ hc, Or.inl ⟨rfl, keep s2 sl h2A hsl (by rw [e1, he, Equiv.swap_apply_right])⟩⟩
  by_cases e2 : cslotAddr sl = cslotAddr s2
  · rw [e2] at hc
    exact ⟨s1, fi, h1A, hc2 _ _ _ _ hc, Or.inl ⟨rfl, keep s1 sl h1A hsl (by rw [e2, he, Equiv.swap_apply_left])⟩⟩
  · exact ⟨sl, fi, hsl, by rw [← ho _ hsl.isSlot e1 e2]; exact hc,
      Or.inl ⟨rfl, keep sl sl hsl hsl (by rw [he, Equiv.swap_apply_of_ne_of_ne e1 e2])⟩⟩

end

end Fl4Proofs.P3
