/-
P3 (DESIGN.md §9), CSpace: **finalising a cap**, for `rec_del`. What the
spec's finality says about the other slots (no other cap shares an object
with a final cap), the same-region facts for zombies, and FL4's
`finalise_cap` against the spec's `finalise_cap` for the caps whose
finalisation is CSpace work: CNode caps (to a zombie), zombies (unchanged),
and the caps whose finalisation does nothing.
-/
import Fl4Proofs.P3.DelAbs
import Fl4Proofs.P3.DelSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## A slot of the typed heap, as the spec names it -/

theorem IsSlot.abs {th : TypedHeap} {y : U64} (h : IsSlot th y) : ∃ sl, AbsSlot th sl ∧ cslotAddr sl = y := by
  obtain ⟨p, i, hi, rfl⟩ := h
  rcases hi with ⟨r, hp, hir⟩ | ⟨ht, hit⟩
  · refine ⟨(p.bv, bitsOf i r), ⟨p, rfl, Or.inl (by simpa using hp)⟩, ?_⟩
    show slotAddr p.bv (Fl4Spec.ofBl _) = _
    rw [slotAddr_ofBl, blVal_bitsOf, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hir]
  · refine ⟨(p.bv, Fl4Spec.tcbCnodeIndex i), ⟨p, rfl, Or.inr ⟨ht, i, hit, rfl⟩⟩, ?_⟩
    show slotAddr p.bv (Fl4Spec.ofBl _) = _
    rw [slotAddr_ofBl, tcbCnodeIndex_blVal i hit]

/-! ## Finality -/

section
open Fl4Spec

/-- **A final cap shares no object with the cap of any other slot.** -/
theorem final_disjoint {σ : State Unit} {xsl ysl : CslotPtr} {ax ay : Cap}
    (hgx : getCap (Z := Unit) xsl σ = ({(ax, σ)}, False)) (hgy : getCap (Z := Unit) ysl σ = ({(ay, σ)}, False))
    (hne : xsl ≠ ysl) (hnx : genObjRefs ax ≠ ∅) (hf : isFinalCap' ax σ) :
    genObjRefs ax ∩ genObjRefs ay = ∅ := by
  obtain ⟨cref, hset⟩ := hf
  have hx : xsl ∈ {cref' : CslotPtr | ∃ cap', ((getCap (Z := Unit) cref' : SMonad Unit Cap) σ).1 = {(cap', σ)} ∧
      genObjRefs ax ∩ genObjRefs cap' ≠ ∅} := ⟨ax, by rw [hgx], by simpa using hnx⟩
  rw [hset] at hx
  by_contra hov
  have hy : ysl ∈ {cref' : CslotPtr | ∃ cap', ((getCap (Z := Unit) cref' : SMonad Unit Cap) σ).1 = {(cap', σ)} ∧
      genObjRefs ax ∩ genObjRefs cap' ≠ ∅} := ⟨ay, by rw [hgy], hov⟩
  rw [hset] at hy
  exact hne ((Set.mem_singleton_iff.1 hx).trans (Set.mem_singleton_iff.1 hy).symm)

theorem genObjRefs_obj {c : Cap} {r : ObjRef} (h : r ∈ objRefs c) : GenObjRef.objRef r ∈ genObjRefs c :=
  Or.inl (Or.inl ⟨r, h, rfl⟩)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- In related states, a final cap's object is in no other slot's cap. -/
theorem final_other {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} (hR : StateRel th (L.mem s) σ)
    (hP : Placed th) {xsl : Fl4Spec.CslotPtr} (hxs : AbsSlot th xsl) {cx : capability.Cap}
    (hcx : capAt (L.mem s) (cslotAddr xsl) = ok cx) (hfin : Fl4Spec.isFinalCap' (absCap cx) σ)
    {r : Fl4Spec.ObjRef} (hr : r ∈ Fl4Spec.objRefs (absCap cx))
    {y : U64} (hy : IsSlot th y) (hyx : y ≠ cslotAddr xsl) : r ∉ Fl4Spec.objRefs (absCap (capV (L.mem s) y)) := by
  obtain ⟨ysl, hys, rfl⟩ := hy.abs
  obtain ⟨cx', ax, hcx', hax, hgx⟩ := hR.abs_cap hxs
  rw [hcx] at hcx'; cases eq_of_ok_eq hcx'
  obtain ⟨cy, ay, hcy, hay, hgy⟩ := hR.abs_cap hys
  rw [hax.abs] at hgx
  rw [hay.abs] at hgy
  have hne : xsl ≠ ysl := fun e => hyx (by rw [e])
  have hd := final_disjoint hgx hgy hne (fun h => by
    have := genObjRefs_obj hr; rw [h] at this; exact this) hfin
  intro hry
  rw [capV_of_capAt hcy] at hry
  have h1 := genObjRefs_obj hr
  have h2 := genObjRefs_obj hry
  have : Fl4Spec.GenObjRef.objRef r ∈ Fl4Spec.genObjRefs (absCap cx) ∩ Fl4Spec.genObjRefs (absCap cy) := ⟨h1, h2⟩
  rw [hd] at this; exact this

end

/-! ## Same-region facts for zombies -/

theorem sr_ut_congr (p sb fi : U64) (d : Bool) {b b' : capability.Cap}
    (hph : objects.cap_is_physical b = objects.cap_is_physical b')
    (hp : capability.Cap.ptr b = capability.Cap.ptr b')
    (hs : objects.cap_size_bits b = objects.cap_size_bits b') :
    objects.same_region_as (.Untyped p sb fi d) b = objects.same_region_as (.Untyped p sb fi d) b' := by
  simp only [objects.same_region_as, hph, hp, hs]

/-- A cap that is not an untyped cap has no zombie in its region. -/
theorem srB_nonut_zombie {a : capability.Cap} (ha : isUt a = false) (p zt n : U64) :
    srB a (.Zombie p zt n) = false := by
  apply srB_of_eq
  cases a <;> simp [isUt] at ha <;> rfl

end

theorem zombie_tcb_val : capability.ZOMBIE_TCB.val = 65 := by simp [capability.ZOMBIE_TCB]

theorem srB_ut_zombie_cnode (q sb fi : U64) (d : Bool) (p r gs g n : U64) (hr : r.val ≠ 65) :
    srB (.Untyped q sb fi d) (.Zombie p r n) = srB (.Untyped q sb fi d) (.CNode p r gs g) := by
  have hne : ¬ r = capability.ZOMBIE_TCB := by intro h; apply hr; rw [h, zombie_tcb_val]
  have e := sr_ut_congr q sb fi d (b := .Zombie p r n) (b' := .CNode p r gs g) rfl rfl
    (by simp only [objects.cap_size_bits, hne, ↓reduceIte])
  rw [srB_eq, srB_eq] at e; exact eq_of_ok_eq e

theorem srB_ut_zombie_tcb (q sb fi : U64) (d : Bool) (p n : U64) :
    srB (.Untyped q sb fi d) (.Zombie p capability.ZOMBIE_TCB n) = srB (.Untyped q sb fi d) (.Thread p) := by
  have e := sr_ut_congr q sb fi d (b := .Zombie p capability.ZOMBIE_TCB n) (b' := .Thread p) rfl rfl
    (by simp only [objects.cap_size_bits, ↓reduceIte])
  rw [srB_eq, srB_eq] at e; exact eq_of_ok_eq e

theorem srB_ut_zombie_zombie (q sb fi : U64) (d : Bool) (p zt n n' : U64) :
    srB (.Untyped q sb fi d) (.Zombie p zt n') = srB (.Untyped q sb fi d) (.Zombie p zt n) := by
  have e := sr_ut_congr q sb fi d (b := .Zombie p zt n') (b' := .Zombie p zt n) rfl rfl
    (by simp only [objects.cap_size_bits])
  rw [srB_eq, srB_eq] at e; exact eq_of_ok_eq e

end Fl4Proofs.P3
