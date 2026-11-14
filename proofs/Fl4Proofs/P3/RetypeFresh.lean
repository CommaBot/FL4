/-
P3 (DESIGN.md §9), untyped: the caps `retype` inserts are fresh for `FinM`,
and the spec's `create_cap` creates no CNode or TCB.

A cap `retype` inserts (`NewKind`, non-empty range) overlaps no cap whose range
misses its own, nor any untyped cap: the generic object references of a
physical cap are at most its object (`objRef_mem`), an untyped cap has none,
and the new caps have only object references (`refs_newKind`). With
`srB_new_left` / `srB_new_right`, such a cap is `same_region_as` neither way
with those caps either (`fresh_new`), which is what `FinM.fresh_ins` asks of
it.
-/
import Fl4Proofs.P3.UntypedMdb
import Fl4Proofs.P3.CancelKSub
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

/-- An object reference of a cap is its object's, and the cap is physical and
not an untyped one. -/
theorem objRef_mem {c : capability.Cap} {q : Fl4Spec.ObjRef}
    (h : Fl4Spec.GenObjRef.objRef q ∈ Fl4Spec.genObjRefs (absCap c)) :
    physF c = true ∧ isUt c = false ∧ q = (ptrF c).bv := by
  cases c <;> simp [Fl4Spec.genObjRefs, Fl4Spec.objRefs, Fl4Spec.capIrqs, Fl4Spec.capIrqOpt, Fl4Spec.archGenRefs,
      Fl4Spec.archCapSetMap, Fl4Spec.archGenObjRefs, Fl4Spec.aobjRef, absCap] at h <;>
    refine ⟨ok_inj (phys_eq _).symm, rfl, ?_⟩ <;> rw [h] <;> congr 1 <;> apply ok_inj <;> rw [← ptr_eq] <;> rfl

/-- The generic references of a new cap are object references. -/
theorem refs_newKind {c : capability.Cap} (hk : NewKind c) {r : Fl4Spec.GenObjRef}
    (h : r ∈ Fl4Spec.genObjRefs (absCap c)) : ∃ q, r = .objRef q := by
  cases c <;> simp [NewKind] at hk <;>
    simp [Fl4Spec.genObjRefs, Fl4Spec.objRefs, Fl4Spec.capIrqs, Fl4Spec.capIrqOpt, Fl4Spec.archGenRefs,
      Fl4Spec.archCapSetMap, Fl4Spec.archGenObjRefs, Fl4Spec.aobjRef, absCap] at h <;> exact ⟨_, h⟩

theorem isFrame_isFr (c : capability.Cap) : isFrame c = isFr c := by cases c <;> rfl

/-- **A new cap is fresh** against a cap that, when physical, is an untyped one
or misses its range (`FinM.fresh_ins`' condition). -/
theorem fresh_new {c w : capability.Cap} (hk : NewKind c) (hcr : baseF c ≤ topF c)
    (hw : physF w = true → baseF w ≤ topF w ∧ (Disj w c ∨ isUt w = true)) :
    ¬ Ovl (absCap c) (absCap w) ∧ (isFrame c = true → srB c w = false) ∧
      (isFrame w = true → srB w c = false) := by
  refine ⟨fun hov => ?_, fun hf => ?_, fun hf => ?_⟩
  · obtain ⟨r, hr1, hr2⟩ := Set.nonempty_iff_ne_empty.2 hov
    obtain ⟨q, rfl⟩ := refs_newKind hk hr1
    obtain ⟨hpc, huc, hq1⟩ := objRef_mem hr1
    obtain ⟨hpw, huw, hq2⟩ := objRef_mem hr2
    obtain ⟨hwr, hd | hu⟩ := hw hpw
    · have : (ptrF c).val = (ptrF w).val := by
        show (ptrF c).bv.toNat = (ptrF w).bv.toNat; rw [← hq1, ← hq2]
      unfold Disj baseF at *; omega
    · rw [hu] at huw; cases huw
  · have huc : isUt c = false := by cases c <;> simp [isFrame] at hf; rfl
    cases e : srB c w
    · rfl
    obtain ⟨hpw, huw, h1, h2, h3⟩ := srB_new_left hk huc hcr e
    rcases (hw hpw).2 with hd | hu
    · unfold Disj at hd; omega
    · rw [hu] at huw; cases huw
  · have huw : isUt w = false := by cases w <;> simp [isFrame] at hf; rfl
    cases e : srB w c
    · rfl
    cases huc : isUt c
    · obtain ⟨hpw, h1, h2⟩ := srB_new_right hk huc huw e
      rcases (hw hpw).2 with hd | hu
      · unfold Disj at hd; omega
      · rw [hu] at huw; cases huw
    · obtain ⟨q, sz, f, d, rfl⟩ := isUt_iff.1 huc
      rw [srB_to_ut e] at huw; cases huw

theorem nks_createCap (t : Fl4Spec.ApiObjectType) (bits : Nat) (untyped : Fl4Spec.CslotPtr) (dev : Bool)
    (x : Fl4Spec.CslotPtr × Fl4Spec.ObjRef) : NKS (Fl4Spec.createCap (Z := Unit) t bits untyped dev x) := by
  obtain ⟨d, o⟩ := x
  unfold Fl4Spec.createCap Fl4Spec.setCdt Fl4Spec.setOriginal
  nks_auto

theorem nks_initArchObjects (t : Fl4Spec.ApiObjectType) (dev : Bool) (ptr : Fl4Spec.ObjRef) (n sz : Nat)
    (refs : List Fl4Spec.ObjRef) : NKS (Fl4Spec.initArchObjects (Z := Unit) t dev ptr n sz refs) := by
  unfold Fl4Spec.initArchObjects
  refine nks_when (nks_mapMx (fun pm => ?_) _)
  unfold Fl4Spec.copyGlobalMappings
  refine nks_bind (nks_gets _) (fun _ => nks_bind (nks_pure _) (fun _ => nks_bind (nks_pure _)
    (fun _ => nks_bind (nks_pure _) (fun _ => nks_mapMx (fun i => ?_) _))))
  unfold Fl4Spec.getPml4e Fl4Spec.storePml4e Fl4Spec.getPml4 Fl4Spec.setPml4
  nks_auto

end Fl4Proofs.P3
