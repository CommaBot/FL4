/-
P3 (DESIGN.md §9), VSpace, line pte gen 13: **no page table at address 0, so no page-table leaf at 0**.

The PTE line's PageMap slot (P2/InvPmU.lean) needs the leaf `lookup_pt_slot` returns to be non-zero (the plan's
`Plan.add` skips `0`, so a leaf at `0` would be written unlocked). Arithmetically `table_of` can wrap to `0`. At a
`JAtZ` state it cannot, by the same route as `JAtZ.fnzJ` (no frame at 0):

* a table of `Z.L4` / `Z.L3` / `Z.L2` / `Z.L1` is a spec arch object at its address (`PtRel`), hence an object of `H`
  there (`SpecCover.arch`), and `H 0 = none` (`JKern.h0`): **`JAtZ.tab_ne0`**;
* the leaf is `peA q i` for a 4 KiB-aligned `q ∈ Z.L1` and `i < 512` (`lookup_pt_slot_rel`, `PtPlaced`), so its value
  is at least `q ≥ 4096`: **`JAtZ.ptLeaf_ne0`**.

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P3.VsUserApart
import Fl4Proofs.P3.VsDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Vs

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- An arch object of the spec is not at address 0 (`SpecCover.arch`, `JKern.h0`). -/
theorem JAtZ.arch_ne0 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {q : U64} {ao : Fl4Spec.ArchKernelObj}
    (h : σ.kheap q.bv = some (.archObj ao)) : q ≠ 0#u64 := by
  rintro rfl
  obtain ⟨n, -, hH⟩ := J.cover.arch _ _ h
  have h0 : H 0#u64 = none := J.kern.h0
  have e : (⟨(0#u64 : U64).bv⟩ : U64) = 0#u64 := rfl
  rw [e, h0] at hH
  cases hH

/-- **No page table of the VSpace sets is at address 0.** -/
theorem JAtZ.tab_ne0 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {q : U64}
    (hq : q ∈ Z.L4 ∨ q ∈ Z.L3 ∨ q ∈ Z.L2 ∨ q ∈ Z.L1) : q ≠ 0#u64 := by
  obtain ⟨-, -, hPt, -, -⟩ := J.xtop.fin
  rcases hq with hq | hq | hq | hq
  · obtain ⟨f, hf, -⟩ := hPt.l4 q hq; exact J.arch_ne0 hf
  · obtain ⟨f, hf, -⟩ := hPt.l3 q hq; exact J.arch_ne0 hf
  · obtain ⟨f, hf, -⟩ := hPt.l2 q hq; exact J.arch_ne0 hf
  · obtain ⟨f, hf, -⟩ := hPt.l1 q hq; exact J.arch_ne0 hf

/-- **The leaf `lookup_pt_slot` finds from a PML4 of `Z.L4` at a user address is not 0.** -/
theorem JAtZ.ptLeaf_ne0 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {root va e : U64} (hr : root ∈ Z.L4)
    (hv : UserV va) (h : vspace.lookup_pt_slot st s root va = ok (.Ok e)) : e ≠ 0#u64 := by
  obtain ⟨hSR, -, hPt, -, -⟩ := J.xtop.fin
  have hP := hSR.2.pt
  obtain ⟨r, hr', -, hsl, -⟩ := spec_ex_fd (lookup_pt_slot_rel (st := st) s σ hPt hP hr va hv)
  rw [h] at hr'
  have er := ok_inj hr'
  subst er
  obtain ⟨q, hq, rfl⟩ := hsl _ rfl
  have hal := hP q (Or.inr (Or.inr (Or.inr hq)))
  have hq0 := J.tab_ne0 (Or.inr (Or.inr (Or.inr hq)))
  have hqv : q.val ≠ 0 := fun h0 => hq0 (UScalar.eq_of_val_eq (by simpa using h0))
  have hb := q.hBounds
  have hf : q.val + 4096 ≤ 2 ^ 64 := by simp only [UScalarTy.numBits] at hb; omega
  have hv' := peA_val hf (vIdx_lt va 12)
  intro h0
  rw [h0] at hv'
  simp at hv'
  omega

end

end Fl4Proofs.P3
