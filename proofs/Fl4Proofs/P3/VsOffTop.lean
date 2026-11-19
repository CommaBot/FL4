/-
P3 (DESIGN.md §9), VSpace: **the composite relation across the zeroing of a
table outside the sets** (`offStable_top`, the `hoffSt` of VsPtUnmapOff's
`pt_unmap_rel_off` and its PD/PDPT forms at `SR := TopSR`): FL4 writes only
words of the table's frame, which no other relation reads (`hno`: no `OObj`
word), the spec changes only the arch object at the table (`OStep.arch`), so
`TopSR.step` keeps the relation at the same sets.
-/
import Fl4Proofs.P3.VsTop
import Fl4Proofs.P3.VsPdptUnmapOff
import Fl4Proofs.P3.VsPdUnmapOff
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **`TopSR` across a write of a table's frame outside the sets** with the
spec's arch object at the table changed. -/
theorem offStable_top {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {q : U64} (s s' : S) (a : A)
    (σ : Fl4Spec.State Unit) (ao ao' : Fl4Spec.ArchKernelObj)
    (hS : TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ)
    (hno : ∀ i : U64, i.val < 512 → ¬ OObj st N T C E R B c s σ (peA q i))
    (hw : WritesIn st s s' (PtW {q})) (hk : σ.kheap q.bv = some (.archObj ao)) :
    TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a (updK σ q.bv (.archObj ao')) :=
  TopSR.step (Rw := PtW {q}) hS hw.1 hw.2.1 (fun b hb _ hr => hw.2.2 b hb hr)
    (fun b ⟨p, hp, i, hi, e⟩ => by rw [Set.mem_singleton_iff.1 hp] at e; rw [e]; exact hno i hi)
    (OStep.arch (Or.inr (Or.inr ⟨_, hk⟩)) _) (fun _ h => h.elim) (fun wp _ => rfl) id

/-- `offStable_top` in the shape of `pt_unmap_rel_off`'s `hoffSt`. -/
theorem offStable_topPT {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {q : U64}
    (hno : ∀ s a σ, TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ →
      ∀ i : U64, i.val < 512 → ¬ OObj st N T C E R B c s σ (peA q i)) :
    ∀ s s' a σ σ', TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ → WritesIn st s s' (PtW {q}) →
      (∃ f f', σ.kheap q.bv = some (.archObj (.pageTable f)) ∧ σ' = updK σ q.bv (.archObj (.pageTable f'))) →
      TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a σ' := by
  rintro s s' a σ σ' hS hw ⟨f, f', hk, rfl⟩
  exact offStable_top s s' a σ _ _ hS (hno s a σ hS) hw hk

/-- `offStable_top` in the shape of `pd_unmap_rel_off`'s `hoffSt`. -/
theorem offStable_topPD {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {q : U64}
    (hno : ∀ s a σ, TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ →
      ∀ i : U64, i.val < 512 → ¬ OObj st N T C E R B c s σ (peA q i)) :
    ∀ s s' a σ σ', TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ → WritesIn st s s' (PtW {q}) →
      (∃ f f', σ.kheap q.bv = some (.archObj (.pageDirectory f)) ∧ σ' = updK σ q.bv (.archObj (.pageDirectory f'))) →
      TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a σ' := by
  rintro s s' a σ σ' hS hw ⟨f, f', hk, rfl⟩
  exact offStable_top s s' a σ _ _ hS (hno s a σ hS) hw hk

/-- `offStable_top` in the shape of `pdpt_unmap_rel_off`'s `hoffSt`. -/
theorem offStable_topPDPT {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {q : U64}
    (hno : ∀ s a σ, TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ →
      ∀ i : U64, i.val < 512 → ¬ OObj st N T C E R B c s σ (peA q i)) :
    ∀ s s' a σ σ', TopSR st th P L4 L3 L2 L1 N T C E R B c AR s a σ → WritesIn st s s' (PtW {q}) →
      (∃ f f', σ.kheap q.bv = some (.archObj (.pdPointerTable f)) ∧
        σ' = updK σ q.bv (.archObj (.pdPointerTable f'))) →
      TopSR st th P L4 L3 L2 L1 N T C E R B c AR s' a σ' := by
  rintro s s' a σ σ' hS hw ⟨f, f', hk, rfl⟩
  exact offStable_top s s' a σ _ _ hS (hno s a σ hS) hw hk

end

end

end Fl4Proofs.P3.Vs
