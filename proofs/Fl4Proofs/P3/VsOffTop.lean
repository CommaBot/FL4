/-
P3 (DESIGN.md §9), VSpace: **the composite relation across the zeroing of a
table outside the sets** (`offStable_top`, the `hoffSt` of VsPtUnmapOff's
`pt_unmap_rel_off` and its PD/PDPT forms at `SR := TopSR`): FL4 writes only
words of the table's frame, which no other relation reads (`hno`: no `OObj`
word), the spec changes only the arch object at the table (`OStep.arch`), so
`TopSR.step` keeps the relation at the same sets. `offStable_foot` (and its
PT/PD/PDPT shapes): the same at `FootSR TopSR s0 W`, the decodes' relation,
from no `OObj` word in the frame at the entry `s0` only (`OObj.back`: an
`OObj` word at a later state with the same kernel base and SCs, `KFoot`, is
one at the entry).
-/
import Fl4Proofs.P3.VsTop
import Fl4Proofs.P3.VsFootW
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

/-- **An `OObj` word after a step keeping the kernel base and the SCs** is
one before. -/
theorem OObj.back {s s' : S} {σ σ' : Fl4Spec.State Unit} (hks : L.ksb s' = L.ksb s)
    (hsc : ∀ p y n, σ'.kheap p = some (.schedContext y n) → σ.kheap p = some (.schedContext y n)) {b : U64}
    (h : OObj st N T C E R B c s' σ' b) : OObj st N T C E R B c s σ b := by
  have hnb : L.nodeBase s' c = L.nodeBase s c := by simp only [P1.LawfulStore.nodeBase, hks]
  unfold OObj at h ⊢
  rw [hnb, hks] at h
  rcases h with h | h | h | h | h | h | ⟨sc, hsc', y, n, hk, ho⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc', y, n, hsc _ _ _ hk, ho⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

/-- A VSpace invocation's spec step keeps the SCs (`KFoot`). -/
theorem KFoot.scBack {σ σ' : Fl4Spec.State Unit} (h : KFoot σ σ') :
    ∀ p y n, σ'.kheap p = some (.schedContext y n) → σ.kheap p = some (.schedContext y n) := by
  intro p y n hp
  by_contra hne
  have e : σ'.kheap p ≠ σ.kheap p := fun e => hne (e ▸ hp)
  rcases h.2.2.1 p e with ⟨ao, ao', -, h2⟩ | ⟨r, cs, cs', -, -, h2⟩ | ⟨t, t', -, h2⟩ <;> rw [hp] at h2 <;> cases h2

/-- **The off-set unmaps' `hoffSt` at `FootSR TopSR`** (any footprint `W`
holding `q`'s frame): `q`'s frame holds no `OObj` word at the entry `s0`,
`σ0`, hence none at a later state with the same kernel base and SCs
(`OObj.back`, `KFoot.scBack`), so `offStable_top` applies. -/
theorem offStable_foot {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {q : U64} {s0 : S} {σ0 : Fl4Spec.State Unit}
    {W : U64 → Prop} (hW : ∀ b, PtW {q} b → W b)
    (hno : ∀ i : U64, i.val < 512 → ¬ OObj st N T C E R B c s0 σ0 (peA q i))
    (s1 s2 : S) (a1 : A) (σ1 : Fl4Spec.State Unit) (ao ao' : Fl4Spec.ArchKernelObj)
    (hS : FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s0 W s1 a1 σ1) (hks : L.ksb s1 = L.ksb s0)
    (hK : KFoot σ0 σ1) (hw : WritesIn st s1 s2 (PtW {q})) (hk : σ1.kheap q.bv = some (.archObj ao)) :
    FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s0 W s2 a1 (updK σ1 q.bv (.archObj ao')) :=
  ⟨offStable_top s1 s2 a1 σ1 ao ao' hS.1 (fun i hi hO => hno i hi (OObj.back hks hK.scBack hO)) hw hk,
    (hS.2.trans hw).mono fun b hb => hb.elim id (hW b)⟩

/-- `offStable_foot` in the shape of `pt_unmap_rel_off`'s `hoffSt`. -/
theorem offStable_footPT {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {q : U64} {s0 : S} {σ0 : Fl4Spec.State Unit}
    {W : U64 → Prop} (hW : ∀ b, PtW {q} b → W b)
    (hno : ∀ i : U64, i.val < 512 → ¬ OObj st N T C E R B c s0 σ0 (peA q i)) :
    ∀ s1 s2 a1 σ1 σ2, FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s0 W s1 a1 σ1 → L.ksb s1 = L.ksb s0 →
      KFoot σ0 σ1 → WritesIn st s1 s2 (PtW {q}) →
      (∃ f f', σ1.kheap q.bv = some (.archObj (.pageTable f)) ∧ σ2 = updK σ1 q.bv (.archObj (.pageTable f'))) →
      FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s0 W s2 a1 σ2 := by
  rintro s1 s2 a1 σ1 σ2 hS hks hK hw ⟨f, f', hk, rfl⟩
  exact offStable_foot hW hno s1 s2 a1 σ1 _ _ hS hks hK hw hk

/-- `offStable_foot` in the shape of `pd_unmap_rel_off`'s `hoffSt`. -/
theorem offStable_footPD {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {q : U64} {s0 : S} {σ0 : Fl4Spec.State Unit}
    {W : U64 → Prop} (hW : ∀ b, PtW {q} b → W b)
    (hno : ∀ i : U64, i.val < 512 → ¬ OObj st N T C E R B c s0 σ0 (peA q i)) :
    ∀ s1 s2 a1 σ1 σ2, FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s0 W s1 a1 σ1 → L.ksb s1 = L.ksb s0 →
      KFoot σ0 σ1 → WritesIn st s1 s2 (PtW {q}) →
      (∃ f f', σ1.kheap q.bv = some (.archObj (.pageDirectory f)) ∧ σ2 = updK σ1 q.bv (.archObj (.pageDirectory f'))) →
      FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s0 W s2 a1 σ2 := by
  rintro s1 s2 a1 σ1 σ2 hS hks hK hw ⟨f, f', hk, rfl⟩
  exact offStable_foot hW hno s1 s2 a1 σ1 _ _ hS hks hK hw hk

/-- `offStable_foot` in the shape of `pdpt_unmap_rel_off`'s `hoffSt`. -/
theorem offStable_footPDPT {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {q : U64} {s0 : S} {σ0 : Fl4Spec.State Unit}
    {W : U64 → Prop} (hW : ∀ b, PtW {q} b → W b)
    (hno : ∀ i : U64, i.val < 512 → ¬ OObj st N T C E R B c s0 σ0 (peA q i)) :
    ∀ s1 s2 a1 σ1 σ2, FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s0 W s1 a1 σ1 → L.ksb s1 = L.ksb s0 →
      KFoot σ0 σ1 → WritesIn st s1 s2 (PtW {q}) →
      (∃ f f', σ1.kheap q.bv = some (.archObj (.pdPointerTable f)) ∧
        σ2 = updK σ1 q.bv (.archObj (.pdPointerTable f'))) →
      FootSR st (TopSR st th P L4 L3 L2 L1 N T C E R B c AR) s0 W s2 a1 σ2 := by
  rintro s1 s2 a1 σ1 σ2 hS hks hK hw ⟨f, f', hk, rfl⟩
  exact offStable_foot hW hno s1 s2 a1 σ1 _ _ hS hks hK hw hk

end

end

end Fl4Proofs.P3.Vs
