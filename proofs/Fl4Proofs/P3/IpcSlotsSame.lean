/-
P3 (DESIGN.md §9), IPC: **`XTopAt` at the same ghost tree after IPC work
keeping the slots** (for the deletion closure's notification finalisation).

* `IRel.slotsSame_of`: FL4 writing words of the other objects (`OObj`)
  from an `IRel` state keeps every slot.
* `iwords_oobj`: the IPC words are such words.
* `XTopAt.irel_same`: from `XTopAt Z` before and `IRel` after (the IPC
  lemmas' post), with the slots kept and the spec's CDT, original-cap bits
  and CNodes/TCBs kept (`KSub`), `XTopAt` at `Z`'s ghost tree `Z.G` and some
  VSpace sets (`Z.mv Z.G V'`).
-/
import Fl4Proofs.P3.IpcXTop
import Fl4Proofs.P3.XTopDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P1 Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **Writes to the other objects keep the slots**, from an `IRel` state. -/
theorem IRel.slotsSame_of {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}
    {c : U64} {s s' : S} {σ : Fl4Spec.State Unit} (h : IRel st th cr N T C E R B c s σ) {W : U64 → Prop}
    (hw : P1.WritesIn st s s' W) (hWO : ∀ b, W b → OObj st N T C E R B c s σ b) :
    SlotsSame th (L.mem s) (L.mem s') := by
  obtain ⟨-, ⟨⟨G, hB⟩, hV⟩, -, -⟩ := h
  obtain ⟨P, L4, L3, L2, L1, -, -, -, -, hP⟩ := hV.ex
  exact slotsSame_of_vobj hB.1 fun b hb hv => hw.mem_eq hb fun hwb => hP.disj b (hWO b hwb) hv

/-- **The slots and the kernel-global base kept** (what the IPC lemmas
return for the deletion closure). -/
def IFrame (th : TypedHeap) (s s' : S) : Prop := SlotsSame th (L.mem s) (L.mem s') ∧ L.ksb s' = L.ksb s

theorem IFrame.refl (th : TypedHeap) (s : S) : IFrame (L := L) th s s := ⟨SlotsSame.refl _ _, rfl⟩

theorem IFrame.trans {th : TypedHeap} {s1 s2 s3 : S} (h1 : IFrame (L := L) th s1 s2) (h2 : IFrame (L := L) th s2 s3) :
    IFrame (L := L) th s1 s3 := ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

theorem IRel.iframe_of {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}
    {c : U64} {s s' : S} {σ : Fl4Spec.State Unit} (h : IRel st th cr N T C E R B c s σ) {W : U64 → Prop}
    (hw : P1.WritesIn st s s' W) (hWO : ∀ b, W b → OObj st N T C E R B c s σ b) : IFrame (L := L) th s s' :=
  ⟨IRel.slotsSame_of h hw hWO, hw.1⟩

/-- `IRel.iframe_of` from the top part alone (`SRT`, any scheduler part). -/
theorem SRT.iframe_of {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}
    {c : U64} {SR' : S → Fl4Spec.State Unit → Prop} {s s' : S} {σ : Fl4Spec.State Unit}
    (h : SRT st th cr N T C E R B c SR' s σ) {W : U64 → Prop}
    (hw : P1.WritesIn st s s' W) (hWO : ∀ b, W b → OObj st N T C E R B c s σ b) : IFrame (L := L) th s s' := by
  obtain ⟨⟨⟨G, hB⟩, hV⟩, -⟩ := h
  obtain ⟨P, L4, L3, L2, L1, -, -, -, -, hP⟩ := hV.ex
  exact ⟨slotsSame_of_vobj hB.1 fun b hb hv => hw.mem_eq hb fun hwb => hP.disj b (hWO b hwb) hv, hw.1⟩

/-- **The IPC words are words of the other objects.** -/
theorem iwords_oobj {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {s : S}
    {σ : Fl4Spec.State Unit} {b : U64} (h : IWords N T E R B b) : OObj st N T C E R B c s σ b := by
  rcases h with h | h | h | ⟨n, hn, h1, h2⟩ | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h1, by omega⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

/-- **`XTopAt` at the same ghost tree after IPC work keeping the slots**
(module docstring). -/
theorem XTopAt.irel_same {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) {cr : Fl4Spec.Cr3}
    (hI : IRel st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ') (hAR : AR a' cr)
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hcdt : σ'.cdt = σ.cdt)
    (hio : σ'.isOriginalCap = σ.isOriginalCap) (hK : KSub σ σ') (hks : L.ksb s' = L.ksb s) :
    ∃ V' : XVs, XTopAt (L := L) AR (Z.mv Z.G V') s' a' σ' := by
  obtain ⟨-, hCR, hFI, -, hMO, -, -⟩ := hX.rel
  obtain ⟨-, -, hM, hC, hMI⟩ := hCR
  obtain ⟨hIR, ⟨⟨G'', hB⟩, hV⟩, hS, hEA⟩ := hI
  obtain ⟨P, L4, L3, L2, L1, hR, hPt, hPI, hCO, hP⟩ := hV.ex
  obtain ⟨hPl', hCR', -, hD', -, hIA', hSA'⟩ := hB
  have hCRZ : CRel Z.th (L.mem s') σ' Z.G :=
    ⟨hCR'.1, hCR'.2.1, hM.of_same hSS, hC.of_same hSS hcdt hio, MdbInv.of_same hM hMI hSS⟩
  refine ⟨(P, L4, L3, L2, L1), ⟨⟨⟨hS, hIR.toE, hIR.toN, hV.irq, hV.io, hV.kr, by rw [hV.cr3]; exact hAR⟩, hP⟩,
    hR, hPt, hPI, hCO⟩, ⟨hPl', hCRZ, hFI.of_same hM hSS hK, hD', ?_, hIA', hSA'⟩, hIR, hEA⟩
  rw [hks]; exact MdbOKV.of_same hM hSS hMO

end

end

end Fl4Proofs.P3
