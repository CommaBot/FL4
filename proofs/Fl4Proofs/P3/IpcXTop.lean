/-
P3 (DESIGN.md §9), IPC: **the IPC proofs' relation and `XTopAt`**.

`IRel` at a typed heap `th` carries, in `RelTopI`, the VSpace and
kernel-state parts of `XTopAt` (`VsP`: VSpace's `FinX` relations and
placement, the IRQ, IO-port and kernel-root relations, the IPC objects and
SCs apart from the kernel-global block), so:

* `XTopAt.irelK`: `XTopAt` at sets `Z`, with the IPC objects outside the
  kernel-global block (`KsApart`), gives `IRel` at `Z.th`;
* `IRel.xtop`: `IRel` with the arch relation gives `XTopAt` at the sets with
  `th` (and `KsApart` again), so the IPC leaves proved on `IRel` end at
  `XTopAt` directly.
-/
import Fl4Proofs.P3.XTopStep
import Fl4Proofs.P3.IpcSchedLift
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **`XTopAt` gives the IPC proofs' `IRel`** at its typed heap, with the IPC
objects outside the kernel-global block. -/
theorem XTopAt.irelK {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : XTopAt (L := L) AR Z s a σ) (hK : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s)) :
    IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ := by
  obtain ⟨⟨⟨⟨hSch, -, -, hIrq, hIo, hKr, -⟩, hP⟩, hR, hPt, hPI, hCO⟩, hB, hIR, hEA⟩ := h
  obtain ⟨Q, R0, hc, -⟩ := hSch.lists
  refine ⟨hIR, ⟨⟨Z.G, hB⟩, ⟨⟨Z.P, Z.L4, Z.L3, Z.L2, Z.L1, hR, hPt, hPI, hCO, hP⟩, hIrq, hIo, hKr,
    fun t ht => ?_, hK.ep, hK.rep, hK.ntfn, hK.buf,
    fun sc hsc x n hk a ha => (hSch.scOut sc hsc x n hk a ha).2.2.2, rfl⟩⟩, hSch, hEA⟩
  have := hc.ksOut t ht; omega

/-- **`IRel` gives `XTopAt`** at the sets with its typed heap, given the arch
relation; and the IPC objects outside the kernel-global block. -/
theorem IRel.xtop {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64}
    {B : Set (U64 × Fl4Spec.Word)} {c : U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : IRel st th cr N T C E R B c s σ) (hAR : AR a cr) :
    (∃ Z : XSets, Z.th = th ∧ Z.N = N ∧ Z.T = T ∧ Z.C = C ∧ Z.E = E ∧ Z.R = R ∧ Z.B = B ∧ Z.c = c ∧
      XTopAt (L := L) AR Z s a σ) ∧ KsApart N T E R B (L.ksb s) := by
  obtain ⟨hIR, ⟨⟨G, hB⟩, hV⟩, hS, hEA⟩ := h
  obtain ⟨P, L4, L3, L2, L1, hR, hPt, hPI, hCO, hP⟩ := hV.ex
  exact ⟨⟨⟨th, G, P, L4, L3, L2, L1, N, T, C, E, R, B, c⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨⟨⟨hS, hIR.toE, hIR.toN, hV.irq, hV.io, hV.kr, by rw [hV.cr3]; exact hAR⟩, hP⟩, hR, hPt, hPI, hCO⟩, hB, hIR, hEA⟩,
    ⟨hV.ksE, hV.ksR, hV.ksN, hV.ksB⟩⟩

end


section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **An IPC leaf on `IRel` ends at `XTopAt`**: from `XTopAt Z` with the IPC
objects outside the kernel-global block, a leaf proved on `IRel` at `Z.th`
(and the spec's CR3), whose FL4 side keeps the arch state (`hAk`), ends at
`XTopAt` at the same typed heap and sets, with `KsApart` again. -/
theorem xtopAt_of_irel {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) (hK : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    {prog : Result ((core.result.Result Unit error.Exc) × S × A)} {spec : Set (Unit × Fl4Spec.State Unit) × Prop}
    (hI : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ → prog ⦃ r => r.1 = .Ok () ∧
      ∃ z ∈ spec.1, RelTopM (L := L) r.2.1 z.2 ∧
        IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c r.2.1 z.2 ⦄)
    (hAk : prog ⦃ r => r.2.2 = a ⦄) :
    prog ⦃ r => r.1 = .Ok () ∧ ∃ z ∈ spec.1, RelTopM (L := L) r.2.1 z.2 ∧
      (∃ Z' : XSets, Z'.th = Z.th ∧ Z'.N = Z.N ∧ Z'.T = Z.T ∧ Z'.C = Z.C ∧ Z'.E = Z.E ∧ Z'.R = Z.R ∧ Z'.B = Z.B ∧
        Z'.c = Z.c ∧ XTopAt (L := L) AR Z' r.2.1 r.2.2 z.2) ∧ KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb r.2.1) ⦄ := by
  have hAR : AR a σ.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  refine WP.spec_mono (WP.spec_and (hI (hX.irelK hK)) hAk) ?_
  rintro r ⟨⟨h1, z, hz, hRT, hIz⟩, ha⟩
  exact ⟨h1, z, hz, hRT, IRel.xtop hIz (by rw [ha]; exact hAR)⟩

/-- **The XLeaf shape** (TopXAll's `XLeaf (XTop AR)`): for every `Z` the
entry's `XTopAt Z` holds at, `KsApart` and the leaf on `IRel` at `Z.th`. -/
theorem xleaf_of_irel {AR : A → Fl4Spec.Cr3 → Prop} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    {prog : Result ((core.result.Result Unit error.Exc) × S × A)} {spec : Set (Unit × Fl4Spec.State Unit) × Prop}
    (hKA : ∀ Z : XSets, XTopAt (L := L) AR Z s a σ → KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hI : ∀ Z : XSets, XTopAt (L := L) AR Z s a σ →
      IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ → prog ⦃ r => r.1 = .Ok () ∧
        ∃ z ∈ spec.1, RelTopM (L := L) r.2.1 z.2 ∧
          IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c r.2.1 z.2 ⦄)
    (hAk : prog ⦃ r => r.2.2 = a ⦄) :
    XLeaf (L := L) (XTop (L := L) AR) s a σ prog spec := by
  rintro ⟨Z, hZ⟩
  refine WP.spec_mono (xtopAt_of_irel hZ (hKA Z hZ) (hI Z hZ) hAk) ?_
  rintro r ⟨h1, z, hz, hRT, ⟨Z', -, -, -, -, -, -, -, -, hZ'⟩, -⟩
  exact ⟨h1, z, hz, hRT, Z', hZ'⟩

end

end

end Fl4Proofs.P3
