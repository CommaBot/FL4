/-
P3 (DESIGN.md §9), m70: g4i's `fastFaultOK_of_p1` without m67's
`FaultNvmPre` [J] (P1 `FaultNvmPre.of_asid`, FastTailFault): at a state with
P1's `EntryInv` (and the `Hyps4` admissibility of its sets), `AsidOff` [J]
alone gives the general path's reads `FastFaultOK`.
-/
import Fl4Proofs.P3.XTopJointKEntryEv5
import Fl4Proofs.P1.FastTailRR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **`FastFaultOK` from the P1 invariants and `AsidOff`** (no `FaultNvmPre`). -/
theorem fastFaultOK_of_p1N {T Ω Cs Sg Rp Scs Nt U : Set U64} {H : P1.Heap} {Z : U64 → Nat} {P3Ok : S → Prop}
    {Adm : P1.PSets → Prop} (hA : P0.ArchTotal arI)
    (GF : ∀ σ : P1.PSets, Adm σ → P1.Hyps4 st arI Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} {s : S} {a : A} {n : I64} (hP : P3Ok s)
    (h : P1.EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hAs : P1.AsidOff (L := L) Ω Sg s) :
    P1.FastFaultOK (L := L) arI s a n := by
  have E0 : P1.EntryHyps0 st arI T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
    have G3 : P1.InvGaps st arI Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
      obtain ⟨P, C, ⟨V, Pd⟩, Pt, G, -⟩ := GF _ hσ
      exact (G.gaps3 hA hσ C Pd Pt P.xfer).gaps hA P C
    exact (P1.EntryHyps.of_gaps hA hσ (fun σ'' h'' => (GF σ'' h'').1) (GF _ hσ).1 G3).toEntryHyps0
  exact fastFaultOK_of_p1 hA GF hσ hP h hAs (P1.FaultNvmPre.of_asid arI hA E0 (GF _ hσ).1.xfer hP h hAs)

end

end Fl4Proofs.P3
