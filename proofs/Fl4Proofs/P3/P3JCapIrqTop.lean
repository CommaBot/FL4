/-
P3 (p3J gen 37): **the IrqHandler leaf for both classes and the top without it** (P3JCapIrq's `decIrqSt`).

* **`midDecIrq_of`** / **`invDecIrq_of`**: `MidDecStW` / `InvDecStW` at `KW ∧ ∃ i, · = .IrqHandler i`, from
  `SInvX σ` and `SpecIrqB σ` at the entry state (`dispEnteredSg`, `ppr0_disp`, `irqB_disp`), the same `decIrqSt` at
  the mid flags `false false true true` and the inv flags `bl call don false`.
* `IsRestCap3` (CNode, Thread, SchedContext), `restCap3_of`, `midDecRest_of_irq` / `invDecRest_of_irq` (gen 36's
  `IsRestCap` predicates from the IrqHandler leaf and the three left).
* **`DispStabFootLq` [J]** {invDecRest / midDecRest at `KW ∧ IsRestCap3`, midSpec, midRecvSw verbatim, `irqB`:
  `SpecIrqB σ` [J] (P3JCapIrq's docstring: l4v `valid_cap`'s `irq ≤ maxIRQ`; FL4 issues handler caps only for
  `irq ≤ 123`, arch/x86_64/interrupt.rs l.19-22 / l.48-50)}; **`dispStabFootLo_of_Lq`**; top
  **`kernel_entry_runMcWKR_sysLq`** (globals verbatim as `_sysLo`, plus `[PlainStore st]` which `_sysLo` already
  has).

Premise honesty: `DispStabFootLq`'s decode fields are `DispStabFootLo`'s at a smaller cap predicate
(`IsRestCap3 → IsRestCap`), midSpec / midRecvSw verbatim — implied by `DispStabFootLo`; `irqB` is new, not
implied by `DispStabFootLo`. `DispStabFootLq` implies `DispStabFootLo` (`dispStabFootLo_of_Lq`).

Named premises: `DispStabFootLq` [J], `SpecIrqB` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JCapIrq
import Fl4Proofs.P3.P3JCapDom
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- (p3J gen 37) The caps left after the IrqHandler leaf: CNode, Thread, SchedContext. -/
def IsRestCap3 : capability.Cap → Prop
  | .CNode .. => True
  | .Thread _ => True
  | .SchedContext .. => True
  | _ => False

theorem restCap3_of {cp : capability.Cap} (h : IsRestCap cp) (hI : ¬ ∃ i, cp = .IrqHandler i) : IsRestCap3 cp := by
  cases cp <;> simp_all [IsRestCap, IsRestCap3]

theorem restCap_of3 {cp : capability.Cap} (h : IsRestCap3 cp) : IsRestCap cp := by
  cases cp <;> simp_all [IsRestCap, IsRestCap3]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop} {Z : XSets} {H : P1.Heap}
  {Cs : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 37) **The mid decode leaf of the IrqHandler cap** (module docstring). -/
theorem midDecIrq_of [Fl4Proofs.P1.PlainStore st] (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hARI : ARIface arI AR) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (hIB : SpecIrqB σ) :
    MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ ∃ i, cp = .IrqHandler i) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  obtain ⟨-, irq, rfl⟩ := hW
  obtain ⟨hnib, hsg⟩ := dispEnteredSg hnd hX hni hBA
  exact decIrqSt hA hARI hMT hKD J hnib hsg (ppr0_disp arI hnd hX hBA J hnib) hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc
    (irqB_disp hnd hX hBA hIB) hget he hexs _ _ _ _ _ _

set_option maxHeartbeats 4000000 in
/-- (p3J gen 37) **The invoking class's decode leaf of the IrqHandler cap** (module docstring). -/
theorem invDecIrq_of [Fl4Proofs.P1.PlainStore st] (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hARI : ARIface arI AR) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {call bl don : Bool} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (hIB : SpecIrqB σ) :
    InvDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ ∃ i, cp = .IrqHandler i) Z H Cs s a σ n
      call bl don := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  obtain ⟨-, irq, rfl⟩ := hW
  obtain ⟨hnib, hsg⟩ := dispEnteredSg hnd hX hni hBA
  exact decIrqSt hA hARI hMT hKD J hnib hsg (ppr0_disp arI hnd hX hBA J hnib) hMb hct a1 a2 a3 a4 a5 a6 sl hsl hc
    (irqB_disp hnd hX hBA hIB) hget he hexs _ _ _ _ _ _

/-- (p3J gen 37) **gen 36's `midDecRest` from the IrqHandler leaf and the three left** (module docstring). -/
theorem midDecRest_of_irq [Fl4Proofs.P1.PlainStore st] (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1)
    (hARI : ARIface arI AR) (hMT : MachPlat arI MR) (hKD : MRKeepD arI MR) {s : S} {a : A}
    {σ : Fl4Spec.State Unit} {n : I64} {c : Fl4Spec.Syscall} (hX : SInvX σ) (hni : σ.curThread ≠ σ.idleThread)
    (hIB : SpecIrqB σ)
    (h : MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap3 cp) Z H Cs s a σ n c) :
    MidDecStW (L := L) arI AR MR (fun cp => SInvCk.KW (absCap cp) ∧ IsRestCap cp) Z H Cs s a σ n c := by
  intro σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
    a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs hW
  by_cases hI : ∃ i, cp = .IrqHandler i
  · exact midDecIrq_of hA hnd hARI hMT hKD hX hni hIB σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr
      hct hn info mi buf buffer r2 er argsU a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, hI⟩
  · exact h σb hBA V' Ac' Lst' D' s' a' hKF J hMb hCb hRRb ct rg sr cr hct hn info mi buf buffer r2 er argsU
      a1 a2 a3 a4 a5 a6 a7 sl cp e exs hsl hc hget he hexs ⟨hW.1, restCap3_of hW.2 hI⟩

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

end Fl4Proofs.P3.Mc
