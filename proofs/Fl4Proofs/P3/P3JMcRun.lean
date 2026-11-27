/-
P3 (p3J gen 17): **the multicore run predicate `RunMc` and one entry clause through it on any core.**

* **`RunMc s a σ := RunCK s a σ ∧ JAtMc s a σ`**: gen 16's run invariant (U40's joint reach and the cap-kind
  invariant) at the current core's projection, and the other cores' idle objects outside it (P3JMc).
  Nothing in `RunCK` / U45nv fixes the current core: `JAtZ` carries `L.cpu s ∈ Cs` (`JKern.cpuCs`) and reads the
  current core's node through `L.cpu s`, so every clause of `kernel_entry_runCK` already holds at an entry on a
  core `c ≠ 0` whose projection is a `RunCK` state (**`kernel_entry_runMc_proj`**).
* **`kernel_entry_runMc_irq`**: the interrupt entry on any core `L.cpu s` (in particular `c ≠ 0`) from a `RunMc`
  state ends in a `RunMc` state, given the named premise **`hFI` [J] (`FIKeepIrq`)**: the interrupt entry keeps the
  other cores' idle objects outside the projection at its outcome (`JAtMc` there). Not discharged: it needs the
  entry's FL4 footprint (P1's `WritesIn` / `KW`-style footprint of `handle_interrupt_entry`, missing the other
  cores' idle TCB / SC words and their nodes' `IDLE_*` words) tied to the post-state ghosts of U45nv's interrupt
  clause, which that clause does not expose (handoff p3J.md gen 17, "what remains").

Named premises: `FIKeepIrq` [J] (above); U45nv's globals as in `kernel_entry_runCK` (`NoVirt`, `KCfgFL4`,
`FpuImplDet`, `FpuWriteDet` [P], the platform hypotheses). No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JCkRun
import Fl4Proofs.P3.P3JMc
import Fl4Proofs.P3.ScSwitchTo
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ

/-- Two postconditions of one program, conjoined. -/
theorem spec_and2 {α : Type} {m : Result α} {P Q : α → Prop} (hP : m ⦃ P ⦄) (hQ : m ⦃ Q ⦄) :
    m ⦃ fun r => P r ∧ Q r ⦄ :=
  Sched.spec_and_eq hP fun r e => by rw [e, WP.spec_ok] at hQ; exact hQ

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The multicore run predicate** (module docstring). -/
def RunMc (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RunCK (L := L) arI AR MR s a σ ∧ JAtMc (L := L) arI AR s a σ

/-- **`FIKeepIrq` [J]** (module docstring): from `s`, the interrupt entry's outcomes related to a spec interrupt
event and a `RunCK` state keep the other cores' idle objects outside the projection. -/
def FIKeepIrq (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
    syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∀ σ', EvOut false .interrupt σ σ' →
      RunCK (L := L) arI AR MR r.1 r.2 σ' → JAtMc (L := L) arI AR r.1 r.2 σ' ⦄

set_option maxHeartbeats 4000000 in
/-- **The interrupt entry on any core, through `RunMc`** (module docstring; `hFI` [J]). -/
theorem kernel_entry_runMc_irq [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatK arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hMap : IoaMap arI)
    (hFpu : FpuImplDet) (hFW : FpuWriteDet) (hCfg : KCfgFL4) (hNV : NoVirt arI)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMc (L := L) arI AR MR s a σ)
    (hFI : FIKeepIrq (L := L) arI AR MR s a σ) :
    ∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
      syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
        RunMc (L := L) arI AR MR r.1 r.2 σ' ⦄ := by
  intro w a1 hw
  obtain ⟨_, _, _, _, _, _, -, -, hI, -⟩ := kernel_entry_runCK arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef
    hPI hSX hDR hMap hFpu hFW hCfg hNV hR.1
  have h2 := spec_and2 (hI w a1 hw) (hFI w a1 hw)
  refine WP.spec_mono h2 ?_
  rintro r ⟨⟨σ', h1, hJ⟩, hK⟩
  exact ⟨σ', h1, hJ, hK σ' h1 hJ⟩

end

end Fl4Proofs.P3.Mc
