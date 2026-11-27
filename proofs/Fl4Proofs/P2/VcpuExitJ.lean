/-
# P2 (vexit gen 3): the serial VM exit from a reachable entry state

`syscall.handle_vcpu_exit.entryB` (P1/VcpuExitBuf) takes, at the entry state,
`hBA` (`BufAt U`) and `hPd` (`PendAt U`) as [P] premises. At a P3 reachable
entry state (`JReachU17`, `kernel_entry_domInvU29`'s premises) both hold:

* `BufAt` for `U = BufU Z σ` over the heap's sets: P3 `JAtZ.bufAtJ`;
* `PendAt` vacuously: every TCB's VCPU word is zero at a joint state (vent's
  `VcpuZ`, `ventS_of_JAtZ`), so the current thread has no bound VCPU
  (`pendAt_of_vcpuZ`).

**`syscall.handle_vcpu_exit.entryJ`** (also `vcpu_exit_local.entryJ`,
`vm_timer_local.entryJ`): at a `JReachU17` state `s` there are `H Cs Ac U`
with `cpu s ∈ Cs` and `EntryInv` at `s`, such that every run of
`handle_vcpu_exit` from `s` satisfying the remaining run premises of `entryB`
ends in `EntryInv`. Remaining premises: `kernel_entry_domInvU29`'s, and
`htk` [P], `hI` [P], `hPF` [P] as in `entryB` (`hBA`, `hPd` gone).

**`syscall.handle_vcpu_exit.entryJ2`** (also `vcpu_exit_local.entryJ2`,
`vm_timer_local.entryJ2`): the same with `hPF` gone too (P2/VcpuExitV
`entryV`: every TCB's VCPU word is kept through the run). Remaining
premises: `kernel_entry_domInvU29`'s, `htk` [P] (with `TmoIbV`: the
timeout fault keeps the buffer-lookup and VCPU words) and `hI` [P] (the IRQ
slots name heap notifications after `vexit_pre`; not needed for
`vcpu_exit_local`).
-/
import Fl4Proofs.P2.VcpuExitV
import Fl4Proofs.P3.BufAtJ
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

attribute [local instance] atCpuI

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **The vexit entry facts at every reachable entry state**: the core in
`Cs`, `EntryInv`, the buffer placement `BufAt` (P3 `JAtZ.bufAtJ`, `U = BufU`)
and every TCB's VCPU word zero (`JExt.vw`). Premises: `kernel_entry_domInvU29`'s. -/
theorem vexitEnt_of_reachU17 {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (H : Heap) (Cs Ac U : Set U64), L.cpu s ∈ Cs ∧
      EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s ∧
      BufAt st (Heap.tcbs H) Cs H (Heap.frame H) (Heap.scs H) (Heap.scBits H) U s ∧
      VcpuZ st (Heap.tcbs H) s := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, ⟨hI, -⟩, -⟩ :=
    kernel_entry_domInvU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  obtain ⟨hc, -, hz⟩ := ventS_of_JAtZ J
  exact ⟨H, Cs, Ac, BufU Z σ, hc, hI, J.bufAtJ, hz⟩

set_option maxHeartbeats 4000000 in
/-- **(vexit gen 3) The serial VM exit from every reachable entry state keeps
`EntryInv`** (module docstring): `entryB` with `hBA` (P3 `JAtZ.bufAtJ`) and
`hPd` (`VcpuZ`, `pendAt_of_vcpuZ`) discharged. Premises:
`kernel_entry_domInvU29`'s, and the run premises `htk` [P], `hI` [P],
`hPF` [P] of `entryB`. -/
theorem syscall.handle_vcpu_exit.entryJ {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (H : Heap) (Cs Ac U : Set U64), L.cpu s ∈ Cs ∧
      EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s ∧
      ∀ (a0 : A) (irq : U64) (stalled : Bool),
      (stalled = false → sched.update_timestamp st arI s a0 ⦃ s1 a1 =>
        vcpu.check st arI s1 a1 (L.curW s1) ⦃ s2 _ => TmoIb st arI (Heap.tcbs H) Cs (Heap.omega H) H
          (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H) (Heap.scBits H) Ac s2 ⦄ ⦄) →
      vexit_pre st arI s a0 stalled ⦃ s1 _ => (irq != syscall.NO_IRQ) = true → IrqNtAt st (Heap.ntfns H) s1 ⦄ →
      vexit_irq st arI s a0 irq stalled ⦃ s2 a2 =>
        syscall.finish_old st arI s2 a2 ⦃ s3 _ => PendAt st U s3 ⦄ ⦄ →
      syscall.handle_vcpu_exit st arI s a0 irq stalled ⦃ s' _ => EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H
        (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H) (Heap.scBits H) Ac s' ⦄ := by
  obtain ⟨H, Cs, Ac, U, hc, hI, hBA, hz⟩ :=
    vexitEnt_of_reachU17 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨H, Cs, Ac, U, hc, hI, fun a0 irq stalled htk hIq hPF => ?_⟩
  exact syscall.handle_vcpu_exit.entryB hA (fun _ hn => hn) s a0 irq stalled hI hBA
    (pendAt_of_vcpuZ hz hI.1.choose_spec.choose_spec.curT) htk hIq hPF


set_option maxHeartbeats 4000000 in
/-- **(vexit gen 3) The serial VM exit from every reachable entry state keeps
`EntryInv`, `hPF` discharged too** (module docstring; `entryV`). Premises:
`kernel_entry_domInvU29`'s, and the run premises `htk` [P] (`TmoIbV`) and
`hI` [P]. -/
theorem syscall.handle_vcpu_exit.entryJ2 {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (H : Heap) (Cs Ac : Set U64), L.cpu s ∈ Cs ∧
      EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s ∧
      ∀ (a0 : A) (irq : U64) (stalled : Bool),
      (stalled = false → sched.update_timestamp st arI s a0 ⦃ s1 a1 =>
        vcpu.check st arI s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbV st arI (Heap.tcbs H) Cs (Heap.omega H) H
          (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H) (Heap.scBits H) Ac s2 ⦄ ⦄) →
      vexit_pre st arI s a0 stalled ⦃ s1 _ => (irq != syscall.NO_IRQ) = true → IrqNtAt st (Heap.ntfns H) s1 ⦄ →
      syscall.handle_vcpu_exit st arI s a0 irq stalled ⦃ s' _ => EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H
        (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H) (Heap.scBits H) Ac s' ⦄ := by
  obtain ⟨H, Cs, Ac, U, hc, hI, hBA, hz⟩ :=
    vexitEnt_of_reachU17 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  exact ⟨H, Cs, Ac, hc, hI, fun a0 irq stalled htk hIq =>
    syscall.handle_vcpu_exit.entryV hA (fun _ hn => hn) s a0 irq stalled hI hBA hz htk hIq⟩

set_option maxHeartbeats 4000000 in
/-- **The x86 local VM exit (no IRQ) from every reachable entry state keeps
`EntryInv`** (`vcpu_exit_local.entryV`). Premises: `kernel_entry_domInvU29`'s
and `htk` [P] (`TmoIbV`). -/
theorem vcpu_exit_local.entryJ2 {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (H : Heap) (Cs Ac : Set U64), L.cpu s ∈ Cs ∧
      EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s ∧
      ∀ (a0 : A) (v n : U64),
      sched.update_timestamp st arI s a0 ⦃ s1 a1 =>
        vcpu.check st arI s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbV st arI (Heap.tcbs H) Cs (Heap.omega H) H
          (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H) (Heap.scBits H) Ac s2 ⦄ ⦄ →
      localvm.handle_vcpu_exit_local st arI s a0 v n ⦃ r => r.1 = true →
        EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
          (Heap.scBits H) Ac r.2.1 ⦄ := by
  obtain ⟨H, Cs, Ac, U, hc, hI, hBA, hz⟩ :=
    vexitEnt_of_reachU17 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  exact ⟨H, Cs, Ac, hc, hI, fun a0 v n htk =>
    vcpu_exit_local.entryV hA (fun _ hn => hn) s a0 v n hI hBA hz htk⟩

end

end Fl4Proofs.P2.Stall
