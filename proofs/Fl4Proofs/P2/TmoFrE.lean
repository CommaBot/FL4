/-
P2 (tmofr gen 2, part E): **the VM exits from every reachable entry state
with no premise beyond `kernel_entry_domInvU29`'s**.

* **`syscall.handle_vcpu_exit.entryJ5`**, **`vm_timer_local.entryJ5`**:
  `entryJ4` (P2/TmoFrC) with its entry-state facts `hnq` [P] and `hni` [P]
  discharged: P3's `kernel_entry_domInvU29Q` (P3/XTopJointDomInv29Q) exports,
  at the same joint state `J`, the spec's `ct_not_in_q` (`SInvX.ctQ`) and
  `valid_idle` (`SInvCQ.idleSt`); `JAtZ.curQ0` turns the first into the
  current thread's clear `Q_QUEUED` bit, `JAtZ.idleNR` the second into the
  idle thread's non-runnable state word.

Premises: `kernel_entry_domInvU29`'s only. No run premise, no entry [P].
-/
import Fl4Proofs.P2.TmoFrC
import Fl4Proofs.P3.XTopJointDomInv29Q
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **(tmofr gen 2) The serial VM exit from every reachable entry state keeps
`EntryInv`**: `entryJ4` with `hnq`/`hni` from `kernel_entry_domInvU29Q`.
Premises: `kernel_entry_domInvU29`'s only. -/
theorem syscall.handle_vcpu_exit.entryJ5 {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
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
      syscall.handle_vcpu_exit st arI s a0 irq stalled ⦃ s' _ => EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H
        (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H) (Heap.scBits H) Ac s' ⦄ := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, ⟨hI, -⟩, hq, hi, -⟩ :=
    kernel_entry_domInvU29Q arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  obtain ⟨hc, -, hz⟩ := ventS_of_JAtZ J
  exact ⟨H, Cs, Ac, hc, hI, fun a0 irq stalled =>
    syscall.handle_vcpu_exit.entryK hA (fun _ hn => hn) s a0 irq stalled hI J.bufAtJ hz (irqOff_of_JAtZ J)
      (irqNtAt_of_JAtZ J) (J.curQ0 hq) (J.idleNR hi) (tmoCapW_of_JAtZ J)⟩

set_option maxHeartbeats 4000000 in
/-- **(tmofr gen 2) The x86 local VM timer exit from every reachable entry
state keeps `EntryInv`**: `vm_timer_local.entryJ4` with `hnq`/`hni` from
`kernel_entry_domInvU29Q`. Premises: `kernel_entry_domInvU29`'s only. -/
theorem vm_timer_local.entryJ5 {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
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
      ∀ (a0 : A) (irq n : U64) (p : localtimer.TimerIrqPlan),
      localvm.handle_vm_timer_irq_local st arI s a0 irq p n ⦃ r => r.1 = true →
        EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
          (Heap.scBits H) Ac r.2.1 ⦄ := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, ⟨hI, -⟩, hq, hi, -⟩ :=
    kernel_entry_domInvU29Q arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  obtain ⟨hc, -, hz⟩ := ventS_of_JAtZ J
  exact ⟨H, Cs, Ac, hc, hI, fun a0 irq n p =>
    vm_timer_local.entryK hA (fun _ hn => hn) s a0 irq n p hI J.bufAtJ hz (irqOff_of_JAtZ J)
      (irqNtAt_of_JAtZ J) (J.curQ0 hq) (J.idleNR hi) (tmoCapW_of_JAtZ J)⟩

end

end Fl4Proofs.P2.Stall
