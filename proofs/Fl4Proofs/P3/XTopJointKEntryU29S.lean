/-
P3 (KENTRY-PLAN lcs, local-path round): **the syscall entry beside the
serial gate, accepted**, and pf1's page-fault entries lifted to U29.

* **`kernel_entry_reachU29S`**: from `JReachU17` and `kernel_entry_reachU29`'s
  premises, an accepted `syscall.handle_syscall_local` (fl4-sync's
  `local_syscall`) has the postcondition of U29's native syscall clause (under
  that clause's inputs) and of its unknown-syscall clause (under that clause's
  inputs). P1 `syscall_local_same`: an accepted local run *is*
  `handle_syscall` (fast paths included), so the clauses carry over as they
  stand. The one added input is fl4-sync's contract on `found` (`local_syscall`
  computes `found = reply_caps` at the entry state for a thread with
  `TRAP_SYSCALLS` clear and the number `SysReplyRecv`, the only case the
  ReplyRecv arm runs); it is an input of the entry, not a state premise, and
  the unknown-syscall clause does not ask it (`UnkSys` makes it vacuous:
  `P1.found_vacuous`).
* **`kernel_entry_reachU29Vm`**: pf1's `kernel_entry_reachU15Vm` at U29
  (`JReachU17`, `KDispHypsKVU29`, the U29 postconditions): an accepted
  `handle_vm_fault_local` has the postcondition of U29's VM-fault clause, and
  an accepted `handle_reply_recv_vm_local` that of its syscall clause at
  `SysReplyRecv` (`found = reply_caps` at the entry state, as there). Through
  `kernel_entry_reachU28V` (it exposes `VxE Z`, which `JAtZ.vmFaultOK` /
  `JAtZ.rrPreAtG` ask), with `KDispHypsKVU29.toU28` as `kernel_entry_reachU29`
  does.

No premise is added to either top beyond U29's; no existing statement changed.
-/
import Fl4Proofs.P3.XTopJointKEntryU29
import Fl4Proofs.P3.XTopJointKEntryVm
import Fl4Proofs.P1.FastSysLocal
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- **The syscall entry beside the serial gate, accepted** (module
docstring): U29's native syscall clause and its unknown-syscall clause for
`handle_syscall_local`, on the runs that return `true`. -/
theorem kernel_entry_reachU29S [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall) (found : U64 × U64), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU29 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        (∀ t f, sched.cur_thread st s = ok t → obj.Tcb.flags st t s = ok f →
          (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 → n = fl4_abi.syscall.SysReplyRecv →
          fastpath.reply_caps st s t = ok (some found)) →
        syscall.handle_syscall_local st arI s a n found ⦃ r => r.1 = true →
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.2.1 r.2.2 σ' ∧ SInvX σ' ∧ MR r.2.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧
            JReachU17 (L := L) arI AR MR r.2.1 r.2.2 σ' ⦄) ∧
      (∀ (n : I64) (found : U64 × U64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s →
        NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall_local st arI s a n found ⦃ r => r.1 = true →
          ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
            RJ (L := L) arI AR r.2.1 r.2.2 σ' ∧ SInvX σ' ∧ MR r.2.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU17 (L := L) arI AR MR r.2.1 r.2.2 σ' ⦄) := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, -, -, -, -, -, -, -, hSys, -, -, -, -, hSU⟩ :=
    kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, fun n c found hct hn hfl hK hDL hFin hfd => ?_,
    fun n found hct hU hND hFin => ?_⟩
  · exact P1.syscall_local_triple arI hA J.bxi (fun _ et => J.cnOff et) hfd (hSys n c hct hn hfl hK hDL hFin)
  · exact P1.syscall_local_triple arI hA J.bxi (fun _ et => J.cnOff et) (P1.found_vacuous J.bxi hU)
      (hSU n hct hU hND hFin)

end

end

end Fl4Proofs.P3.SInvR.G5
