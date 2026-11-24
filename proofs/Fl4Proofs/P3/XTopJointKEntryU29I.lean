/-
P3 (KENTRY-PLAN lci): **`kernel_entry_reachU29I`**, the I/O port entry beside
the serial gate, accepted.

From `kernel_entry_reachU29`'s premises and `JReachU17 s a σ`: the same
`JAtZ` witnesses, and an accepted `syscall.handle_ioport_local s a n` (fl4-sync
`local_syscall`, `SysCall` / `SysSend` on an I/O port label) has the
postcondition of `kernel_entry_reachU29`'s syscall clause at `n`, under that
clause's own inputs. P1 `ioport_local_triple`: on its `true` results the local
entry ends where `syscall.handle_syscall … n` ends (the same `FAULT_IP` write
and `update_timestamp`; `budget_ok` then passes without writing, since the
local entry checked `sufficient` at that state; `dispatch_syscall` reaches
`handle_invocation` with the local entry's arguments and the same `CAP`
read; the same `after_invocation` / `finish`). The local entry's other checks
(`action`, `yield_to`, `extra_caps`, `ioport.invocation_ok`,
`schedulable_here`) only narrow when it runs.

Premises: exactly `kernel_entry_reachU29`'s. Inputs of the clause: those of
U29's syscall clause (the flag fact is used by P1 for the general entry's
flags read after the `FAULT_IP` write; `BXI` comes from `JAtZ`). No premise
added. No existing top statement changed.
-/
import Fl4Proofs.P3.XTopJointKEntryU29
import Fl4Proofs.P1.FastIoLocal
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- **The I/O port entry beside the serial gate, accepted** (module
docstring): `kernel_entry_reachU29`'s syscall clause for
`handle_ioport_local`, on the runs that return `true`. -/
theorem kernel_entry_reachU29I [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
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
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
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
        syscall.handle_ioport_local st arI s a n ⦃ r => r.1 = true →
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.2.1 r.2.2 σ' ∧ SInvX σ' ∧ MR r.2.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧
            JReachU17 (L := L) arI AR MR r.2.1 r.2.2 σ' ⦄) := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, -, -, -, -, -, -, -, hSys, -, -, -, -, -⟩ :=
    kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, fun n c hct hn hflag hK hDec hFin => ?_⟩
  exact P1.ioport_local_triple arI hA J.bxi hflag (hSys n c hct hn hflag hK hDec hFin)

end

end

end Fl4Proofs.P3.SInvR.G5
