/-
P3 (DESIGN.md §9), invariant line g5d (KENTRY-PLAN g5d; g5c's handoff (1),
(3)): **`kernel_entryJ38E`** = `kernel_entryJ37E` without the entry premise
`FlagsRel`, and **`kernel_entry_reachIF`** = `kernel_entry_reachIP` without
its per-state `FlagsRel` premise.

`FlagsRel Z.T mem σ` (FL4's flags word `t+3456` gives the spec's
`tcb_flags`, l4v `tcb_relation`'s flags part) is now carried: g5d widened
`Sched.McpRel` (a field of `JAtZ`, `JRest`, `JAtZR`, `JAtZS`, kept by every
step) to relate the flags word with the MCP word (`flagsA`), its spec frame
`McpKeep` to keep `(tcb_mcpriority, tcb_flags)`, and every footprint lemma
that keeps the MCP word to keep the flags word too (`FinW` no longer admits
offset 3456; `KFoot.ne_flags`, `FinW.nf`, `JAtZ.cnW_nf`, the `*_keeps`
lemmas). The writers: SetFlags (`JAtZ.flagsWrJM`, `McpRel.setF`), SetMCP
(`McpRel.set`, flags word kept), the TCB retype (both words zero,
`McpRel.addT`, `w2f_zero`). So `FlagsRel` holds at every `JAtZ` state
(`FlagsRel.of_mcp`), across a syscall and across every event alike (every
`JAtZ` producer keeps `McpRel`).

`JReachIP`'s step never asked `FlagsRel`; with it a theorem of `JAtZ`,
`kernel_entry_reachIF` asks at a reachable state only `LargeFrOK` (and the
per-syscall `hflag`, `hK`, `hDM`, `hFin`, `hFast`) and its exits need
`SpecUtZ` to be reachable again (KENTRY-PLAN g5d for the two open carries).
-/
import Fl4Proofs.P3.XTopJointKEntry37E
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

/-- **`FlagsRel` at every `JAtZ` state** (`McpRel`'s flags part). -/
theorem _root_.Fl4Proofs.P3.JAtZ.flagsRel {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] : FlagsRel Z.T (L.mem s) σ :=
  FlagsRel.of_mcp J.mcp

/-- **`kernel_entryJ38E`**: `kernel_entryJ37E` without `hFl : FlagsRel`
(`JAtZ.flagsRel`). -/
theorem kernel_entryJ38E [Fl4Proofs.P1.PlainStore st] {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hct : σ.curThread ≠ σ.idleThread)
    (hR : MR a σ.machineState) (hX : SInvX σ) (hI : SInvIP σ)
    (hLF : LargeFrOK Z.G (L.mem s))
    (n : I64) (c : Fl4Spec.Syscall)
    (hn : NativeSys n c)
    (hflag : ∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hK : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        KDispHypsKV36E (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c)
    (hDM : ∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
      (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
        JDispMRI (L := L) arI AR MR s' a' σb n c)
    (hFin : ∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
      (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
        JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
        KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2)
    (hARI : ARIface arI AR) (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR)
    (hFast : n = fl4_abi.syscall.SysReplyRecv →
      FastRR (L := L) (arI := arI) s a n (fun r => KPostM (L := L) arI AR MR c σ r)) :
    syscall.handle_syscall st arI s a n ⦃ r => (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).2 ∨
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧
        MR r.2 σ'.machineState ∧ SInvX σ' ∧ SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ⦄ :=
  kernel_entryJ37E (MR := MR) s a σ J hct hR hX hI J.flagsRel hLF n c hn hflag hK hDM hFin hARI hA hnd
    hM hKD hPA hIA hmrt hmb hT hmax htu hRef hPI hFast

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **Refinement at every `JReachIP` state without `FlagsRel`**
(`kernel_entryJ38E`): at the ghosts `jreach_invIP` gives, the syscall entry
from a non-idle thread refines the spec's; every exit is related (`RJ`),
satisfies `SInvX`, `MR`, `SpecIoP`, `IoNoOverlap` and `FlagsRel` (at any
ghosts of its `JAtZ`), and is reachable again once `SpecUtZ` holds there.
Per-state premises: `LargeFrOK` at the entry, `hflag`, `hK`
(`KDispHypsKV36E`), `hDM` (`JDispMRI` [W]), `hFin`, `hFast`. -/
theorem kernel_entry_reachIF [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachIP (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvIP σ ∧ MR a σ.machineState ∧
      FlagsRel Z.T (L.mem s) σ ∧
      ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
      LargeFrOK Z.G (L.mem s) →
      (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
        ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
      (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
        (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
          JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
          KDispHypsKV36E (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
      (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
        (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
          JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
          JDispMRI (L := L) arI AR MR s' a' σb n c) →
      (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
        (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
          JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
          KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2) →
      (n = fl4_abi.syscall.SysReplyRecv →
        FastRR (L := L) (arI := arI) s a n (fun r => KPostM (L := L) arI AR MR c σ r)) →
      syscall.handle_syscall st arI s a n ⦃ r => (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).2 ∨
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧
          (SpecUtZ σ' → JReachIP (L := L) arI AR MR r.1 r.2 σ') ⦄ := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hI, hR, hall⟩ :=
    kernel_entry_reachIP (L := L) hARI hA hnd hM hKD hPA hIA hmrt hmb hT hmax htu hRef hPI hJ
  exact ⟨Z, H, Cs, Ac, Lst, D, J, hX, hI, hR, J.flagsRel,
    fun n c hct hn hLF => hall n c hct hn J.flagsRel hLF⟩

end

end

end Fl4Proofs.P3.SInvR.G5
