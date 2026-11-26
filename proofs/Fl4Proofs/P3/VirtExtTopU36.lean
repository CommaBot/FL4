/-
P3x for virtualization (line virt, gen 7, item 1): **U36I's syscall clause against the extended spec**
(`fl4KernelEntrySyscallV onCore true c σ`), with `NR` at every exit, at `virtKind = none`.

**`kernel_entry_syscallU36IV`**: premises U36I's (`kernel_entry_reachU36I`, XTopJointKEntryU36I) verbatim, plus
`hvk : virtKind = .none` [S], `onCore`, and `hNR : NR σ` (VirtR7e; e.g. `VirtNvK2.nr_boot` at boot, `runNR_nr` /
the exits of this theorem afterwards). Conclusion: U36I's `JAtZ` / `SInvX` witnesses and its syscall clause with
the ported entry `fl4KernelEntrySyscall true c σ` replaced by **`fl4KernelEntrySyscallV onCore true c σ`** and
`NR σ'` added at the exit; the clause's own premises are U36I's verbatim (`hflag`, `hK` = `KDispHypsKVU32`, `hDL`
= `JDecMRLK`, `hFin` = `KFinAtR13`) plus the scope below.

**Route scope.** Gen 6 (VirtExtTop.kentryV_post) needed `ScopeE c σ` [S]: no decode point of the entry on one of
the three routes. Here the clause asks only **`ScopeE6 c σ` [S]** (VirtAgree): at every on-route decode point the
ported and the extended decoder give the same single error (`ErrAgree`); `scopeE6_of` : `ScopeE → ScopeE6`.
VirtAgreeDec proves that this is what U36I's own premise forces at every on-route point it covers
(`agree_thread88`, `agree_frame60`, `agree_untypedGate`: U36I's `XCapP` leaf at the invoked slot + FL4's route-B
error ⇒ `DecAgreeAt`, the last one with gen 2's [P] `hvirt`). **Remaining gap (not closed):** deriving `ScopeE6 c σ`
from the clause's `hK` needs, for each spec dispatch state σb (`BudgetAt σ σb true`), an FL4 state `s'` with
`KFrontB s a s' a'` and `JAtZ … s' a' σb` (the front-end run: `FAULT_IP` write + `budget_ok`, JAtZ.budgetOkB) and,
at it, FL4's front-end reads (`msg_info`, `lookup_slot`, `lookup_ipc_buffer`, `lookup_extra_caps`, MRs:
FrontEndExtra) related to the spec decode point, to instantiate `JPathAtMU30` at the invoked slot and feed the
route-B side conditions (`hstall` via `JAtZ.stallT`, `ExtraSRel` via `ExtraOK`, the message words via
`JAtZ.argsJ`, `hnv` via `NVC`). That joint front-end walk lives inside U33's proof and is not exported; it is
the open item for `ScopeE6` to disappear.

Named premises: U36I's ([P] `MachPlatF`, `IpiF`, `IrqPlatK`, …; [J] `KDispHypsKVU32` / `JDecMRLK` / `KFinAtR13` in
the syscall clause, as U36I), `hvk` [S], `hNR` (state fact, discharged at boot by `nr_boot` and carried by this
theorem's exits), `hr : ScopeE6 c σ` [S] (syscall clause). No new [J]/[P]/[W]. New file only.
-/
import Fl4Proofs.P3.VirtAgree
import Fl4Proofs.P3.XTopJointKEntryU36I
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- **U36I's syscall clause against the extended spec** (module docstring): premises U36I's verbatim, `hvk` [S],
`hNR`, and in the clause the widened route scope `ScopeE6 c σ` [S]. -/
theorem kernel_entry_syscallU36IV [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlatF arI MR) (hIp : IpiF arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPAi : ∀ a c, AR a c → arI.irq_pending a ⦃ r => AR r.2 c ⦄) (hIA : IrqPlatK arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    (hvk : Fl4Spec.virtKind = .none) (onCore : Fl4Spec.ObjRef → Bool)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU36I (L := L) arI AR MR s a σ) (hNR : VirtR7e.NR σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU32 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        VirtAgree.ScopeE6 c σ →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscallV (Z := Unit) onCore true c σ).1 ∧
            (RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU36I (L := L) arI AR MR r.1 r.2 σ') ∧
            VirtR7e.NR σ' ⦄)
  := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, -, -, -, -, -, -, -, hSys, -, -, -, -, -⟩ :=
    kernel_entry_reachU36I arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, fun n c hct hn hfl hK hDL hFin hr => ?_⟩
  exact VirtAgree.kentryV_post6 hvk onCore hNR hr (hSys n c hct hn hfl hK hDL hFin)

end

end

end Fl4Proofs.P3.SInvR.G5
