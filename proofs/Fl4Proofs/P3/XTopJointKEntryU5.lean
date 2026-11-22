/-
P3 (issue #16, g6b): **`kernel_entry_reachU5`** = g6a's `kernel_entry_reachU4`
with the fixed finish bundle (INV-PLAN §1.U3L.H).

* `KFinAtR5`: `KFinAtR31` without `sni` (`SniHyp`) and `send` (`SendHyp`).
  Both are theorems now (ScSniProof): `sniHyp_of` from `ArchTotal` and
  `SetDlDet` [P], `sendHyp_of` from `ArchTotal`. (`SniHyp` itself was narrowed
  in place to `SniPre` states, where it is consumed: before, it was false at
  every related state whose current thread has no SC.) `KFinEv5`: `KFinEv`
  with `KFinAtR5`.
* `SetDlDetR MR` [P]: the timer's opaque `setDeadlineImpl` has at most one
  outcome at every `MR`-related machine state. With `MachPlat.frame` (`MR` does
  not read `machineStateRest`) and the `MR` state the top's reachability
  carries, it gives the state-free `SetDlDet` (`setDlDet_of`).
* `kernel_entry_reachU5`: `kernel_entry_reachU4` with `hFin` / every `KFinEv`
  asking `KFinAtR5`, and the new platform premise `hDR`. Premises removed: D4
  `sni`, D5 `send` (both ∀st). Added: `hDR` (a fact of the opaque timer
  operation, under `MR`).
-/
import Fl4Proofs.P3.XTopJointKEntryU4
import Fl4Proofs.P3.ScSniProof
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **[P] The timer's opaque `setDeadlineImpl` has at most one outcome at an
`MR`-related machine state** (module docstring). -/
def SetDlDetR (MR : A → Fl4Spec.MachineState → Prop) : Prop :=
  ∀ (a : A) (ms : Fl4Spec.MachineState), MR a ms → ∀ (d : Fl4Spec.Word64) (x y : Unit × Fl4Spec.MachineStateRest),
    x ∈ (Fl4Spec.setDeadlineImpl d ms.machineStateRest).1 → y ∈ (Fl4Spec.setDeadlineImpl d ms.machineStateRest).1 →
      x = y

/-- `SetDlDet` from `SetDlDetR` at one `MR` state: `MR` does not read the
machine-state rest (`MachPlat.frame`). -/
theorem setDlDet_of {MR : A → Fl4Spec.MachineState → Prop} (hM : MachPlat arI MR) (hDR : SetDlDetR (A := A) MR)
    {a : A} {ms : Fl4Spec.MachineState} (h : MR a ms) : SetDlDet := fun d mr x y hx hy =>
  hDR a { ms with machineStateRest := mr } (hM.frame a ms _ h rfl rfl rfl rfl) d x y hx hy

/-- **`KFinAtR31` without `sni` and `send`** (module docstring). -/
structure KFinAtR5 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ
  arch : ArchSwF st arI Z.N Z.T Z.C Z.c
  archNd : ArchNdF st Z.N Z.T Z.C Z.c
  tail : sched.schedule st arI s a ⦃ r => ∀ (rf : S × A) σ1 σ' (D1 : Set U64), Fires σ σ1 →
      timer.fire st arI s a = ok rf →
      ((∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZR (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) ∨
       ∃ (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D2 : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D2 rf.1 rf.2 σ1) →
      Fl4Spec.schedule (Z := Unit) σ1 = ({((), σ')}, False) →
      P1.WritesIn st rf.1 r.1 (KFootN st Z.T Z.N Z.C Z.c rf.1 σ1) →
      SchedRel st Z.N Z.T Z.C Z.c r.1 σ' → Inv σ' → CurInv σ' → ActIdle σ' →
      SchTailHypsR AR Z H D1 r.1 r.2 σ' ⦄

variable {arI}

theorem KFinAtR5.to31 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (hA : P0.ArchTotal arI) (hD : SetDlDet) (F : KFinAtR5 (L := L) arI AR Z H Cs s a σ) :
    KFinAtR31 (L := L) arI AR Z H Cs s a σ :=
  ⟨F.hd, F.arch, F.archNd, sniHyp_of hA hD, sendHyp_of hA, F.tail⟩

variable (arI)

/-- `KFinEv` with `KFinAtR5`. -/
def KFinEv5 (AR : A → Fl4Spec.Cr3 → Prop) (ev : Fl4Spec.Event) (Kf : S → A → Prop) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
      (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1,
    ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
      Kf s' a' → JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 → KFinAtR5 (L := L) arI AR Z' H' Cs' s' a' x.2

variable {arI}

theorem KFinEv5.to {AR : A → Fl4Spec.Cr3 → Prop} {ev : Fl4Spec.Event} {Kf : S → A → Prop} {σ : Fl4Spec.State Unit}
    (hA : P0.ArchTotal arI) (hD : SetDlDet) (h : KFinEv5 (L := L) arI AR ev Kf σ) : KFinEv (L := L) arI AR ev Kf σ :=
  fun x hx Z' H' Cs' Ac' Lst' D' s' a' hK J => (h x hx Z' H' Cs' Ac' Lst' D' s' a' hK J).to31 hA hD

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU4` with `KFinAtR5`** (module docstring): no
∀-state timer or IPI premise; KFinAtR31 is satisfiable in its `sni`/`send`
fields (they are theorems). -/
theorem kernel_entry_reachU5 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInVal arI) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU3 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU4 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR5 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv5 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv5 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv5 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv5 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv5 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU4 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hJ
  have hD : SetDlDet := setDlDet_of arI hM hDR hR
  exact ⟨Z, H, Cs, Ac, Lst, D, J, hX, hW, hI, hN, hR, hFl, hPg,
    fun n c hct hn hfl hK hDL hFin => hSys n c hct hn hfl hK hDL
      (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hF J' => (hFin x hx Z' H' Cs' Ac' Lst' D' s' a' hF J').to31 hA hD),
    fun w a1 hw hF => hIrq w a1 hw (hF.to hA hD),
    fun n c hct hu hF => hUs n c hct hu (hF.to hA hD),
    fun ad c ft hct hv hF => hVm ad c ft hct hv (hF.to hA hD),
    fun v hct hv hF => hTr v hct hv (fun ev he w hw => (hF ev he w hw).to hA hD),
    fun n hct hu hnd' hF => hSU n hct hu hnd' (fun ev he w hw => (hF ev he w hw).to hA hD)⟩

end

end

end Fl4Proofs.P3.SInvR.G5
