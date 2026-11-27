/-
P3 (issue #16, g7a): **`kernel_entry_reachU6`** = g6a's `kernel_entry_reachU4`
without the finish bundle's `hd` (INV-PLAN §1.U3L D1): `σ.domainTime ≠ 0 ∨
NdOK s σ` at every pre-finish outcome is now a theorem.

* DomDecode's `DomRel` (carried in `RelTopM` / `XTopAt`) gained the
  `DOM_SCHED_IDX` word 0 (g7a): FL4 writes it only in `domain_set_start` (0)
  and `next_domain` (back to the start index 0, entry 1 being the end marker;
  SchedIdx's `sched.schedule.idx`).
* `JAtZR.hdOK`: at a `JAtZR` state whose spec state is `DomListOK`, `NdOK`:
  `DomRel` from `XTopAt`, the index word 0 and `domain_index = 0`
  (`DomListOK.idx0` with `DomRel`'s two entries).
* `DomListOK` at every outcome where the bundle is asked: SpecInvDom's `DP`
  family (`dp_specFront`: the FaultIP write and the event's handling with the
  preemption path; `dpe_handleE`/`dpe_fl4HandleEvent` for `KFinEv`), from
  `SInvX`'s `SInvA.dom` at the entry.
* `KFinAtR31N` (`KFinAtR31` without `hd`), `KFinEvN`, `.toR31`, `.toEv`.
-/
import Fl4Proofs.P3.XTopJointKEntryU4
import Fl4Proofs.P3.SchedIdx
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

/-- `specFront` keeps `DomListOK` (SpecInvDom's `DP` family). -/
theorem dp_specFront (hnd : Fl4Spec.numDomains = 1) (c : Fl4Spec.Syscall) {σ : Fl4Spec.State Unit}
    (hV : DomListOK σ) : ∀ x ∈ (specFront c σ).1, DomListOK x.2 := fun x hx =>
  SInvDom.dp_bind (SInvDom.dp_of_dl (SInvDom.dl_fl4SyscallFaultIP σ.curThread)) (fun _ =>
    SInvDom.dpe_handleE (SInvDom.dpe_fl4HandleEvent hnd true _) fun _ => SInvDom.dpe_of_dle (by dl_auto)) σ x hV hx

/-- The event handling keeps `DomListOK`. -/
theorem dp_event (hnd : Fl4Spec.numDomains = 1) (ev : Fl4Spec.Event) {σ : Fl4Spec.State Unit}
    (hV : DomListOK σ) : ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
      (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1, DomListOK x.2 := fun x hx =>
  SInvDom.dpe_handleE (SInvDom.dpe_fl4HandleEvent hnd true ev) (fun _ => SInvDom.dpe_of_dle (by dl_auto)) σ x hV hx

/-- `SInvX`'s `DomListOK`. -/
theorem sinvX_dom {σ : Fl4Spec.State Unit} (hX : SInvX σ) : DomListOK σ := hX.1.1.1.1.1.1.1.1.dom

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KFinAtR31` without `hd`.** -/
structure KFinAtR31N (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  arch : ArchSwF st arI Z.N Z.T Z.C Z.c
  archNd : ArchNdF st Z.N Z.T Z.C Z.c
  sni : SniHyp st arI Z.N Z.T Z.C Z.c
  send : SendHyp st arI Z.N Z.T Z.C Z.c
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

/-- `KFinEv` with `KFinAtR31N`. -/
def KFinEvN (AR : A → Fl4Spec.Cr3 → Prop) (ev : Fl4Spec.Event) (Kf : S → A → Prop) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
      (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1,
    ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
      Kf s' a' → JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 → KFinAtR31N (L := L) arI AR Z' H' Cs' s' a' x.2

variable {arI}

/-- **`hd` at a `JAtZR` state with `DomListOK`** (module docstring). -/
theorem _root_.Fl4Proofs.P3.JAtZR.hdOK {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : DomListOK σ) :
    σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ := by
  have hD : DomRel (L.mem s) (L.ksb s) σ := J.xtop.rel.2.2.2.1
  refine Or.inr ⟨hD, hV, ?_⟩
  rw [hD.2.2.2, hV.idx0 hD.1]; rfl

theorem KFinAtR31N.toR31 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (h : KFinAtR31N (L := L) arI AR Z H Cs s a σ)
    (hd : σ.domainTime ≠ 0 ∨ NdOK (L := L) s σ) : KFinAtR31 (L := L) arI AR Z H Cs s a σ :=
  ⟨hd, h.arch, h.archNd, h.sni, h.send, h.tail⟩

theorem KFinEvN.toEv (hnd : Fl4Spec.numDomains = 1) {AR : A → Fl4Spec.Cr3 → Prop} {ev : Fl4Spec.Event}
    {Kf : S → A → Prop} {σ : Fl4Spec.State Unit} (hV : DomListOK σ) (h : KFinEvN (L := L) arI AR ev Kf σ) :
    KFinEv (L := L) arI AR ev Kf σ := fun x hx Z' H' Cs' Ac' Lst' D' s' a' hK J' =>
  (h x hx Z' H' Cs' Ac' Lst' D' s' a' hK J').toR31 (J'.hdOK (dp_event hnd ev hV x hx))

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU4` without `KFinAtR31.hd`** (module docstring). -/
theorem kernel_entry_reachU6 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st)
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
            KFinAtR31N (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEvN (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEvN (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEvN (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEvN (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEvN (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU3 (L := L) arI AR MR r.1 r.2 σ' ⦄) := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU4 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hJ
  have hV := sinvX_dom hX
  have hVf : ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1, DomListOK w.2 := fun w hw =>
    SInvDom.dp_of_dl (SInvDom.dl_fl4SyscallFaultIP σ.curThread) σ w hV hw
  exact ⟨Z, H, Cs, Ac, Lst, D, J, hX, hW, hI, hN, hR, hFl, hPg,
    fun n c hct hn hfl hK hDL hFin => hSys n c hct hn hfl hK hDL
      (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hF J' =>
        (hFin x hx Z' H' Cs' Ac' Lst' D' s' a' hF J').toR31 (J'.hdOK (dp_specFront hnd c hV x hx))),
    fun w a1 hIh hE => hIrq w a1 hIh (hE.toEv hnd hV),
    fun n c hct hU hE => hUs n c hct hU (hE.toEv hnd hV),
    fun ad c ft hct hVm' hE => hVm ad c ft hct hVm' (hE.toEv hnd hV),
    fun v hct hv hE => hTr v hct hv fun ev hK w hw => (hE ev hK w hw).toEv hnd (hVf w hw),
    fun n hct hU hD hE => hSU n hct hU hD fun ev hK w hw => (hE ev hK w hw).toEv hnd (hVf w hw)⟩

end

end

end Fl4Proofs.P3.SInvR.G5
