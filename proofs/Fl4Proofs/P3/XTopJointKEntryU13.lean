/-
P3 (issue #16, sd7; KENTRY-PLAN g7a-4, g7b-4 step 2): **`kernel_entry_reachU13`** =
g7a-3's `kernel_entry_reachU11` without D7 `idle` (INV-PLAN §1.U3L).

* `IdleVtS σ` (SpecInvSiE: the idle TCB's vtable slot holds the null cap, spec only) is
  carried with the reachable states: **`JReachU13 s a σ := JReachU3 s a σ ∧ IdleVtS σ`**
  (`JReachU3` itself unchanged). Every clause of U13 ends in `JReachU13` at the exit
  state: U11's exit gives `JReachU3`, and `IdleVtS σ'` comes from the whole-entry
  lemmas `kentry_idleVtS` / `kcall_idleVtS` / `fip_kcall_idleVtS` at the entry, with
  sg1's `SpecGlobS`, `IdleOutV` and ut8's `UtInv3` from `SInvX` (as `kentry_sinvX` /
  `kentry_zr` carry their facts).
* `KFinAtR13` = `KFinAtR11` without `idle`; `KFinEv13` likewise. U11's `idle`
  (`IdleVt` at the finish state) from `IdleVtS` there (`front_idleVtS` for the syscall
  finish and the trap / unknown-syscall events, `handleE_idleVtS` for the other events)
  and the idle TCB at the finish state's `JAtZR` (`JAtZR.idleTcb`: the idle word is in
  `T`, `SchedCore.idleT`, and a `T` thread is a spec TCB, `StateRel.tcb`): `idleVt_of`.

Premise removed (relative to U11): D7 `idle` [J] (in the syscall finish bundle and in
every event's). Added: none; the start-state fact `IdleVtS σ` is asked at one state, in
`JReachU13`'s base (`JReachU13.start`; it holds at boot, `boot_idleVtS`).
-/
import Fl4Proofs.P3.XTopJointKEntryU11
import Fl4Proofs.P3.SpecInvSiE
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

theorem sinvX_sg {σ : Fl4Spec.State Unit} (hX : SInvX σ) : SInvG.SpecGlobS σ := hX.1.1.1.1.1.1.1.1.sg

theorem sinvX_idleOut {σ : Fl4Spec.State Unit} (hX : SInvX σ) : SInvG.IdleOutV σ := hX.1.1.1.1.1.1.1.1.idleOut

/-- `IdleVt` from the spec-only vtable fact and the idle TCB. -/
theorem idleVt_of {σ : Fl4Spec.State Unit} (hx : ∃ x, σ.kheap σ.idleThread = some (.tcb x))
    (h : SInvIV.IdleVtS σ) : IdleVt σ := by
  obtain ⟨x, hx⟩ := hx
  refine ⟨x, hx, fun p asid e => ?_⟩
  have hc : SInvU.capAt σ (σ.idleThread, Fl4Spec.tcbCnodeIndex 1) = some x.tcbVtable := by
    unfold SInvU.capAt; rw [hx]; exact tcbCnodeMap_one x
  have e2 : x.tcbVtable = .nullCap := h _ hc
  rw [e2] at e; cases e

/-- `IdleVtS` at the exit of a kernel event. -/
theorem evOut_idleVtS {fip : Bool} {ev : Fl4Spec.Event} {σ σ' : Fl4Spec.State Unit} (hX : SInvX σ)
    (hV : SInvIV.IdleVtS σ) (h : EvOut fip ev σ σ') : SInvIV.IdleVtS σ' := by
  cases fip
  · unfold EvOut at h
    exact SInvIV.kcall_idleVtS true ev (sinvX_sg hX) (sinvX_idleOut hX) (sinvX_ut3 hX) hV _ h
  · unfold EvOut at h
    obtain ⟨w, hw, h⟩ := h
    exact SInvIV.fip_kcall_idleVtS σ.curThread ev (sinvX_sg hX) (sinvX_idleOut hX) (sinvX_ut3 hX) hV _ ⟨w, hw, h⟩

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KFinAtR11` without `idle`.** -/
structure KFinAtR13 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  arch : ArchSwF st arI Z.N Z.T Z.C Z.c
  archNd : ArchNdF st Z.N Z.T Z.C Z.c

/-- `KFinEv11` with `KFinAtR13`. -/
def KFinEv13 (AR : A → Fl4Spec.Cr3 → Prop) (ev : Fl4Spec.Event) (Kf : S → A → Prop) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
      (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1,
    ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
      Kf s' a' → JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 → KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2

variable {arI}

/-- **The idle thread is a spec TCB at a `JAtZR` state** (the idle word is a `T` thread). -/
theorem _root_.Fl4Proofs.P3.JAtZR.idleTcb {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) : ∃ x, σ.kheap σ.idleThread = some (.tcb x) := by
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hth : Z.th (nodeW st s Z.c layout.node.IDLE_THREAD) = some .tcb := (hJ.tcb _).2 (J.zH.1 _ hc.idleT)
  obtain ⟨x, hkx, -⟩ := J.xtop.rel.2.1.1.tcb _ hth
  exact ⟨x, by rw [hs.idleTh]; exact hkx⟩

theorem KFinAtR13.to11 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : KFinAtR13 (L := L) arI AR Z H Cs s a σ) (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hV : SInvIV.IdleVtS σ) : KFinAtR11 (L := L) arI AR Z H Cs s a σ :=
  ⟨h.arch, h.archNd, idleVt_of J.idleTcb hV⟩

theorem KFinEv13.to11 {AR : A → Fl4Spec.Cr3 → Prop} {ev : Fl4Spec.Event} {Kf : S → A → Prop}
    {σ : Fl4Spec.State Unit} (hV : ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
      (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1, SInvIV.IdleVtS x.2)
    (h : KFinEv13 (L := L) arI AR ev Kf σ) : KFinEv11 (L := L) arI AR ev Kf σ :=
  fun x hx Z' H' Cs' Ac' Lst' D' s' a' hK J' => (h x hx Z' H' Cs' Ac' Lst' D' s' a' hK J').to11 J' (hV x hx)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states carrying the idle vtable fact** (module docstring). -/
abbrev JReachU13 (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  JReachU3 (L := L) arI AR MR s a σ ∧ SInvIV.IdleVtS σ

variable {arI AR MR}

/-- The base: a start state of `JReachU3` with the idle vtable fact (one state). -/
theorem JReachU13.start {s : S} {a : A} {σ : Fl4Spec.State Unit} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hvx : VxE Z) (hX : SInvX σ)
    (hI : SInvIP σ) (hM : MR a σ.machineState) (hP : SInvUZ.UtPgR σ) (hV : SInvIV.IdleVtS σ) :
    JReachU13 (L := L) arI AR MR s a σ :=
  ⟨JReachU3.start J hvx hX hI hM hP, hV⟩

variable (arI AR MR)

set_option maxHeartbeats 8000000 in
/-- **`kernel_entry_reachU11` without D7 `idle`** (module docstring). -/
theorem kernel_entry_reachU13 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU13 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ SInvR.B8w.SInvW σ ∧ SInvIP σ ∧
      SInvIo.IoNoOverlap σ ∧ MR a σ.machineState ∧ FlagsRel Z.T (L.mem s) σ ∧ SInvUZ.UtPgR σ ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKVU7 (L := L) arI AR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            ∀ ct', sched.cur_thread st s' = ok ct' →
              JDecMRLK (L := L) arI VtxK AR MR (Z.mv Z.G V') H Cs D' s' a' σb ct') →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ SInvUZ.UtPgR σ' ∧ JReachU13 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU13 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv13 (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU13 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU13 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU13 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          SpecIoP σ' ∧ SInvIo.IoNoOverlap σ' ∧ SpecUtZ σ' ∧ JReachU13 (L := L) arI AR MR r.1 r.2 σ' ⦄) := by
  have hV := hJ.2
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    kernel_entry_reachU11 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ.1
  have hG := sinvX_sg hX
  have hO := sinvX_idleOut hX
  have hU := sinvX_ut3 hX
  have hVh : ∀ ev, ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
      (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1, SInvIV.IdleVtS x.2 :=
    fun ev => SInvIV.handleE_idleVtS true ev hG hO hU hV
  have hVf : ∀ ev, ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
      ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
        (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run w.2).1, SInvIV.IdleVtS x.2 :=
    fun ev w hw x hx => SInvIV.front_idleVtS σ.curThread true ev hG hO hU hV x ⟨w, hw, hx⟩
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hW, hI, hN, hR, hFl, hPg,
    fun n c hct hn hfl hK hDL hFin => ?_, fun w a1 hIh hE => ?_, fun n c hct hU' hE => ?_,
    fun ad c ft hct hVm' hE => ?_, fun v hct hv hE => ?_, fun n hct hU' hD hE => ?_⟩
  · refine WP.spec_mono (hSys n c hct hn hfl hK hDL fun x hx Z' H' Cs' Ac' Lst' D' s' a' hF J' =>
      (hFin x hx Z' H' Cs' Ac' Lst' D' s' a' hF J').to11 J'
        (SInvIV.front_idleVtS σ.curThread true (.syscallEvent c) hG hO hU hV x hx))
      fun r ⟨σ', hy, hRJ, hX', hM', h1, h2, h3, h4, hk⟩ => ?_
    exact ⟨σ', hy, hRJ, hX', hM', h1, h2, h3, h4, hk, SInvIV.kentry_idleVtS c hG hO hU hV _ hy⟩
  · exact WP.spec_mono (hIrq w a1 hIh (hE.to11 (hVh _))) fun r ⟨σ', hO', hRJ, hX', hM', h1, h2, h3, hk⟩ =>
      ⟨σ', hO', hRJ, hX', hM', h1, h2, h3, hk, evOut_idleVtS hX hV hO'⟩
  · exact WP.spec_mono (hUs n c hct hU' (hE.to11 (hVh _))) fun r ⟨σ', hO', hRJ, hX', hM', h1, h2, h3, hk⟩ =>
      ⟨σ', hO', hRJ, hX', hM', h1, h2, h3, hk, evOut_idleVtS hX hV hO'⟩
  · exact WP.spec_mono (hVm ad c ft hct hVm' (hE.to11 (hVh _))) fun r ⟨σ', hO', hRJ, hX', hM', h1, h2, h3, hk⟩ =>
      ⟨σ', hO', hRJ, hX', hM', h1, h2, h3, hk, evOut_idleVtS hX hV hO'⟩
  · exact WP.spec_mono (hTr v hct hv fun ev hK w hw => (hE ev hK w hw).to11 (hVf ev w hw))
      fun r ⟨ev, σ', hK, hO', hRJ, hX', hM', h1, h2, h3, hk⟩ =>
      ⟨ev, σ', hK, hO', hRJ, hX', hM', h1, h2, h3, hk, evOut_idleVtS hX hV hO'⟩
  · exact WP.spec_mono (hSU n hct hU' hD fun ev hK w hw => (hE ev hK w hw).to11 (hVf ev w hw))
      fun r ⟨ev, σ', hK, hO', hRJ, hX', hM', h1, h2, h3, hk⟩ =>
      ⟨ev, σ', hK, hO', hRJ, hX', hM', h1, h2, h3, hk, evOut_idleVtS hX hV hO'⟩

end

end

end Fl4Proofs.P3.SInvR.G5
