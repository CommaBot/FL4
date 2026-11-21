/-
P3 (DESIGN.md §9), invariant line G4 (g4i, KENTRY-PLAN g4i): **the
induction where every FL4 event entry is proved** (no `JEvRef`).

* `JReachE4`: `JReachE3`'s `start` / `step` / `irq` / `user` / `vmf`, and in
  place of the generic `event` step the two FaultIP entries: `trap`
  (`int $N`, a vector below 256 [P]) and `sysU` (the unknown syscall through
  `handle_syscall`, under the [S] scope `UnkSys` / `NoDbgSys`). `irq` was
  already free of `ct ≠ idle`. `JReachE4.toE3`, `jreach_invE4`.
* `kernel_entry_reachE4`: at every `JReachE4` state, the native syscall
  entry (J37N's per-state premises), the interrupt entry from any current
  thread (`jEvRef_irqA`: g4i's idle case, no `ct ≠ idle`), the user-exception
  and VM-fault entries (`UserHw` / `VmfHw`), `int $N` (`jEvRef_trap`) and the
  unknown syscall (`jEvRef_sysU`: `UnkSys`, `NoDbgSys` [S], `FastFaultOK` [J]
  at the entry state, `StoreExt` [P]), each with its finish bundle `KFinEv` /
  `hFin`, ending related with `SInvX`, `MR` and `JReachE4` again. No clause
  takes `JEvRef`.
-/
import Fl4Proofs.P3.XTopJointKEntryEv6
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states, every event entry proved** (module docstring). -/
inductive JReachE4 : S → A → Fl4Spec.State Unit → Prop
  | start {s : S} {a : A} {σ : Fl4Spec.State Unit} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
      {Lst : U64 → List U64} {D : Set U64} :
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SInvX σ → MR a σ.machineState → JReachE4 s a σ
  | step {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (c : Fl4Spec.Syscall) :
      JReachE4 s a σ → σ.curThread ≠ σ.idleThread → NativeSys n c →
      syscall.handle_syscall st arI s a n = ok (s', a') →
      ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 →
      RJM (L := L) arI AR MR s' a' σ' → JReachE4 s' a' σ'
  | irq {s : S} {a a1 : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (w : U64) :
      JReachE4 s a σ → IrqHw AR MR a a1 σ w → syscall.handle_interrupt_entry st arI s a1 w = ok (s', a') →
      EvOut false .interrupt σ σ' → RJM (L := L) arI AR MR s' a' σ' → JReachE4 s' a' σ'
  | user {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n c : U64) :
      JReachE4 s a σ → σ.curThread ≠ σ.idleThread → UserHw n c →
      syscall.handle_user_exception st arI s a n c = ok (s', a') →
      EvOut false (.userLevelFault n.bv c.bv) σ σ' → RJM (L := L) arI AR MR s' a' σ' → JReachE4 s' a' σ'
  | vmf {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (ad c : U64)
      (ft : Fl4Spec.VMFaultType) :
      JReachE4 s a σ → σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
      syscall.handle_vm_fault st arI s a ad c = ok (s', a') →
      EvOut false (.vmFaultEvent ft) σ σ' → RJM (L := L) arI AR MR s' a' σ' → JReachE4 s' a' σ'
  | trap {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (v : U64)
      (ev : Fl4Spec.Event) :
      JReachE4 s a σ → σ.curThread ≠ σ.idleThread → v.val < 256 → KEvSpec (.trap v) true ev →
      syscall.handle_trap_syscall st arI s a v = ok (s', a') → EvOut true ev σ σ' →
      RJM (L := L) arI AR MR s' a' σ' → JReachE4 s' a' σ'
  | sysU {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (ev : Fl4Spec.Event) :
      JReachE4 s a σ → σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
      KEvSpec (.sysU n) true ev → syscall.handle_syscall st arI s a n = ok (s', a') → EvOut true ev σ σ' →
      RJM (L := L) arI AR MR s' a' σ' → JReachE4 s' a' σ'

variable {arI AR MR}

/-- Every `JReachE4` state is a `JReachE3` state (`trap` / `sysU` are `JReachE3.event` steps). -/
theorem JReachE4.toE3 {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JReachE4 (L := L) arI AR MR s a σ) :
    JReachE3 (L := L) arI AR MR s a σ := by
  induction h with
  | @start s a σ Z H Cs Ac Lst D J hX hR => exact JReachE3.start J hX hR
  | @step s a σ s' a' σ' n c _ hct hn hv hy hRJ ih => exact JReachE3.step n c ih hct hn hv hy hRJ
  | @irq s a a1 σ s' a' σ' w _ hI hv hO hRJ ih => exact JReachE3.irq w ih hI hv hO hRJ
  | @user s a σ s' a' σ' n c _ hct hU hv hO hRJ ih => exact JReachE3.user n c ih hct hU hv hO hRJ
  | @vmf s a σ s' a' σ' ad c ft _ hct hV hv hO hRJ ih => exact JReachE3.vmf ad c ft ih hct hV hv hO hRJ
  | @trap s a σ s' a' σ' v ev _ hct _ hK hv hO hRJ ih =>
    exact JReachE3.event (.trap v) true ev ih hK (fun _ => hct) hv hO hRJ
  | @sysU s a σ s' a' σ' n ev _ hct _ _ hK hv hO hRJ ih =>
    exact JReachE3.event (.sysU n) true ev ih hK (fun _ => hct) hv hO hRJ

/-- **The invariant** of `JReachE4`: `JAtZ` at some ghosts, `SInvX`, `MR`. -/
theorem jreach_invE4 (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JReachE4 (L := L) arI AR MR s a σ) :
    (∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) ∧ SInvX σ ∧ MR a σ.machineState :=
  jreach_invE3 hnd h.toE3

set_option maxHeartbeats 8000000 in
/-- **Refinement at every reachable state, no `JEvRef`** (module docstring). -/
theorem kernel_entry_reachE4 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hmrt : ∀ a, sporadic.max_release_time arI a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : ∀ a : A, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInVal arI) (hSX : P1.StoreExt st)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachE4 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ SInvX σ ∧ MR a σ.machineState ∧
      (∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
        (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
          ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            KDispHypsKV35 (L := L) arI AR MR (Z.mv Z.G V') H Cs D' s' a' σb n c) →
        (∀ σb, BudgetAt σ σb true → ∀ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64)
          (s' : S) (a' : A), KFrontB (L := L) arI s a s' a' →
            JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' s' a' σb →
            JDispMRI (L := L) arI AR MR s' a' σb n c) →
        (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64)
          (D' : Set U64) (s' : S) (a' : A), KFrontF (L := L) arI n s a s' a' →
            JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
            KFinAtR31 (L := L) arI AR Z' H' Cs' s' a' x.2) →
        (n = fl4_abi.syscall.SysReplyRecv →
          FastRR (L := L) (arI := arI) s a n (fun r => KPostMS (L := L) arI AR MR c σ r)) →
        syscall.handle_syscall st arI s a n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
            RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
            JReachE4 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (w : U64) (a1 : A), IrqHw AR MR a a1 σ w →
        KFinEv (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
        syscall.handle_interrupt_entry st arI s a1 w ⦃ r => ∃ σ', EvOut false .interrupt σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          JReachE4 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n c : U64), σ.curThread ≠ σ.idleThread → UserHw n c →
        KFinEv (L := L) arI AR (.userLevelFault n.bv c.bv) (KFrontF2 (st := st) arI (brU (st := st) arI n c) s a) σ →
        syscall.handle_user_exception st arI s a n c ⦃ r => ∃ σ', EvOut false (.userLevelFault n.bv c.bv) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          JReachE4 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
        KFinEv (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
        syscall.handle_vm_fault st arI s a ad c ⦃ r => ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          JReachE4 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (v : U64), σ.curThread ≠ σ.idleThread → v.val < 256 →
        (∀ ev, KEvSpec (.trap v) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv (L := L) arI AR ev (KFrontTrap (st := st) arI s a) w.2) →
        syscall.handle_trap_syscall st arI s a v ⦃ r => ∃ ev σ', KEvSpec (.trap v) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          JReachE4 (L := L) arI AR MR r.1 r.2 σ' ⦄) ∧
      (∀ (n : I64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
        P1.FastFaultOK (L := L) arI s a n →
        (∀ ev, KEvSpec (.sysU n) true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
          KFinEv (L := L) arI AR ev (KFrontSysU (st := st) arI n s a) w.2) →
        syscall.handle_syscall st arI s a n ⦃ r => ∃ ev σ', KEvSpec (.sysU n) true ev ∧ EvOut true ev σ σ' ∧
          RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ' ∧ MR r.2 σ'.machineState ∧
          JReachE4 (L := L) arI AR MR r.1 r.2 σ' ⦄) := by
  obtain ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, hX, hR⟩ := jreach_invE4 hnd hJ
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hR, fun n c hct hn hflag hK hDM hFin hFast => ?_,
    fun w a1 hI hFin => ?_, fun n c hct hU hFin => ?_, fun ad c ft hct hV hFin => ?_,
    fun v hct hv hFin => ?_, fun n hct hU hD hFF hFin => ?_⟩
  · have hE := kernel_entryJ37N (MR := MR) s a σ J hct hR hX n c hn hflag hK hDM hFin hARI hA hnd hM hKD hPA hIA
      hmrt hmb hT hmax htu hRef hPI hFast
    obtain ⟨⟨s', a'⟩, hv, σ', hy, hRJ, hM', hX'⟩ := spec_exists hE
    rw [hv, WP.spec_ok]
    exact ⟨σ', hy, hRJ, hX', hM', JReachE4.step n c hJ hct hn hv hy ⟨hRJ, hM'⟩⟩
  · have hE := jEvRef_irqA J hX hI hFin hARI hA hnd hM hKD hIA hmrt hmb hT hmax htu
    obtain ⟨⟨s', a'⟩, hv, σ', hO, hRJM⟩ := spec_exists hE
    rw [hv, WP.spec_ok]
    exact ⟨σ', hO, hRJM.1, kcall_sinvX hnd true .interrupt hX (fun h => absurd rfl h) _ hO, hRJM.2,
      JReachE4.irq w hJ hI hv hO hRJM⟩
  · have hE := jEvRef_user n c J hX hct hR (jFltHyp_user hnd hM hKD hA hX hct n c hU) hFin hARI hA hnd hM hKD hmrt
      hmb hT hmax htu
    obtain ⟨⟨s', a'⟩, hv, σ', hO, hRJM⟩ := spec_exists hE
    rw [show syscall.handle_user_exception st arI s a n c = (KEv.user n c).run st arI s a from rfl, hv, WP.spec_ok]
    exact ⟨σ', hO, hRJM.1, sinvX_evOut hnd hX (fun _ => hct) (fun h => by cases h) hO, hRJM.2,
      JReachE4.user n c hJ hct hU hv hO hRJM⟩
  · have hE := jEvRef_vmf ad c ft J hX hct hR (jFltHyp_vmf hnd hM hKD hA hX hct ad c ft hV) hFin hARI hA hnd hM hKD
      hmrt hmb hT hmax htu
    obtain ⟨⟨s', a'⟩, hv, σ', hO, hRJM⟩ := spec_exists hE
    rw [show syscall.handle_vm_fault st arI s a ad c = (KEv.vmf ad c).run st arI s a from rfl, hv, WP.spec_ok]
    exact ⟨σ', hO, hRJM.1, sinvX_evOut hnd hX (fun _ => hct) (fun h => by cases h) hO, hRJM.2,
      JReachE4.vmf ad c ft hJ hct hV hv hO hRJM⟩
  · have hE := jEvRef_trap hnd v hv J hX hct hR hFin hARI hA hM hKD hmrt hmb hT hmax htu
    obtain ⟨⟨s', a'⟩, hrun, ev, σ', hK, hO, hRJM⟩ := spec_exists hE
    rw [hrun, WP.spec_ok]
    exact ⟨ev, σ', hK, hO, hRJM.1, sinvX_evOut hnd hX (fun _ => hct) (fun _ => sinvX_fip hX) hO, hRJM.2,
      JReachE4.trap v ev hJ hct hv hK hrun hO hRJM⟩
  · have hE := jEvRef_sysU hnd n J hX hct hR hU hD hSX hFF hFin hARI hA hM hKD hmrt hmb hT hmax htu
    obtain ⟨⟨s', a'⟩, hrun, ev, σ', hK, hO, hRJM⟩ := spec_exists hE
    rw [hrun, WP.spec_ok]
    exact ⟨ev, σ', hK, hO, hRJM.1, sinvX_evOut hnd hX (fun _ => hct) (fun _ => sinvX_fip hX) hO, hRJM.2,
      JReachE4.sysU n ev hJ hct hU hD hK hrun hO hRJM⟩

end

end

end Fl4Proofs.P3
