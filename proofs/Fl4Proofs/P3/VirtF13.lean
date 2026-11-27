/-
P3x for virtualization (line virt, gen 13, item 1, spec half): **FL4's report ops (`Ext/VirtKernelF`) are the
ported kernel on `NR` states**, in the same scope as the `V` ops (VirtScope8), so the extended-spec top moves onto
the FL4-faithful step `fl4CallKernelVF onCore remoteCur` with no new premise.

The `…VF` definitions are the `…V` ones with `vmCheckF` / `vmEnterF` / `vcpuDetachF` / `associateVcpuTcbF` /
`sendSignalVF` / `performVcpuInvocationF` substituted (gen 12, `Ext/VirtKernelF`). On an `NR` state none of the
substituted operations is reached with an effect: no thread is `runningVM` (so `sendSignalVF` takes the ported
branch — its extra `vmSignalCompletes` read is deterministic and keeps the state, whatever `onCore` / `remoteCur`
say — and `vmCheckF` of the current thread does nothing), there is no VCPU (so `vcpuDetachF` does nothing and
`isVmEnterCall` is false, `vmEnterF` is never reached), and no virtualization cap is decoded. The proofs are the
`V` chain's (VirtR7b, VirtR7d, VirtAwaken, VirtNvTcb, VirtR7e, VirtR7eK, VirtAgree, VirtScope8, VirtExtTop,
VirtKEntryV2) with the `F` names; the leaves that differ are new:

* `vmSignalCompletes_det`, **`sendSignalVF_eq_nr`** (on `NoRunVM`, `sendSignalVF = sendSignal`, every
  `onCore` / `remoteCur`), `vmCheckF_ctExit`, `vcpuDetachF_nvv`, `finaliseCapVF_eq`, `fl4PerformInvocationVF_base`.
* Twins: `activateThreadV_vmCheckF`, `exitTailVF_eq`, `fl4KernelExitVF_eq`, the timer chain (`timerSignalVF_iff`,
  `timerFireVF_iff`, `timerFiresVF_iff`, `fl4AwakenVF_eq`, `fl4KernelExitVF_eq'`), the interrupt paths
  (`when_sendSignalVF_eq`, `handleInterruptVF_eq`, `maybeHandleInterruptVF_eq`, `preemptionPathVF_eq`), deletion
  (`finaliseCapVF_agree`, `recDelFVF_mono`, `recDel_agreeF`, `recDelVF_eq`, `capDeleteVF_eq`, `capRevokeFVF_mono`,
  `capRevoke_agreeF`, `capRevokeVF_eq`), `invokeCnodeVF_eq`, `installTcbCapVF_eq`, `installTcbFrameCapVF_eq`,
  `toPF`, `invokeTcbVF_eq`, `fl4PerformInvocationVF_eqNR`, `fl4HandleInvocationVF_eqNR6`, `invoke_congrF6(0)`,
  `fl4HandleSyscallVF_eqNR8`, `fl4HandleEventVF_unknown_nvv`, `fl4HandleEventVF_interrupt`,
  `fl4HandleEventVF_syscall8`, `fl4HandleEventVF_eqNR8`, **`fl4CallKernelVF_eqNR8`**,
  **`fl4KernelEntrySyscallVF_eqNR8`**, `kentryVF_post8`.
* **F = V**: `fl4CallKernelVF_eq_V8`, `fl4KernelEntrySyscallVF_eq_V8` (both are the ported step there).
* Exit predicates `EvOutVF`, `EvOutVTF` (VirtExtTop's `EvOutV`, VirtKEntryV's `EvOutVT` on the F step) and their
  transports from the `V` exits `evOutVF_of_V`, `evOutVTF_of_V`, `kentryVF_of_V`, and `kentryVF_post8` from the
  ported one.

Named premises: only those of the `V` chain — `hvk : virtKind = .none` [S] and the scope `OffRouteS8` / `ScopeE8`
[S] (VirtScope8) where the `V` lemma has it. `remoteCur` is a parameter, never constrained (on `NoRunVM` states
FL4's `signal_completes` is not consulted). No [J]/[P]/[W]. New file only.
-/
import Fl4Proofs.P3.VirtScope8
import Fl4Proofs.P3.VirtKEntryV
import Fl4Proofs.P3.VirtReportEq
import Fl4Spec.Ext.VirtKernelF
open Aeneas Aeneas.Std Result
open Classical

namespace Fl4Proofs.P3.VirtF13
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvDom
  Fl4Proofs.P3.SInvTY Fl4Proofs.P3.VirtR7b Fl4Proofs.P3.VirtR7d Fl4Proofs.P3.VirtAwaken Fl4Proofs.P3.VirtR7e
  Fl4Proofs.P3.VirtR7eK Fl4Proofs.P3.VirtR7eK2 Fl4Proofs.P3.VirtNvTcb Fl4Proofs.P3.VirtNvcW Fl4Proofs.P3.VirtOffNv
  Fl4Proofs.P3.VirtInvOK Fl4Proofs.P3.VirtTcbOK Fl4Proofs.P3.VirtNvInv Fl4Proofs.P3.VirtNvK1 Fl4Proofs.P3.VirtTyK7
  Fl4Proofs.P3.VirtNvK2 Fl4Proofs.P3.VirtExtTop Fl4Proofs.P3.VirtAgree Fl4Proofs.P3.VirtScope8

noncomputable section

set_option maxHeartbeats 4000000

/-! ## The new leaves -/

/-- FL4's `signal_completes` read at a TCB: one outcome, the state kept. -/
theorem vmSignalCompletes_det (onCore remoteCur : ObjRef → Bool) {σ : State Unit} {t : ObjRef} {x : Tcb}
    (hk : σ.kheap t = some (.tcb x)) :
    ∃ c, vmSignalCompletes (Z := Unit) onCore remoteCur t σ = ({(c, σ)}, False) := by
  unfold vmSignalCompletes
  rw [Notif.nd_bind_one (VirtReportEq.getTcbVcpu_eq σ t)]
  rcases hv : tcbVcpuOf σ t with _ | v
  · exact ⟨false, rfl⟩
  · obtain ⟨st, hst, -⟩ := tcbVcpuOf_some hv
    dsimp only
    rw [Notif.nd_bind_one (VirtReportEq.getVcpu_eq hst), Notif.nd_bind_one (VirtReportEq.vmFullReply_eq hk)]
    exact ⟨_, rfl⟩

/-- **FL4's `send_signal` is the ported `sendSignal` on every `NoRunVM` state**, for every `onCore`,
`remoteCur`, notification and badge. -/
theorem sendSignalVF_eq_nr (onCore remoteCur : ObjRef → Bool) {σ : State Unit} (hn : NoRunVM σ) (n : ObjRef)
    (b : Badge) : sendSignalVF (Z := Unit) onCore remoteCur n b σ = sendSignal n b σ := by
  rw [← sendSignalV_eq_nr onCore hn n b]
  unfold sendSignalVF sendSignalV
  refine nd_bind_congr_on _ _ _ σ fun y hy => ?_
  obtain ⟨h1, h2⟩ := SInvI.mem_getSimpleKo hy
  obtain ⟨x, s1⟩ := y
  dsimp only at h1 h2 ⊢
  subst h2
  rcases ho : x.ntfnObj with _ | _ | _ <;> rcases hbt : x.ntfnBoundTcb with _ | t
  all_goals try rfl
  show (getThreadState (Z := Unit) t >>= fun st => vmSignalCompletes onCore remoteCur t >>= fun comp =>
      if st = .runningVM ∧ comp = true then _ else sendSignal n b) s1 =
    (getThreadState (Z := Unit) t >>= fun st => if st = .runningVM ∧ onCore t = true then _ else sendSignal n b) s1
  refine nd_bind_congr_on _ _ _ s1 fun z hz => ?_
  unfold getThreadState at hz
  obtain ⟨x0, hk0, rfl⟩ := SInvQ.q1_mem_threadGet hz
  obtain ⟨c, hc⟩ := vmSignalCompletes_det onCore remoteCur hk0
  rw [Notif.nd_bind_one hc]
  have hst := hn t x0 hk0
  simp only [hst, false_and, ↓reduceIte]

/-- The exit's `vmCheckF` of the current thread does nothing at a `CtExit` state. -/
theorem vmCheckF_ctExit {σ : State Unit} (h : SInvAll.CtExit σ) :
    (NonDet.gets (fun s : State Unit => s.curThread) >>= fun ct => vmCheckF (Z := Unit) ct) σ =
      ({((), σ)}, False) := by
  obtain ⟨x, hk, hs⟩ := h
  rw [nd_bind_apply]
  have hv : vmCheckF (Z := Unit) σ.curThread σ = ({((), σ)}, False) :=
    VirtReportEq.vmCheckF_not_runningVM hk (by rcases hs with hs | hs <;> rw [hs] <;> exact fun h => by cases h)
  show ({r | ∃ x ∈ ({(σ.curThread, σ)} : Set (ObjRef × State Unit)), r ∈ (vmCheckF x.1 x.2).1},
    False ∨ ∃ x ∈ ({(σ.curThread, σ)} : Set (ObjRef × State Unit)), (vmCheckF x.1 x.2).2) = _
  simp only [Set.mem_singleton_iff, exists_eq_left, hv, false_or]
  rfl

theorem vcpuDetachF_nvv {σ : State Unit} (hv : NVV σ) (t : ObjRef) :
    vcpuDetachF (Z := Unit) t σ = ({((), σ)}, False) := by
  have ht : tcbVcpuOf σ t = none := tcbVcpuOf_none.2 fun v st h => by rw [vcpuAt_nvv hv v] at h; cases h
  unfold vcpuDetachF
  rw [nd_bind_det _ _ σ none (by simp only [getTcbVcpu, NonDet.gets]; rw [ht])]
  rfl

/-- `finaliseCapVF` of an unhooked cap is the ported `finalise_cap` (`finaliseCapV_eq`'s twin). -/
theorem finaliseCapVF_eq (cap : Cap) (final : Bool) (h : ¬ FinaliseHooked cap) :
    finaliseCapVF (Z := Unit) cap final = finaliseCap cap final := by
  unfold finaliseCapVF
  cases cap with
  | archObjectCap a =>
    cases a with
    | vcpuCap _ => exact absurd trivial h
    | eptCap _ _ m =>
      cases m with
      | none => rfl
      | some _ => exact absurd trivial h
    | pageCap _ _ _ mt _ m =>
      cases mt with
      | vmEptMap =>
        cases m with
        | none => rfl
        | some _ => exact absurd trivial h
      | _ => rfl
    | ioPortCap _ _ => exact absurd trivial h
    | _ => rfl
  | threadCap _ => exact absurd trivial h
  | _ => rfl

/-- The F perform of an unsubstituted invocation is the ported one (`fl4PerformInvocationV_base`'s twin). -/
theorem fl4PerformInvocationVF_base (onCore remoteCur : ObjRef → Bool) (block call canDonate : Bool)
    (i : Fl4Invocation) (h : ¬ PerformSubst i) :
    fl4PerformInvocationVF (Z := Unit) onCore remoteCur block call canDonate (.base i) =
      fl4PerformInvocation block call canDonate i := by
  cases i with
  | invokeUntyped _ => exact absurd trivial h
  | invokeNotification _ _ => exact absurd trivial h
  | invokeTCB _ => exact absurd trivial h
  | invokeCNode _ => exact absurd trivial h
  | _ => rfl

/-! ## The exit (VirtR7d's twins) -/

theorem activateThreadV_vmCheckF {σ : State Unit} (hn : NoRunVM σ) :
    (activateThreadV (Z := Unit) >>= fun _ =>
      NonDet.gets (fun s : State Unit => s.curThread) >>= fun ct => vmCheckF (Z := Unit) ct) σ =
      activateThread σ := by
  rw [nd_bind_eq_of (activateThreadV_eq hn)]
  refine VirtR7.nd_bind_pure_out _ _ σ fun y hy => ?_
  obtain ⟨⟨⟩, σ'⟩ := y
  exact vmCheckF_ctExit (SInvAll.ctExit_activateThread σ _ hy)

theorem exitTailVF_eq {σ : State Unit} (hn : NoRunVM σ) :
    (schedule (Z := Unit) >>= fun _ => activateThreadV (Z := Unit) >>= fun _ =>
      NonDet.gets (fun s : State Unit => s.curThread) >>= fun ct => vmCheckF (Z := Unit) ct) σ =
      (schedule (Z := Unit) >>= fun _ => activateThread (Z := Unit)) σ :=
  nd_bind_congr_on _ _ _ σ fun y hy => activateThreadV_vmCheckF (noRunVM_schedule σ hn y hy)

theorem fl4KernelExitVF_eq (onCore remoteCur : ObjRef → Bool) {σ : State Unit} (hn : NoRunVM σ)
    (haw : fl4AwakenVF (Z := Unit) onCore remoteCur σ = fl4Awaken σ) :
    fl4KernelExitVF (Z := Unit) onCore remoteCur σ =
      (fl4Awaken (Z := Unit) >>= fun _ => schedule (Z := Unit) >>= fun _ => activateThread (Z := Unit)) σ := by
  unfold fl4KernelExitVF
  rw [nd_bind_eq_of haw]
  exact nd_bind_congr_on _ _ _ σ fun y hy => exitTailVF_eq (noRunVM_fl4Awaken σ hn y hy)

/-! ## Timers and interrupts (VirtAwaken's twins) -/

theorem timerSignalVF_iff (onCore remoteCur : ObjRef → Bool) {σ σ' : State Unit} (hn : NoRunVM σ) :
    fl4TimerSignalVF (Z := Unit) onCore remoteCur σ σ' ↔ fl4TimerSignal σ σ' := by
  unfold fl4TimerSignalVF fl4TimerSignal
  simp only [sendSignalVF_eq_nr onCore remoteCur hn]

theorem timerFireVF_iff (onCore remoteCur : ObjRef → Bool) {σ σ' : State Unit} (hn : NoRunVM σ) :
    fl4TimerFireVF (Z := Unit) onCore remoteCur σ σ' ↔ fl4TimerFire σ σ' := by
  unfold fl4TimerFireVF fl4TimerFire
  simp only [timerSignalVF_iff onCore remoteCur hn]

theorem timerFiresVF_iff (onCore remoteCur : ObjRef → Bool) {σ σ' : State Unit} (hn : NoRunVM σ) :
    Relation.ReflTransGen (fl4TimerFireVF (Z := Unit) onCore remoteCur) σ σ' ↔ fl4TimerFires σ σ' := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hst ih =>
      have hb := noRunVM_fl4Awaken σ hn ((), _) (mem_fl4Awaken.2 ih)
      exact ih.tail ((timerFireVF_iff onCore remoteCur hb).1 hst)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hst ih =>
      have hb := noRunVM_fl4Awaken σ hn ((), _) (mem_fl4Awaken.2 hab)
      exact ih.tail ((timerFireVF_iff onCore remoteCur hb).2 hst)

theorem fl4AwakenVF_eq (onCore remoteCur : ObjRef → Bool) {σ : State Unit} (hn : NoRunVM σ) :
    fl4AwakenVF (Z := Unit) onCore remoteCur σ = fl4Awaken σ :=
  Prod.ext (Set.ext fun _ => timerFiresVF_iff onCore remoteCur hn) rfl

/-- **FL4's exit (with `vmCheckF`) is the ported exit tail** on every `NoRunVM` state. -/
theorem fl4KernelExitVF_eq' (onCore remoteCur : ObjRef → Bool) {σ : State Unit} (hn : NoRunVM σ) :
    fl4KernelExitVF (Z := Unit) onCore remoteCur σ =
      (fl4Awaken (Z := Unit) >>= fun _ => schedule (Z := Unit) >>= fun _ => activateThread (Z := Unit)) σ :=
  fl4KernelExitVF_eq onCore remoteCur hn (fl4AwakenVF_eq onCore remoteCur hn)

theorem when_sendSignalVF_eq (onCore remoteCur : ObjRef → Bool) (c : Prop) [Decidable c] (n : ObjRef) (b : Badge)
    {σ : State Unit} (hn : NoRunVM σ) :
    NonDet.when c (sendSignalVF (Z := Unit) onCore remoteCur n b) σ = NonDet.when c (sendSignal n b) σ := by
  unfold NonDet.when
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact sendSignalVF_eq_nr onCore remoteCur hn n b
  · rw [if_neg h, if_neg h]

theorem handleInterruptVF_eq (onCore remoteCur : ObjRef → Bool) {σ : State Unit} (hn : NoRunVM σ) (irq : Irq) :
    handleInterruptVF (Z := Unit) onCore remoteCur irq σ = handleInterrupt irq σ := by
  unfold handleInterruptVF handleInterrupt
  by_cases hi : irq > maxIRQ
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi]
    refine bind_nr (ns_getIrqState irq) hn fun st s1 h1 => ?_
    cases st
    all_goals try rfl
    refine bind_nr (ns_getIrqSlot irq) h1 fun slot s2 h2 => ?_
    refine bind_nr (ns_getCap slot) h2 fun cap s3 h3 => ?_
    exact nd_bind_eq_of (when_sendSignalVF_eq onCore remoteCur _ _ _ h3) _

theorem maybeHandleInterruptVF_eq (onCore remoteCur : ObjRef → Bool) {σ : State Unit} (hn : NoRunVM σ)
    (ik : Bool) : maybeHandleInterruptVF (Z := Unit) onCore remoteCur ik σ = maybeHandleInterrupt ik σ := by
  unfold maybeHandleInterruptVF maybeHandleInterrupt
  refine bind_nr (ik_doMachineOp (fun _ _ h => h) _) hn fun io s1 h1 => ?_
  cases io with
  | none => rfl
  | some irq => exact handleInterruptVF_eq onCore remoteCur h1 irq

theorem preemptionPathVF_eq (onCore remoteCur : ObjRef → Bool) {σ : State Unit} (hn : NoRunVM σ) :
    preemptionPathVF (Z := Unit) onCore remoteCur σ = preemptionPath σ := by
  unfold preemptionPathVF preemptionPath
  refine bind_nr (ik_gets _) hn fun ct s1 h1 => ?_
  refine bind_nr (ik_gets _) h1 fun sch s2 h2 => ?_
  by_cases hs : sch = true
  · rw [if_pos hs, if_pos hs]
    exact bind_nr ns_checkBudget h2 fun _ s3 h3 => maybeHandleInterruptVF_eq onCore remoteCur h3 true
  · rw [if_neg hs, if_neg hs]
    refine bind_nr (ik_gets _) h2 fun csc s3 h3 => bind_nr (ns_getScActive _) h3 fun a s4 h4 => ?_
    by_cases ha : a = true
    · rw [if_pos ha, if_pos ha]
      exact bind_nr (ik_gets _) h4 fun _ s5 h5 =>
        bind_nr (ns_chargeBudget _ _) h5 fun _ s6 h6 => maybeHandleInterruptVF_eq onCore remoteCur h6 true
    · rw [if_neg ha, if_neg ha]
      exact bind_nr (ik_modify (g := fun s : State Unit => { s with consumedTime := 0 }) fun _ h => h) h4
        fun _ s5 h5 => maybeHandleInterruptVF_eq onCore remoteCur h5 true

/-! ## Deletion (VirtR7b's twins) -/

theorem finaliseCapVF_agree {σ : State Unit} {c : Cap} (hc : ¬ IsVirtCap c) (hv : NVV σ) (fin : Bool) :
    finaliseCapVF (Z := Unit) c fin σ = finaliseCap c fin σ := by
  by_cases hh : FinaliseHooked c
  · cases c with
    | threadCap t =>
      show (NonDet.when fin (vcpuDetachF t) >>= fun _ => finaliseCap (.threadCap t) fin) σ = _
      refine nd_bind_det _ _ σ () ?_
      cases fin with
      | false => rfl
      | true => exact vcpuDetachF_nvv hv t
    | archObjectCap a =>
      cases a with
      | ioPortCap f l =>
        show (ioPortRevoke (.ioPortCap f l) >>= fun _ => finaliseCap (.archObjectCap (.ioPortCap f l)) fin) σ = _
        rw [ioPortRevoke_eq]
        exact nd_bind_det _ _ σ () rfl
      | vcpuCap _ => exact absurd trivial hc
      | eptCap _ _ m => exact absurd trivial hc
      | pageCap _ _ _ mt _ m => cases mt <;> first | exact absurd trivial hc | cases hh
      | _ => cases hh
    | _ => cases hh
  · rw [finaliseCapVF_eq c fin hh]

theorem recDelFVF_mono :
    NDMono (fun (r : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))) c => recDelFVF (Z := Unit) r c) := by
  intro f g hfg k s
  show ExceptT.run (recDelFVF (Z := Unit) f k) s ≤ ExceptT.run (recDelFVF (Z := Unit) g k) s
  cases k with
  | cTEDeleteCall sl e => unfold recDelFVF; nd_mono hfg
  | finaliseSlotCall sl e => unfold recDelFVF; nd_mono hfg
  | reduceZombieCall c sl e =>
    cases c with
    | zombie ptr bits n =>
      cases n with
      | zero => exact le_rfl
      | succ n => cases e <;> (unfold recDelFVF; nd_mono hfg)
    | _ => exact le_rfl

theorem recDel_agreeF (f g : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)))
    (hpf : ∀ i, Pres NV (f i)) (hfg : ∀ i s, NV s → f i s = g i s) (k : RecDelCall) (s : State Unit)
    (hs : NV s) : recDelF (Z := Unit) f k s = recDelFVF (Z := Unit) g k s := by
  show ExceptT.run (recDelF (Z := Unit) f k) s = ExceptT.run (recDelFVF (Z := Unit) g k) s
  cases k with
  | cTEDeleteCall sl e =>
    unfold recDelF recDelFVF
    exact nde_bind_congr (hfg _ s hs) fun _ _ _ => rfl
  | finaliseSlotCall sl e =>
    obtain ⟨o, r⟩ := sl
    unfold recDelF recDelFVF
    refine nde_bind_congr rfl fun cap t hmem => ?_
    obtain ⟨rfl, hcap⟩ := vih_mem_getCap (mem_run_liftE' hmem)
    by_cases hn : cap = .nullCap
    · rw [if_pos hn, if_pos hn]
    rw [if_neg hn, if_neg hn]
    refine nde_bind_congr rfl fun fin t2 hmem2 => ?_
    have ht2 : t2 = t := by
      have h := mem_run_liftE' hmem2
      exact (Prod.mk.inj (Set.mem_singleton_iff.1 (h : (fin, t2) ∈ ({(decide (isFinalCap' cap t), t)} : Set _)))).2
    subst ht2
    have hv : ¬ IsVirtCap cap := hs.1 (o, r) cap hcap
    refine nde_bind_congr (run_liftE_congr (finaliseCapVF_agree hv hs.2 fin).symm) fun p t3 hmem3 => ?_
    have hI3 : NV t3 := nv_step (ike_liftE (nvc_finaliseCap cap fin)) (ike_liftE (ty_finaliseCap cap fin)) hs hmem3
    have hr : ¬ IsVirtCap p.1 := nv_finaliseCap_rem cap fin t2 _ (mem_run_liftE' hmem3) hv
    obtain ⟨rem, ci⟩ := p
    dsimp only at hr ⊢
    by_cases h1 : capRemoveable rem (o, r)
    · rw [if_pos h1, if_pos h1]
    rw [if_neg h1, if_neg h1]
    by_cases h2 : capCyclicZombie rem (o, r) ∧ ¬ e = true
    · rw [if_pos h2, if_pos h2]
    rw [if_neg h2, if_neg h2]
    refine nde_bind_congr rfl fun _ t4 hmem4 => ?_
    have hI4 : NV t4 := nv_step (ike_liftE (nvc_setCap _ hr)) (ike_liftE (ty_setCap _ _)) hI3 hmem4
    refine nde_bind_congr (hfg _ t4 hI4) fun _ t5 hmem5 => ?_
    have hI5 : NV t5 := hpf _ t4 hI4 _ hmem5
    refine nde_bind_congr rfl fun _ t6 hmem6 => ?_
    have hI6 : NV t6 := nv_step (hv_preemptionPoint (P := NVC)) (ty_preemptionPoint (OS := NVT)) hI5 hmem6
    exact hfg _ t6 hI6
  | reduceZombieCall c sl e =>
    cases c with
    | zombie ptr bits n =>
      cases n with
      | zero => rfl
      | succ n =>
        cases e with
        | false => rfl
        | true =>
          unfold recDelF recDelFVF
          refine nde_bind_congr rfl fun _ t1 hmem1 => ?_
          have ht1 : t1 = s := (Prod.mk.inj (Set.mem_singleton_iff.1 hmem1)).2
          subst ht1
          exact nde_bind_congr (hfg _ t1 hs) fun _ _ _ => rfl
    | _ => rfl

theorem recDelVF_eq (k : RecDelCall) {s : State Unit} (hs : NV s) : recDelVF (Z := Unit) k s = recDel k s := by
  unfold recDelVF recDel
  exact lfp_agree NV _ _ recDelF_mono recDelFVF_mono (fun k => nv_recDel k)
    (fun f g hf _ hfg k s hs => recDel_agreeF f g hf hfg k s hs) k s hs

theorem capDeleteVF_eq (sl : CslotPtr) {s : State Unit} (hs : NV s) :
    capDeleteVF (Z := Unit) sl s = capDelete sl s := by
  show ExceptT.run (capDeleteVF (Z := Unit) sl) s = ExceptT.run (capDelete (Z := Unit) sl) s
  unfold capDeleteVF capDelete
  exact nde_bind_congr (recDelVF_eq _ hs) fun _ _ _ => rfl

theorem capRevokeFVF_mono :
    NDMono (fun (r : CslotPtr → NonDet (State Unit) (Except Unit Unit)) c => capRevokeFVF (Z := Unit) r c) := by
  intro f g hfg k s
  show ExceptT.run (capRevokeFVF (Z := Unit) f k) s ≤ ExceptT.run (capRevokeFVF (Z := Unit) g k) s
  unfold capRevokeFVF; nd_mono hfg

theorem capRevoke_agreeF (f g : CslotPtr → NonDet (State Unit) (Except Unit Unit))
    (_hpf : ∀ i, Pres NV (f i)) (hfg : ∀ i s, NV s → f i s = g i s) (sl : CslotPtr) (s : State Unit)
    (hs : NV s) : capRevokeF (Z := Unit) f sl s = capRevokeFVF (Z := Unit) g sl s := by
  show ExceptT.run (capRevokeF (Z := Unit) f sl) s = ExceptT.run (capRevokeFVF (Z := Unit) g sl) s
  unfold capRevokeF capRevokeFVF withoutPreemption
  refine nde_bind_congr rfl fun cap t1 hmem1 => ?_
  have hI1 : NV t1 := nv_step (ike_liftE (hv_getCap (P := NVC) _)) (ike_liftE (ty_getCap _)) hs hmem1
  refine nde_bind_congr rfl fun cdt t2 hmem2 => ?_
  have hI2 : NV t2 := nv_step (ike_liftE (ik_gets _)) (ike_liftE (ik_gets _)) hI1 hmem2
  refine nde_bind_congr rfl fun d t3 hmem3 => ?_
  have hI3 : NV t3 := nv_step (ike_returnOk _) (ike_returnOk _) hI2 hmem3
  unfold NonDetE.whenE
  by_cases hc : cap ≠ .nullCap ∧ d ≠ ∅
  · rw [if_pos hc, if_pos hc]
    refine nde_bind_congr rfl fun child t4 hmem4 => ?_
    have hI4 : NV t4 := nv_step (ike_liftE (hv_selectExt (P := NVC) _ _)) (ike_liftE (ty_selectExt _ _)) hI3 hmem4
    refine nde_bind_congr rfl fun cap' t5 hmem5 => ?_
    have hI5 : NV t5 := nv_step (ike_liftE (hv_getCap (P := NVC) _)) (ike_liftE (ty_getCap _)) hI4 hmem5
    refine nde_bind_congr rfl fun _ t6 hmem6 => ?_
    have hI6 : NV t6 := nv_step (ike_assertE _) (ike_assertE _) hI5 hmem6
    refine nde_bind_congr (capDeleteVF_eq child hI6).symm fun _ t7 hmem7 => ?_
    have hI7 : NV t7 := nv_capDelete child t6 hI6 _ hmem7
    refine nde_bind_congr rfl fun _ t8 hmem8 => ?_
    have hI8 : NV t8 := nv_step (hv_preemptionPoint (P := NVC)) (ty_preemptionPoint (OS := NVT)) hI7 hmem8
    exact hfg _ t8 hI8
  · rw [if_neg hc, if_neg hc]

theorem capRevokeVF_eq (sl : CslotPtr) {s : State Unit} (hs : NV s) :
    capRevokeVF (Z := Unit) sl s = capRevoke sl s := by
  unfold capRevokeVF capRevoke
  exact lfp_agree NV _ _ capRevokeF_mono capRevokeFVF_mono (fun k => nv_capRevoke k)
    (fun f g hf _ hfg k s hs => capRevoke_agreeF f g hf hfg k s hs) sl s hs

/-! ## CNode and TCB invocations (VirtNvTcb's twins) -/

theorem invokeCnodeVF_eq (i : CnodeInvocation) {s : State Unit} (hs : NV s) :
    invokeCnodeVF (Z := Unit) i s = invokeCnode i s := by
  cases i with
  | revokeCall sl => exact capRevokeVF_eq sl hs
  | deleteCall sl => exact capDeleteVF_eq sl hs
  | _ => rfl

theorem installTcbCapVF_eq (target : ObjRef) (slot : CslotPtr) (n : Nat) (so : Option (Cap × CslotPtr))
    {s : State Unit} (hs : NV s) :
    installTcbCapVF (Z := Unit) target slot n so s = installTcbCap target slot n so s := by
  cases so with
  | none => rfl
  | some p =>
    obtain ⟨c, src⟩ := p
    show ExceptT.run (installTcbCapVF (Z := Unit) target slot n (some (c, src))) s =
      ExceptT.run (installTcbCap (Z := Unit) target slot n (some (c, src))) s
    unfold installTcbCapVF installTcbCap
    exact nde_bind_congr (capDeleteVF_eq _ hs) fun _ _ _ => rfl

theorem installTcbFrameCapVF_eq (target : ObjRef) (slot : CslotPtr)
    (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) {s : State Unit} (hs : NV s) :
    installTcbFrameCapVF (Z := Unit) target slot buffer s = installTcbFrameCap target slot buffer s := by
  cases buffer with
  | none => rfl
  | some p =>
    obtain ⟨ptr, frame⟩ := p
    show ExceptT.run (installTcbFrameCapVF (Z := Unit) target slot (some (ptr, frame))) s =
      ExceptT.run (installTcbFrameCap (Z := Unit) target slot (some (ptr, frame))) s
    unfold installTcbFrameCapVF installTcbFrameCap
    exact nde_bind_congr (capDeleteVF_eq _ hs) fun _ _ _ => rfl

/-- An outcome of FL4's install from an `NV` state is one of the ported install (`toP`'s twin). -/
theorem toPF {target : ObjRef} {slot : CslotPtr} {n : Nat} {o : Option (Cap × CslotPtr)} {s : State Unit}
    {hs : NV s} {x : Except Unit Unit × State Unit}
    (m : x ∈ (ExceptT.run (installTcbCapVF (Z := Unit) target slot n o) s).1) :
    x ∈ (ExceptT.run (installTcbCap (Z := Unit) target slot n o) s).1 := by
  change x ∈ (installTcbCapVF (Z := Unit) target slot n o s).1 at m
  rw [installTcbCapVF_eq target slot n o hs] at m
  exact m

theorem invokeTcbVF_eq (i : TcbInvocation) {s : State Unit} (hs : NV s) (hc : TcbCapsOK i) :
    invokeTcbVF (Z := Unit) i s = invokeTcb i s := by
  cases i with
  | threadControlCaps target slot fh th cr vr buf =>
    obtain ⟨h1, h2, h3, h4⟩ := hc
    show ExceptT.run (invokeTcbVF (Z := Unit) (.threadControlCaps target slot fh th cr vr buf)) s =
      ExceptT.run (invokeTcb (Z := Unit) (.threadControlCaps target slot fh th cr vr buf)) s
    unfold invokeTcbVF invokeTcb
    refine nde_bind_congr (installTcbCapVF_eq _ _ _ _ hs) fun _ t1 m1 => ?_
    have n1 := nv_installTcbCap target slot 3 h1 s hs _ (toPF (hs := hs) m1)
    refine nde_bind_congr (installTcbCapVF_eq _ _ _ _ n1) fun _ t2 m2 => ?_
    have n2 := nv_installTcbCap target slot 4 h2 t1 n1 _ (toPF (hs := n1) m2)
    refine nde_bind_congr (installTcbCapVF_eq _ _ _ _ n2) fun _ t3 m3 => ?_
    have n3 := nv_installTcbCap target slot 0 h3 t2 n2 _ (toPF (hs := n2) m3)
    refine nde_bind_congr (installTcbCapVF_eq _ _ _ _ n3) fun _ t4 m4 => ?_
    have n4 := nv_installTcbCap target slot 1 h4 t3 n3 _ (toPF (hs := n3) m4)
    exact nde_bind_congr (installTcbFrameCapVF_eq _ _ _ n4) fun _ _ _ => rfl
  | threadControlSched target slot fh mcp prio sc =>
    show ExceptT.run (invokeTcbVF (Z := Unit) (.threadControlSched target slot fh mcp prio sc)) s =
      ExceptT.run (invokeTcb (Z := Unit) (.threadControlSched target slot fh mcp prio sc)) s
    unfold invokeTcbVF invokeTcb
    exact nde_bind_congr (installTcbCapVF_eq _ _ _ _ hs) fun _ _ _ => rfl
  | _ => rfl

/-! ## The perform and the invocation (VirtR7e / VirtAgree's twins) -/

theorem fl4PerformInvocationVF_eqNR (onCore remoteCur : ObjRef → Bool) (blk call don : Bool) (i : Fl4Invocation)
    {s : State Unit} (hs : NR s) (hi : InvOK i) :
    ExceptT.run (fl4PerformInvocationVF (Z := Unit) onCore remoteCur blk call don (.base i)) s =
      ExceptT.run (fl4PerformInvocation blk call don i) s := by
  by_cases hp : PerformSubst i
  · cases i with
    | invokeUntyped ui =>
      obtain ⟨src, reset, base, rb, t, sz, slots, dev⟩ := ui
      show ExceptT.run (fl4InvokeUntypedV (Z := Unit) (.retype src reset base rb t sz slots dev) >>= fun _ =>
          NonDetE.returnOk []) s = ExceptT.run (fl4InvokeUntyped (.retype src reset base rb t sz slots dev) >>= fun _ =>
          NonDetE.returnOk []) s
      exact nde_bind_congr (VirtR7.fl4InvokeUntypedV_run src reset base rb t sz slots dev hi s) fun _ _ _ => rfl
    | invokeNotification ep b =>
      show ExceptT.run (withoutPreemption (sendSignalVF (Z := Unit) onCore remoteCur ep b) >>= fun _ =>
          NonDetE.returnOk []) s = ExceptT.run (withoutPreemption (sendSignal ep b) >>= fun _ =>
          NonDetE.returnOk []) s
      exact nde_bind_congr (run_liftE_congr (sendSignalVF_eq_nr onCore remoteCur hs.2 ep b)) fun _ _ _ => rfl
    | invokeTCB ti => exact invokeTcbVF_eq ti hs.1 hi
    | invokeCNode ci =>
      show ExceptT.run (invokeCnodeVF (Z := Unit) ci >>= fun _ => NonDetE.returnOk []) s =
        ExceptT.run (invokeCnode ci >>= fun _ => NonDetE.returnOk []) s
      exact nde_bind_congr (invokeCnodeVF_eq ci hs.1) fun _ _ _ => rfl
    | _ => exact (hp : False).elim
  · rw [fl4PerformInvocationVF_base onCore remoteCur blk call don i hp]

theorem fl4HandleInvocationVF_eqNR6 (hvk : virtKind = .none) (onCore remoteCur : ObjRef → Bool)
    (rep calling blocking don fp : Bool) (cptr : CapRef) {s : State Unit} (hs : NR s) (hoff : OffRoute6 fp cptr s) :
    ExceptT.run (fl4HandleInvocationVF (Z := Unit) onCore remoteCur rep calling blocking don fp cptr) s =
      ExceptT.run (fl4HandleInvocationR rep calling blocking don fp cptr) s := by
  unfold fl4HandleInvocationVF fl4HandleInvocationR
  refine nde_bind_congr rfl fun thread s0 h0 => ?_
  have h0' := mem_run_liftE' h0
  simp only [NonDet.gets, Set.mem_singleton_iff, Prod.mk.injEq] at h0'
  obtain ⟨rfl, rfl⟩ := h0'
  refine nde_bind_congr rfl fun info s1 h1 => ?_
  have h1' := mem_run_liftE' h1
  have n1 : NR s1 := nr_getMessageInfo _ _ hs _ h1'
  refine syscall_congrV _ _ _ _ _ _ _ Fl4InvocationV.base (fun a t ha => ?_) (fun a t b u ha hb => ?_)
  · obtain ⟨slot, cap, ex, buf⟩ := a
    dsimp only
    rw [run_liftME_bind]
    refine nde_bind_congr rfl fun args u hu => ?_
    have hu' := mem_run_liftE' hu
    have hd : DecPt cptr s0 info (slot, cap, ex, buf) args u := ⟨s1, t, h1', ha, hu'⟩
    rcases hoff info (slot, cap, ex, buf) args u hd with hr | ⟨e, hP, hV⟩
    · rw [fl4DecodeInvocationV_base _ _ _ _ _ _ _ _ (good_of_route3 hvk hs.1.1 hd hr).1]
    · dsimp only at hP hV
      rw [hV, run_liftME_err hP]
  · obtain ⟨slot, cap, ex, buf⟩ := a
    have nt : NR t := nr_lookupPart _ cptr info s1 n1 _ ha
    dsimp only at hb ⊢
    rw [ExceptT.run_bind] at hb
    obtain ⟨⟨r1, t2⟩, hr1, hb'⟩ := hb
    cases r1 with
    | error e =>
      exfalso
      simp only [ExceptT.bindCont] at hb'
      cases Set.mem_singleton_iff.1 hb'
    | ok args =>
      simp only [ExceptT.bindCont] at hb'
      have hr1' := mem_run_liftE' hr1
      have n2 : NR t2 := nr_getMrs _ _ _ t nt _ hr1'
      have hd : DecPt cptr s0 info (slot, cap, ex, buf) args t2 := ⟨s1, t, h1', ha, hr1'⟩
      rcases hoff info (slot, cap, ex, buf) args t2 hd with hr | ⟨e, hP, -⟩
      · have hInv := (good_of_route3 hvk hs.1.1 hd hr).2 b u hb'
        have nu : NR u := nr_fl4Decode _ _ _ _ _ _ _ _ t2 n2 _ hb'
        refine nde_bind_congr rfl fun _ v hv => ?_
        have nv : NR v := nr_setRestart _ u nu _ (mem_run_liftE' hv)
        exact nde_bind_congr (fl4PerformInvocationVF_eqNR onCore remoteCur blocking calling don b nv hInv)
          fun _ _ _ => rfl
      · exfalso
        have hb2 := hb'
        dsimp only at hP
        rw [hP] at hb2
        cases (Prod.mk.inj (Set.mem_singleton_iff.1 hb2)).1

theorem invoke_congrF6 (hvk : virtKind = .none) (onCore remoteCur : ObjRef → Bool) (rep calling blocking don fp : Bool)
    (reg : Register) {k : Unit → PMonad Unit Unit} {t : State Unit} (ht : NR t)
    (hoff : ∀ cptr t', (cptr, t') ∈ (getCapReg (Z := Unit) reg t).1 → OffRoute6 fp cptr t') :
    ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) reg) >>= fun cptr =>
        fl4HandleInvocationVF onCore remoteCur rep calling blocking don fp cptr >>= k) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) reg) >>= fun cptr =>
        fl4HandleInvocationR rep calling blocking don fp cptr >>= k) t := by
  refine nde_bind_congr rfl fun cptr t' h => ?_
  have h' := mem_run_liftE' h
  exact nde_bind_congr (fl4HandleInvocationVF_eqNR6 hvk onCore remoteCur rep calling blocking don fp cptr
    (nr_getCapReg reg t ht _ h') (hoff cptr t' h')) fun _ _ _ => rfl

theorem invoke_congrF60 (hvk : virtKind = .none) (onCore remoteCur : ObjRef → Bool)
    (rep calling blocking don fp : Bool) (reg : Register) {t : State Unit} (ht : NR t)
    (hoff : ∀ cptr t', (cptr, t') ∈ (getCapReg (Z := Unit) reg t).1 → OffRoute6 fp cptr t') :
    ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) reg) >>= fun cptr =>
        fl4HandleInvocationVF onCore remoteCur rep calling blocking don fp cptr) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) reg) >>= fun cptr =>
        fl4HandleInvocationR rep calling blocking don fp cptr) t := by
  refine nde_bind_congr rfl fun cptr t' h => ?_
  have h' := mem_run_liftE' h
  exact fl4HandleInvocationVF_eqNR6 hvk onCore remoteCur rep calling blocking don fp cptr
    (nr_getCapReg reg t ht _ h') (hoff cptr t' h')

/-! ## Syscalls, events, the kernel step (VirtR7eK / VirtScope8's twins) -/

theorem fl4HandleSyscallVF_eqNR8 (hvk : virtKind = .none) (onCore remoteCur : ObjRef → Bool) (rep : Bool)
    (c : Syscall) {t : State Unit} (ht : NR t) (hoff : OffRouteS8 c t) :
    ExceptT.run (fl4HandleSyscallVF (Z := Unit) onCore remoteCur rep c) t =
      ExceptT.run (fl4HandleSyscall rep c) t := by
  cases c with
  | sysSend =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationVF onCore remoteCur rep false true false false cptr) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep false true false false cptr) t
    exact invoke_congrF60 hvk onCore remoteCur rep false true false false cap_register ht
      fun cptr t' h => hoff _ rfl cptr t' h
  | sysNBSend =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationVF onCore remoteCur rep false false false false cptr) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep false false false false cptr) t
    exact invoke_congrF60 hvk onCore remoteCur rep false false false false cap_register ht
      fun cptr t' h => hoff _ rfl cptr t' h
  | sysCall =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationVF onCore remoteCur rep true true true false cptr) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep true true true false cptr) t
    exact invoke_congrF60 hvk onCore remoteCur rep true true true false cap_register ht
      fun cptr t' h => hoff _ rfl cptr t' h
  | sysReplyRecv =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationVF onCore remoteCur rep false false true true cptr >>= fun _ =>
          withoutPreemption (handleRecv (Z := Unit) true true)) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ =>
          withoutPreemption (handleRecv (Z := Unit) true true)) t
    exact invoke_congrF6 hvk onCore remoteCur rep false false true true replyRegister
      (k := fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) ht fun cptr t' h => hoff _ rfl cptr t' h
  | sysNBSendRecv =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) nbsendRecvDest) >>= fun cptr =>
        fl4HandleInvocationVF onCore remoteCur rep false false true true cptr >>= fun _ =>
          withoutPreemption (handleRecv (Z := Unit) true true)) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) nbsendRecvDest) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ =>
          withoutPreemption (handleRecv (Z := Unit) true true)) t
    exact invoke_congrF6 hvk onCore remoteCur rep false false true true nbsendRecvDest
      (k := fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) ht fun cptr t' h => hoff _ rfl cptr t' h
  | sysNBSendWait =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationVF onCore remoteCur rep false false true true cptr >>= fun _ =>
          withoutPreemption (handleRecv (Z := Unit) true false)) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ =>
          withoutPreemption (handleRecv (Z := Unit) true false)) t
    exact invoke_congrF6 hvk onCore remoteCur rep false false true true replyRegister
      (k := fun _ => withoutPreemption (handleRecv (Z := Unit) true false)) ht fun cptr t' h => hoff _ rfl cptr t' h
  | sysRecv => rfl
  | sysYield => rfl
  | sysWait => rfl
  | sysNBWait => rfl
  | sysNBRecv => rfl

theorem fl4HandleEventVF_unknown_nvv (onCore remoteCur : ObjRef → Bool) (rep : Bool) {σ : State Unit} (hv : NVV σ)
    (num : Nat) :
    (fl4HandleEventVF (Z := Unit) onCore remoteCur rep (.unknownSyscall num)).run σ =
      (handleEvent (Z := Unit) (.unknownSyscall num)).run σ := by
  unfold fl4HandleEventVF
  rw [ExceptT.run_bind]
  have hg : (NonDetE.liftE (ε := Unit) (NonDet.gets (isVmEnterCall (Z := Unit) num))).run σ =
      ({(.ok false, σ)}, False) := by
    refine run_liftE ?_
    show ({(isVmEnterCall (Z := Unit) num σ, σ)}, False) = _
    rw [isVmEnterCall_nvv hv num]
  rw [nd_bind_single hg]
  rfl

theorem fl4HandleEventVF_interrupt (onCore remoteCur : ObjRef → Bool) (rep : Bool) {σ : State Unit}
    (hn : NoRunVM σ) :
    ExceptT.run (fl4HandleEventVF (Z := Unit) onCore remoteCur rep .interrupt) σ =
      ExceptT.run (fl4HandleEvent rep .interrupt) σ := by
  show ExceptT.run (withoutPreemption (updateTimeStamp >>= fun _ => checkBudget >>= fun _ =>
      maybeHandleInterruptVF (Z := Unit) onCore remoteCur false)) σ =
    ExceptT.run (withoutPreemption (updateTimeStamp >>= fun _ => checkBudget >>= fun _ =>
      maybeHandleInterrupt (Z := Unit) false)) σ
  refine run_liftE_congr ?_
  refine bind_nr ns_updateTimeStamp hn fun _ s1 h1 => ?_
  exact bind_nr ns_checkBudget h1 fun _ s2 h2 => maybeHandleInterruptVF_eq onCore remoteCur h2 false

theorem fl4HandleEventVF_syscall8 (hvk : virtKind = .none) (onCore remoteCur : ObjRef → Bool) (rep : Bool)
    (c : Syscall) {σ : State Unit} (hs : NR σ) (hoff : ∀ t, EntryPt σ t → OffRouteS8 c t) :
    ExceptT.run (fl4HandleEventVF (Z := Unit) onCore remoteCur rep (.syscallEvent c)) σ =
      ExceptT.run (fl4HandleEvent rep (.syscallEvent c)) σ := by
  show ExceptT.run (NonDetE.liftE updateTimeStamp >>= fun _ => NonDetE.liftE checkBudgetRestart >>= fun restart =>
      NonDetE.whenE restart (fl4HandleSyscallVF (Z := Unit) onCore remoteCur rep c)) σ =
    ExceptT.run (NonDetE.liftE updateTimeStamp >>= fun _ => NonDetE.liftE checkBudgetRestart >>= fun restart =>
      NonDetE.whenE restart (fl4HandleSyscall (Z := Unit) rep c)) σ
  refine nde_bind_congr rfl fun _ t1 h1 => ?_
  have h1' := mem_run_liftE' h1
  refine nde_bind_congr rfl fun restart t h2 => ?_
  have h2' := mem_run_liftE' h2
  unfold NonDetE.whenE
  cases restart with
  | false => rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
  | true =>
    rw [if_pos rfl, if_pos rfl]
    have he : EntryPt σ t := ⟨t1, h1', h2'⟩
    have hnv : NV t := ⟨nvc_entryPt hs.1.1 he, ty_checkBudgetRestart t1 (ty_updateTimeStamp σ hs.1.2 _ h1') _ h2'⟩
    have hnr : NoRunVM t := ns_checkBudgetRestart t1 (ns_updateTimeStamp σ hs.2 _ h1') _ h2'
    exact fl4HandleSyscallVF_eqNR8 hvk onCore remoteCur rep c ⟨hnv, hnr⟩ (hoff t he)

theorem fl4HandleEventVF_eqNR8 (hvk : virtKind = .none) (onCore remoteCur : ObjRef → Bool) (rep : Bool)
    (ev : Event) {σ : State Unit} (hs : NR σ)
    (hoff : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS8 c t) :
    ExceptT.run (fl4HandleEventVF (Z := Unit) onCore remoteCur rep ev) σ =
      ExceptT.run (fl4HandleEvent rep ev) σ := by
  cases ev with
  | syscallEvent c => exact fl4HandleEventVF_syscall8 hvk onCore remoteCur rep c hs (hoff c rfl)
  | unknownSyscall n => exact fl4HandleEventVF_unknown_nvv onCore remoteCur rep hs.1.2 n
  | interrupt => exact fl4HandleEventVF_interrupt onCore remoteCur rep hs.2
  | _ => rfl

/-- **FL4's kernel step (`fl4CallKernelVF`) is the ported one** on an `NR` state in the fp-exact scope (premises
`hvk`, `hoff` [S], as `fl4CallKernelV_eqNR8`), for every `onCore` and `remoteCur`. -/
theorem fl4CallKernelVF_eqNR8 (hvk : virtKind = .none) (onCore remoteCur : ObjRef → Bool) (rep : Bool) (ev : Event)
    {σ : State Unit} (hs : NR σ) (hoff : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS8 c t) :
    fl4CallKernelVF (Z := Unit) onCore remoteCur rep ev σ = fl4CallKernel rep ev σ := by
  unfold fl4CallKernelVF fl4CallKernel
  have hH : ExceptT.run (NonDetE.handleE (fl4HandleEventVF (Z := Unit) onCore remoteCur rep ev)
        (fun _ => withoutPreemption (preemptionPathVF onCore remoteCur))) σ =
      ExceptT.run (NonDetE.handleE (fl4HandleEvent (Z := Unit) rep ev)
        (fun _ => withoutPreemption preemptionPath)) σ := by
    unfold NonDetE.handleE
    rw [ExceptT.run_mk, ExceptT.run_mk]
    refine (nd_bind_eq_of (fl4HandleEventVF_eqNR8 hvk onCore remoteCur rep ev hs hoff) _).trans
      (nd_bind_congr_on _ _ _ σ fun y hy => ?_)
    obtain ⟨r, u⟩ := y
    cases r with
    | ok a => rfl
    | error e =>
      have hu : NoRunVM u := ns_fl4HandleEvent rep ev σ hs.2 _ hy
      exact run_liftE_congr (preemptionPathVF_eq onCore remoteCur hu)
  rw [nd_bind_eq_of hH]
  refine nd_bind_congr_on _ _ _ σ fun y hy => ?_
  have hu : NoRunVM y.2 := ike_handleE (ns_fl4HandleEvent rep ev) (fun _ => ike_liftE ns_preemptionPath) σ hs.2 _ hy
  exact fl4KernelExitVF_eq' onCore remoteCur hu

/-- **FL4's syscall entry is the ported one** on an `NR` state in the fp-exact scope. -/
theorem fl4KernelEntrySyscallVF_eqNR8 (hvk : virtKind = .none) (onCore remoteCur : ObjRef → Bool) (rep : Bool)
    (c : Syscall) {σ : State Unit} (hs : NR σ) (hr : ScopeE8 c σ) :
    fl4KernelEntrySyscallVF (Z := Unit) onCore remoteCur rep c σ = fl4KernelEntrySyscall rep c σ := by
  unfold fl4KernelEntrySyscallVF fl4KernelEntrySyscall
  refine nd_bind_congr_on _ _ _ σ fun y hy => ?_
  simp only [NonDet.gets, Set.mem_singleton_iff] at hy
  subst hy
  refine nd_bind_congr_on _ _ _ σ fun w hw => ?_
  exact fl4CallKernelVF_eqNR8 hvk onCore remoteCur rep _ (nr_fl4SyscallFaultIP _ σ hs w hw)
    fun c' e t ht => by cases e; exact hr w hw t ht

/-! ## F = V on `NR` states -/

/-- **On an `NR` state in scope the FL4 step and the `V` step coincide** (both are the ported step). -/
theorem fl4CallKernelVF_eq_V8 (hvk : virtKind = .none) (onCore remoteCur : ObjRef → Bool) (rep : Bool) (ev : Event)
    {σ : State Unit} (hs : NR σ) (hoff : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS8 c t) :
    fl4CallKernelVF (Z := Unit) onCore remoteCur rep ev σ = fl4CallKernelV onCore rep ev σ :=
  (fl4CallKernelVF_eqNR8 hvk onCore remoteCur rep ev hs hoff).trans
    (fl4CallKernelV_eqNR8 hvk onCore rep ev hs hoff).symm

theorem fl4KernelEntrySyscallVF_eq_V8 (hvk : virtKind = .none) (onCore remoteCur : ObjRef → Bool) (rep : Bool)
    (c : Syscall) {σ : State Unit} (hs : NR σ) (hr : ScopeE8 c σ) :
    fl4KernelEntrySyscallVF (Z := Unit) onCore remoteCur rep c σ = fl4KernelEntrySyscallV onCore rep c σ :=
  (fl4KernelEntrySyscallVF_eqNR8 hvk onCore remoteCur rep c hs hr).trans
    (fl4KernelEntrySyscallV_eqNR8 hvk onCore rep c hs hr).symm

/-! ## The exits -/

/-- A ported-spec syscall exit is an FL4-faithful one (`kentryV_post8`'s twin). -/
theorem kentryVF_post8 (hvk : virtKind = .none) (onCore remoteCur : ObjRef → Bool) {α : Type} {m : Result α}
    {P : α → State Unit → Prop} {c : Syscall} {σ : State Unit} (hs : NR σ) (hr : ScopeE8 c σ)
    (h : m ⦃ r => ∃ σ', ((), σ') ∈ (fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ P r σ' ⦄) :
    m ⦃ r => ∃ σ', ((), σ') ∈ (fl4KernelEntrySyscallVF (Z := Unit) onCore remoteCur true c σ).1 ∧ P r σ' ∧
      NR σ' ⦄ := by
  refine WP.spec_mono h ?_
  intro r ⟨σ', h1, h2⟩
  refine ⟨σ', ?_, h2, nr_kentry8 hvk hs hr h1⟩
  rw [fl4KernelEntrySyscallVF_eqNR8 hvk onCore remoteCur true c hs hr]
  exact h1

/-- `VirtExtTop.EvOutV` on FL4's step. -/
def EvOutVF (onCore remoteCur : ObjRef → Bool) (ev : Event) (σ σ' : State Unit) : Prop :=
  ((), σ') ∈ (fl4CallKernelVF (Z := Unit) onCore remoteCur true ev σ).1

/-- `VirtKEntryV.EvOutVT` on FL4's step: the `FaultIP` write, then `fl4CallKernelVF`. -/
def EvOutVTF (onCore remoteCur : ObjRef → Bool) (ev : Event) (σ σ' : State Unit) : Prop :=
  ∃ w ∈ (fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
    ((), σ') ∈ (fl4CallKernelVF (Z := Unit) onCore remoteCur true ev w.2).1

/-- A non-syscall event exit of the `V` step from an `NR` state is one of FL4's step. -/
theorem evOutVF_of_V (hvk : virtKind = .none) (onCore remoteCur : ObjRef → Bool) {ev : Event} {σ σ' : State Unit}
    (hev : ∀ c, ev ≠ .syscallEvent c) (hs : NR σ) (h : VirtExtTop.EvOutV onCore ev σ σ') :
    EvOutVF onCore remoteCur ev σ σ' := by
  show ((), σ') ∈ (fl4CallKernelVF (Z := Unit) onCore remoteCur true ev σ).1
  rw [fl4CallKernelVF_eq_V8 hvk onCore remoteCur true ev hs fun c e => absurd e (hev c)]
  exact h

/-- A non-syscall `EvOutVT` exit (after the `FaultIP` write) from an `NR` state is one of FL4's step. -/
theorem evOutVTF_of_V (hvk : virtKind = .none) (onCore remoteCur : ObjRef → Bool) {ev : Event} {σ σ' : State Unit}
    (hev : ∀ c, ev ≠ .syscallEvent c) (hs : NR σ) (h : VirtKEntryV.EvOutVT onCore ev σ σ') :
    EvOutVTF onCore remoteCur ev σ σ' := by
  obtain ⟨w, hw, hO⟩ := h
  refine ⟨w, hw, ?_⟩
  rw [fl4CallKernelVF_eq_V8 hvk onCore remoteCur true ev (nr_fl4SyscallFaultIP _ σ hs w hw)
    fun c e => absurd e (hev c)]
  exact hO

/-- A syscall exit of the `V` entry from an `NR` state in scope is one of FL4's entry. -/
theorem kentryVF_of_V (hvk : virtKind = .none) (onCore remoteCur : ObjRef → Bool) {c : Syscall} {σ σ' : State Unit}
    (hs : NR σ) (hr : ScopeE8 c σ) (h : ((), σ') ∈ (fl4KernelEntrySyscallV (Z := Unit) onCore true c σ).1) :
    ((), σ') ∈ (fl4KernelEntrySyscallVF (Z := Unit) onCore remoteCur true c σ).1 := by
  rw [fl4KernelEntrySyscallVF_eq_V8 hvk onCore remoteCur true c hs hr]
  exact h

end

end Fl4Proofs.P3.VirtF13
