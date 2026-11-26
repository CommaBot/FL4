/-
P3x for virtualization, spec side (line virt, gen 4; proofs/VIRT-PLAN.md §10 "Remaining (R7)" (e)):
**the extended kernel step `fl4CallKernelV` is the ported `fl4CallKernel` on `NR` states off the
virtualization routes**.

Spec: `Fl4Spec/Ext/VirtKernel` (`fl4HandleSyscallV`, `fl4HandleEventV`, `fl4CallKernelV`: `Ext/Entry`'s
`fl4HandleSyscall` / `fl4HandleEvent` / `fl4CallKernel` with the extended dispatcher, `SysVMEnter`,
`handleInterruptV`, `preemptionPathV`, `fl4KernelExitV`), against `Ext/Entry`. Nothing of the port changes.

* `fl4HandleSyscallV_eqNR`: every syscall, from an `NR` state (VirtR7e) where the invoked capability register
  read is `OffRoute` (`OffRouteS`).
* `isVmEnterCall_nvv`: no VCPU ⇒ no unknown syscall is a VMEnter; `fl4HandleEventV_syscall`,
  `fl4HandleEventV_unknown_nvv`, `fl4HandleEventV_interrupt`; `fl4HandleEventV_eqNR`: every event — the
  syscall event from its entry points (`EntryPt`: after `update_time_stamp` and a passing
  `check_budget_restart`), the unknown syscall (`NVV`), the interrupt (`maybeHandleInterruptV_eq`), the rest
  definitionally.
* **`fl4CallKernelV_eqNR`**: `fl4CallKernelV onCore rep ev σ = fl4CallKernel rep ev σ` on an `NR` state, given
  the two premises below. The preemption path is `preemptionPathV_eq`, the exit `fl4KernelExitV_eq'` (VirtAwaken),
  both at states where `NoRunVM` holds by invA's `ns_*` frames of the ported event.

Named premises:
* **`hoff : ∀ t, EntryPt σ t → OffRouteS c t` [S]** (syscall events only): the scope of VirtR7e's `OffRoute`, at
  each entry point and for the capability register the syscall reads. On-route entries are covered against the
  extended spec by the route-B posts (`decOKV_thread88_noVirt`, `decOKV_frame60_noVirt`, `decOKV_untyped_vtxGate`).
* **`hnvc : ∀ t, EntryPt σ t → NVC t` [W]** (syscall events only): no virtualization cap appears in a slot across
  the entry's budget check. Open: `NVV` and `NoRunVM` are proved there (`ty_*` / `ns_*`), but `check_budget_restart`
  can reach the timeout-fault IPC, a cap writer, and `NVC`'s frame family for the cap writers (the vih3 G/W/Y
  pattern of SpecInvValidIrqHandlersG with `¬ IsVirtCap` for `CA`) is not built yet.

No [J]/[P]. New file only.
-/
import Fl4Proofs.P3.VirtR7e
open Classical

namespace Fl4Proofs.P3.VirtR7eK
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvL Fl4Proofs.P3.SInvTY Fl4Proofs.P3.VirtR7b
  Fl4Proofs.P3.VirtR7d Fl4Proofs.P3.VirtAwaken Fl4Proofs.P3.VirtR7e

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Syscalls -/

/-- The capability register an invoking syscall reads. -/
def sysReg : Syscall → Option Register
  | .sysSend => some cap_register
  | .sysNBSend => some cap_register
  | .sysCall => some cap_register
  | .sysReplyRecv => some replyRegister
  | .sysNBSendRecv => some nbsendRecvDest
  | .sysNBSendWait => some replyRegister
  | _ => none

/-- **The syscall's invocation is off the virtualization routes** (the [S] premise, module docstring). -/
def OffRouteS (c : Syscall) (t : State Unit) : Prop :=
  ∀ reg, sysReg c = some reg → ∀ cptr t', (cptr, t') ∈ (getCapReg (Z := Unit) reg t).1 → ∀ fp, OffRoute fp cptr t'

theorem nr_getCapReg (reg : Register) : IK NR (getCapReg (Z := Unit) reg) :=
  nr_of (SInvV.hv_getCapReg (P := NVC) reg) (ty_getCapReg reg) (ns_getCapReg reg)

/-- One invoking syscall: read the register, invoke, continue the same way. -/
theorem invoke_congr (onCore : ObjRef → Bool) (rep calling blocking don fp : Bool) (reg : Register)
    {k : Unit → PMonad Unit Unit} {t : State Unit} (ht : NR t)
    (hoff : ∀ cptr t', (cptr, t') ∈ (getCapReg (Z := Unit) reg t).1 → OffRoute fp cptr t') :
    ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) reg) >>= fun cptr =>
        fl4HandleInvocationV onCore rep calling blocking don fp cptr >>= k) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) reg) >>= fun cptr =>
        fl4HandleInvocationR rep calling blocking don fp cptr >>= k) t := by
  refine nde_bind_congr rfl fun cptr t' h => ?_
  have h' := mem_run_liftE' h
  exact nde_bind_congr (fl4HandleInvocationV_eqNR onCore rep calling blocking don fp cptr
    (nr_getCapReg reg t ht _ h') (hoff cptr t' h')) fun _ _ _ => rfl

/-- One invoking syscall without a continuation. -/
theorem invoke_congr0 (onCore : ObjRef → Bool) (rep calling blocking don fp : Bool) (reg : Register)
    {t : State Unit} (ht : NR t)
    (hoff : ∀ cptr t', (cptr, t') ∈ (getCapReg (Z := Unit) reg t).1 → OffRoute fp cptr t') :
    ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) reg) >>= fun cptr =>
        fl4HandleInvocationV onCore rep calling blocking don fp cptr) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) reg) >>= fun cptr =>
        fl4HandleInvocationR rep calling blocking don fp cptr) t := by
  refine nde_bind_congr rfl fun cptr t' h => ?_
  have h' := mem_run_liftE' h
  exact fl4HandleInvocationV_eqNR onCore rep calling blocking don fp cptr
    (nr_getCapReg reg t ht _ h') (hoff cptr t' h')

/-- **Every syscall of the extended kernel is the ported one** from an `NR` state, off the routes. -/
theorem fl4HandleSyscallV_eqNR (onCore : ObjRef → Bool) (rep : Bool) (c : Syscall) {t : State Unit}
    (ht : NR t) (hoff : OffRouteS c t) :
    ExceptT.run (fl4HandleSyscallV (Z := Unit) onCore rep c) t = ExceptT.run (fl4HandleSyscall rep c) t := by
  cases c with
  | sysSend =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationV onCore rep false true false false cptr) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep false true false false cptr) t
    exact invoke_congr0 onCore rep false true false false cap_register ht fun cptr t' h => hoff _ rfl cptr t' h _
  | sysNBSend =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationV onCore rep false false false false cptr) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep false false false false cptr) t
    exact invoke_congr0 onCore rep false false false false cap_register ht fun cptr t' h => hoff _ rfl cptr t' h _
  | sysCall =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationV onCore rep true true true false cptr) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) cap_register) >>= fun cptr =>
        fl4HandleInvocationR rep true true true false cptr) t
    exact invoke_congr0 onCore rep true true true false cap_register ht fun cptr t' h => hoff _ rfl cptr t' h _
  | sysReplyRecv =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationV onCore rep false false true true cptr >>= fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) t
    exact invoke_congr onCore rep false false true true replyRegister (k := fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) ht fun cptr t' h => hoff _ rfl cptr t' h _
  | sysNBSendRecv =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) nbsendRecvDest) >>= fun cptr =>
        fl4HandleInvocationV onCore rep false false true true cptr >>= fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) nbsendRecvDest) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) t
    exact invoke_congr onCore rep false false true true nbsendRecvDest (k := fun _ => withoutPreemption (handleRecv (Z := Unit) true true)) ht fun cptr t' h => hoff _ rfl cptr t' h _
  | sysNBSendWait =>
    show ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationV onCore rep false false true true cptr >>= fun _ => withoutPreemption (handleRecv (Z := Unit) true false)) t =
      ExceptT.run (NonDetE.liftE (getCapReg (Z := Unit) replyRegister) >>= fun cptr =>
        fl4HandleInvocationR rep false false true true cptr >>= fun _ => withoutPreemption (handleRecv (Z := Unit) true false)) t
    exact invoke_congr onCore rep false false true true replyRegister (k := fun _ => withoutPreemption (handleRecv (Z := Unit) true false)) ht fun cptr t' h => hoff _ rfl cptr t' h _
  | sysRecv => rfl
  | sysYield => rfl
  | sysWait => rfl
  | sysNBWait => rfl
  | sysNBRecv => rfl

/-! ## Events -/

theorem isVmEnterCall_nvv {σ : State Unit} (hv : NVV σ) (num : Nat) : isVmEnterCall num σ = false := by
  have ht : tcbVcpuOf σ σ.curThread = none :=
    tcbVcpuOf_none.2 fun v st h => by rw [vcpuAt_nvv hv v] at h; cases h
  unfold isVmEnterCall
  simp [ht]

/-- The unknown-syscall branch is the ported `handleEvent` without VCPUs (VirtR7's `_noVirt` for `NVV`). -/
theorem fl4HandleEventV_unknown_nvv (onCore : ObjRef → Bool) (rep : Bool) {σ : State Unit} (hv : NVV σ)
    (num : Nat) :
    (fl4HandleEventV (Z := Unit) onCore rep (.unknownSyscall num)).run σ =
      (handleEvent (Z := Unit) (.unknownSyscall num)).run σ := by
  unfold fl4HandleEventV
  rw [ExceptT.run_bind]
  have hg : (NonDetE.liftE (ε := Unit) (NonDet.gets (isVmEnterCall (Z := Unit) num))).run σ =
      ({(.ok false, σ)}, False) := by
    refine run_liftE ?_
    show ({(isVmEnterCall (Z := Unit) num σ, σ)}, False) = _
    rw [isVmEnterCall_nvv hv num]
  rw [nd_bind_single hg]
  rfl

/-- The entry points of a syscall event: after `update_time_stamp` and a passing `check_budget_restart`. -/
def EntryPt (σ t : State Unit) : Prop :=
  ∃ t1, ((), t1) ∈ (updateTimeStamp (Z := Unit) σ).1 ∧ (true, t) ∈ (checkBudgetRestart (Z := Unit) t1).1

/-- The syscall event. -/
theorem fl4HandleEventV_syscall (onCore : ObjRef → Bool) (rep : Bool) (c : Syscall) {σ : State Unit} (hs : NR σ)
    (hoff : ∀ t, EntryPt σ t → OffRouteS c t) (hnvc : ∀ t, EntryPt σ t → NVC t) :
    ExceptT.run (fl4HandleEventV (Z := Unit) onCore rep (.syscallEvent c)) σ =
      ExceptT.run (fl4HandleEvent rep (.syscallEvent c)) σ := by
  show ExceptT.run (NonDetE.liftE updateTimeStamp >>= fun _ => NonDetE.liftE checkBudgetRestart >>= fun restart =>
      NonDetE.whenE restart (fl4HandleSyscallV (Z := Unit) onCore rep c)) σ =
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
    have hnv : NV t := ⟨hnvc t he, ty_checkBudgetRestart t1 (ty_updateTimeStamp σ hs.1.2 _ h1') _ h2'⟩
    have hnr : NoRunVM t := ns_checkBudgetRestart t1 (ns_updateTimeStamp σ hs.2 _ h1') _ h2'
    exact fl4HandleSyscallV_eqNR onCore rep c ⟨hnv, hnr⟩ (hoff t he)

/-- The interrupt event. -/
theorem fl4HandleEventV_interrupt (onCore : ObjRef → Bool) (rep : Bool) {σ : State Unit} (hn : NoRunVM σ) :
    ExceptT.run (fl4HandleEventV (Z := Unit) onCore rep .interrupt) σ =
      ExceptT.run (fl4HandleEvent rep .interrupt) σ := by
  show ExceptT.run (withoutPreemption (updateTimeStamp >>= fun _ => checkBudget >>= fun _ =>
      maybeHandleInterruptV (Z := Unit) onCore false)) σ =
    ExceptT.run (withoutPreemption (updateTimeStamp >>= fun _ => checkBudget >>= fun _ =>
      maybeHandleInterrupt (Z := Unit) false)) σ
  refine run_liftE_congr ?_
  refine bind_nr ns_updateTimeStamp hn fun _ s1 h1 => ?_
  exact bind_nr ns_checkBudget h1 fun _ s2 h2 => maybeHandleInterruptV_eq onCore h2 false

/-- **Every event of the extended kernel is the ported one** from an `NR` state (premises: module docstring). -/
theorem fl4HandleEventV_eqNR (onCore : ObjRef → Bool) (rep : Bool) (ev : Event) {σ : State Unit} (hs : NR σ)
    (hoff : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS c t)
    (hnvc : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → NVC t) :
    ExceptT.run (fl4HandleEventV (Z := Unit) onCore rep ev) σ = ExceptT.run (fl4HandleEvent rep ev) σ := by
  cases ev with
  | syscallEvent c => exact fl4HandleEventV_syscall onCore rep c hs (hoff c rfl) (hnvc c rfl)
  | unknownSyscall n => exact fl4HandleEventV_unknown_nvv onCore rep hs.1.2 n
  | interrupt => exact fl4HandleEventV_interrupt onCore rep hs.2
  | _ => rfl

/-! ## The kernel step -/

/-- **R7 (e): the extended kernel step is the ported one** on an `NR` state (premises: module docstring). -/
theorem fl4CallKernelV_eqNR (onCore : ObjRef → Bool) (rep : Bool) (ev : Event) {σ : State Unit} (hs : NR σ)
    (hoff : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → OffRouteS c t)
    (hnvc : ∀ c, ev = .syscallEvent c → ∀ t, EntryPt σ t → NVC t) :
    fl4CallKernelV (Z := Unit) onCore rep ev σ = fl4CallKernel rep ev σ := by
  unfold fl4CallKernelV fl4CallKernel
  have hH : ExceptT.run (NonDetE.handleE (fl4HandleEventV (Z := Unit) onCore rep ev)
        (fun _ => withoutPreemption (preemptionPathV onCore))) σ =
      ExceptT.run (NonDetE.handleE (fl4HandleEvent (Z := Unit) rep ev)
        (fun _ => withoutPreemption preemptionPath)) σ := by
    unfold NonDetE.handleE
    rw [ExceptT.run_mk, ExceptT.run_mk]
    refine (nd_bind_eq_of (fl4HandleEventV_eqNR onCore rep ev hs hoff hnvc) _).trans
      (nd_bind_congr_on _ _ _ σ fun y hy => ?_)
    obtain ⟨r, u⟩ := y
    cases r with
    | ok a => rfl
    | error e =>
      have hu : NoRunVM u := ns_fl4HandleEvent rep ev σ hs.2 _ hy
      exact run_liftE_congr (preemptionPathV_eq onCore hu)
  rw [nd_bind_eq_of hH]
  refine nd_bind_congr_on _ _ _ σ fun y hy => ?_
  have hu : NoRunVM y.2 := ike_handleE (ns_fl4HandleEvent rep ev) (fun _ => ike_liftE ns_preemptionPath) σ hs.2 _ hy
  exact fl4KernelExitV_eq' onCore hu

end

end Fl4Proofs.P3.VirtR7eK
