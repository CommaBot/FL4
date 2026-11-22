/- s26: `ZD` across the syscalls, the events and the kernel entry (SpecInvUtZS4 with `ZD`; see SpecInvDvS2). -/
import Fl4Proofs.P3.SpecInvDvS3
open Classical

namespace Fl4Proofs.P3.SInvDV
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

variable {N : Irq → ObjRef}

/-! ## The syscall paths and events -/

set_option maxHeartbeats 4000000 in
theorem zd_fl4HandleSyscall (hG : PerfGapD) (rep : Bool) (c : Syscall) : IKDE (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c with
  | sysSend =>
    simp only [fl4HandleSyscall]
    exact ikde_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) (by zd_split) fun _ => zd_handleInvocationR hG _ _ _ _ _ _
  | sysNBSend =>
    simp only [fl4HandleSyscall]
    exact ikde_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) (by zd_split) fun _ => zd_handleInvocationR hG _ _ _ _ _ _
  | sysCall =>
    simp only [fl4HandleSyscall]
    exact ikde_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) (by zd_split) fun _ => zd_handleInvocationR hG _ _ _ _ _ _
  | sysReplyRecv =>
    simp only [fl4HandleSyscall]
    exact ikde_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) (by zd_split) fun _ =>
      ikde_bind (zd_handleInvocationR hG _ _ _ _ _ _) fun _ => by zd_split
  | sysNBSendRecv =>
    simp only [fl4HandleSyscall]
    exact ikde_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) (by zd_split) fun _ =>
      ikde_bind (zd_handleInvocationR hG _ _ _ _ _ _) fun _ => by zd_split
  | sysNBSendWait =>
    simp only [fl4HandleSyscall]
    exact ikde_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) (by zd_split) fun _ =>
      ikde_bind (zd_handleInvocationR hG _ _ _ _ _ _) fun _ => by zd_split
  | sysRecv => simp only [fl4HandleSyscall]; exact ikd_of_ik (by zd_split)
  | sysYield => simp only [fl4HandleSyscall]; exact ikd_of_ik (by zd_split)
  | sysWait => simp only [fl4HandleSyscall]; exact ikd_of_ik (by zd_split)
  | sysNBWait => simp only [fl4HandleSyscall]; exact ikd_of_ik (by zd_split)
  | sysNBRecv => simp only [fl4HandleSyscall]; exact ikd_of_ik (by zd_split)

set_option maxHeartbeats 4000000 in
theorem zd_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    IKHE (ε := Unit) ZD (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; zd_split

set_option maxHeartbeats 4000000 in
theorem zd_fl4HandleEvent (hG : PerfGapD) (rep : Bool) (ev : Event) : IKDE (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    refine ikde_bind_uk (fun _ => ike_liftE (uk_updateTimeStamp)) (fun _ => by nk_auto)
      (ike_zd (fun _ => ike_liftE (by hv_auto)) (fun _ => ike_liftE ob_updateTimeStamp)) fun _ => ?_
    intro N σ hI hN hZ y hy
    obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hy
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
      simp only [Except.ok.injEq] at hr; subst hr
      have hIx : P3 N x.2 := un_checkBudgetRestart σ hI x hx
      have hNx : NodeIs N x.2 := (show SInvU.NK N (checkBudgetRestart (Z := Unit)) by nk_auto) σ hN x hx
      have hZx : ZD x.2 := ik_zd (fun _ => hd_checkBudgetRestart) (fun _ => ob_checkBudgetRestart) σ hZ x hx
      unfold NonDetE.whenE at hy
      split at hy
      · exact zd_fl4HandleSyscall hG rep c N x.2 hIx hNx hZx y hy
      · rw [Set.mem_singleton_iff.1 hy]; exact hZx
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz; cases he
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact ikd_of_ik (zd_handleEvent_other ev fun c e => h ⟨c, e⟩)

theorem zd_preempt : IKHE (ε := Unit) ZD (withoutPreemption (Z := Unit) preemptionPath) := by
  zd_split

set_option maxHeartbeats 4000000 in
theorem zd_fl4CallKernel (hG : PerfGapD) (rep : Bool) (ev : Event) : IKD (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine ikd_bind_post ?_ fun _ => by zd_split
  intro N σ hI hN hZ x hx
  unfold NonDetE.handleE at hx
  rw [ExceptT.run_mk] at hx
  obtain ⟨z, hz, hx⟩ := hx
  have hz' := zd_fl4HandleEvent hG rep ev N σ hI hN hZ z hz
  obtain ⟨r, s⟩ := z
  cases r with
  | ok a => rw [Set.mem_singleton_iff.1 hx]; exact hz'
  | error e => exact zd_preempt s hz' x hx

/-! ## Tops -/

/-- **`ZD` across the FaultIP write** (no premise). -/
theorem zd_fl4SyscallFaultIP (t : ObjRef) : IKH ZD (fl4SyscallFaultIP (Z := Unit) t) :=
  ik_zd (fun _ => hv_fl4SyscallFaultIP t) (fun _ => ob_fl4SyscallFaultIP t)

set_option maxHeartbeats 4000000 in
theorem zd_kentry (hG : PerfGapD) (c : Syscall) : IKD (fl4KernelEntrySyscall (Z := Unit) true c) := by
  unfold fl4KernelEntrySyscall
  intro N σ hI hN hZ y hy
  obtain ⟨x, hx, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hx] at hy
  obtain ⟨x1, hx1, hy⟩ := hy
  exact zd_fl4CallKernel hG true _ N x1.2 (p3_of_view (uk_mem (fun _ => uk_fl4SyscallFaultIP _) hx1) hI)
    (nk_fl4SyscallFaultIP _ σ hN x1 hx1) (zd_fl4SyscallFaultIP _ σ hZ x1 hx1)
    y hy

/-- **`ZD` across the syscall entry, given `PerfGapD`** (`UtInv3`: the carried
untyped invariant, `SInvA.ut`). -/
theorem kentry_zd_of (hG : PerfGapD) (c : Syscall) {σ : State Unit} (hU : UtInv3 σ) (hZ : ZD σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, ZD y.2 :=
  zd_kentry hG c σ.interruptIrqNode σ (utInv3_iff.1 hU) rfl hZ

/-- **`ZD` across every kernel event, given `PerfGapD`.** -/
theorem kcall_zd_of (hG : PerfGapD) (rep : Bool) (ev : Event) {σ : State Unit} (hU : UtInv3 σ) (hZ : ZD σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ZD y.2 :=
  zd_fl4CallKernel hG rep ev σ.interruptIrqNode σ (utInv3_iff.1 hU) rfl hZ

/-- **`ZD` across the non-syscall events, with no premise** (they reach no perform). -/
theorem kcall_zd_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) {σ : State Unit} (hZ : ZD σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ZD y.2 := by
  intro y hy
  unfold fl4CallKernel at hy
  refine (ik_bind ?_ fun _ => by zd_split) σ hZ y hy
  refine ike_handleE ?_ fun _ => zd_preempt
  rw [fl4HandleEvent_other rep ev h]
  exact zd_handleEvent_other ev h

end

end Fl4Proofs.P3.SInvDV
