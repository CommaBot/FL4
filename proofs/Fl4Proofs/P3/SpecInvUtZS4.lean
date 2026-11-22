/- g5h: `ZR` across the syscalls, the events and the kernel entry (KENTRY-PLAN g5h; see SpecInvUtZS2). -/
import Fl4Proofs.P3.SpecInvUtZS3
open Classical

namespace Fl4Proofs.P3.SInvUZ
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

variable {N : Irq → ObjRef}

/-! ## The syscall paths and events -/

set_option maxHeartbeats 4000000 in
theorem zr_fl4HandleSyscall (hG : PerfGapZ) (rep : Bool) (c : Syscall) : IKZE (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c with
  | sysSend =>
    simp only [fl4HandleSyscall]
    exact ikze_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) (by zr_split) fun _ => zr_handleInvocationR hG _ _ _ _ _ _
  | sysNBSend =>
    simp only [fl4HandleSyscall]
    exact ikze_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) (by zr_split) fun _ => zr_handleInvocationR hG _ _ _ _ _ _
  | sysCall =>
    simp only [fl4HandleSyscall]
    exact ikze_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) (by zr_split) fun _ => zr_handleInvocationR hG _ _ _ _ _ _
  | sysReplyRecv =>
    simp only [fl4HandleSyscall]
    exact ikze_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) (by zr_split) fun _ =>
      ikze_bind (zr_handleInvocationR hG _ _ _ _ _ _) fun _ => by zr_split
  | sysNBSendRecv =>
    simp only [fl4HandleSyscall]
    exact ikze_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) (by zr_split) fun _ =>
      ikze_bind (zr_handleInvocationR hG _ _ _ _ _ _) fun _ => by zr_split
  | sysNBSendWait =>
    simp only [fl4HandleSyscall]
    exact ikze_bind_uk (fun _ => by uk_auto) (fun _ => by nk_auto) (by zr_split) fun _ =>
      ikze_bind (zr_handleInvocationR hG _ _ _ _ _ _) fun _ => by zr_split
  | sysRecv => simp only [fl4HandleSyscall]; exact ikz_of_ik (by zr_split)
  | sysYield => simp only [fl4HandleSyscall]; exact ikz_of_ik (by zr_split)
  | sysWait => simp only [fl4HandleSyscall]; exact ikz_of_ik (by zr_split)
  | sysNBWait => simp only [fl4HandleSyscall]; exact ikz_of_ik (by zr_split)
  | sysNBRecv => simp only [fl4HandleSyscall]; exact ikz_of_ik (by zr_split)

set_option maxHeartbeats 4000000 in
theorem zr_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    IKHE (ε := Unit) ZR (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; zr_split

set_option maxHeartbeats 4000000 in
theorem zr_fl4HandleEvent (hG : PerfGapZ) (rep : Bool) (ev : Event) : IKZE (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    refine ikze_bind_uk (fun _ => ike_liftE (uk_updateTimeStamp)) (fun _ => by nk_auto)
      (ike_zr (fun _ => ike_liftE (by hv_auto)) (fun _ _ => ike_liftE yk_updateTimeStamp)) fun _ => ?_
    intro N σ hI hN hZ y hy
    obtain ⟨z, hz, ⟨r, hr, hy⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE' hy
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
      simp only [Except.ok.injEq] at hr; subst hr
      have hIx : P3 N x.2 := un_checkBudgetRestart σ hI x hx
      have hNx : NodeIs N x.2 := (show SInvU.NK N (checkBudgetRestart (Z := Unit)) by nk_auto) σ hN x hx
      have hZx : ZR x.2 := ik_zr (fun _ => hu_checkBudgetRestart) (fun _ _ => yk_checkBudgetRestart) σ hZ x hx
      unfold NonDetE.whenE at hy
      split at hy
      · exact zr_fl4HandleSyscall hG rep c N x.2 hIx hNx hZx y hy
      · rw [Set.mem_singleton_iff.1 hy]; exact hZx
    · obtain ⟨x, hx, rfl⟩ := mem_liftE' hz; cases he
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact ikz_of_ik (zr_handleEvent_other ev fun c e => h ⟨c, e⟩)

theorem zr_preempt : IKHE (ε := Unit) ZR (withoutPreemption (Z := Unit) preemptionPath) := by
  zr_split

set_option maxHeartbeats 4000000 in
theorem zr_fl4CallKernel (hG : PerfGapZ) (rep : Bool) (ev : Event) : IKZ (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel
  refine ikz_bind_post ?_ fun _ => by zr_split
  intro N σ hI hN hZ x hx
  unfold NonDetE.handleE at hx
  rw [ExceptT.run_mk] at hx
  obtain ⟨z, hz, hx⟩ := hx
  have hz' := zr_fl4HandleEvent hG rep ev N σ hI hN hZ z hz
  obtain ⟨r, s⟩ := z
  cases r with
  | ok a => rw [Set.mem_singleton_iff.1 hx]; exact hz'
  | error e => exact zr_preempt s hz' x hx

/-! ## Tops -/

/-- **`ZR` across the FaultIP write** (no premise). -/
theorem zr_fl4SyscallFaultIP (t : ObjRef) : IKH ZR (fl4SyscallFaultIP (Z := Unit) t) :=
  ik_zr (fun _ => hv_fl4SyscallFaultIP t) (fun _ _ => yk_fl4SyscallFaultIP t)

set_option maxHeartbeats 4000000 in
theorem zr_kentry (hG : PerfGapZ) (c : Syscall) : IKZ (fl4KernelEntrySyscall (Z := Unit) true c) := by
  unfold fl4KernelEntrySyscall
  intro N σ hI hN hZ y hy
  obtain ⟨x, hx, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hx] at hy
  obtain ⟨x1, hx1, hy⟩ := hy
  exact zr_fl4CallKernel hG true _ N x1.2 (p3_of_view (uk_mem (fun _ => uk_fl4SyscallFaultIP _) hx1) hI)
    (nk_fl4SyscallFaultIP _ σ hN x1 hx1) (zr_fl4SyscallFaultIP _ σ hZ x1 hx1)
    y hy

/-- **`ZR` across the syscall entry, given `PerfGapZ`** (`UtInv3`: the carried
untyped invariant, `SInvA.ut`). -/
theorem kentry_zr_of (hG : PerfGapZ) (c : Syscall) {σ : State Unit} (hU : UtInv3 σ) (hZ : ZR σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, ZR y.2 :=
  zr_kentry hG c σ.interruptIrqNode σ (utInv3_iff.1 hU) rfl hZ

/-- **`ZR` across every kernel event, given `PerfGapZ`.** -/
theorem kcall_zr_of (hG : PerfGapZ) (rep : Bool) (ev : Event) {σ : State Unit} (hU : UtInv3 σ) (hZ : ZR σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ZR y.2 :=
  zr_fl4CallKernel hG rep ev σ.interruptIrqNode σ (utInv3_iff.1 hU) rfl hZ

/-- **`ZR` across the non-syscall events, with no premise** (they reach no perform). -/
theorem kcall_zr_other (rep : Bool) (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) {σ : State Unit} (hZ : ZR σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ZR y.2 := by
  intro y hy
  unfold fl4CallKernel at hy
  refine (ik_bind ?_ fun _ => by zr_split) σ hZ y hy
  refine ike_handleE ?_ fun _ => zr_preempt
  rw [fl4HandleEvent_other rep ev h]
  exact zr_handleEvent_other ev h

end

end Fl4Proofs.P3.SInvUZ
