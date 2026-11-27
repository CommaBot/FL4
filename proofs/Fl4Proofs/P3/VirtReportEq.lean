/-
P3 (DESIGN.md §9), virtualization: the FL4 report ops of `Ext/VirtReport`
(FL4 #80 / #81 / #85) against the old ones of `Ext/VirtVcpu` /
`Ext/VirtEntry`, where they agree.

* `vmenterReportF_pending` (pure): with a pending exit and no full-state
  caller, FL4's report writes the old `vmenterReport`'s 30 MRs, message
  info 1, badge 0, and clears `PENDING`.
* **`vmReportF_eq_pending`**: there `vmReportF t b` is `vmReport t b`
  followed by FaultIP := NextIP (`vmFaultIpNext`, #81) — the only
  difference.
* `vmCheckF_eq_pending`: the pending-exit branch of the check likewise.
* `vcpuDetachF_eq` (a thread not `runningVM`), `vcpuDetachF_noVirt`,
  `vmCheckF_not_runningVM`: no report, so new = old (= nothing for the
  check).

Not equal elsewhere (the reason the new ops exist): every completed
VMEnter writes FaultIP; a non-pending report of a full-state caller
writes 30 MRs (MR2 masked, MR3 the reason, `finish_notification`); a
non-pending, non-full report writes only MR0..2 (the old `vmReport` of a
thread without VCPU wrote 30 zeros; the old notification completion
`vmNotifyComplete` wrote none without VCPU, FL4 three zeros).

No premise: every statement assumes only facts of the given state.
-/
import Fl4Spec.Ext.VirtReport
import Fl4Spec.Ext.VirtP3x
import Fl4Proofs.P3.EpXferSpec
import Fl4Proofs.P3.EpRecvSend

namespace Fl4Proofs.P3.VirtReportEq
open Fl4Spec Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

theorem nd_bind_assoc_fun {σ' α β γ : Type} (m : NonDet σ' α) (f : α → NonDet σ' β) (g : β → NonDet σ' γ) :
    ((m >>= f) >>= g) = (m >>= fun a => f a >>= g) := by
  funext s; exact (nd_bind_assoc m f g s).symm

/-! ## The pure report -/

/-- With a pending exit and no full-state caller FL4's report is the old
`vmenterReport` (any badge: a pending exit reports badge 0). -/
theorem vmenterReportF_pending (k : VirtKind) (s : VcpuState) (hp : s.exit.pending = true)
    (b b' : Word) :
    vmenterReportF k (some s) false b =
      ⟨(List.finRange 30).map (vmenterReport k (some s) b').mrs,
        (vmenterReport k (some s) b').msgInfo, (vmenterReport k (some s) b').badge, true⟩ := by
  have hm : vmenterFullMrs k (some s) false = (vmenterReport k (some s) b').mrs := by
    funext i
    simp only [vmenterFullMrs, vmenterReport, hp]
    simp
  simp only [vmenterReportF, hp, hm]
  simp [vmenterReport, hp]

/-! ## Deterministic reads -/

variable {Z : Type} [StateExt Z]

theorem kheap_of_vcpuAt {σ : State Z} {v : ObjRef} {s : VcpuState} (hv : vcpuAt σ v = some s) :
    σ.kheap v = some (.archObj (.vcpu s)) := by
  unfold vcpuAt at hv
  split at hv
  · rename_i st h; cases hv; exact h
  · cases hv

theorem getVcpu_eq {σ : State Z} {v : ObjRef} {s : VcpuState} (hv : vcpuAt σ v = some s) :
    getVcpu (Z := Z) v σ = ({(s, σ)}, False) := by
  unfold getVcpu
  rw [nd_bind_one (getObject_eq (kheap_of_vcpuAt hv))]
  rfl

theorem getTcbVcpu_eq (σ : State Z) (t : ObjRef) :
    getTcbVcpu (Z := Z) t σ = ({(tcbVcpuOf σ t, σ)}, False) := rfl

theorem vmFullReply_eq {σ : State Z} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) :
    vmFullReply (Z := Z) t σ =
      ({(decide (x.tcbArch.tcbContext.userRegs msg_info_register = 30), σ)}, False) := by
  unfold vmFullReply
  rw [nd_bind_one (asUser_getRegister_eq hk _)]
  rfl

/-! ## The report -/

/-- **FL4's report = the old report + FaultIP := NextIP** on a pending
exit of a caller that is not full-state (`msg_info ≠ 30`). -/
theorem vmReportF_eq_pending {σ : State Z} {t v : ObjRef} {x : Tcb} {s : VcpuState}
    (hk : σ.kheap t = some (.tcb x)) (hmi : x.tcbArch.tcbContext.userRegs msg_info_register ≠ 30)
    (hb : tcbVcpuOf σ t = some v) (hv : vcpuAt σ v = some s) (hp : s.exit.pending = true) (b : Word) :
    vmReportF (Z := Z) t b σ = (vmReport t b >>= fun _ => vmFaultIpNext t) σ := by
  unfold vmReportF vmReport
  simp only [nd_bind_assoc_fun]
  rw [nd_bind_one (getTcbVcpu_eq σ t), nd_bind_one (getTcbVcpu_eq σ t), hb]
  dsimp only
  simp only [nd_bind_assoc_fun]
  rw [nd_bind_one (getVcpu_eq hv), nd_bind_one (getVcpu_eq hv), nd_pure_bind', nd_pure_bind',
    nd_bind_one (vmFullReply_eq hk), decide_eq_false hmi, nd_pure_bind', nd_pure_bind',
    vmenterReportF_pending _ s hp b b]

/-! ## Detach and check -/

/-- A thread that is not `runningVM` gets no report: `vcpuDetachF` is
`vcpuDetach`. -/
theorem vcpuDetachF_eq {σ : State Z} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hs : x.tcbState ≠ .runningVM) :
    vcpuDetachF (Z := Z) t σ = vcpuDetach t σ := by
  unfold vcpuDetachF vcpuDetach
  rw [nd_bind_one (getTcbVcpu_eq σ t), nd_bind_one (getTcbVcpu_eq σ t)]
  cases tcbVcpuOf σ t with
  | none => rfl
  | some v =>
    dsimp only
    rw [nd_bind_one (getThreadState_eq hk), nd_bind_one (getThreadState_eq hk)]
    unfold NonDet.when
    rw [if_neg hs, if_neg hs]

/-- `vcpuDetachF` does nothing without virtualization objects. -/
theorem vcpuDetachF_noVirt {σ : State Z} (hn : NoVirtObjects σ) (t : ObjRef) :
    vcpuDetachF (Z := Z) t σ = ({((), σ)}, False) := by
  unfold vcpuDetachF
  rw [nd_bind_det _ _ σ none (by simp only [getTcbVcpu, NonDet.gets, hn.tcbVcpuOf])]
  rfl

/-- `vmCheckF` of a thread that is not `runningVM` does nothing. -/
theorem vmCheckF_not_runningVM {σ : State Z} {t : ObjRef} {x : Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hs : x.tcbState ≠ .runningVM) :
    vmCheckF (Z := Z) t σ = ({((), σ)}, False) := by
  unfold vmCheckF
  rw [nd_bind_one (getThreadState_eq hk)]
  unfold NonDet.when
  rw [if_neg hs]
  rfl

/-- The check of a `runningVM` thread with a pending exit (not a
full-state caller): the old check is `vmReport t 0`, FL4's adds
FaultIP := NextIP. -/
theorem vmCheckF_eq_pending {σ : State Z} {t v : ObjRef} {x : Tcb} {s : VcpuState}
    (hk : σ.kheap t = some (.tcb x)) (hs : x.tcbState = .runningVM)
    (hmi : x.tcbArch.tcbContext.userRegs msg_info_register ≠ 30)
    (hb : tcbVcpuOf σ t = some v) (hv : vcpuAt σ v = some s) (hp : s.exit.pending = true) :
    vmCheck (Z := Z) t σ = vmReport t 0 σ ∧
      vmCheckF (Z := Z) t σ = (vmReport t 0 >>= fun _ => vmFaultIpNext t) σ := by
  constructor
  · unfold vmCheck
    rw [nd_bind_one (getThreadState_eq hk)]
    unfold NonDet.when
    rw [if_pos hs, nd_bind_one (getTcbVcpu_eq σ t), hb]
    dsimp only
    rw [nd_bind_one (getVcpu_eq hv), nd_pure_bind', hp]
    rfl
  · unfold vmCheckF
    rw [nd_bind_one (getThreadState_eq hk)]
    unfold NonDet.when
    rw [if_pos hs, nd_bind_one (getTcbVcpu_eq σ t), hb]
    dsimp only
    rw [nd_bind_one (getVcpu_eq hv), nd_pure_bind', hp]
    exact vmReportF_eq_pending hk hmi hb hv hp 0

end

end Fl4Proofs.P3.VirtReportEq
