/-
P3 (issue #16, sd7; KENTRY-PLAN g7a-4 (2)): **`SI N t` kept by the cap-writing
ancestors that need no decode fact**: sg1's generated SpecInvSgG (family `IK (S N M)`,
prefix `sg`) mechanically renamed to the family `IK (SI N t)`, prefix `si`. Leaves
(SpecInvSiA): the `UK` frames (`iw_of_uk`), `cap_delete_one`, `rec_del` /
`cap_delete`, the TCB installs, `do_normal_transfer`.
-/
import Fl4Proofs.P3.SpecInvSiA
open Classical

namespace Fl4Proofs.P3.SInvIV
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvG
noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : Irq → ObjRef} {t : ObjRef}

syntax "iw_leaf" : tactic
macro_rules | `(tactic| iw_leaf) => `(tactic| fail "no iw_leaf")
macro_rules | `(tactic| iw_leaf) => `(tactic| (refine iw_of_uk fun _ => ?_; uk_leaf; done))
macro_rules | `(tactic| iw_leaf) => `(tactic| (refine iwe_of_uk fun _ => ?_; uk_leaf; done))
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_capDeleteOne _)
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_recDel_cte _ _)
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_recDel_fin _ _)
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_capDelete _)
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_doNormalTransfer _ _ _ _ _ _ _)
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_installTcbCap _ _ _ _ (by decide))
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_checkCapAt_ins _ _ _ _ _ (by decide))

macro "iw_auto" : tactic => `(tactic| repeat' (first | iw_leaf | contradiction | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

theorem iw_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : IKE (SI N t) m) : IKE (SI N t) (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; iw_auto
  all_goals first | exact h_m
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible refine iw_capFaultOnFailure _ _ _ ?_)

theorem iw_deletingIrqHandler (irq : Irq) : IK (SI N t) (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; iw_auto
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_deletingIrqHandler _)

theorem iw_finaliseCap (a0 : Cap) (a1 : Bool) : IK (SI N t) (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; iw_auto
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_finaliseCap _ _)

theorem iw_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : IKE (SI N t) f) (h_g : IKE (SI N t) g) : IKE (SI N t) (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; iw_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible refine iw_orChoiceE _ _ _ ?_ ?_)

theorem iw_withoutPreemption {α : Type} (m : SMonad Unit α) (h_m : IK (SI N t) m) : IKE (SI N t) (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; iw_auto
  all_goals first | exact h_m
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible refine iw_withoutPreemption _ ?_)


/-- One step of `cap_revoke`, its recursive calls keeping `SI N t`. -/
theorem iw_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, IK (SI N t) (f k)) (sl : CslotPtr) : IKE (SI N t) (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, IKE (SI N t) (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  iw_auto
  all_goals exact hrec' _

theorem iw_capRevoke (sl : CslotPtr) : IKE (SI N t) (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => iw_capRevokeF hf k) sl
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_capRevoke _)

theorem iw_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : IKE (SI N t) m) : IK (SI N t) (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; iw_auto
  all_goals first | exact h_m
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible refine iw_emptyOnFailure _ ?_)

theorem iw_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : IKE (SI N t) m) : IKE (SI N t) (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; iw_auto
  all_goals first | exact h_m
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible refine iw_lookupErrorOnFailure _ _ ?_)

theorem iw_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : IKE (SI N t) m) : IKE (SI N t) (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; iw_auto
  all_goals first | exact h_m
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible refine iw_unifyFailure _ ?_)

theorem iw_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : IKE (SI N t) m) : IK (SI N t) (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; iw_auto
  all_goals first | exact h_m
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible refine iw_constOnFailure _ _ ?_)

theorem iw_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : IK (SI N t) (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; iw_auto
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_doIpcTransfer _ _ _ _ _)

theorem iw_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : IK (SI N t) (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; iw_auto
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_sendIpc _ _ _ _ _ _ _ _)

theorem iw_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : IK (SI N t) (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; iw_auto
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_sendFaultIpc _ _ _ _)

theorem iw_handleTimeout (tptr : ObjRef) (ex : Fault) : IK (SI N t) (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; iw_auto
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_handleTimeout _ _)

theorem iw_endTimeslice (canTimeout : Bool) : IK (SI N t) (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; iw_auto
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_endTimeslice _)

theorem iw_chargeBudget (consumed : Ticks) (canTimeout : Bool) : IK (SI N t) (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; iw_auto
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_chargeBudget _ _)

theorem iw_checkBudget  : IK (SI N t) (checkBudget (Z := Unit)) := by
  unfold checkBudget; iw_auto
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_checkBudget)

theorem iw_checkBudgetRestart  : IK (SI N t) (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; iw_auto
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_checkBudgetRestart)

theorem iw_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : IK (SI N t) (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; iw_auto
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_doReplyTransfer _ _ _)

theorem iw_handleFault (thread : ObjRef) (ex : Fault) : IK (SI N t) (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; iw_auto
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_handleFault _ _)

set_option maxHeartbeats 4000000 in
theorem iw_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    IK (SI N t) (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; iw_auto
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_receiveIpc _ _ _ _)

theorem iw_handleRecv (isBlocking canReply : Bool) : IK (SI N t) (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; iw_auto
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_handleRecv _ _)

theorem iw_handleYield  : IK (SI N t) (handleYield (Z := Unit)) := by
  unfold handleYield; iw_auto
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_handleYield)

theorem iw_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : IKE (SI N t) (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; iw_auto
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_installTcbFrameCap _ _ _)

theorem iw_invokeTcb (a0 : TcbInvocation) : IKE (SI N t) (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; iw_auto
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_invokeTcb _)

theorem iw_preemptionPath  : IK (SI N t) (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; iw_auto
macro_rules | `(tactic| iw_leaf) => `(tactic| with_reducible exact iw_preemptionPath)

end

end Fl4Proofs.P3.SInvIV
