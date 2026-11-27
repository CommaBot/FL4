/- s27: global-PML4 frame lemmas `GpK g` (sg1's SpecInvSgI4 renamed; see SpecInvGpK1). -/
import Fl4Proofs.P3.SpecInvGpK3
open Classical

namespace Fl4Proofs.P3.SInvGp
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem gpk_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : GpK N (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; gpk_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getExtraCptrs _ _)

theorem gpk_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : GpKE N (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_lookupSlotForThread _ _)

theorem gpk_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : GpKE N (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_lookupCapAndSlot _ _)

theorem gpk_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : GpKE N (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_lookupExtraCaps _ _ _)

theorem gpk_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : GpKE N m) : GpK N (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; gpk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible refine gpk_emptyOnFailure _ ?_)

theorem gpk_loadCapTransfer (buffer : ObjRef) : GpK N (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_loadCapTransfer _)

theorem gpk_lookupCap (thread : ObjRef) (ref : CapRef) : GpKE N (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_lookupCap _ _)

theorem gpk_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : GpKE N m) : GpKE N (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; gpk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible refine gpk_unifyFailure _ ?_)

theorem gpk_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : GpK N (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getReceiveSlots _ _)

theorem gpk_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : GpKE N m) : GpK N (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; gpk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible refine gpk_constOnFailure _ _ ?_)

theorem gpk_deriveCap (slot : CslotPtr) (cap : Cap) : GpKE N (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_deriveCap _ _)

theorem gpk_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : GpK N (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setExtraBadge _ _ _)

theorem gpk_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      GpK N (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; gpk_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => gpk_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | gpk_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_transferCapsLoop _ _ _ _ _ _)

theorem gpk_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : GpK N (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_transferCaps _ _ _ _ _)

theorem gpk_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : GpK N (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_doNormalTransfer _ _ _ _ _ _ _)

theorem gpk_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : GpK N (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_doIpcTransfer _ _ _ _ _)

theorem gpk_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : GpK N (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_replyPush _ _ _ _)

theorem gpk_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : GpK N (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_orderedInsert _ _ _ _)

theorem gpk_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : GpK N (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_tcbAppend _ _)

theorem gpk_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : GpK N (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_tcbEpAppend _ _ _)

theorem gpk_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : GpK N (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_sendIpcBlocked _ _ _ _ _ _)

theorem gpk_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : GpK N (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_sendIpc _ _ _ _ _ _ _ _)

theorem gpk_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : GpK N (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_sendFaultIpc _ _ _ _)

theorem gpk_handleTimeout (tptr : ObjRef) (ex : Fault) : GpK N (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_handleTimeout _ _)

theorem gpk_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : GpK N (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_readyTimesAppend _ _)

theorem gpk_tcbReleaseEnqueue (tcbPtr : ObjRef) : GpK N (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_tcbReleaseEnqueue _)

theorem gpk_postpone (scPtr : ObjRef) : GpK N (postpone (Z := Unit) scPtr) := by
  unfold postpone; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_postpone _)

theorem gpk_endTimeslice (canTimeout : Bool) : GpK N (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_endTimeslice _)

theorem gpk_getRefills (scPtr : ObjRef) : GpK N (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getRefills _)

theorem gpk_refillSize (scPtr : ObjRef) : GpK N (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_refillSize _)

theorem gpk_refillSingle (scPtr : ObjRef) : GpK N (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_refillSingle _)

theorem gpk_getRefillTail (scPtr : ObjRef) : GpK N (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getRefillTail _)

theorem gpk_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : GpK N (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_refillAddTail _ _)

theorem gpk_refillFull (scPtr : ObjRef) : GpK N (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_refillFull _)

theorem gpk_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : GpK N (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_updateRefillTl _ _)

theorem gpk_scheduleUsed (scPtr : ObjRef) (new : Refill) : GpK N (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_scheduleUsed _ _)

theorem gpk_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : GpK N (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_chargeEntireHeadRefill _ _)

theorem gpk_handleOverrun (scPtr : ObjRef) (usage : Ticks) : GpK N (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_handleOverrun _ _)

theorem gpk_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : GpK N (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_mergeNonoverlappingHeadRefill _)

theorem gpk_headInsufficientLoop (scPtr : ObjRef) : GpK N (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_headInsufficientLoop _)

theorem gpk_refillBudgetCheck (usage : Ticks) : GpK N (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_refillBudgetCheck _)

theorem gpk_refillResetRr (cscPtr : ObjRef) : GpK N (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_refillResetRr _)

theorem gpk_chargeBudget (consumed : Ticks) (canTimeout : Bool) : GpK N (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_chargeBudget _ _)

theorem gpk_checkBudget  : GpK N (checkBudget (Z := Unit)) := by
  unfold checkBudget; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_checkBudget)

theorem gpk_checkBudgetRestart  : GpK N (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_checkBudgetRestart)

theorem gpk_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : GpK N m) : GpK N (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; gpk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible refine gpk_checkCapAt _ _ _ ?_)

theorem gpk_checkDomainTime  : GpK N (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_checkDomainTime)

theorem gpk_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : GpKE N (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_checkHandlerEp _ _)

theorem gpk_checkPrio (newPrio : Data) (authTcb : ObjRef) : GpKE N (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_checkPrio _ _)

theorem gpk_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : GpKE N (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_checkValidIpcBuffer _ _)

theorem gpk_nextDomain  : GpK N (nextDomain (Z := Unit)) := by
  unfold nextDomain; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_nextDomain)

theorem gpk_switchToThread (t : ObjRef) : GpK N (switchToThread (Z := Unit) t) := by
  unfold switchToThread; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_switchToThread _)

theorem gpk_guardedSwitchTo (thread : ObjRef) : GpK N (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_guardedSwitchTo _)

theorem gpk_switchToIdleThread  : GpK N (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_switchToIdleThread)

theorem gpk_chooseThread  : GpK N (chooseThread (Z := Unit)) := by
  unfold chooseThread; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_chooseThread)

theorem gpk_refillBudgetCheckRoundRobin (usage : Ticks) : GpK N (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_refillBudgetCheckRoundRobin _)

theorem gpk_commitTime  : GpK N (commitTime (Z := Unit)) := by
  unfold commitTime; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_commitTime)

theorem gpk_schedContextResume (scPtr : ObjRef) : GpK N (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_schedContextResume _)

theorem gpk_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : GpK N (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_maybeDonateSc _ _)

theorem gpk_completeSignal (ntfnptr tptr : ObjRef) : GpK N (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_completeSignal _ _)

theorem gpk_copyGlobalMappings (newPm : ObjRef) : GpK N (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_copyGlobalMappings _)

theorem gpk_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : GpK N (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_createCap _ _ _ _ _)

theorem gpk_dataToObjType (type : Data) : GpKE N (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_dataToObjType _)

theorem gpk_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : GpKE N (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeBindNotification _ _)

theorem gpk_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : GpKE N (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_lookupPivotSlot _ _ _)

theorem gpk_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : GpKE N (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_lookupSourceSlot _ _ _)

theorem gpk_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : GpKE N (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeCnodeInvocation _ _ _ _)

theorem gpk_slotCapLongRunningDelete (slot : CslotPtr) : GpK N (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_slotCapLongRunningDelete _)

theorem gpk_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : GpKE N (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeCvSpace _ _ _ _)
end

end Fl4Proofs.P3.SInvGp
