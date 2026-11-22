/- s26: the object half `OBK O` of device `valid_untyped`, part 4 (SpecInvUtZK4 renamed; see SpecInvDvK1). -/
import Fl4Proofs.P3.SpecInvDvK3
open Classical

namespace Fl4Proofs.P3.SInvDV
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {OS : ObSet}



theorem ob_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : OBK OS (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; ob_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getExtraCptrs _ _)

theorem ob_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : OBKE OS (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_lookupSlotForThread _ _)

theorem ob_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : OBKE OS (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_lookupCapAndSlot _ _)

theorem ob_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : OBKE OS (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_lookupExtraCaps _ _ _)

theorem ob_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : OBKE OS m) : OBK OS (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; ob_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible refine ob_emptyOnFailure _ ?_)

theorem ob_loadCapTransfer (buffer : ObjRef) : OBK OS (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_loadCapTransfer _)

theorem ob_lookupCap (thread : ObjRef) (ref : CapRef) : OBKE OS (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_lookupCap _ _)

theorem ob_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : OBKE OS m) : OBKE OS (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; ob_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible refine ob_unifyFailure _ ?_)

theorem ob_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : OBK OS (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getReceiveSlots _ _)

theorem ob_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : OBKE OS m) : OBK OS (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; ob_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible refine ob_constOnFailure _ _ ?_)

theorem ob_deriveCap (slot : CslotPtr) (cap : Cap) : OBKE OS (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_deriveCap _ _)

theorem ob_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : OBK OS (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setExtraBadge _ _ _)

theorem ob_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      OBK OS (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; ob_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => ob_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | ob_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_transferCapsLoop _ _ _ _ _ _)

theorem ob_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : OBK OS (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_transferCaps _ _ _ _ _)

theorem ob_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : OBK OS (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_doNormalTransfer _ _ _ _ _ _ _)

theorem ob_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : OBK OS (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_doIpcTransfer _ _ _ _ _)

theorem ob_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : OBK OS (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_replyPush _ _ _ _)

theorem ob_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : OBK OS (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_orderedInsert _ _ _ _)

theorem ob_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : OBK OS (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_tcbAppend _ _)

theorem ob_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : OBK OS (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_tcbEpAppend _ _ _)

theorem ob_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : OBK OS (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_sendIpcBlocked _ _ _ _ _ _)

theorem ob_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : OBK OS (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_sendIpc _ _ _ _ _ _ _ _)

theorem ob_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : OBK OS (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_sendFaultIpc _ _ _ _)

theorem ob_handleTimeout (tptr : ObjRef) (ex : Fault) : OBK OS (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_handleTimeout _ _)

theorem ob_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : OBK OS (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_readyTimesAppend _ _)

theorem ob_tcbReleaseEnqueue (tcbPtr : ObjRef) : OBK OS (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_tcbReleaseEnqueue _)

theorem ob_postpone (scPtr : ObjRef) : OBK OS (postpone (Z := Unit) scPtr) := by
  unfold postpone; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_postpone _)

theorem ob_endTimeslice (canTimeout : Bool) : OBK OS (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_endTimeslice _)

theorem ob_getRefills (scPtr : ObjRef) : OBK OS (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getRefills _)

theorem ob_refillSize (scPtr : ObjRef) : OBK OS (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_refillSize _)

theorem ob_refillSingle (scPtr : ObjRef) : OBK OS (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_refillSingle _)

theorem ob_getRefillTail (scPtr : ObjRef) : OBK OS (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getRefillTail _)

theorem ob_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : OBK OS (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_refillAddTail _ _)

theorem ob_refillFull (scPtr : ObjRef) : OBK OS (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_refillFull _)

theorem ob_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : OBK OS (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_updateRefillTl _ _)

theorem ob_scheduleUsed (scPtr : ObjRef) (new : Refill) : OBK OS (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_scheduleUsed _ _)

theorem ob_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : OBK OS (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_chargeEntireHeadRefill _ _)

theorem ob_handleOverrun (scPtr : ObjRef) (usage : Ticks) : OBK OS (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_handleOverrun _ _)

theorem ob_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : OBK OS (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_mergeNonoverlappingHeadRefill _)

theorem ob_headInsufficientLoop (scPtr : ObjRef) : OBK OS (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_headInsufficientLoop _)

theorem ob_refillBudgetCheck (usage : Ticks) : OBK OS (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_refillBudgetCheck _)

theorem ob_refillResetRr (cscPtr : ObjRef) : OBK OS (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_refillResetRr _)

theorem ob_chargeBudget (consumed : Ticks) (canTimeout : Bool) : OBK OS (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_chargeBudget _ _)

theorem ob_checkBudget  : OBK OS (checkBudget (Z := Unit)) := by
  unfold checkBudget; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_checkBudget)

theorem ob_checkBudgetRestart  : OBK OS (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_checkBudgetRestart)

theorem ob_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : OBK OS m) : OBK OS (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; ob_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible refine ob_checkCapAt _ _ _ ?_)

theorem ob_checkDomainTime  : OBK OS (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_checkDomainTime)

theorem ob_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : OBKE OS (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_checkHandlerEp _ _)

theorem ob_checkPrio (newPrio : Data) (authTcb : ObjRef) : OBKE OS (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_checkPrio _ _)

theorem ob_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : OBKE OS (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_checkValidIpcBuffer _ _)

theorem ob_nextDomain  : OBK OS (nextDomain (Z := Unit)) := by
  unfold nextDomain; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_nextDomain)

theorem ob_switchToThread (t : ObjRef) : OBK OS (switchToThread (Z := Unit) t) := by
  unfold switchToThread; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_switchToThread _)

theorem ob_guardedSwitchTo (thread : ObjRef) : OBK OS (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_guardedSwitchTo _)

theorem ob_switchToIdleThread  : OBK OS (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_switchToIdleThread)

theorem ob_chooseThread  : OBK OS (chooseThread (Z := Unit)) := by
  unfold chooseThread; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_chooseThread)

theorem ob_refillBudgetCheckRoundRobin (usage : Ticks) : OBK OS (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_refillBudgetCheckRoundRobin _)

theorem ob_commitTime  : OBK OS (commitTime (Z := Unit)) := by
  unfold commitTime; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_commitTime)

theorem ob_schedContextResume (scPtr : ObjRef) : OBK OS (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_schedContextResume _)

theorem ob_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : OBK OS (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_maybeDonateSc _ _)

theorem ob_completeSignal (ntfnptr tptr : ObjRef) : OBK OS (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_completeSignal _ _)

theorem ob_copyGlobalMappings (newPm : ObjRef) : OBK OS (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_copyGlobalMappings _)

theorem ob_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : OBK OS (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_createCap _ _ _ _ _)

theorem ob_dataToObjType (type : Data) : OBKE OS (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_dataToObjType _)

theorem ob_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : OBKE OS (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeBindNotification _ _)

theorem ob_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : OBKE OS (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_lookupPivotSlot _ _ _)

theorem ob_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : OBKE OS (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_lookupSourceSlot _ _ _)

theorem ob_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : OBKE OS (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeCnodeInvocation _ _ _ _)

theorem ob_slotCapLongRunningDelete (slot : CslotPtr) : OBK OS (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_slotCapLongRunningDelete _)

theorem ob_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : OBKE OS (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeCvSpace _ _ _ _)
end

end Fl4Proofs.P3.SInvDV
