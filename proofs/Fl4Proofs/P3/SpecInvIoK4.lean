/- sg1: idle-thread frame lemmas `IoK t` (ut7's SpecInvUtNK4 renamed; see SpecInvSgI1). -/
import Fl4Proofs.P3.SpecInvIoK3
open Classical

namespace Fl4Proofs.P3.SInvIo
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : IoPort → Bool}

theorem iok_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : IoK N (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; iok_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_getExtraCptrs _ _)

theorem iok_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : IoKE N (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_lookupSlotForThread _ _)

theorem iok_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : IoKE N (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_lookupCapAndSlot _ _)

theorem iok_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : IoKE N (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_lookupExtraCaps _ _ _)

theorem iok_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : IoKE N m) : IoK N (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; iok_auto
  all_goals first | exact h_m
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible refine iok_emptyOnFailure _ ?_)

theorem iok_loadCapTransfer (buffer : ObjRef) : IoK N (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_loadCapTransfer _)

theorem iok_lookupCap (thread : ObjRef) (ref : CapRef) : IoKE N (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_lookupCap _ _)

theorem iok_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : IoKE N m) : IoKE N (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; iok_auto
  all_goals first | exact h_m
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible refine iok_unifyFailure _ ?_)

theorem iok_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : IoK N (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_getReceiveSlots _ _)

theorem iok_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : IoKE N m) : IoK N (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; iok_auto
  all_goals first | exact h_m
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible refine iok_constOnFailure _ _ ?_)

theorem iok_deriveCap (slot : CslotPtr) (cap : Cap) : IoKE N (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_deriveCap _ _)

theorem iok_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : IoK N (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_setExtraBadge _ _ _)

theorem iok_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      IoK N (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; iok_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => iok_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | iok_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_transferCapsLoop _ _ _ _ _ _)

theorem iok_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : IoK N (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_transferCaps _ _ _ _ _)

theorem iok_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : IoK N (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_doNormalTransfer _ _ _ _ _ _ _)

theorem iok_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : IoK N (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_doIpcTransfer _ _ _ _ _)

theorem iok_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : IoK N (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_replyPush _ _ _ _)

theorem iok_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : IoK N (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_orderedInsert _ _ _ _)

theorem iok_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : IoK N (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_tcbAppend _ _)

theorem iok_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : IoK N (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_tcbEpAppend _ _ _)

theorem iok_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : IoK N (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_sendIpcBlocked _ _ _ _ _ _)

theorem iok_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : IoK N (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_sendIpc _ _ _ _ _ _ _ _)

theorem iok_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : IoK N (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_sendFaultIpc _ _ _ _)

theorem iok_handleTimeout (tptr : ObjRef) (ex : Fault) : IoK N (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_handleTimeout _ _)

theorem iok_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : IoK N (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_readyTimesAppend _ _)

theorem iok_tcbReleaseEnqueue (tcbPtr : ObjRef) : IoK N (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_tcbReleaseEnqueue _)

theorem iok_postpone (scPtr : ObjRef) : IoK N (postpone (Z := Unit) scPtr) := by
  unfold postpone; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_postpone _)

theorem iok_endTimeslice (canTimeout : Bool) : IoK N (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_endTimeslice _)

theorem iok_getRefills (scPtr : ObjRef) : IoK N (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_getRefills _)

theorem iok_refillSize (scPtr : ObjRef) : IoK N (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_refillSize _)

theorem iok_refillSingle (scPtr : ObjRef) : IoK N (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_refillSingle _)

theorem iok_getRefillTail (scPtr : ObjRef) : IoK N (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_getRefillTail _)

theorem iok_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : IoK N (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_refillAddTail _ _)

theorem iok_refillFull (scPtr : ObjRef) : IoK N (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_refillFull _)

theorem iok_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : IoK N (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_updateRefillTl _ _)

theorem iok_scheduleUsed (scPtr : ObjRef) (new : Refill) : IoK N (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_scheduleUsed _ _)

theorem iok_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : IoK N (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_chargeEntireHeadRefill _ _)

theorem iok_handleOverrun (scPtr : ObjRef) (usage : Ticks) : IoK N (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_handleOverrun _ _)

theorem iok_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : IoK N (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_mergeNonoverlappingHeadRefill _)

theorem iok_headInsufficientLoop (scPtr : ObjRef) : IoK N (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_headInsufficientLoop _)

theorem iok_refillBudgetCheck (usage : Ticks) : IoK N (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_refillBudgetCheck _)

theorem iok_refillResetRr (cscPtr : ObjRef) : IoK N (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_refillResetRr _)

theorem iok_chargeBudget (consumed : Ticks) (canTimeout : Bool) : IoK N (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_chargeBudget _ _)

theorem iok_checkBudget  : IoK N (checkBudget (Z := Unit)) := by
  unfold checkBudget; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_checkBudget)

theorem iok_checkBudgetRestart  : IoK N (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_checkBudgetRestart)

theorem iok_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : IoK N m) : IoK N (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; iok_auto
  all_goals first | exact h_m
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible refine iok_checkCapAt _ _ _ ?_)

theorem iok_checkDomainTime  : IoK N (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_checkDomainTime)

theorem iok_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : IoKE N (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_checkHandlerEp _ _)

theorem iok_checkPrio (newPrio : Data) (authTcb : ObjRef) : IoKE N (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_checkPrio _ _)

theorem iok_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : IoKE N (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_checkValidIpcBuffer _ _)

theorem iok_nextDomain  : IoK N (nextDomain (Z := Unit)) := by
  unfold nextDomain; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_nextDomain)

theorem iok_switchToThread (t : ObjRef) : IoK N (switchToThread (Z := Unit) t) := by
  unfold switchToThread; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_switchToThread _)

theorem iok_guardedSwitchTo (thread : ObjRef) : IoK N (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_guardedSwitchTo _)

theorem iok_switchToIdleThread  : IoK N (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_switchToIdleThread)

theorem iok_chooseThread  : IoK N (chooseThread (Z := Unit)) := by
  unfold chooseThread; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_chooseThread)

theorem iok_refillBudgetCheckRoundRobin (usage : Ticks) : IoK N (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_refillBudgetCheckRoundRobin _)

theorem iok_commitTime  : IoK N (commitTime (Z := Unit)) := by
  unfold commitTime; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_commitTime)

theorem iok_schedContextResume (scPtr : ObjRef) : IoK N (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_schedContextResume _)

theorem iok_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : IoK N (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_maybeDonateSc _ _)

theorem iok_completeSignal (ntfnptr tptr : ObjRef) : IoK N (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_completeSignal _ _)

theorem iok_copyGlobalMappings (newPm : ObjRef) : IoK N (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_copyGlobalMappings _)

theorem iok_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : IoK N (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_createCap _ _ _ _ _)

theorem iok_dataToObjType (type : Data) : IoKE N (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_dataToObjType _)

theorem iok_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : IoKE N (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeBindNotification _ _)

theorem iok_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : IoKE N (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_lookupPivotSlot _ _ _)

theorem iok_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : IoKE N (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_lookupSourceSlot _ _ _)

theorem iok_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : IoKE N (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeCnodeInvocation _ _ _ _)

theorem iok_slotCapLongRunningDelete (slot : CslotPtr) : IoK N (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_slotCapLongRunningDelete _)

theorem iok_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : IoKE N (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeCvSpace _ _ _ _)
end

end Fl4Proofs.P3.SInvIo
