/- virt gen 4: the object-type family `TYK`, part 4 (SpecInvDvK4 with `aType` for `objBits`, proofs/scratch/virt/mkty2.py; see VirtTyK1). -/
import Fl4Proofs.P3.VirtTyK3
open Classical

namespace Fl4Proofs.P3.SInvTY
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {OS : TySet}



theorem ty_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : TYK OS (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; ty_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getExtraCptrs _ _)

theorem ty_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : TYKE OS (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_lookupSlotForThread _ _)

theorem ty_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : TYKE OS (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_lookupCapAndSlot _ _)

theorem ty_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : TYKE OS (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_lookupExtraCaps _ _ _)

theorem ty_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : TYKE OS m) : TYK OS (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; ty_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible refine ty_emptyOnFailure _ ?_)

theorem ty_loadCapTransfer (buffer : ObjRef) : TYK OS (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_loadCapTransfer _)

theorem ty_lookupCap (thread : ObjRef) (ref : CapRef) : TYKE OS (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_lookupCap _ _)

theorem ty_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : TYKE OS m) : TYKE OS (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; ty_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible refine ty_unifyFailure _ ?_)

theorem ty_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : TYK OS (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getReceiveSlots _ _)

theorem ty_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : TYKE OS m) : TYK OS (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; ty_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible refine ty_constOnFailure _ _ ?_)

theorem ty_deriveCap (slot : CslotPtr) (cap : Cap) : TYKE OS (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_deriveCap _ _)

theorem ty_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : TYK OS (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setExtraBadge _ _ _)

theorem ty_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      TYK OS (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; ty_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => ty_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | ty_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_transferCapsLoop _ _ _ _ _ _)

theorem ty_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : TYK OS (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_transferCaps _ _ _ _ _)

theorem ty_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : TYK OS (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_doNormalTransfer _ _ _ _ _ _ _)

theorem ty_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : TYK OS (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_doIpcTransfer _ _ _ _ _)

theorem ty_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : TYK OS (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_replyPush _ _ _ _)

theorem ty_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : TYK OS (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_orderedInsert _ _ _ _)

theorem ty_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : TYK OS (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_tcbAppend _ _)

theorem ty_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : TYK OS (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_tcbEpAppend _ _ _)

theorem ty_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : TYK OS (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_sendIpcBlocked _ _ _ _ _ _)

theorem ty_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : TYK OS (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_sendIpc _ _ _ _ _ _ _ _)

theorem ty_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : TYK OS (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_sendFaultIpc _ _ _ _)

theorem ty_handleTimeout (tptr : ObjRef) (ex : Fault) : TYK OS (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_handleTimeout _ _)

theorem ty_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : TYK OS (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_readyTimesAppend _ _)

theorem ty_tcbReleaseEnqueue (tcbPtr : ObjRef) : TYK OS (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_tcbReleaseEnqueue _)

theorem ty_postpone (scPtr : ObjRef) : TYK OS (postpone (Z := Unit) scPtr) := by
  unfold postpone; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_postpone _)

theorem ty_endTimeslice (canTimeout : Bool) : TYK OS (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_endTimeslice _)

theorem ty_getRefills (scPtr : ObjRef) : TYK OS (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getRefills _)

theorem ty_refillSize (scPtr : ObjRef) : TYK OS (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_refillSize _)

theorem ty_refillSingle (scPtr : ObjRef) : TYK OS (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_refillSingle _)

theorem ty_getRefillTail (scPtr : ObjRef) : TYK OS (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getRefillTail _)

theorem ty_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : TYK OS (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_refillAddTail _ _)

theorem ty_refillFull (scPtr : ObjRef) : TYK OS (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_refillFull _)

theorem ty_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : TYK OS (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_updateRefillTl _ _)

theorem ty_scheduleUsed (scPtr : ObjRef) (new : Refill) : TYK OS (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_scheduleUsed _ _)

theorem ty_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : TYK OS (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_chargeEntireHeadRefill _ _)

theorem ty_handleOverrun (scPtr : ObjRef) (usage : Ticks) : TYK OS (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_handleOverrun _ _)

theorem ty_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : TYK OS (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_mergeNonoverlappingHeadRefill _)

theorem ty_headInsufficientLoop (scPtr : ObjRef) : TYK OS (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_headInsufficientLoop _)

theorem ty_refillBudgetCheck (usage : Ticks) : TYK OS (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_refillBudgetCheck _)

theorem ty_refillResetRr (cscPtr : ObjRef) : TYK OS (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_refillResetRr _)

theorem ty_chargeBudget (consumed : Ticks) (canTimeout : Bool) : TYK OS (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_chargeBudget _ _)

theorem ty_checkBudget  : TYK OS (checkBudget (Z := Unit)) := by
  unfold checkBudget; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_checkBudget)

theorem ty_checkBudgetRestart  : TYK OS (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_checkBudgetRestart)

theorem ty_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : TYK OS m) : TYK OS (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; ty_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible refine ty_checkCapAt _ _ _ ?_)

theorem ty_checkDomainTime  : TYK OS (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_checkDomainTime)

theorem ty_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : TYKE OS (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_checkHandlerEp _ _)

theorem ty_checkPrio (newPrio : Data) (authTcb : ObjRef) : TYKE OS (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_checkPrio _ _)

theorem ty_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : TYKE OS (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_checkValidIpcBuffer _ _)

theorem ty_nextDomain  : TYK OS (nextDomain (Z := Unit)) := by
  unfold nextDomain; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_nextDomain)

theorem ty_switchToThread (t : ObjRef) : TYK OS (switchToThread (Z := Unit) t) := by
  unfold switchToThread; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_switchToThread _)

theorem ty_guardedSwitchTo (thread : ObjRef) : TYK OS (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_guardedSwitchTo _)

theorem ty_switchToIdleThread  : TYK OS (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_switchToIdleThread)

theorem ty_chooseThread  : TYK OS (chooseThread (Z := Unit)) := by
  unfold chooseThread; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_chooseThread)

theorem ty_refillBudgetCheckRoundRobin (usage : Ticks) : TYK OS (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_refillBudgetCheckRoundRobin _)

theorem ty_commitTime  : TYK OS (commitTime (Z := Unit)) := by
  unfold commitTime; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_commitTime)

theorem ty_schedContextResume (scPtr : ObjRef) : TYK OS (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_schedContextResume _)

theorem ty_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : TYK OS (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_maybeDonateSc _ _)

theorem ty_completeSignal (ntfnptr tptr : ObjRef) : TYK OS (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_completeSignal _ _)

theorem ty_copyGlobalMappings (newPm : ObjRef) : TYK OS (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_copyGlobalMappings _)

theorem ty_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : TYK OS (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_createCap _ _ _ _ _)

theorem ty_dataToObjType (type : Data) : TYKE OS (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_dataToObjType _)

theorem ty_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : TYKE OS (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeBindNotification _ _)

theorem ty_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : TYKE OS (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_lookupPivotSlot _ _ _)

theorem ty_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : TYKE OS (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_lookupSourceSlot _ _ _)

theorem ty_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : TYKE OS (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeCnodeInvocation _ _ _ _)

theorem ty_slotCapLongRunningDelete (slot : CslotPtr) : TYK OS (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_slotCapLongRunningDelete _)

theorem ty_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : TYKE OS (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeCvSpace _ _ _ _)
end

end Fl4Proofs.P3.SInvTY
