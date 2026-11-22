/- g5g: the memory half `YK D F` of untyped_ranges_zero, part 4 (sg1's SpecInvSgI4 renamed; see SpecInvUtZK1). -/
import Fl4Proofs.P3.SpecInvUtZK3
open Classical

namespace Fl4Proofs.P3.SInvUZ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {PD : PgSet} {FS : Set Nat}


theorem yk_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : YK PD FS (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; yk_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getExtraCptrs _ _)

theorem yk_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : YKE PD FS (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_lookupSlotForThread _ _)

theorem yk_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : YKE PD FS (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_lookupCapAndSlot _ _)

theorem yk_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : YKE PD FS (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_lookupExtraCaps _ _ _)

theorem yk_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : YKE PD FS m) : YK PD FS (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; yk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible refine yk_emptyOnFailure _ ?_)

theorem yk_loadCapTransfer (buffer : ObjRef) : YK PD FS (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_loadCapTransfer _)

theorem yk_lookupCap (thread : ObjRef) (ref : CapRef) : YKE PD FS (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_lookupCap _ _)

theorem yk_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : YKE PD FS m) : YKE PD FS (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; yk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible refine yk_unifyFailure _ ?_)

theorem yk_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : YK PD FS (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getReceiveSlots _ _)

theorem yk_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : YKE PD FS m) : YK PD FS (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; yk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible refine yk_constOnFailure _ _ ?_)

theorem yk_deriveCap (slot : CslotPtr) (cap : Cap) : YKE PD FS (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_deriveCap _ _)

theorem yk_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : YK PD FS (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setExtraBadge _ _ _)

theorem yk_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      YK PD FS (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; yk_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => yk_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | yk_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_transferCapsLoop _ _ _ _ _ _)

theorem yk_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : YK PD FS (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_transferCaps _ _ _ _ _)

theorem yk_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : YK PD FS (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_doNormalTransfer _ _ _ _ _ _ _)

theorem yk_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : YK PD FS (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_doIpcTransfer _ _ _ _ _)

theorem yk_replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : YK PD FS (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_replyPush _ _ _ _)

theorem yk_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : YK PD FS (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_orderedInsert _ _ _ _)

theorem yk_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : YK PD FS (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_tcbAppend _ _)

theorem yk_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : YK PD FS (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_tcbEpAppend _ _ _)

theorem yk_sendIpcBlocked (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : YK PD FS (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_sendIpcBlocked _ _ _ _ _ _)

theorem yk_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : YK PD FS (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_sendIpc _ _ _ _ _ _ _ _)

theorem yk_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : YK PD FS (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_sendFaultIpc _ _ _ _)

theorem yk_handleTimeout (tptr : ObjRef) (ex : Fault) : YK PD FS (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_handleTimeout _ _)

theorem yk_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : YK PD FS (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_readyTimesAppend _ _)

theorem yk_tcbReleaseEnqueue (tcbPtr : ObjRef) : YK PD FS (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_tcbReleaseEnqueue _)

theorem yk_postpone (scPtr : ObjRef) : YK PD FS (postpone (Z := Unit) scPtr) := by
  unfold postpone; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_postpone _)

theorem yk_endTimeslice (canTimeout : Bool) : YK PD FS (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_endTimeslice _)

theorem yk_getRefills (scPtr : ObjRef) : YK PD FS (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getRefills _)

theorem yk_refillSize (scPtr : ObjRef) : YK PD FS (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_refillSize _)

theorem yk_refillSingle (scPtr : ObjRef) : YK PD FS (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_refillSingle _)

theorem yk_getRefillTail (scPtr : ObjRef) : YK PD FS (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getRefillTail _)

theorem yk_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : YK PD FS (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_refillAddTail _ _)

theorem yk_refillFull (scPtr : ObjRef) : YK PD FS (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_refillFull _)

theorem yk_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : YK PD FS (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_updateRefillTl _ _)

theorem yk_scheduleUsed (scPtr : ObjRef) (new : Refill) : YK PD FS (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_scheduleUsed _ _)

theorem yk_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : YK PD FS (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_chargeEntireHeadRefill _ _)

theorem yk_handleOverrun (scPtr : ObjRef) (usage : Ticks) : YK PD FS (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_handleOverrun _ _)

theorem yk_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : YK PD FS (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_mergeNonoverlappingHeadRefill _)

theorem yk_headInsufficientLoop (scPtr : ObjRef) : YK PD FS (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_headInsufficientLoop _)

theorem yk_refillBudgetCheck (usage : Ticks) : YK PD FS (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_refillBudgetCheck _)

theorem yk_refillResetRr (cscPtr : ObjRef) : YK PD FS (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_refillResetRr _)

theorem yk_chargeBudget (consumed : Ticks) (canTimeout : Bool) : YK PD FS (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_chargeBudget _ _)

theorem yk_checkBudget  : YK PD FS (checkBudget (Z := Unit)) := by
  unfold checkBudget; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_checkBudget)

theorem yk_checkBudgetRestart  : YK PD FS (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_checkBudgetRestart)

theorem yk_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : YK PD FS m) : YK PD FS (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; yk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible refine yk_checkCapAt _ _ _ ?_)

theorem yk_checkDomainTime  : YK PD FS (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_checkDomainTime)

theorem yk_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : YKE PD FS (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_checkHandlerEp _ _)

theorem yk_checkPrio (newPrio : Data) (authTcb : ObjRef) : YKE PD FS (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_checkPrio _ _)

theorem yk_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : YKE PD FS (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_checkValidIpcBuffer _ _)

theorem yk_nextDomain  : YK PD FS (nextDomain (Z := Unit)) := by
  unfold nextDomain; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_nextDomain)

theorem yk_switchToThread (t : ObjRef) : YK PD FS (switchToThread (Z := Unit) t) := by
  unfold switchToThread; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_switchToThread _)

theorem yk_guardedSwitchTo (thread : ObjRef) : YK PD FS (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_guardedSwitchTo _)

theorem yk_switchToIdleThread  : YK PD FS (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_switchToIdleThread)

theorem yk_chooseThread  : YK PD FS (chooseThread (Z := Unit)) := by
  unfold chooseThread; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_chooseThread)

theorem yk_refillBudgetCheckRoundRobin (usage : Ticks) : YK PD FS (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_refillBudgetCheckRoundRobin _)

theorem yk_commitTime  : YK PD FS (commitTime (Z := Unit)) := by
  unfold commitTime; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_commitTime)

theorem yk_schedContextResume (scPtr : ObjRef) : YK PD FS (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_schedContextResume _)

theorem yk_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : YK PD FS (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_maybeDonateSc _ _)

theorem yk_completeSignal (ntfnptr tptr : ObjRef) : YK PD FS (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_completeSignal _ _)

theorem yk_copyGlobalMappings (newPm : ObjRef) : YK PD FS (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_copyGlobalMappings _)

theorem yk_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : YK PD FS (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_createCap _ _ _ _ _)

theorem yk_dataToObjType (type : Data) : YKE PD FS (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_dataToObjType _)

theorem yk_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : YKE PD FS (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeBindNotification _ _)

theorem yk_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : YKE PD FS (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_lookupPivotSlot _ _ _)

theorem yk_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : YKE PD FS (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_lookupSourceSlot _ _ _)

theorem yk_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : YKE PD FS (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeCnodeInvocation _ _ _ _)

theorem yk_slotCapLongRunningDelete (slot : CslotPtr) : YK PD FS (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_slotCapLongRunningDelete _)

theorem yk_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : YKE PD FS (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeCvSpace _ _ _ _)
end

end Fl4Proofs.P3.SInvUZ
