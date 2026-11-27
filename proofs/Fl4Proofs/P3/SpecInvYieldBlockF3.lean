/- iolay gen 5: YieldBlock frame lemmas, part 3: SpecInvYieldScopeF3's generated lemmas (gen.py `ys` mode, skip list
proofs/scratch/invA/skipYS.txt) for the strengthened invariant, without the functions that reach a blocking writer
(proofs/scratch/invA/skipYB.txt; hand-proved in SpecInvYieldBlockH). -/
import Fl4Proofs.P3.SpecInvYieldBlockF2
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {L : List ObjRef}

theorem yb_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : YBK L (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_makeArchFaultMsg _ _)

theorem yb_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : YBK L (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_makeFaultMsg _ _)

theorem yb_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : YBK L (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_doFaultTransfer _ _ _ _)

theorem yb_loadWordOffs (ptr : ObjRef) (offs : Nat) : YBK L (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_loadWordOffs _ _)

theorem yb_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : YBK L (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_copyMrs _ _ _ _ _)

theorem yb_getMessageInfo (thread : ObjRef) : YBK L (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getMessageInfo _)

theorem yb_getExtraCptrs (b : Option ObjRef) (mi : MessageInfo) : YBK L (getExtraCptrs (Z := Unit) b mi) := by
  unfold getExtraCptrs
  split
  · exact ik_liftM _ (ik_mapM (fun _ => by unfold loadWordOffs; yb_auto) _)
  · exact ik_pure _
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getExtraCptrs _ _)

theorem yb_lookupSlotForThread (thread : ObjRef) (cref : CapRef) : YBKE L (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_lookupSlotForThread _ _)

theorem yb_lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : YBKE L (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_lookupCapAndSlot _ _)

theorem yb_lookupExtraCaps (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : YBKE L (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_lookupExtraCaps _ _ _)

theorem yb_emptyOnFailure {F α : Type} (m : NonDetE (State Unit) F (List α)) (h_m : YBKE L m) : YBK L (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; yb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible refine yb_emptyOnFailure _ ?_)

theorem yb_loadCapTransfer (buffer : ObjRef) : YBK L (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_loadCapTransfer _)

theorem yb_lookupCap (thread : ObjRef) (ref : CapRef) : YBKE L (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_lookupCap _ _)

theorem yb_unifyFailure {F α : Type} (m : NonDetE (State Unit) F α) (h_m : YBKE L m) : YBKE L (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; yb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible refine yb_unifyFailure _ ?_)

theorem yb_getReceiveSlots (a0 : ObjRef) (a1 : Option ObjRef) : YBK L (getReceiveSlots (Z := Unit) a0 a1) := by
  unfold getReceiveSlots; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getReceiveSlots _ _)

theorem yb_constOnFailure {F α : Type} (c : α) (m : NonDetE (State Unit) F α) (h_m : YBKE L m) : YBK L (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; yb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible refine yb_constOnFailure _ _ ?_)

theorem yb_deriveCap (slot : CslotPtr) (cap : Cap) : YBKE L (deriveCap (Z := Unit) slot cap) := by
  unfold deriveCap; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_deriveCap _ _)

theorem yb_setExtraBadge (buffer : ObjRef) (badge : Word) (n : Nat) : YBK L (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setExtraBadge _ _ _)

theorem yb_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (cs : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      YBK L (transferCapsLoop (Z := Unit) ep rb n cs sl mi)
  | n, [], sl, mi => by unfold transferCapsLoop; yb_auto
  | n, (c, s) :: cs, sl, mi => by
    have ih := fun sl' mi' => yb_transferCapsLoop ep rb (n + 1) cs sl' mi'
    unfold transferCapsLoop
    repeat' (first | exact ih _ _ | (exact ike_liftE (ih _ _)) | yb_leaf | ik_step0 | ik_unfold)
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_transferCapsLoop _ _ _ _ _ _)

theorem yb_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : YBK L (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_transferCaps _ _ _ _ _)

theorem yb_doNormalTransfer (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : YBK L (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_doNormalTransfer _ _ _ _ _ _ _)

theorem yb_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : YBK L (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_doIpcTransfer _ _ _ _ _)

theorem yb_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β) (R : β → β → Prop) : YBK L (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_orderedInsert _ _ _ _)

theorem yb_tcbAppend (tptr : ObjRef) (qs : List ObjRef) : YBK L (tcbAppend (Z := Unit) tptr qs) := by
  unfold tcbAppend; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_tcbAppend _ _)

theorem yb_tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : YBK L (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_tcbEpAppend _ _ _)

theorem yb_readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : YBK L (readyTimesAppend (Z := Unit) tptr qs) := by
  unfold readyTimesAppend; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_readyTimesAppend _ _)

theorem yb_tcbReleaseEnqueue (tcbPtr : ObjRef) : YBK L (tcbReleaseEnqueue (Z := Unit) tcbPtr) := by
  unfold tcbReleaseEnqueue; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_tcbReleaseEnqueue _)

theorem yb_postpone (scPtr : ObjRef) : YBK L (postpone (Z := Unit) scPtr) := by
  unfold postpone; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_postpone _)

theorem yb_getRefills (scPtr : ObjRef) : YBK L (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getRefills _)

theorem yb_refillSize (scPtr : ObjRef) : YBK L (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_refillSize _)

theorem yb_refillSingle (scPtr : ObjRef) : YBK L (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_refillSingle _)

theorem yb_getRefillTail (scPtr : ObjRef) : YBK L (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getRefillTail _)

theorem yb_refillAddTail (scPtr : ObjRef) (newRefill : Refill) : YBK L (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_refillAddTail _ _)

theorem yb_refillFull (scPtr : ObjRef) : YBK L (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_refillFull _)

theorem yb_updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : YBK L (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_updateRefillTl _ _)

theorem yb_scheduleUsed (scPtr : ObjRef) (new : Refill) : YBK L (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_scheduleUsed _ _)

theorem yb_chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : YBK L (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_chargeEntireHeadRefill _ _)

theorem yb_handleOverrun (scPtr : ObjRef) (usage : Ticks) : YBK L (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_handleOverrun _ _)

theorem yb_mergeNonoverlappingHeadRefill (scPtr : ObjRef) : YBK L (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_mergeNonoverlappingHeadRefill _)

theorem yb_headInsufficientLoop (scPtr : ObjRef) : YBK L (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_headInsufficientLoop _)

theorem yb_refillBudgetCheck (usage : Ticks) : YBK L (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_refillBudgetCheck _)

theorem yb_refillResetRr (cscPtr : ObjRef) : YBK L (refillResetRr (Z := Unit) cscPtr) := by
  unfold refillResetRr; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_refillResetRr _)

theorem yb_checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Unit Unit) (h_m : YBK L m) : YBK L (checkCapAt (Z := Unit) cap slot m) := by
  unfold checkCapAt; yb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible refine yb_checkCapAt _ _ _ ?_)

theorem yb_checkDomainTime  : YBK L (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_checkDomainTime)

theorem yb_checkHandlerEp (pos : Nat) (hCapHSlot : Cap × CslotPtr) : YBKE L (checkHandlerEp (Z := Unit) pos hCapHSlot) := by
  unfold checkHandlerEp; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_checkHandlerEp _ _)

theorem yb_checkPrio (newPrio : Data) (authTcb : ObjRef) : YBKE L (checkPrio (Z := Unit) newPrio authTcb) := by
  unfold checkPrio; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_checkPrio _ _)

theorem yb_checkValidIpcBuffer (vptr : VSpaceRef) (c : Cap) : YBKE L (checkValidIpcBuffer (Z := Unit) vptr c) := by
  unfold checkValidIpcBuffer; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_checkValidIpcBuffer _ _)

theorem yb_nextDomain  : YBK L (nextDomain (Z := Unit)) := by
  unfold nextDomain; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_nextDomain)

theorem yb_switchToThread (t : ObjRef) : YBK L (switchToThread (Z := Unit) t) := by
  unfold switchToThread; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_switchToThread _)

theorem yb_guardedSwitchTo (thread : ObjRef) : YBK L (guardedSwitchTo (Z := Unit) thread) := by
  unfold guardedSwitchTo; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_guardedSwitchTo _)

theorem yb_switchToIdleThread  : YBK L (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_switchToIdleThread)

theorem yb_chooseThread  : YBK L (chooseThread (Z := Unit)) := by
  unfold chooseThread; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_chooseThread)

theorem yb_refillBudgetCheckRoundRobin (usage : Ticks) : YBK L (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_refillBudgetCheckRoundRobin _)

theorem yb_commitTime  : YBK L (commitTime (Z := Unit)) := by
  unfold commitTime; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_commitTime)

theorem yb_schedContextResume (scPtr : ObjRef) : YBK L (schedContextResume (Z := Unit) scPtr) := by
  unfold schedContextResume; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_schedContextResume _)

theorem yb_maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : YBK L (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_maybeDonateSc _ _)

theorem yb_completeSignal (ntfnptr tptr : ObjRef) : YBK L (completeSignal (Z := Unit) ntfnptr tptr) := by
  unfold completeSignal; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_completeSignal _ _)

theorem yb_copyGlobalMappings (newPm : ObjRef) : YBK L (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_copyGlobalMappings _)

theorem yb_createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) (a0 : CslotPtr × ObjRef) : YBK L (createCap (Z := Unit) type bits untyped isDevice a0) := by
  unfold createCap; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_createCap _ _ _ _ _)

theorem yb_dataToObjType (type : Data) : YBKE L (dataToObjType (Z := Unit) type) := by
  unfold dataToObjType; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_dataToObjType _)

theorem yb_decodeBindNotification (cap : Cap) (extraCaps : List (Cap × CslotPtr)) : YBKE L (decodeBindNotification (Z := Unit) cap extraCaps) := by
  unfold decodeBindNotification; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeBindNotification _ _)

theorem yb_lookupPivotSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : YBKE L (lookupPivotSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupPivotSlot; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_lookupPivotSlot _ _ _)

theorem yb_lookupSourceSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : YBKE L (lookupSourceSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupSourceSlot; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_lookupSourceSlot _ _ _)

theorem yb_decodeCnodeInvocation (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) : YBKE L (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeCnodeInvocation _ _ _ _)

theorem yb_slotCapLongRunningDelete (slot : CslotPtr) : YBK L (slotCapLongRunningDelete (Z := Unit) slot) := by
  unfold slotCapLongRunningDelete; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_slotCapLongRunningDelete _)

theorem yb_decodeCvSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : YBKE L (decodeCvSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeCvSpace; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeCvSpace _ _ _ _)

theorem yb_subframeNode (nodeCap : Cap) (index depth : Data) : YBKE L (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_subframeNode _ _ _)

theorem yb_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : YBKE L (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeDeriveSubframe _ _ _ _)

theorem yb_decodeDomainScheduleConfigure (args : List Data) : YBKE L (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeDomainScheduleConfigure _)

theorem yb_decodeDomainScheduleSetStart (args : List Data) : YBKE L (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeDomainScheduleSetStart _)

theorem yb_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : YBKE L (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeDomainSet _ _)

theorem yb_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : YBKE L (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeDomainInvocation _ _ _)

theorem yb_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : YBK L (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_fl4GetMr _ _ _)

theorem yb_fl4Arg (buf : Option ObjRef) (i : Nat) : YBKE L (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_fl4Arg _ _)

theorem yb_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : YBKE L (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeFl4ConfigureSingleStepping _ _)

theorem yb_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : YBKE L (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeFl4FpuTransfer _ _ _ _)

theorem yb_fl4CheckBpNum (bp : Data) : YBKE L (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_fl4CheckBpNum _)

theorem yb_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : YBKE L (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeFl4GetBreakpoint _ _)

theorem yb_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, YBKE L (check x0)) : YBKE L (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; yb_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible refine yb_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem yb_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : YBKE L (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeIrqControlRemapped _ _ _)

theorem yb_fl4ArchCheckIrq (irq : Data) : YBKE L (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_fl4ArchCheckIrq _)

theorem yb_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : YBKE L (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeFl4IrqControl _ _ _ _ _)

theorem yb_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : YBKE L (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeFl4SetBreakpoint _ _)

theorem yb_decodeFl4SetFlags (args : List Data) (t : ObjRef) : YBKE L (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeFl4SetFlags _ _)

theorem yb_decodeFl4SetTimer (args : List Data) (t : ObjRef) : YBKE L (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeFl4SetTimer _ _)

theorem yb_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : YBKE L (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeFl4UnsetBreakpoint _ _)

theorem yb_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : YBKE L (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeFl4TcbExt _ _ _ _ _)

theorem yb_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : YBKE L (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeIrqControlInvocation _ _ _ _)

theorem yb_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : YBKE L (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeIrqHandlerInvocation _ _ _)

theorem yb_getScReleased (scPtr : ObjRef) : YBK L (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getScReleased _)

theorem yb_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : YBKE L (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeSchedContextBind _ _)
end

end Fl4Proofs.P3.SInv
