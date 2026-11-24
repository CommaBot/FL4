/-
P3 (DESIGN.md §9): **every cap's domain-schedule frame** (`DomFrame`) but the
Domain cap's.

* `dke_fl4Perform`: every invocation but `invokeDomain` keeps
  `domain_list` and `domain_start_index` (`DK`, VsDom; deletions by
  DomRecDel).
* `okAll_decode_notDom`: a cap other than the Domain cap decodes to no
  `invokeDomain`; `dk_spec_notDom`, the spec half of `DomFrame` for every
  such cap.
* `domFrame_of`: `DomFrame` for every cap but the Domain cap, from FL4's
  half (`DecDomHyp`, the cap's branch of `decode_invocation` keeping the
  kernel-global base and the five domain-schedule words).
-/
import Fl4Proofs.P3.CnodeDom
import Fl4Proofs.P3.DomFb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open Fl4Spec Classical

noncomputable section

/-! ## `perform_invocation` -/

/-- The invocations other than the Domain cap's. -/
def NotDomInv (i : Fl4Invocation) : Prop := ∀ d, i ≠ .invokeDomain d

/-! ### Leaves -/

theorem dke_withoutPreemption' {α : Type} {m : SMonad Unit α} (h : DK m) :
    DKE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; exact dke_liftE h
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible refine dke_withoutPreemption' ?_)

macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_invokeTcb _)
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_invokeFl4Tcb _)
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_invokeCnode _)

/-! ### The spec functions -/

theorem dk_lookupSlotForThread' (thread : ObjRef) (cref : CapRef) : DKE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_lookupSlotForThread' _ _)

theorem dk_lookupCapAndSlot' (thread : ObjRef) (cptr : CapRef) : DKE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_lookupCapAndSlot' _ _)

theorem dk_lookupCap' (thread : ObjRef) (ref : CapRef) : DKE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_lookupCap' _ _)

theorem dk_captransferFromWords' (ptr : Word) : DK (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_captransferFromWords' _)

theorem dk_loadCapTransfer' (buffer : ObjRef) : DK (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_loadCapTransfer' _)

theorem dk_setExtraBadge' (buffer : ObjRef) (badge : Word) (n : Nat) : DK (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setExtraBadge' _ _ _)

theorem dk_archPostResetUntyped' (_isDevice : Bool) (_sz : Nat) : DK (archPostResetUntyped (Z := Unit) _isDevice _sz) := by
  unfold archPostResetUntyped; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_archPostResetUntyped' _ _)

theorem dk_resetUntypedCap' (srcSlot : CslotPtr) : DKE (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_resetUntypedCap' _)

theorem dk_retypeRegionWith' (bitsApi : ApiObjectType → Nat → Nat) (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) : DK (retypeRegionWith (Z := Unit) bitsApi ptr numObjects oBits type dev) := by
  unfold retypeRegionWith; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_retypeRegionWith' _ _ _ _ _ _)

theorem dk_copyGlobalMappings' (newPm : ObjRef) : DK (copyGlobalMappings (Z := Unit) newPm) := by
  unfold copyGlobalMappings; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_copyGlobalMappings' _)

theorem dk_initArchObjects' (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : DK (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_initArchObjects' _ _ _ _ _ _)

theorem dk_createCap' (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool)
    (d : CslotPtr × ObjRef) : DK (createCap (Z := Unit) type bits untyped isDevice d) := by
  obtain ⟨dest, oref⟩ := d
  unfold createCap; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_createCap' _ _ _ _ _)

theorem dk_getRefillTail' (scPtr : ObjRef) : DK (getRefillTail (Z := Unit) scPtr) := by
  unfold getRefillTail; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getRefillTail' _)

theorem dk_getRefills' (scPtr : ObjRef) : DK (getRefills (Z := Unit) scPtr) := by
  unfold getRefills; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getRefills' _)

theorem dk_refillAddTail' (scPtr : ObjRef) (newRefill : Refill) : DK (refillAddTail (Z := Unit) scPtr newRefill) := by
  unfold refillAddTail; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_refillAddTail' _ _)

theorem dk_refillFull' (scPtr : ObjRef) : DK (refillFull (Z := Unit) scPtr) := by
  unfold refillFull; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_refillFull' _)

theorem dk_updateRefillTl' (scPtr : ObjRef) (f : Refill → Refill) : DK (updateRefillTl (Z := Unit) scPtr f) := by
  unfold updateRefillTl; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_updateRefillTl' _ _)

theorem dk_scheduleUsed' (scPtr : ObjRef) (new : Refill) : DK (scheduleUsed (Z := Unit) scPtr new) := by
  unfold scheduleUsed; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_scheduleUsed' _ _)

theorem dk_refillSize' (scPtr : ObjRef) : DK (refillSize (Z := Unit) scPtr) := by
  unfold refillSize; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_refillSize' _)

theorem dk_refillSingle' (scPtr : ObjRef) : DK (refillSingle (Z := Unit) scPtr) := by
  unfold refillSingle; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_refillSingle' _)

theorem dk_chargeEntireHeadRefill' (scPtr : ObjRef) (usage : Ticks) : DK (chargeEntireHeadRefill (Z := Unit) scPtr usage) := by
  unfold chargeEntireHeadRefill; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_chargeEntireHeadRefill' _ _)

theorem dk_mergeNonoverlappingHeadRefill' (scPtr : ObjRef) : DK (mergeNonoverlappingHeadRefill (Z := Unit) scPtr) := by
  unfold mergeNonoverlappingHeadRefill; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_mergeNonoverlappingHeadRefill' _)

theorem dk_updateIrqState' (irq : Irq) (irqState : X64IRQState) : DK (updateIrqState (Z := Unit) irq irqState) := by
  unfold updateIrqState; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_updateIrqState' _ _)

theorem dke_archInvokeIrqControl' (i : ArchIrqControlInvocation) : DKE (archInvokeIrqControl (Z := Unit) i) := by
  cases i <;> unfold archInvokeIrqControl <;> dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_archInvokeIrqControl' _)

theorem dk_invokeIrqControl' (i : IrqControlInvocation) : DKE (invokeIrqControl (Z := Unit) i) := by
  cases i <;> unfold invokeIrqControl <;> dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_invokeIrqControl' _)

theorem dke_invokeUntypedWith' (b : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) :
    DKE (invokeUntypedWith (Z := Unit) b ui) := by
  cases ui; unfold invokeUntypedWith; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_invokeUntypedWith' _ _)

theorem dke_fl4InvokeUntyped' (ui : UntypedInvocation) : DKE (fl4InvokeUntyped (Z := Unit) ui) :=
  dke_invokeUntypedWith' _ ui
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_fl4InvokeUntyped' _)

theorem dke_invokeFl4IrqControl' (i : Fl4IrqControlInvocation) : DKE (invokeFl4IrqControl (Z := Unit) i) := by
  cases i <;> unfold invokeFl4IrqControl <;> dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_invokeFl4IrqControl' _)

theorem dk_makeArchFaultMsg' (f : ArchFault) (t : ObjRef) : DK (makeArchFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeArchFaultMsg <;> dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_makeArchFaultMsg' _ _)

theorem dke_unifyFailure' {F α : Type} {m : NonDetE (State Unit) F α} (h : DKE m) :
    DKE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible refine dke_unifyFailure' ?_)

theorem dk_emptyOnFailure' {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : DKE m) :
    DK (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible refine dk_emptyOnFailure' ?_)

theorem dk_constOnFailure' {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : DKE m) :
    DK (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact dk_catch h fun _ => dk_pure' _
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible refine dk_constOnFailure' _ ?_)

theorem dke_capFaultOnFailure' {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : DKE m) :
    DKE (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact dke_handleE h fun _ => dke_throw _
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible refine dke_capFaultOnFailure' _ _ ?_)

theorem dk_loadWordOffs' (ptr : ObjRef) (offs : Nat) : DK (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; exact dk_doMachineOp _
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_loadWordOffs' _ _)

theorem dk_getExtraCptrs' (b : Option ObjRef) (mi : MessageInfo) : DK (getExtraCptrs (Z := Unit) b mi) := by
  cases b
  · unfold getExtraCptrs; exact dk_pure _
  · unfold getExtraCptrs; exact dk_liftM _ (dk_mapM (fun _ => dk_loadWordOffs' _ _) _)
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getExtraCptrs' _ _)

theorem dk_getReceiveSlots' (t : ObjRef) (b : Option ObjRef) : DK (getReceiveSlots (Z := Unit) t b) := by
  cases b <;> unfold getReceiveSlots <;> dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getReceiveSlots' _ _)

theorem dk_transferCapsLoop' (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (slots : List CslotPtr) (mi : MessageInfo),
      DK (transferCapsLoop (Z := Unit) ep rb n caps slots mi)
  | n, [], slots, mi => by unfold transferCapsLoop; dk_auto
  | n, (c, sl) :: rest, slots, mi => by
    have ih := dk_transferCapsLoop' ep rb (n + 1) rest
    unfold transferCapsLoop
    dk_auto
    all_goals first | exact ih _ _ | skip
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_transferCapsLoop' _ _ _ _ _ _)

theorem dk_lookupExtraCaps' (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : DKE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_lookupExtraCaps' _ _ _)

theorem dk_copyMrs' (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : DK (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_copyMrs' _ _ _ _ _)

theorem dk_transferCaps' (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : DK (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_transferCaps' _ _ _ _ _)

theorem dk_makeFaultMsg' (f : Fault) (t : ObjRef) : DK (makeFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeFaultMsg <;> dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_makeFaultMsg' _ _)

theorem dk_handleOverrun' (scPtr : ObjRef) (usage : Ticks) : DK (handleOverrun (Z := Unit) scPtr usage) := by
  unfold handleOverrun; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_handleOverrun' _ _)

theorem dk_headInsufficientLoop' (scPtr : ObjRef) : DK (headInsufficientLoop (Z := Unit) scPtr) := by
  unfold headInsufficientLoop; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_headInsufficientLoop' _)

theorem dk_getMessageInfo' (thread : ObjRef) : DK (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getMessageInfo' _)

theorem dk_tcbEpAppend' (tptr epPtr : ObjRef) (isRecv : Bool) : DK (tcbEpAppend (Z := Unit) tptr epPtr isRecv) := by
  unfold tcbEpAppend; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_tcbEpAppend' _ _ _)

theorem dk_doNormalTransfer' (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : DK (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_doNormalTransfer' _ _ _ _ _ _ _)

theorem dk_doFaultTransfer' (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : DK (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_doFaultTransfer' _ _ _ _)

theorem dk_bindScReply' (scPtr replyPtr : ObjRef) : DK (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_bindScReply' _ _)

theorem dk_isValidTimeoutHandler' (tptr : ObjRef) : DK (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_isValidTimeoutHandler' _)

theorem dk_doIpcTransfer' (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : DK (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_doIpcTransfer' _ _ _ _ _)

theorem dk_replyPush' (caller callee replyPtr : ObjRef) (canDonate : Bool) : DK (replyPush (Z := Unit) caller callee replyPtr canDonate) := by
  unfold replyPush; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_replyPush' _ _ _ _)

theorem dk_sendIpcBlocked' (thread epptr : ObjRef) (badge : Badge) (canGrant canGrantReply call : Bool) : DK (sendIpcBlocked (Z := Unit) thread epptr badge canGrant canGrantReply call) := by
  unfold sendIpcBlocked; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_sendIpcBlocked' _ _ _ _ _ _)

theorem dk_sendIpc' (b c : Bool) (bd : Badge) (g gr d : Bool) (t e : ObjRef) : DK (sendIpc (Z := Unit) b c bd g gr d t e) := by
  unfold sendIpc; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_sendIpc' _ _ _ _ _ _ _ _)

theorem dk_sendFaultIpc' (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : DK (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_sendFaultIpc' _ _ _ _)

theorem dk_refillBudgetCheckRoundRobin' (usage : Ticks) : DK (refillBudgetCheckRoundRobin (Z := Unit) usage) := by
  unfold refillBudgetCheckRoundRobin; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_refillBudgetCheckRoundRobin' _)

theorem dk_refillBudgetCheck' (usage : Ticks) : DK (refillBudgetCheck (Z := Unit) usage) := by
  unfold refillBudgetCheck; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_refillBudgetCheck' _)

theorem dk_maybeAddEmptyTail' (scPtr : ObjRef) : DK (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_maybeAddEmptyTail' _)

theorem dk_maybeDonateSc' (tcbPtr ntfnPtr : ObjRef) : DK (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_maybeDonateSc' _ _)

theorem dk_updateWaitingNtfn' (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : DK (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_updateWaitingNtfn' _ _ _)

theorem dk_handleTimeout' (tptr : ObjRef) (ex : Fault) : DK (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_handleTimeout' _ _)

theorem dk_getMrs' (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : DK (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getMrs' _ _ _)

theorem dk_handleFaultReply' (f : Fault) (t : ObjRef) (x : Data) (y : List Data) :
    DK (handleFaultReply (Z := Unit) f t x y) := by
  cases f <;> unfold handleFaultReply <;> dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_handleFaultReply' _ _ _ _)

theorem dk_returnConsumed' (scPtr : ObjRef) : DK (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_returnConsumed' _)

theorem dk_schedContextBindNtfn' (sc ntfn : ObjRef) : DK (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_schedContextBindNtfn' _ _)

theorem dk_schedContextYieldTo' (scPtr : ObjRef) : DK (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_schedContextYieldTo' _)

theorem dk_getScActive' (scPtr : ObjRef) : DK (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getScActive' _)

theorem dk_commitTime' : DK (commitTime (Z := Unit) ) := by
  unfold commitTime; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_commitTime' )

theorem dk_refillNew' (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : DK (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_refillNew' _ _ _ _)

theorem dk_refillUpdate' (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : DK (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_refillUpdate' _ _ _ _)

theorem dk_archInvokeIrqHandler' (i : IrqHandlerInvocation) : DK (archInvokeIrqHandler (Z := Unit) i) := by
  cases i <;> unfold archInvokeIrqHandler <;> dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_archInvokeIrqHandler' _)

theorem dk_sendSignal' (n : ObjRef) (b : Badge) : DK (sendSignal (Z := Unit) n b) := by
  unfold sendSignal; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_sendSignal' _ _)

theorem dk_doReplyTransfer' (s r : ObjRef) (g : Bool) : DK (doReplyTransfer (Z := Unit) s r g) := by
  unfold doReplyTransfer; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_doReplyTransfer' _ _ _)

theorem dk_invokeSchedContext' (i : SchedContextInvocation) : DK (invokeSchedContext (Z := Unit) i) := by
  cases i <;> unfold invokeSchedContext <;> dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_invokeSchedContext' _)

theorem dk_invokeSchedControlConfigureFlags' (i : SchedControlInvocation) : DK (invokeSchedControlConfigureFlags (Z := Unit) i) := by
  cases i <;> unfold invokeSchedControlConfigureFlags <;> dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_invokeSchedControlConfigureFlags' _)

theorem dk_invokeIrqHandler' (i : IrqHandlerInvocation) : DK (invokeIrqHandler (Z := Unit) i) := by
  cases i <;> unfold invokeIrqHandler <;> dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_invokeIrqHandler' _)

theorem dke_fl4Perform (blk call don : Bool) (inv : Fl4Invocation) (h : NotDomInv inv) :
    DKE (fl4PerformInvocation (Z := Unit) blk call don inv) := by
  cases inv
  case invokeDomain d => exact absurd rfl (h d)
  all_goals simp only [fl4PerformInvocation]
  all_goals dk_auto

/-! ## The decode -/

/-- **A cap other than the Domain cap decodes to no `invokeDomain`.** -/
theorem okAll_decode_notDom (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) (hc : cap ≠ .domainCap) :
    OkAll NotDomInv (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap excaps buffer) := by
  unfold fl4DecodeInvocation
  split
  all_goals first
    | (exfalso; exact hc rfl)
    | skip
  all_goals try unfold fl4DecodeTcbInvocation
  all_goals repeat' (first
    | exact okAll_throw
    | exact okAll_returnOk (fun _ h => by cases h)
    | exact okAll_liftME (okAll_true _) (fun _ _ _ h => by cases h)
    | (apply okAll_ite <;> intro _)
    | split)

theorem absCap_ne_domain {c : fl4_core.capability.Cap} (hc : c ≠ .Domain) : absCap c ≠ .domainCap := by
  cases c <;> simp [absCap] at hc ⊢

/-- **The spec half of `DomFrame` for every cap but the Domain cap.** -/
theorem dk_spec_notDom {fp : Bool} {slbl : Data} {args : List Data} {ci : CapRef} {sl : CslotPtr}
    {c : fl4_core.capability.Cap} (hc : c ≠ .Domain) {excaps : List (Cap × CslotPtr)} {buffer : Option ObjRef}
    {blk call don : Bool} {σ : State Unit} {tcb : Tcb} (hkt : σ.kheap σ.curThread = some (.tcb tcb)) :
    ∀ inv σ1, DecOut (specDec fp slbl args ci sl c excaps buffer) σ inv →
      setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1,
        y.2.domainList = σ.domainList ∧ y.2.domainStartIndex = σ.domainStartIndex := by
  intro inv σ1 hd he y hy
  have h1 := setThreadState_dom hkt he
  have hi := hd.okAll (okAll_decode_notDom fp slbl args ci sl (absCap c) excaps buffer (absCap_ne_domain hc))
  have h2 := Vs.DK.dom (dke_fl4Perform blk call don inv hi) hy
  exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

end

end Fl4Proofs.P3.Vs

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Spec

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **FL4's half of a cap's `DomFrame`**: the cap's branch of
`decode_invocation` keeps the kernel-global base and the five words of the
domain schedule. -/
def DecDomHyp (s : S) (ar : A) (lbl length slot : U64) (c : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) : Prop :=
  syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ res =>
    L.ksb res.2.1 = L.ksb s ∧ ∀ o ∈ domOffs, L.mem res.2.1 (ksW (L.ksb s) o) = L.mem s (ksW (L.ksb s) o) ⦄

/-- **Every cap but the Domain cap has its `DomFrame`**, from FL4's half
(`DecDomHyp`) and the spec's (`dk_spec_notDom`). -/
theorem domFrame_of (s : S) (ar : A) (σ : State Unit) (lbl length slot : U64) (c : capability.Cap)
    (hc : c ≠ .Domain) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    {tcb : Tcb} (hkt : σ.kheap σ.curThread = some (.tcb tcb)) (slbl : Data) (args : List Data) (ci : CapRef)
    (sl : CslotPtr) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef)
    (hF : DecDomHyp (L := L) arI s ar lbl length slot c blk call don fp buf extra) :
    DomFrame (L := L) arI s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer :=
  ⟨hF, Vs.dk_spec_notDom hc hkt⟩

/-- FL4's half for the Null cap: the decode only fails. -/
theorem decDomHyp_null (s : S) (ar : A) (lbl length slot : U64) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64) (hct : sched.cur_thread st s = ok ct) :
    DecDomHyp (L := L) arI s ar lbl length slot .Null blk call don fp buf extra := by
  unfold DecDomHyp syscall.decode_invocation
  rw [hct]; simp only [bind_ok, WP.spec_ok]
  simp

/-- FL4's half for a Zombie cap: the decode only fails. -/
theorem decDomHyp_zombie (s : S) (ar : A) (lbl length slot : U64) (p zt n : U64) (blk call don fp : Bool)
    (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64) (hct : sched.cur_thread st s = ok ct) :
    DecDomHyp (L := L) arI s ar lbl length slot (.Zombie p zt n) blk call don fp buf extra := by
  unfold DecDomHyp syscall.decode_invocation
  rw [hct]; simp only [bind_ok, WP.spec_ok]
  simp

/-- FL4's half for a Thread cap, from `TcbDomHyp` (TcbDom). -/
theorem decDomHyp_thread (s : S) (ar : A) (lbl length slot : U64) (p : U64) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hF : fp = false → TcbDomHyp (L := L) arI s ar lbl p ⟨length, buf, call, slot, extra⟩) :
    DecDomHyp (L := L) arI s ar lbl length slot (.Thread p) blk call don fp buf extra := by
  unfold DecDomHyp syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact hF rfl
  · simp only [↓reduceIte, WP.spec_ok]
    simp

/-- FL4's half for a CNode cap, from `CnodeDomHyp` (CnodeDom). -/
theorem decDomHyp_cnode (s : S) (ar : A) (lbl length slot : U64) (p r gs g : U64) (blk call don fp : Bool)
    (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hF : fp = false → CnodeDomHyp (L := L) arI s ar lbl length (.CNode p r gs g) buf extra) :
    DecDomHyp (L := L) arI s ar lbl length slot (.CNode p r gs g) blk call don fp buf extra := by
  unfold DecDomHyp syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact hF rfl
  · simp only [↓reduceIte, WP.spec_ok]
    simp

end

end

end Fl4Proofs.P3
