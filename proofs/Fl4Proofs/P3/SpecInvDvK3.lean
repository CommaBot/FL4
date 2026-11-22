/- s26: the object half `OBK O` of device `valid_untyped`, part 3 (SpecInvUtZK3 renamed; see SpecInvDvK1). -/
import Fl4Proofs.P3.SpecInvDvK2
open Classical

namespace Fl4Proofs.P3.SInvDV
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {OS : ObSet}



theorem ob_tcbEpDequeue (tptr epPtr : ObjRef) : OBK OS (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_tcbEpDequeue _ _)

theorem ob_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : OBK OS (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_blockedCancelIpc _ _ _)

theorem ob_isRoundRobin (scPtr : ObjRef) : OBK OS (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_isRoundRobin _)

theorem ob_getRefillHead (scPtr : ObjRef) : OBK OS (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getRefillHead _)

theorem ob_refillPopHead (scPtr : ObjRef) : OBK OS (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_refillPopHead _)

theorem ob_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : OBK OS (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_updateRefillHd _ _)

theorem ob_mergeOverlappingRefills (scPtr : ObjRef) : OBK OS (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_mergeOverlappingRefills _)

theorem ob_refillHeadOverlappingLoop (scPtr : ObjRef) : OBK OS (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_refillHeadOverlappingLoop _)

theorem ob_refillUnblockCheck (scPtr : ObjRef) : OBK OS (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_refillUnblockCheck _)

theorem ob_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : OBK OS (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_ifCondRefillUnblockCheck _ _ _)

theorem ob_restartThreadIfNoFault (t : ObjRef) : OBK OS (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_restartThreadIfNoFault _)

theorem ob_removeAndRestartEpQueuedThread (t epptr : ObjRef) : OBK OS (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_removeAndRestartEpQueuedThread _ _)

theorem ob_cancelAllIpc (epptr : ObjRef) : OBK OS (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_cancelAllIpc _)

theorem ob_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : OBK OS (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_tcbNtfnDequeue _ _)

theorem ob_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : OBK OS (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_removeAndRestartNtfnQueuedThread _ _)

theorem ob_cancelAllSignals (ntfnptr : ObjRef) : OBK OS (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_cancelAllSignals _)

theorem ob_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : OBK OS (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_removeAndRestartBadgedThread _ _ _)

theorem ob_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : OBK OS (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_cancelBadgedSends _ _)

theorem ob_cancelSignal (threadptr ntfnptr : ObjRef) : OBK OS (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_cancelSignal _ _)

theorem ob_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : OBK OS (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getSkObjRef _ _ _)

theorem ob_replyRemoveTcb (tptr rptr : ObjRef) : OBK OS (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_replyRemoveTcb _ _)

theorem ob_cancelIpc (tptr : ObjRef) : OBK OS (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_cancelIpc _)

theorem ob_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : OBK OS (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_capSwap _ _ _ _)

theorem ob_capSwapForDelete (slot1 slot2 : CslotPtr) : OBK OS (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_capSwapForDelete _ _)

theorem ob_deletedIrqHandler (irq : Irq) : OBK OS (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_deletedIrqHandler _)

theorem ob_postCapDeletion (cap : Cap) : OBK OS (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_postCapDeletion _)

theorem ob_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : OBK OS (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_emptySlot _ _)

theorem ob_replyUnlinkSc (scPtr replyPtr : ObjRef) : OBK OS (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_replyUnlinkSc _ _)

theorem ob_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : OBK OS (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getScObjRef _ _)

theorem ob_testReschedule (fromTptr : ObjRef) : OBK OS (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_testReschedule _)

theorem ob_schedContextDonate (scPtr tcbPtr : ObjRef) : OBK OS (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_schedContextDonate _ _)

theorem ob_replyRemove (caller r : ObjRef) : OBK OS (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_replyRemove _ _)

theorem ob_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : OBK OS (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_schedContextMaybeUnbindNtfn _)

theorem ob_unbindMaybeNotification (ntfnptr : ObjRef) : OBK OS (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_unbindMaybeNotification _)

theorem ob_fastFinalise (a0 : Cap) (a1 : Bool) : OBK OS (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_fastFinalise _ _)

theorem ob_capDeleteOne (slot : CslotPtr) : OBK OS (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_capDeleteOne _)

theorem ob_getIrqSlot (irq : Irq) : OBK OS (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getIrqSlot _)

theorem ob_deletingIrqHandler (irq : Irq) : OBK OS (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_deletingIrqHandler _)

theorem ob_prepareThreadDelete (threadPtr : ObjRef) : OBK OS (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_prepareThreadDelete _)

theorem ob_schedContextSetInactive (scPtr : ObjRef) : OBK OS (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_schedContextSetInactive _)

theorem ob_schedContextUnbindTcb (scPtr : ObjRef) : OBK OS (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_schedContextUnbindTcb _)

theorem ob_schedContextUnbindAllTcbs (scPtr : ObjRef) : OBK OS (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_schedContextUnbindAllTcbs _)

theorem ob_schedContextUnbindNtfn (scPtr : ObjRef) : OBK OS (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_schedContextUnbindNtfn _)

theorem ob_schedContextUnbindReply (scPtr : ObjRef) : OBK OS (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_schedContextUnbindReply _)

theorem ob_schedContextUnbindYieldFrom (scPtr : ObjRef) : OBK OS (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_schedContextUnbindYieldFrom _)

theorem ob_updateRestartPc (threadPtr : ObjRef) : OBK OS (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_updateRestartPc _)

theorem ob_suspend (thread : ObjRef) : OBK OS (suspend (Z := Unit) thread) := by
  unfold suspend; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_suspend _)

theorem ob_unbindFromSc (tcbPtr : ObjRef) : OBK OS (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_unbindFromSc _)

theorem ob_unbindNotification (tcb : ObjRef) : OBK OS (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_unbindNotification _)

theorem ob_finaliseCap (a0 : Cap) (a1 : Bool) : OBK OS (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_finaliseCap _ _)

theorem ob_getScActive (scPtr : ObjRef) : OBK OS (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getScActive _)

theorem ob_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : OBKE OS f) (h_g : OBKE OS g) : OBKE OS (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; ob_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible refine ob_orChoiceE _ _ _ ?_ ?_)

theorem ob_updateTimeStamp  : OBK OS (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_updateTimeStamp)

theorem ob_preemptionPoint  : OBKE OS (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_preemptionPoint)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem ob_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, OBK OS (f k)) (k : RecDelCall) : OBKE OS (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, OBKE OS (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; ob_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; ob_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> ob_auto
    all_goals exact hrec' _

theorem ob_recDel (c : RecDelCall) : OBKE OS (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => ob_recDelF hf k) c
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_recDel _)

theorem ob_capDelete (slot : CslotPtr) : OBKE OS (capDelete (Z := Unit) slot) := by
  unfold capDelete; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_capDelete _)

theorem ob_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : OBKE OS m) : OBKE OS (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; ob_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible refine ob_capFaultOnFailure _ _ _ ?_)

theorem ob_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : OBK OS (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_capMove _ _ _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem ob_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, OBK OS (f k)) (sl : CslotPtr) : OBKE OS (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, OBKE OS (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  ob_auto
  all_goals exact hrec' _

theorem ob_capRevoke (sl : CslotPtr) : OBKE OS (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => ob_capRevokeF hf k) sl
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_capRevoke _)

theorem ob_captransferFromWords (ptr : Word) : OBK OS (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_captransferFromWords _)

theorem ob_isValidTimeoutHandler (tptr : ObjRef) : OBK OS (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_isValidTimeoutHandler _)

theorem ob_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : OBK OS (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_makeArchFaultMsg _ _)

theorem ob_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : OBK OS (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_makeFaultMsg _ _)

theorem ob_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : OBK OS (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_doFaultTransfer _ _ _ _)

theorem ob_loadWordOffs (ptr : ObjRef) (offs : Nat) : OBK OS (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_loadWordOffs _ _)

theorem ob_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : OBK OS (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_copyMrs _ _ _ _ _)

theorem ob_getMessageInfo (thread : ObjRef) : OBK OS (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getMessageInfo _)
end

end Fl4Proofs.P3.SInvDV
