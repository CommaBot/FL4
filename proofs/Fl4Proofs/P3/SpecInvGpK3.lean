/- s27: global-PML4 frame lemmas `GpK g` (sg1's SpecInvSgI3 renamed; see SpecInvGpK1). -/
import Fl4Proofs.P3.SpecInvGpK2
open Classical

namespace Fl4Proofs.P3.SInvGp
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem gpk_tcbEpDequeue (tptr epPtr : ObjRef) : GpK N (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_tcbEpDequeue _ _)

theorem gpk_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : GpK N (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_blockedCancelIpc _ _ _)

theorem gpk_isRoundRobin (scPtr : ObjRef) : GpK N (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_isRoundRobin _)

theorem gpk_getRefillHead (scPtr : ObjRef) : GpK N (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getRefillHead _)

theorem gpk_refillPopHead (scPtr : ObjRef) : GpK N (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_refillPopHead _)

theorem gpk_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : GpK N (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_updateRefillHd _ _)

theorem gpk_mergeOverlappingRefills (scPtr : ObjRef) : GpK N (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_mergeOverlappingRefills _)

theorem gpk_refillHeadOverlappingLoop (scPtr : ObjRef) : GpK N (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_refillHeadOverlappingLoop _)

theorem gpk_refillUnblockCheck (scPtr : ObjRef) : GpK N (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_refillUnblockCheck _)

theorem gpk_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : GpK N (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_ifCondRefillUnblockCheck _ _ _)

theorem gpk_restartThreadIfNoFault (t : ObjRef) : GpK N (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_restartThreadIfNoFault _)

theorem gpk_removeAndRestartEpQueuedThread (t epptr : ObjRef) : GpK N (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_removeAndRestartEpQueuedThread _ _)

theorem gpk_cancelAllIpc (epptr : ObjRef) : GpK N (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_cancelAllIpc _)

theorem gpk_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : GpK N (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_tcbNtfnDequeue _ _)

theorem gpk_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : GpK N (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_removeAndRestartNtfnQueuedThread _ _)

theorem gpk_cancelAllSignals (ntfnptr : ObjRef) : GpK N (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_cancelAllSignals _)

theorem gpk_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : GpK N (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_removeAndRestartBadgedThread _ _ _)

theorem gpk_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : GpK N (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_cancelBadgedSends _ _)

theorem gpk_cancelSignal (threadptr ntfnptr : ObjRef) : GpK N (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_cancelSignal _ _)

theorem gpk_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : GpK N (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getSkObjRef _ _ _)

theorem gpk_replyRemoveTcb (tptr rptr : ObjRef) : GpK N (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_replyRemoveTcb _ _)

theorem gpk_cancelIpc (tptr : ObjRef) : GpK N (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_cancelIpc _)

theorem gpk_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : GpK N (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_capSwap _ _ _ _)

theorem gpk_capSwapForDelete (slot1 slot2 : CslotPtr) : GpK N (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_capSwapForDelete _ _)

theorem gpk_deletedIrqHandler (irq : Irq) : GpK N (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_deletedIrqHandler _)

theorem gpk_postCapDeletion (cap : Cap) : GpK N (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_postCapDeletion _)

theorem gpk_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : GpK N (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_emptySlot _ _)

theorem gpk_replyUnlinkSc (scPtr replyPtr : ObjRef) : GpK N (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_replyUnlinkSc _ _)

theorem gpk_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : GpK N (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getScObjRef _ _)

theorem gpk_testReschedule (fromTptr : ObjRef) : GpK N (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_testReschedule _)

theorem gpk_schedContextDonate (scPtr tcbPtr : ObjRef) : GpK N (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_schedContextDonate _ _)

theorem gpk_replyRemove (caller r : ObjRef) : GpK N (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_replyRemove _ _)

theorem gpk_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : GpK N (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_schedContextMaybeUnbindNtfn _)

theorem gpk_unbindMaybeNotification (ntfnptr : ObjRef) : GpK N (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_unbindMaybeNotification _)

theorem gpk_fastFinalise (a0 : Cap) (a1 : Bool) : GpK N (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fastFinalise _ _)

theorem gpk_capDeleteOne (slot : CslotPtr) : GpK N (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_capDeleteOne _)

theorem gpk_getIrqSlot (irq : Irq) : GpK N (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getIrqSlot _)

theorem gpk_deletingIrqHandler (irq : Irq) : GpK N (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_deletingIrqHandler _)

theorem gpk_prepareThreadDelete (threadPtr : ObjRef) : GpK N (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_prepareThreadDelete _)

theorem gpk_schedContextSetInactive (scPtr : ObjRef) : GpK N (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_schedContextSetInactive _)

theorem gpk_schedContextUnbindTcb (scPtr : ObjRef) : GpK N (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_schedContextUnbindTcb _)

theorem gpk_schedContextUnbindAllTcbs (scPtr : ObjRef) : GpK N (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_schedContextUnbindAllTcbs _)

theorem gpk_schedContextUnbindNtfn (scPtr : ObjRef) : GpK N (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_schedContextUnbindNtfn _)

theorem gpk_schedContextUnbindReply (scPtr : ObjRef) : GpK N (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_schedContextUnbindReply _)

theorem gpk_schedContextUnbindYieldFrom (scPtr : ObjRef) : GpK N (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_schedContextUnbindYieldFrom _)

theorem gpk_updateRestartPc (threadPtr : ObjRef) : GpK N (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_updateRestartPc _)

theorem gpk_suspend (thread : ObjRef) : GpK N (suspend (Z := Unit) thread) := by
  unfold suspend; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_suspend _)

theorem gpk_unbindFromSc (tcbPtr : ObjRef) : GpK N (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_unbindFromSc _)

theorem gpk_unbindNotification (tcb : ObjRef) : GpK N (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_unbindNotification _)

theorem gpk_finaliseCap (a0 : Cap) (a1 : Bool) : GpK N (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_finaliseCap _ _)

theorem gpk_getScActive (scPtr : ObjRef) : GpK N (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getScActive _)

theorem gpk_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : GpKE N f) (h_g : GpKE N g) : GpKE N (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; gpk_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible refine gpk_orChoiceE _ _ _ ?_ ?_)

theorem gpk_updateTimeStamp  : GpK N (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_updateTimeStamp)

theorem gpk_preemptionPoint  : GpKE N (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_preemptionPoint)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem gpk_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, GpK N (f k)) (k : RecDelCall) : GpKE N (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, GpKE N (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; gpk_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; gpk_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> gpk_auto
    all_goals exact hrec' _

theorem gpk_recDel (c : RecDelCall) : GpKE N (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => gpk_recDelF hf k) c
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_recDel _)

theorem gpk_capDelete (slot : CslotPtr) : GpKE N (capDelete (Z := Unit) slot) := by
  unfold capDelete; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_capDelete _)

theorem gpk_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : GpKE N m) : GpKE N (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; gpk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible refine gpk_capFaultOnFailure _ _ _ ?_)

theorem gpk_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : GpK N (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_capMove _ _ _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem gpk_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, GpK N (f k)) (sl : CslotPtr) : GpKE N (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, GpKE N (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  gpk_auto
  all_goals exact hrec' _

theorem gpk_capRevoke (sl : CslotPtr) : GpKE N (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => gpk_capRevokeF hf k) sl
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_capRevoke _)

theorem gpk_captransferFromWords (ptr : Word) : GpK N (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_captransferFromWords _)

theorem gpk_isValidTimeoutHandler (tptr : ObjRef) : GpK N (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_isValidTimeoutHandler _)

theorem gpk_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : GpK N (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_makeArchFaultMsg _ _)

theorem gpk_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : GpK N (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_makeFaultMsg _ _)

theorem gpk_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : GpK N (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_doFaultTransfer _ _ _ _)

theorem gpk_loadWordOffs (ptr : ObjRef) (offs : Nat) : GpK N (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_loadWordOffs _ _)

theorem gpk_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : GpK N (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_copyMrs _ _ _ _ _)

theorem gpk_getMessageInfo (thread : ObjRef) : GpK N (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getMessageInfo _)
end

end Fl4Proofs.P3.SInvGp
