/- sg1: idle-thread frame lemmas `IoK t` (ut7's SpecInvUtNK3 renamed; see SpecInvSgI1). -/
import Fl4Proofs.P3.SpecInvIoK2
open Classical

namespace Fl4Proofs.P3.SInvIo
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : IoPort → Bool}

theorem iok_tcbEpDequeue (tptr epPtr : ObjRef) : IoK N (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_tcbEpDequeue _ _)

theorem iok_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : IoK N (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_blockedCancelIpc _ _ _)

theorem iok_isRoundRobin (scPtr : ObjRef) : IoK N (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_isRoundRobin _)

theorem iok_getRefillHead (scPtr : ObjRef) : IoK N (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_getRefillHead _)

theorem iok_refillPopHead (scPtr : ObjRef) : IoK N (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_refillPopHead _)

theorem iok_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : IoK N (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_updateRefillHd _ _)

theorem iok_mergeOverlappingRefills (scPtr : ObjRef) : IoK N (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_mergeOverlappingRefills _)

theorem iok_refillHeadOverlappingLoop (scPtr : ObjRef) : IoK N (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_refillHeadOverlappingLoop _)

theorem iok_refillUnblockCheck (scPtr : ObjRef) : IoK N (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_refillUnblockCheck _)

theorem iok_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : IoK N (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_ifCondRefillUnblockCheck _ _ _)

theorem iok_restartThreadIfNoFault (t : ObjRef) : IoK N (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_restartThreadIfNoFault _)

theorem iok_removeAndRestartEpQueuedThread (t epptr : ObjRef) : IoK N (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_removeAndRestartEpQueuedThread _ _)

theorem iok_cancelAllIpc (epptr : ObjRef) : IoK N (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_cancelAllIpc _)

theorem iok_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : IoK N (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_tcbNtfnDequeue _ _)

theorem iok_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : IoK N (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_removeAndRestartNtfnQueuedThread _ _)

theorem iok_cancelAllSignals (ntfnptr : ObjRef) : IoK N (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_cancelAllSignals _)

theorem iok_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : IoK N (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_removeAndRestartBadgedThread _ _ _)

theorem iok_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : IoK N (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_cancelBadgedSends _ _)

theorem iok_cancelSignal (threadptr ntfnptr : ObjRef) : IoK N (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_cancelSignal _ _)

theorem iok_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : IoK N (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_getSkObjRef _ _ _)

theorem iok_replyRemoveTcb (tptr rptr : ObjRef) : IoK N (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_replyRemoveTcb _ _)

theorem iok_cancelIpc (tptr : ObjRef) : IoK N (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_cancelIpc _)

theorem iok_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : IoK N (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_capSwap _ _ _ _)

theorem iok_capSwapForDelete (slot1 slot2 : CslotPtr) : IoK N (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_capSwapForDelete _ _)

theorem iok_deletedIrqHandler (irq : Irq) : IoK N (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_deletedIrqHandler _)

theorem iok_replyUnlinkSc (scPtr replyPtr : ObjRef) : IoK N (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_replyUnlinkSc _ _)

theorem iok_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : IoK N (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_getScObjRef _ _)

theorem iok_testReschedule (fromTptr : ObjRef) : IoK N (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_testReschedule _)

theorem iok_schedContextDonate (scPtr tcbPtr : ObjRef) : IoK N (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_schedContextDonate _ _)

theorem iok_replyRemove (caller r : ObjRef) : IoK N (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_replyRemove _ _)

theorem iok_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : IoK N (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_schedContextMaybeUnbindNtfn _)

theorem iok_unbindMaybeNotification (ntfnptr : ObjRef) : IoK N (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_unbindMaybeNotification _)

theorem iok_fastFinalise (a0 : Cap) (a1 : Bool) : IoK N (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_fastFinalise _ _)

theorem iok_getIrqSlot (irq : Irq) : IoK N (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_getIrqSlot _)

theorem iok_prepareThreadDelete (threadPtr : ObjRef) : IoK N (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_prepareThreadDelete _)

theorem iok_schedContextSetInactive (scPtr : ObjRef) : IoK N (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_schedContextSetInactive _)

theorem iok_schedContextUnbindTcb (scPtr : ObjRef) : IoK N (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_schedContextUnbindTcb _)

theorem iok_schedContextUnbindAllTcbs (scPtr : ObjRef) : IoK N (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_schedContextUnbindAllTcbs _)

theorem iok_schedContextUnbindNtfn (scPtr : ObjRef) : IoK N (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_schedContextUnbindNtfn _)

theorem iok_schedContextUnbindReply (scPtr : ObjRef) : IoK N (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_schedContextUnbindReply _)

theorem iok_schedContextUnbindYieldFrom (scPtr : ObjRef) : IoK N (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_schedContextUnbindYieldFrom _)

theorem iok_updateRestartPc (threadPtr : ObjRef) : IoK N (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_updateRestartPc _)

theorem iok_suspend (thread : ObjRef) : IoK N (suspend (Z := Unit) thread) := by
  unfold suspend; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_suspend _)

theorem iok_unbindFromSc (tcbPtr : ObjRef) : IoK N (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_unbindFromSc _)

theorem iok_unbindNotification (tcb : ObjRef) : IoK N (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_unbindNotification _)

theorem iok_getScActive (scPtr : ObjRef) : IoK N (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_getScActive _)

theorem iok_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : IoKE N f) (h_g : IoKE N g) : IoKE N (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; iok_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible refine iok_orChoiceE _ _ _ ?_ ?_)

theorem iok_updateTimeStamp  : IoK N (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_updateTimeStamp)

theorem iok_preemptionPoint  : IoKE N (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_preemptionPoint)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem iok_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : IoKE N m) : IoKE N (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; iok_auto
  all_goals first | exact h_m
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible refine iok_capFaultOnFailure _ _ _ ?_)

theorem iok_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : IoK N (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_capMove _ _ _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem iok_captransferFromWords (ptr : Word) : IoK N (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_captransferFromWords _)

theorem iok_isValidTimeoutHandler (tptr : ObjRef) : IoK N (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_isValidTimeoutHandler _)

theorem iok_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : IoK N (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_makeArchFaultMsg _ _)

theorem iok_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : IoK N (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_makeFaultMsg _ _)

theorem iok_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : IoK N (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_doFaultTransfer _ _ _ _)

theorem iok_loadWordOffs (ptr : ObjRef) (offs : Nat) : IoK N (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_loadWordOffs _ _)

theorem iok_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : IoK N (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_copyMrs _ _ _ _ _)

theorem iok_getMessageInfo (thread : ObjRef) : IoK N (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_getMessageInfo _)
end

end Fl4Proofs.P3.SInvIo
