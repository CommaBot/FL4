/- virt gen 3: the object-type family `TYK`, part 3 (SpecInvDvK3 with `aType` for `objBits`, proofs/scratch/virt/mkty.py; see VirtTyK1). -/
import Fl4Proofs.P3.VirtTyK2
open Classical

namespace Fl4Proofs.P3.SInvTY
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {OS : TySet}



theorem ty_tcbEpDequeue (tptr epPtr : ObjRef) : TYK OS (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_tcbEpDequeue _ _)

theorem ty_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : TYK OS (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_blockedCancelIpc _ _ _)

theorem ty_isRoundRobin (scPtr : ObjRef) : TYK OS (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_isRoundRobin _)

theorem ty_getRefillHead (scPtr : ObjRef) : TYK OS (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getRefillHead _)

theorem ty_refillPopHead (scPtr : ObjRef) : TYK OS (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_refillPopHead _)

theorem ty_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : TYK OS (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_updateRefillHd _ _)

theorem ty_mergeOverlappingRefills (scPtr : ObjRef) : TYK OS (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_mergeOverlappingRefills _)

theorem ty_refillHeadOverlappingLoop (scPtr : ObjRef) : TYK OS (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_refillHeadOverlappingLoop _)

theorem ty_refillUnblockCheck (scPtr : ObjRef) : TYK OS (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_refillUnblockCheck _)

theorem ty_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : TYK OS (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_ifCondRefillUnblockCheck _ _ _)

theorem ty_restartThreadIfNoFault (t : ObjRef) : TYK OS (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_restartThreadIfNoFault _)

theorem ty_removeAndRestartEpQueuedThread (t epptr : ObjRef) : TYK OS (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_removeAndRestartEpQueuedThread _ _)

theorem ty_cancelAllIpc (epptr : ObjRef) : TYK OS (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_cancelAllIpc _)

theorem ty_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : TYK OS (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_tcbNtfnDequeue _ _)

theorem ty_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : TYK OS (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_removeAndRestartNtfnQueuedThread _ _)

theorem ty_cancelAllSignals (ntfnptr : ObjRef) : TYK OS (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_cancelAllSignals _)

theorem ty_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : TYK OS (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_removeAndRestartBadgedThread _ _ _)

theorem ty_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : TYK OS (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_cancelBadgedSends _ _)

theorem ty_cancelSignal (threadptr ntfnptr : ObjRef) : TYK OS (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_cancelSignal _ _)

theorem ty_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : TYK OS (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getSkObjRef _ _ _)

theorem ty_replyRemoveTcb (tptr rptr : ObjRef) : TYK OS (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_replyRemoveTcb _ _)

theorem ty_cancelIpc (tptr : ObjRef) : TYK OS (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_cancelIpc _)

theorem ty_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : TYK OS (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_capSwap _ _ _ _)

theorem ty_capSwapForDelete (slot1 slot2 : CslotPtr) : TYK OS (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_capSwapForDelete _ _)

theorem ty_deletedIrqHandler (irq : Irq) : TYK OS (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_deletedIrqHandler _)

theorem ty_postCapDeletion (cap : Cap) : TYK OS (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_postCapDeletion _)

theorem ty_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : TYK OS (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_emptySlot _ _)

theorem ty_replyUnlinkSc (scPtr replyPtr : ObjRef) : TYK OS (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_replyUnlinkSc _ _)

theorem ty_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : TYK OS (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getScObjRef _ _)

theorem ty_testReschedule (fromTptr : ObjRef) : TYK OS (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_testReschedule _)

theorem ty_schedContextDonate (scPtr tcbPtr : ObjRef) : TYK OS (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_schedContextDonate _ _)

theorem ty_replyRemove (caller r : ObjRef) : TYK OS (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_replyRemove _ _)

theorem ty_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : TYK OS (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_schedContextMaybeUnbindNtfn _)

theorem ty_unbindMaybeNotification (ntfnptr : ObjRef) : TYK OS (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_unbindMaybeNotification _)

theorem ty_fastFinalise (a0 : Cap) (a1 : Bool) : TYK OS (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_fastFinalise _ _)

theorem ty_capDeleteOne (slot : CslotPtr) : TYK OS (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_capDeleteOne _)

theorem ty_getIrqSlot (irq : Irq) : TYK OS (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getIrqSlot _)

theorem ty_deletingIrqHandler (irq : Irq) : TYK OS (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_deletingIrqHandler _)

theorem ty_prepareThreadDelete (threadPtr : ObjRef) : TYK OS (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_prepareThreadDelete _)

theorem ty_schedContextSetInactive (scPtr : ObjRef) : TYK OS (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_schedContextSetInactive _)

theorem ty_schedContextUnbindTcb (scPtr : ObjRef) : TYK OS (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_schedContextUnbindTcb _)

theorem ty_schedContextUnbindAllTcbs (scPtr : ObjRef) : TYK OS (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_schedContextUnbindAllTcbs _)

theorem ty_schedContextUnbindNtfn (scPtr : ObjRef) : TYK OS (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_schedContextUnbindNtfn _)

theorem ty_schedContextUnbindReply (scPtr : ObjRef) : TYK OS (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_schedContextUnbindReply _)

theorem ty_schedContextUnbindYieldFrom (scPtr : ObjRef) : TYK OS (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_schedContextUnbindYieldFrom _)

theorem ty_updateRestartPc (threadPtr : ObjRef) : TYK OS (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_updateRestartPc _)

theorem ty_suspend (thread : ObjRef) : TYK OS (suspend (Z := Unit) thread) := by
  unfold suspend; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_suspend _)

theorem ty_unbindFromSc (tcbPtr : ObjRef) : TYK OS (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_unbindFromSc _)

theorem ty_unbindNotification (tcb : ObjRef) : TYK OS (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_unbindNotification _)

theorem ty_finaliseCap (a0 : Cap) (a1 : Bool) : TYK OS (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_finaliseCap _ _)

theorem ty_getScActive (scPtr : ObjRef) : TYK OS (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getScActive _)

theorem ty_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : TYKE OS f) (h_g : TYKE OS g) : TYKE OS (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; ty_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible refine ty_orChoiceE _ _ _ ?_ ?_)

theorem ty_updateTimeStamp  : TYK OS (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_updateTimeStamp)

theorem ty_preemptionPoint  : TYKE OS (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_preemptionPoint)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem ty_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, TYK OS (f k)) (k : RecDelCall) : TYKE OS (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, TYKE OS (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; ty_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; ty_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> ty_auto
    all_goals exact hrec' _

theorem ty_recDel (c : RecDelCall) : TYKE OS (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => ty_recDelF hf k) c
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_recDel _)

theorem ty_capDelete (slot : CslotPtr) : TYKE OS (capDelete (Z := Unit) slot) := by
  unfold capDelete; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_capDelete _)

theorem ty_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : TYKE OS m) : TYKE OS (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; ty_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible refine ty_capFaultOnFailure _ _ _ ?_)

theorem ty_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : TYK OS (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_capMove _ _ _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem ty_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, TYK OS (f k)) (sl : CslotPtr) : TYKE OS (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, TYKE OS (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  ty_auto
  all_goals exact hrec' _

theorem ty_capRevoke (sl : CslotPtr) : TYKE OS (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => ty_capRevokeF hf k) sl
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_capRevoke _)

theorem ty_captransferFromWords (ptr : Word) : TYK OS (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_captransferFromWords _)

theorem ty_isValidTimeoutHandler (tptr : ObjRef) : TYK OS (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_isValidTimeoutHandler _)

theorem ty_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : TYK OS (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_makeArchFaultMsg _ _)

theorem ty_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : TYK OS (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_makeFaultMsg _ _)

theorem ty_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : TYK OS (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_doFaultTransfer _ _ _ _)

theorem ty_loadWordOffs (ptr : ObjRef) (offs : Nat) : TYK OS (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_loadWordOffs _ _)

theorem ty_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : TYK OS (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_copyMrs _ _ _ _ _)

theorem ty_getMessageInfo (thread : ObjRef) : TYK OS (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getMessageInfo _)
end

end Fl4Proofs.P3.SInvTY
