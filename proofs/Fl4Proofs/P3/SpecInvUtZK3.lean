/- g5g: the memory half `YK D F` of untyped_ranges_zero, part 3 (sg1's SpecInvSgI3 renamed; see SpecInvUtZK1). -/
import Fl4Proofs.P3.SpecInvUtZK2
open Classical

namespace Fl4Proofs.P3.SInvUZ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {PD : PgSet} {FS : Set Nat}


theorem yk_tcbEpDequeue (tptr epPtr : ObjRef) : YK PD FS (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_tcbEpDequeue _ _)

theorem yk_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : YK PD FS (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_blockedCancelIpc _ _ _)

theorem yk_isRoundRobin (scPtr : ObjRef) : YK PD FS (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_isRoundRobin _)

theorem yk_getRefillHead (scPtr : ObjRef) : YK PD FS (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getRefillHead _)

theorem yk_refillPopHead (scPtr : ObjRef) : YK PD FS (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_refillPopHead _)

theorem yk_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : YK PD FS (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_updateRefillHd _ _)

theorem yk_mergeOverlappingRefills (scPtr : ObjRef) : YK PD FS (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_mergeOverlappingRefills _)

theorem yk_refillHeadOverlappingLoop (scPtr : ObjRef) : YK PD FS (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_refillHeadOverlappingLoop _)

theorem yk_refillUnblockCheck (scPtr : ObjRef) : YK PD FS (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_refillUnblockCheck _)

theorem yk_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : YK PD FS (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_ifCondRefillUnblockCheck _ _ _)

theorem yk_restartThreadIfNoFault (t : ObjRef) : YK PD FS (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_restartThreadIfNoFault _)

theorem yk_removeAndRestartEpQueuedThread (t epptr : ObjRef) : YK PD FS (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_removeAndRestartEpQueuedThread _ _)

theorem yk_cancelAllIpc (epptr : ObjRef) : YK PD FS (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_cancelAllIpc _)

theorem yk_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : YK PD FS (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_tcbNtfnDequeue _ _)

theorem yk_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : YK PD FS (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_removeAndRestartNtfnQueuedThread _ _)

theorem yk_cancelAllSignals (ntfnptr : ObjRef) : YK PD FS (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_cancelAllSignals _)

theorem yk_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : YK PD FS (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_removeAndRestartBadgedThread _ _ _)

theorem yk_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : YK PD FS (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_cancelBadgedSends _ _)

theorem yk_cancelSignal (threadptr ntfnptr : ObjRef) : YK PD FS (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_cancelSignal _ _)

theorem yk_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : YK PD FS (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getSkObjRef _ _ _)

theorem yk_replyRemoveTcb (tptr rptr : ObjRef) : YK PD FS (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_replyRemoveTcb _ _)

theorem yk_cancelIpc (tptr : ObjRef) : YK PD FS (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_cancelIpc _)

theorem yk_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : YK PD FS (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_capSwap _ _ _ _)

theorem yk_capSwapForDelete (slot1 slot2 : CslotPtr) : YK PD FS (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_capSwapForDelete _ _)

theorem yk_deletedIrqHandler (irq : Irq) : YK PD FS (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_deletedIrqHandler _)

theorem yk_postCapDeletion (cap : Cap) : YK PD FS (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_postCapDeletion _)

theorem yk_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : YK PD FS (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_emptySlot _ _)

theorem yk_replyUnlinkSc (scPtr replyPtr : ObjRef) : YK PD FS (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_replyUnlinkSc _ _)

theorem yk_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : YK PD FS (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getScObjRef _ _)

theorem yk_testReschedule (fromTptr : ObjRef) : YK PD FS (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_testReschedule _)

theorem yk_schedContextDonate (scPtr tcbPtr : ObjRef) : YK PD FS (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_schedContextDonate _ _)

theorem yk_replyRemove (caller r : ObjRef) : YK PD FS (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_replyRemove _ _)

theorem yk_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : YK PD FS (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_schedContextMaybeUnbindNtfn _)

theorem yk_unbindMaybeNotification (ntfnptr : ObjRef) : YK PD FS (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_unbindMaybeNotification _)

theorem yk_fastFinalise (a0 : Cap) (a1 : Bool) : YK PD FS (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_fastFinalise _ _)

theorem yk_capDeleteOne (slot : CslotPtr) : YK PD FS (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_capDeleteOne _)

theorem yk_getIrqSlot (irq : Irq) : YK PD FS (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getIrqSlot _)

theorem yk_deletingIrqHandler (irq : Irq) : YK PD FS (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_deletingIrqHandler _)

theorem yk_prepareThreadDelete (threadPtr : ObjRef) : YK PD FS (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_prepareThreadDelete _)

theorem yk_schedContextSetInactive (scPtr : ObjRef) : YK PD FS (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_schedContextSetInactive _)

theorem yk_schedContextUnbindTcb (scPtr : ObjRef) : YK PD FS (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_schedContextUnbindTcb _)

theorem yk_schedContextUnbindAllTcbs (scPtr : ObjRef) : YK PD FS (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_schedContextUnbindAllTcbs _)

theorem yk_schedContextUnbindNtfn (scPtr : ObjRef) : YK PD FS (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_schedContextUnbindNtfn _)

theorem yk_schedContextUnbindReply (scPtr : ObjRef) : YK PD FS (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_schedContextUnbindReply _)

theorem yk_schedContextUnbindYieldFrom (scPtr : ObjRef) : YK PD FS (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_schedContextUnbindYieldFrom _)

theorem yk_updateRestartPc (threadPtr : ObjRef) : YK PD FS (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_updateRestartPc _)

theorem yk_suspend (thread : ObjRef) : YK PD FS (suspend (Z := Unit) thread) := by
  unfold suspend; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_suspend _)

theorem yk_unbindFromSc (tcbPtr : ObjRef) : YK PD FS (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_unbindFromSc _)

theorem yk_unbindNotification (tcb : ObjRef) : YK PD FS (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_unbindNotification _)

theorem yk_finaliseCap (a0 : Cap) (a1 : Bool) : YK PD FS (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_finaliseCap _ _)

theorem yk_getScActive (scPtr : ObjRef) : YK PD FS (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getScActive _)

theorem yk_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : YKE PD FS f) (h_g : YKE PD FS g) : YKE PD FS (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; yk_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible refine yk_orChoiceE _ _ _ ?_ ?_)

theorem yk_updateTimeStamp  : YK PD FS (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_updateTimeStamp)

theorem yk_preemptionPoint  : YKE PD FS (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_preemptionPoint)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem yk_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, YK PD FS (f k)) (k : RecDelCall) : YKE PD FS (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, YKE PD FS (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; yk_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; yk_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> yk_auto
    all_goals exact hrec' _

theorem yk_recDel (c : RecDelCall) : YKE PD FS (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => yk_recDelF hf k) c
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_recDel _)

theorem yk_capDelete (slot : CslotPtr) : YKE PD FS (capDelete (Z := Unit) slot) := by
  unfold capDelete; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_capDelete _)

theorem yk_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : YKE PD FS m) : YKE PD FS (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; yk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible refine yk_capFaultOnFailure _ _ _ ?_)

theorem yk_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : YK PD FS (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_capMove _ _ _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem yk_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, YK PD FS (f k)) (sl : CslotPtr) : YKE PD FS (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, YKE PD FS (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  yk_auto
  all_goals exact hrec' _

theorem yk_capRevoke (sl : CslotPtr) : YKE PD FS (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => yk_capRevokeF hf k) sl
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_capRevoke _)

theorem yk_captransferFromWords (ptr : Word) : YK PD FS (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_captransferFromWords _)

theorem yk_isValidTimeoutHandler (tptr : ObjRef) : YK PD FS (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_isValidTimeoutHandler _)

theorem yk_makeArchFaultMsg (a0 : ArchFault) (a1 : ObjRef) : YK PD FS (makeArchFaultMsg (Z := Unit) a0 a1) := by
  unfold makeArchFaultMsg; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_makeArchFaultMsg _ _)

theorem yk_makeFaultMsg (a0 : Fault) (a1 : ObjRef) : YK PD FS (makeFaultMsg (Z := Unit) a0 a1) := by
  unfold makeFaultMsg; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_makeFaultMsg _ _)

theorem yk_doFaultTransfer (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : YK PD FS (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_doFaultTransfer _ _ _ _)

theorem yk_loadWordOffs (ptr : ObjRef) (offs : Nat) : YK PD FS (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_loadWordOffs _ _)

theorem yk_copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : YK PD FS (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_copyMrs _ _ _ _ _)

theorem yk_getMessageInfo (thread : ObjRef) : YK PD FS (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getMessageInfo _)
end

end Fl4Proofs.P3.SInvUZ
