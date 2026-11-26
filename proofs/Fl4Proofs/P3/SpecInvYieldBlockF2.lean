/- iolay gen 5: YieldBlock frame lemmas, part 2: SpecInvYieldScopeF2's generated lemmas (gen.py `ys` mode, skip list
proofs/scratch/invA/skipYS.txt) for the strengthened invariant, without the functions that reach a blocking writer
(proofs/scratch/invA/skipYB.txt; hand-proved in SpecInvYieldBlockH). -/
import Fl4Proofs.P3.SpecInvYieldBlockF1
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {L : List ObjRef}

theorem yb_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : YBK L (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_threadGet _ _)

theorem yb_lazyFpuRestore (threadPtr : ObjRef) : YBK L (lazyFpuRestore (Z := Unit) threadPtr) := by
  unfold lazyFpuRestore; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_lazyFpuRestore _)

theorem yb_archPostSetFlags (t : ObjRef) (flags : TcbFlags) : YBK L (archPostSetFlags (Z := Unit) t flags) := by
  unfold archPostSetFlags; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archPostSetFlags _ _)

theorem yb_archPrepareNextDomain  : YBK L (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archPrepareNextDomain)

theorem yb_archPrepareSetDomain (t : ObjRef) (newDom : Domain) : YBK L (archPrepareSetDomain (Z := Unit) t newDom) := by
  unfold archPrepareSetDomain; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archPrepareSetDomain _ _)

theorem yb_archSwitchToIdleThread  : YBK L (archSwitchToIdleThread (Z := Unit)) := by
  unfold archSwitchToIdleThread; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archSwitchToIdleThread)

theorem yb_archSwitchToThread (t : ObjRef) : YBK L (archSwitchToThread (Z := Unit) t) := by
  unfold archSwitchToThread; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_archSwitchToThread _)

theorem yb_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : YBK L (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getTcbObjRef _ _)

theorem yb_getScRefillReady (scPtr : ObjRef) : YBK L (getScRefillReady (Z := Unit) scPtr) := by
  unfold getScRefillReady; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getScRefillReady _)

theorem yb_getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : YBK L (getScRefillSufficient (Z := Unit) scPtr usage) := by
  unfold getScRefillSufficient; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getScRefillSufficient _ _)

theorem yb_setSchedulerAction (action : SchedulerAction) : YBK L (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setSchedulerAction _)

theorem yb_getTcbQueue (d : Domain) (prio : Priority) : YBK L (getTcbQueue (Z := Unit) d prio) := by
  unfold getTcbQueue; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getTcbQueue _ _)

theorem yb_setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : YBK L (setTcbQueue (Z := Unit) d prio queue) := by
  unfold setTcbQueue; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setTcbQueue _ _ _)

theorem yb_tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) : YBK L (tcbSchedAction (Z := Unit) action thread) := by
  unfold tcbSchedAction; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_tcbSchedAction _ _)

theorem yb_rescheduleRequired  : YBK L (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_rescheduleRequired)

theorem yb_possibleSwitchTo (target : ObjRef) : YBK L (possibleSwitchTo (Z := Unit) target) := by
  unfold possibleSwitchTo; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_possibleSwitchTo _)

theorem yb_tcbReleaseRemove (tcbPtr : ObjRef) : YBK L (tcbReleaseRemove (Z := Unit) tcbPtr) := by
  unfold tcbReleaseRemove; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_tcbReleaseRemove _)

theorem yb_tcbReleaseDequeue  : YBK L (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_tcbReleaseDequeue)

theorem yb_awaken  : YBK L (awaken (Z := Unit)) := by
  unfold awaken; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_awaken)

theorem yb_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : YBK L (getSimpleKo (Z := Unit) f ptr) := by
  unfold getSimpleKo; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getSimpleKo _ _)

theorem yb_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) : YBK L (updateSkObjRef (Z := Unit) C f ref new) := by
  unfold updateSkObjRef; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_updateSkObjRef _ _ _ _)

theorem yb_bindNotification (tcbptr ntfnptr : ObjRef) : YBK L (bindNotification (Z := Unit) tcbptr ntfnptr) := by
  unfold bindNotification; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_bindNotification _ _)

theorem yb_getSchedContext (ptr : ObjRef) : YBK L (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getSchedContext _)

theorem yb_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : YBK L (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_updateSchedContext _ _)

theorem yb_bindScReply (scPtr replyPtr : ObjRef) : YBK L (bindScReply (Z := Unit) scPtr replyPtr) := by
  unfold bindScReply; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_bindScReply _ _)

theorem yb_getBlockingObject (state : ThreadState) : YBK L (getBlockingObject (Z := Unit) state) := by
  unfold getBlockingObject; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getBlockingObject _)

theorem yb_getThreadState (ref : ObjRef) : YBK L (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getThreadState _)

theorem yb_setThreadStateAct (tcbPtr : ObjRef) : YBK L (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setThreadStateAct _)

theorem yb_replyUnlinkTcb (t r : ObjRef) : YBK L (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_replyUnlinkTcb _ _)

theorem yb_tcbEpDequeue (tptr epPtr : ObjRef) : YBK L (tcbEpDequeue (Z := Unit) tptr epPtr) := by
  unfold tcbEpDequeue; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_tcbEpDequeue _ _)

theorem yb_blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) : YBK L (blockedCancelIpc (Z := Unit) state tptr replyOpt) := by
  unfold blockedCancelIpc; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_blockedCancelIpc _ _ _)

theorem yb_isRoundRobin (scPtr : ObjRef) : YBK L (isRoundRobin (Z := Unit) scPtr) := by
  unfold isRoundRobin; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_isRoundRobin _)

theorem yb_getRefillHead (scPtr : ObjRef) : YBK L (getRefillHead (Z := Unit) scPtr) := by
  unfold getRefillHead; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getRefillHead _)

theorem yb_refillPopHead (scPtr : ObjRef) : YBK L (refillPopHead (Z := Unit) scPtr) := by
  unfold refillPopHead; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_refillPopHead _)

theorem yb_updateRefillHd (scPtr : ObjRef) (f : Refill → Refill) : YBK L (updateRefillHd (Z := Unit) scPtr f) := by
  unfold updateRefillHd; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_updateRefillHd _ _)

theorem yb_mergeOverlappingRefills (scPtr : ObjRef) : YBK L (mergeOverlappingRefills (Z := Unit) scPtr) := by
  unfold mergeOverlappingRefills; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_mergeOverlappingRefills _)

theorem yb_refillHeadOverlappingLoop (scPtr : ObjRef) : YBK L (refillHeadOverlappingLoop (Z := Unit) scPtr) := by
  unfold refillHeadOverlappingLoop; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_refillHeadOverlappingLoop _)

theorem yb_refillUnblockCheck (scPtr : ObjRef) : YBK L (refillUnblockCheck (Z := Unit) scPtr) := by
  unfold refillUnblockCheck; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_refillUnblockCheck _)

theorem yb_ifCondRefillUnblockCheck (scOpt : Option ObjRef) (active asst : Option Bool) : YBK L (ifCondRefillUnblockCheck (Z := Unit) scOpt active asst) := by
  unfold ifCondRefillUnblockCheck; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_ifCondRefillUnblockCheck _ _ _)

theorem yb_restartThreadIfNoFault (t : ObjRef) : YBK L (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_restartThreadIfNoFault _)

theorem yb_removeAndRestartEpQueuedThread (t epptr : ObjRef) : YBK L (removeAndRestartEpQueuedThread (Z := Unit) t epptr) := by
  unfold removeAndRestartEpQueuedThread; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_removeAndRestartEpQueuedThread _ _)

theorem yb_cancelAllIpc (epptr : ObjRef) : YBK L (cancelAllIpc (Z := Unit) epptr) := by
  unfold cancelAllIpc; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_cancelAllIpc _)

theorem yb_tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : YBK L (tcbNtfnDequeue (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnDequeue; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_tcbNtfnDequeue _ _)

theorem yb_removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : YBK L (removeAndRestartNtfnQueuedThread (Z := Unit) t ntfnptr) := by
  unfold removeAndRestartNtfnQueuedThread; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_removeAndRestartNtfnQueuedThread _ _)

theorem yb_cancelAllSignals (ntfnptr : ObjRef) : YBK L (cancelAllSignals (Z := Unit) ntfnptr) := by
  unfold cancelAllSignals; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_cancelAllSignals _)

theorem yb_removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : YBK L (removeAndRestartBadgedThread (Z := Unit) t epptr badge) := by
  unfold removeAndRestartBadgedThread; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_removeAndRestartBadgedThread _ _ _)

theorem yb_cancelBadgedSends (epptr : ObjRef) (badge : Badge) : YBK L (cancelBadgedSends (Z := Unit) epptr badge) := by
  unfold cancelBadgedSends; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_cancelBadgedSends _ _)

theorem yb_cancelSignal (threadptr ntfnptr : ObjRef) : YBK L (cancelSignal (Z := Unit) threadptr ntfnptr) := by
  unfold cancelSignal; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_cancelSignal _ _)

theorem yb_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (ref : ObjRef) : YBK L (getSkObjRef (Z := Unit) C f ref) := by
  unfold getSkObjRef; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getSkObjRef _ _ _)

theorem yb_replyRemoveTcb (tptr rptr : ObjRef) : YBK L (replyRemoveTcb (Z := Unit) tptr rptr) := by
  unfold replyRemoveTcb; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_replyRemoveTcb _ _)

theorem yb_cancelIpc (tptr : ObjRef) : YBK L (cancelIpc (Z := Unit) tptr) := by
  unfold cancelIpc; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_cancelIpc _)

theorem yb_capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : YBK L (capSwap (Z := Unit) cap1 slot1 cap2 slot2) := by
  unfold capSwap; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_capSwap _ _ _ _)

theorem yb_capSwapForDelete (slot1 slot2 : CslotPtr) : YBK L (capSwapForDelete (Z := Unit) slot1 slot2) := by
  unfold capSwapForDelete; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_capSwapForDelete _ _)

theorem yb_deletedIrqHandler (irq : Irq) : YBK L (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_deletedIrqHandler _)

theorem yb_postCapDeletion (cap : Cap) : YBK L (postCapDeletion (Z := Unit) cap) := by
  unfold postCapDeletion; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_postCapDeletion _)

theorem yb_emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : YBK L (emptySlot (Z := Unit) slot cleanupInfo) := by
  unfold emptySlot; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_emptySlot _ _)

theorem yb_replyUnlinkSc (scPtr replyPtr : ObjRef) : YBK L (replyUnlinkSc (Z := Unit) scPtr replyPtr) := by
  unfold replyUnlinkSc; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_replyUnlinkSc _ _)

theorem yb_getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : YBK L (getScObjRef (Z := Unit) f ref) := by
  unfold getScObjRef; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getScObjRef _ _)

theorem yb_testReschedule (fromTptr : ObjRef) : YBK L (testReschedule (Z := Unit) fromTptr) := by
  unfold testReschedule; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_testReschedule _)

theorem yb_schedContextDonate (scPtr tcbPtr : ObjRef) : YBK L (schedContextDonate (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextDonate; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_schedContextDonate _ _)

theorem yb_replyRemove (caller r : ObjRef) : YBK L (replyRemove (Z := Unit) caller r) := by
  unfold replyRemove; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_replyRemove _ _)

theorem yb_schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : YBK L (schedContextMaybeUnbindNtfn (Z := Unit) ntfnPtr) := by
  unfold schedContextMaybeUnbindNtfn; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_schedContextMaybeUnbindNtfn _)

theorem yb_unbindMaybeNotification (ntfnptr : ObjRef) : YBK L (unbindMaybeNotification (Z := Unit) ntfnptr) := by
  unfold unbindMaybeNotification; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_unbindMaybeNotification _)

theorem yb_fastFinalise (a0 : Cap) (a1 : Bool) : YBK L (fastFinalise (Z := Unit) a0 a1) := by
  unfold fastFinalise; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_fastFinalise _ _)

theorem yb_capDeleteOne (slot : CslotPtr) : YBK L (capDeleteOne (Z := Unit) slot) := by
  unfold capDeleteOne; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_capDeleteOne _)

theorem yb_getIrqSlot (irq : Irq) : YBK L (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getIrqSlot _)

theorem yb_deletingIrqHandler (irq : Irq) : YBK L (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_deletingIrqHandler _)

theorem yb_prepareThreadDelete (threadPtr : ObjRef) : YBK L (prepareThreadDelete (Z := Unit) threadPtr) := by
  unfold prepareThreadDelete; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_prepareThreadDelete _)

theorem yb_schedContextSetInactive (scPtr : ObjRef) : YBK L (schedContextSetInactive (Z := Unit) scPtr) := by
  unfold schedContextSetInactive; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_schedContextSetInactive _)

theorem yb_schedContextUnbindTcb (scPtr : ObjRef) : YBK L (schedContextUnbindTcb (Z := Unit) scPtr) := by
  unfold schedContextUnbindTcb; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_schedContextUnbindTcb _)

theorem yb_schedContextUnbindAllTcbs (scPtr : ObjRef) : YBK L (schedContextUnbindAllTcbs (Z := Unit) scPtr) := by
  unfold schedContextUnbindAllTcbs; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_schedContextUnbindAllTcbs _)

theorem yb_schedContextUnbindNtfn (scPtr : ObjRef) : YBK L (schedContextUnbindNtfn (Z := Unit) scPtr) := by
  unfold schedContextUnbindNtfn; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_schedContextUnbindNtfn _)

theorem yb_schedContextUnbindReply (scPtr : ObjRef) : YBK L (schedContextUnbindReply (Z := Unit) scPtr) := by
  unfold schedContextUnbindReply; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_schedContextUnbindReply _)

theorem yb_schedContextCancelYieldTo (thread : ObjRef) : YBK L (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_schedContextCancelYieldTo _)

theorem yb_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : YBK L (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_lookupIpcBuffer _ _)

theorem yb_setMessageInfo (thread : ObjRef) (info : MessageInfo) : YBK L (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setMessageInfo _ _)

theorem yb_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : YBK L (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_storeWordOffs _ _ _)

theorem yb_replyFromKernel (thread : ObjRef) (x : Data × List Data) : YBK L (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_replyFromKernel _ _)

theorem yb_schedContextUpdateConsumed (scPtr : ObjRef) : YBK L (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_schedContextUpdateConsumed _)

theorem yb_setConsumed (scPtr tcbPtr : ObjRef) : YBK L (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setConsumed _ _)

theorem yb_completeYieldTo (tcbPtr : ObjRef) : YBK L (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_completeYieldTo _)

theorem yb_schedContextUnbindYieldFrom (scPtr : ObjRef) : YBK L (schedContextUnbindYieldFrom (Z := Unit) scPtr) := by
  unfold schedContextUnbindYieldFrom; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_schedContextUnbindYieldFrom _)

theorem yb_updateRestartPc (threadPtr : ObjRef) : YBK L (updateRestartPc (Z := Unit) threadPtr) := by
  unfold updateRestartPc; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_updateRestartPc _)

theorem yb_suspend (thread : ObjRef) : YBK L (suspend (Z := Unit) thread) := by
  unfold suspend; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_suspend _)

theorem yb_unbindFromSc (tcbPtr : ObjRef) : YBK L (unbindFromSc (Z := Unit) tcbPtr) := by
  unfold unbindFromSc; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_unbindFromSc _)

theorem yb_unbindNotification (tcb : ObjRef) : YBK L (unbindNotification (Z := Unit) tcb) := by
  unfold unbindNotification; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_unbindNotification _)

theorem yb_finaliseCap (a0 : Cap) (a1 : Bool) : YBK L (finaliseCap (Z := Unit) a0 a1) := by
  unfold finaliseCap; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_finaliseCap _ _)

theorem yb_getScActive (scPtr : ObjRef) : YBK L (getScActive (Z := Unit) scPtr) := by
  unfold getScActive; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getScActive _)

theorem yb_orChoiceE {ε α : Type} (c : DetExtMonad Bool) (f g : NonDetE (State Unit) ε α) (h_f : YBKE L f) (h_g : YBKE L g) : YBKE L (orChoiceE (Z := Unit) c f g) := by
  unfold orChoiceE; yb_auto
  all_goals first | exact h_f | exact h_g
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible refine yb_orChoiceE _ _ _ ?_ ?_)

theorem yb_updateTimeStamp  : YBK L (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_updateTimeStamp)

theorem yb_preemptionPoint  : YBKE L (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_preemptionPoint)


/-- One step of `rec_del`, its recursive calls keeping the invariant. -/
theorem yb_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, YBK L (f k)) (k : RecDelCall) : YBKE L (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, YBKE L (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; yb_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; yb_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> yb_auto
    all_goals exact hrec' _

theorem yb_recDel (c : RecDelCall) : YBKE L (recDel (Z := Unit) c) := by
  unfold recDel
  exact ik_lfp (fun f hf k => yb_recDelF hf k) c
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_recDel _)

theorem yb_capDelete (slot : CslotPtr) : YBKE L (capDelete (Z := Unit) slot) := by
  unfold capDelete; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_capDelete _)

theorem yb_capFaultOnFailure {α : Type} (cptr : ObjRef) (rp : Bool) (m : LFMonad Unit α) (h_m : YBKE L m) : YBKE L (capFaultOnFailure (Z := Unit) cptr rp m) := by
  unfold capFaultOnFailure; yb_auto
  all_goals first | exact h_m
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible refine yb_capFaultOnFailure _ _ _ ?_)

theorem yb_capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : YBK L (capMove (Z := Unit) newCap srcSlot destSlot) := by
  unfold capMove; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_capMove _ _ _)


/-- One step of `cap_revoke`, its recursive calls keeping the invariant. -/
theorem yb_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, YBK L (f k)) (sl : CslotPtr) : YBKE L (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, YBKE L (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  yb_auto
  all_goals exact hrec' _

theorem yb_capRevoke (sl : CslotPtr) : YBKE L (capRevoke (Z := Unit) sl) := by
  unfold capRevoke
  exact ik_lfp (fun f hf k => yb_capRevokeF hf k) sl
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_capRevoke _)

theorem yb_captransferFromWords (ptr : Word) : YBK L (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_captransferFromWords _)

theorem yb_isValidTimeoutHandler (tptr : ObjRef) : YBK L (isValidTimeoutHandler (Z := Unit) tptr) := by
  unfold isValidTimeoutHandler; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_isValidTimeoutHandler _)
end

end Fl4Proofs.P3.SInv
