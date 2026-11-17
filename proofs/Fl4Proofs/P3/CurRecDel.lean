/-
P3 (DESIGN.md §9): **the spec keeps `cur_thread`** (`CTK`), a mechanical copy
of DomRecDel's `DK` (the domain schedule) for `cur_thread`: no step of the
arch invocations, the deletions or `install_tcb_cap` writes it.
-/
import Fl4Proofs.P3.CurVsOps
import Fl4Proofs.P3.DelSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs.CurK
open Fl4Spec Classical

noncomputable section

/-! ## `CTK`: `suspend` keeps the domain schedule -/


theorem ctk_threadSet' (f : Tcb → Tcb) (t : ObjRef) : CTK (threadSet (Z := Unit) f t) := by
  unfold threadSet; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_threadSet' _ _)

theorem ctk_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : CTK (threadGet (Z := Unit) f t) := by
  unfold threadGet; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_threadGet' _ _)

theorem ctk_setThreadState' (t : ObjRef) (ts : ThreadState) : CTK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setThreadState' _ _)

theorem ctk_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    CTK (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getSimpleKo' _ _)

theorem ctk_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    CTK (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setSimpleKo' _ _ _)

theorem ctk_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef) :
    CTK (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_updateSkObjRef' _ _ _ _)

theorem ctk_getSchedContext' (q : ObjRef) : CTK (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getSchedContext' _)

theorem ctk_updateSchedContext' (q : ObjRef) (f : SchedContext → SchedContext) :
    CTK (updateSchedContext (Z := Unit) q f) := by
  unfold updateSchedContext; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_updateSchedContext' _ _)

theorem ctk_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : CTK (asUser (Z := Unit) t u) := by
  unfold asUser; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_asUser' _ _)

theorem ctk_replyUnlinkTcb' (t r : ObjRef) : CTK (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_replyUnlinkTcb' _ _)

theorem ctk_getThreadState' (t : ObjRef) : CTK (getThreadState (Z := Unit) t) := by
  unfold getThreadState; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getThreadState' _)

theorem ctk_cancelIpc' (t : ObjRef) : CTK (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState blockedCancelIpc getBlockingObject tcbEpDequeue cancelSignal tcbNtfnDequeue
    replyRemoveTcb getReplyObjRef getSkObjRef
  ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_cancelIpc' _)

theorem ctk_suspend' (t : ObjRef) : CTK (suspend (Z := Unit) t) := by
  unfold suspend updateRestartPc tcbSchedAction getTcbQueue setTcbQueue tcbReleaseRemove
    schedContextCancelYieldTo getTcbObjRef getThreadState
  ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_suspend' _)


theorem ctk_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) : CTK (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getSkObjRef' _ _ _)

theorem ctk_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : CTK (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getScObjRef' _ _)

theorem ctk_getIrqSlot' (irq : Irq) : CTK (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getIrqSlot' _)

theorem ctk_isFinalCap' (c : Cap) : CTK (isFinalCap (Z := Unit) c) := by
  unfold isFinalCap; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_isFinalCap' _)

theorem ctk_hwAsidInvalidate' (a : Asid) (v : ObjRef) : CTK (hwAsidInvalidate (Z := Unit) a v) := by
  unfold hwAsidInvalidate; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_hwAsidInvalidate' _ _)

theorem ctk_getCurrentCr3' : CTK (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getCurrentCr3' )

theorem ctk_setCurrentCr3' (c : Cr3) : CTK (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setCurrentCr3' _)

theorem ctk_setCurrentVspaceRoot' (v : ObjRef) (a : Asid) : CTK (setCurrentVspaceRoot (Z := Unit) v a) := by
  unfold setCurrentVspaceRoot; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setCurrentVspaceRoot' _ _)

theorem ctk_setVmRoot' (t : ObjRef) : CTK (setVmRoot (Z := Unit) t) := by
  unfold setVmRoot; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setVmRoot' _)

theorem ctk_freeIoportRange' (f l : IoPort) : CTK (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_freeIoportRange' _ _)

theorem ctk_setIrqState' (i : IrqState) (irq : Irq) : CTK (setIrqState (Z := Unit) i irq) := by
  unfold setIrqState; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setIrqState' _ _)

theorem ctk_deletedIrqHandler' (irq : Irq) : CTK (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_deletedIrqHandler' _)

theorem ctk_lookupIpcBuffer' (b : Bool) (t : ObjRef) : CTK (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_lookupIpcBuffer' _ _)

theorem ctk_zipWithMx' {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, CTK (g a b)) :
    ∀ l1 l2, CTK (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => ctk_bind (h a b) (fun _ => ctk_zipWithMx' h l1 l2)
  | [], _ => ctk_pure' _
  | _ :: _, [] => ctk_pure' _
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible refine ctk_zipWithMx' (fun _ _ => ?_) _ _)

theorem ctk_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : CTK (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_storeWordOffs' _ _ _)

theorem ctk_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : CTK (setMrs (Z := Unit) t b m) := by
  unfold setMrs; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setMrs' _ _ _)

theorem ctk_setMessageInfo' (t : ObjRef) (i : MessageInfo) : CTK (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setMessageInfo' _ _)

theorem ctk_archThreadSet' (f : ArchTcb → ArchTcb) (t : ObjRef) : CTK (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_archThreadSet' _ _)

theorem ctk_saveFpuState' (t : ObjRef) : CTK (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_saveFpuState' _)

theorem ctk_loadFpuState' (t : ObjRef) : CTK (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_loadFpuState' _)

theorem ctk_setX64CurrentFpuOwner' (o : Option ObjRef) : CTK (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setX64CurrentFpuOwner' _)

theorem ctk_switchLocalFpuOwner' (o : Option ObjRef) : CTK (switchLocalFpuOwner (Z := Unit) o) := by
  unfold switchLocalFpuOwner; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_switchLocalFpuOwner' _)

theorem ctk_getTcbQueue' (d : Domain) (p : Priority) : CTK (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getTcbQueue' _ _)

theorem ctk_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : CTK (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setTcbQueue' _ _ _)

theorem ctk_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) : CTK (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_tcbSchedAction' _ _)

theorem ctk_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : CTK (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getTcbObjRef' _ _)

theorem ctk_setSchedulerAction' (a : SchedulerAction) : CTK (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setSchedulerAction' _)

theorem ctk_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : CTK (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getScRefillSufficient' _ _)

theorem ctk_getScRefillReady' (sc : ObjRef) : CTK (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getScRefillReady' _)

theorem ctk_tcbReleaseRemove' (t : ObjRef) : CTK (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_tcbReleaseRemove' _)

theorem ctk_rescheduleRequired' : CTK (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_rescheduleRequired' )

theorem ctk_testReschedule' (t : ObjRef) : CTK (testReschedule (Z := Unit) t) := by
  unfold testReschedule; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_testReschedule' _)

theorem ctk_possibleSwitchTo' (t : ObjRef) : CTK (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_possibleSwitchTo' _)

theorem ctk_tcbEpDequeue' (t e : ObjRef) : CTK (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_tcbEpDequeue' _ _)

theorem ctk_tcbNtfnDequeue' (t n : ObjRef) : CTK (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_tcbNtfnDequeue' _ _)

theorem ctk_isRoundRobin' (sc : ObjRef) : CTK (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_isRoundRobin' _)

theorem ctk_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : CTK (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_updateRefillHd' _ _)

theorem ctk_getRefillHead' (sc : ObjRef) : CTK (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getRefillHead' _)

theorem ctk_refillPopHead' (sc : ObjRef) : CTK (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_refillPopHead' _)

theorem ctk_mergeOverlappingRefills' (sc : ObjRef) : CTK (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_mergeOverlappingRefills' _)

theorem ctk_refillHeadOverlappingLoop' (sc : ObjRef) : CTK (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_refillHeadOverlappingLoop' _)

theorem ctk_refillUnblockCheck' (sc : ObjRef) : CTK (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_refillUnblockCheck' _)

theorem ctk_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) : CTK (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_ifCondRefillUnblockCheck' _ _ _)

theorem ctk_ifSporadicCurScAssertRefillUnblockCheck' (o : Option ObjRef) : CTK (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScAssertRefillUnblockCheck; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_ifSporadicCurScAssertRefillUnblockCheck' _)

theorem ctk_restartThreadIfNoFault' (t : ObjRef) : CTK (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_restartThreadIfNoFault' _)

theorem ctk_removeAndRestartEpQueuedThread' (t e : ObjRef) : CTK (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  unfold removeAndRestartEpQueuedThread; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_removeAndRestartEpQueuedThread' _ _)

theorem ctk_removeAndRestartNtfnQueuedThread' (t n : ObjRef) : CTK (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_removeAndRestartNtfnQueuedThread' _ _)

theorem ctk_replyUnlinkSc' (sc r : ObjRef) : CTK (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_replyUnlinkSc' _ _)

theorem ctk_schedContextDonate' (sc t : ObjRef) : CTK (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_schedContextDonate' _ _)

theorem ctk_schedContextUpdateConsumed' (sc : ObjRef) : CTK (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_schedContextUpdateConsumed' _)

theorem ctk_replyFromKernel' (t : ObjRef) (x : Data × List Data) : CTK (replyFromKernel (Z := Unit) t x) := by
  unfold replyFromKernel; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_replyFromKernel' _ _)

theorem ctk_setConsumed' (sc t : ObjRef) : CTK (setConsumed (Z := Unit) sc t) := by
  unfold setConsumed; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setConsumed' _ _)

theorem ctk_schedContextCancelYieldTo' (t : ObjRef) : CTK (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_schedContextCancelYieldTo' _)

theorem ctk_fpuRelease' (t : ObjRef) : CTK (fpuRelease (Z := Unit) t) := by
  unfold fpuRelease; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_fpuRelease' _)

theorem ctk_deleteAsidPool' (b : Asid) (p : ObjRef) : CTK (deleteAsidPool (Z := Unit) b p) := by
  unfold deleteAsidPool; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_deleteAsidPool' _ _)

theorem ctk_deleteAsid' (a : Asid) (p : ObjRef) : CTK (deleteAsid (Z := Unit) a p) := by
  unfold deleteAsid; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_deleteAsid' _ _)

theorem ctk_archPostCapDeletion' (c : ArchCap) : CTK (archPostCapDeletion (Z := Unit) c) := by
  unfold archPostCapDeletion; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_archPostCapDeletion' _)

theorem ctk_postCapDeletion' (c : Cap) : CTK (postCapDeletion (Z := Unit) c) := by
  unfold postCapDeletion; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_postCapDeletion' _)

theorem ctk_emptySlot' (sl : CslotPtr) (c : Cap) : CTK (emptySlot (Z := Unit) sl c) := by
  unfold emptySlot; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_emptySlot' _ _)

theorem ctk_cancelAllIpc' (e : ObjRef) : CTK (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_cancelAllIpc' _)

theorem ctk_schedContextMaybeUnbindNtfn' (n : ObjRef) : CTK (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_schedContextMaybeUnbindNtfn' _)

theorem ctk_unbindMaybeNotification' (n : ObjRef) : CTK (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_unbindMaybeNotification' _)

theorem ctk_cancelAllSignals' (n : ObjRef) : CTK (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_cancelAllSignals' _)

theorem ctk_replyRemove' (t r : ObjRef) : CTK (replyRemove (Z := Unit) t r) := by
  unfold replyRemove; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_replyRemove' _ _)

theorem ctk_unbindNotification' (t : ObjRef) : CTK (unbindNotification (Z := Unit) t) := by
  unfold unbindNotification; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_unbindNotification' _)

theorem ctk_schedContextUnbindTcb' (sc : ObjRef) : CTK (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_schedContextUnbindTcb' _)

theorem ctk_completeYieldTo' (t : ObjRef) : CTK (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_completeYieldTo' _)

theorem ctk_unbindFromSc' (t : ObjRef) : CTK (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_unbindFromSc' _)

theorem ctk_schedContextUnbindAllTcbs' (sc : ObjRef) : CTK (schedContextUnbindAllTcbs (Z := Unit) sc) := by
  unfold schedContextUnbindAllTcbs; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_schedContextUnbindAllTcbs' _)

theorem ctk_schedContextUnbindNtfn' (sc : ObjRef) : CTK (schedContextUnbindNtfn (Z := Unit) sc) := by
  unfold schedContextUnbindNtfn; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_schedContextUnbindNtfn' _)

theorem ctk_schedContextUnbindReply' (sc : ObjRef) : CTK (schedContextUnbindReply (Z := Unit) sc) := by
  unfold schedContextUnbindReply; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_schedContextUnbindReply' _)

theorem ctk_schedContextUnbindYieldFrom' (sc : ObjRef) : CTK (schedContextUnbindYieldFrom (Z := Unit) sc) := by
  unfold schedContextUnbindYieldFrom; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_schedContextUnbindYieldFrom' _)

theorem ctk_schedContextSetInactive' (sc : ObjRef) : CTK (schedContextSetInactive (Z := Unit) sc) := by
  unfold schedContextSetInactive; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_schedContextSetInactive' _)

theorem ctk_prepareThreadDelete' (t : ObjRef) : CTK (prepareThreadDelete (Z := Unit) t) := by
  unfold prepareThreadDelete; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_prepareThreadDelete' _)

theorem ctk_archFinaliseCap' (c : ArchCap) (x : Bool) : CTK (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_archFinaliseCap' _ _)

theorem ctk_fastFinalise' (c : Cap) (b : Bool) : CTK (fastFinalise (Z := Unit) c b) := by
  unfold fastFinalise; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_fastFinalise' _ _)

theorem ctk_capDeleteOne' (sl : CslotPtr) : CTK (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_capDeleteOne' _)

theorem ctk_deletingIrqHandler' (irq : Irq) : CTK (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_deletingIrqHandler' _)

/-! ## `finalise_cap` -/

theorem ctk_finaliseCap (c : Cap) (b : Bool) : CTK (finaliseCap (Z := Unit) c b) := by
  cases c <;> unfold finaliseCap <;> ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_finaliseCap _ _)

/-! ## `rec_del` and `cap_delete` -/

theorem ctk_capSwap' (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) : CTK (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap setCdt; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_capSwap' _ _ _ _)

theorem ctk_capSwapForDelete' (s1 s2 : CslotPtr) : CTK (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_capSwapForDelete' _ _)

theorem ctke_preemptionPoint' : CTKE (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint orChoiceE updateTimeStamp getScActive; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctke_preemptionPoint')

/-- One step of `rec_del` keeps the schedule, its recursive calls keeping it. -/
theorem ctk_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, CTK (f k)) (k : RecDelCall) : CTKE (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, CTKE (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; ctk_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; ctk_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> ctk_auto
    all_goals exact hrec' _

/-- **`rec_del` keeps the domain schedule.** -/
theorem ctk_recDel (c : RecDelCall) : CTKE (recDel (Z := Unit) c) := by
  intro σ x hx
  let f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)) := fun _ t =>
    ({y | y.2.curThread = t.curThread ∧ y.2.curThread = t.curThread}, True)
  have hf : ∀ k t, RDF f k t ≤ f k t := fun k t =>
    ⟨fun y hy => ctk_recDelF (f := f) (fun _ _ _ hz => hz) k t y hy, fun _ => trivial⟩
  exact (lfp_le_prefixed RDF f hf c σ).1 hx
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_recDel _)

/-- **`cap_delete` keeps the domain schedule.** -/
theorem ctk_capDelete (sl : CslotPtr) : CTKE (capDelete (Z := Unit) sl) := by
  unfold capDelete; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_capDelete _)

/-! ## `cap_revoke` and the CNode invocations -/

/-- One step of `cap_revoke` keeps the schedule, its recursive calls keeping it. -/
theorem ctk_capRevokeF {f : CslotPtr → NonDet (State Unit) (Except Unit Unit)}
    (hrec : ∀ k, CTK (f k)) (sl : CslotPtr) : CTKE (capRevokeF (Z := Unit) f sl) := by
  have hrec' : ∀ k, CTKE (ε := Unit) (f k : NonDetE (State Unit) Unit Unit) := hrec
  unfold capRevokeF withoutPreemption selectExt
  ctk_auto
  all_goals exact hrec' _

/-- **`cap_revoke` keeps the domain schedule.** -/
theorem ctk_capRevoke (sl : CslotPtr) : CTKE (capRevoke (Z := Unit) sl) := by
  intro σ x hx
  let f : CslotPtr → NonDet (State Unit) (Except Unit Unit) := fun _ t =>
    ({y | y.2.curThread = t.curThread ∧ y.2.curThread = t.curThread}, True)
  have hf : ∀ k t, (fun r c => capRevokeF (Z := Unit) r c) f k t ≤ f k t := fun k t =>
    ⟨fun y hy => ctk_capRevokeF (f := f) (fun _ _ _ hz => hz) k t y hy, fun _ => trivial⟩
  exact (lfp_le_prefixed _ f hf sl σ).1 hx
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_capRevoke _)

theorem ctk_capMove' (c : Cap) (s1 s2 : CslotPtr) : CTK (capMove (Z := Unit) c s1 s2) := by
  unfold capMove; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_capMove' _ _ _)

theorem ctk_removeAndRestartBadgedThread' (t e : ObjRef) (b : Badge) :
    CTK (removeAndRestartBadgedThread (Z := Unit) t e b) := by
  unfold removeAndRestartBadgedThread; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_removeAndRestartBadgedThread' _ _ _)

theorem ctk_cancelBadgedSends' (e : ObjRef) (b : Badge) : CTK (cancelBadgedSends (Z := Unit) e b) := by
  unfold cancelBadgedSends; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_cancelBadgedSends' _ _)

/-- **Every CNode invocation keeps the domain schedule.** -/
theorem ctke_invokeCnode (i : CnodeInvocation) : CTKE (invokeCnode (Z := Unit) i) := by
  cases i <;> unfold invokeCnode withoutPreemption <;> ctk_auto

end

end Fl4Proofs.P3.Vs.CurK
