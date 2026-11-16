/-
P3 (DESIGN.md §9): **the spec's deletions keep the domain schedule** (`DK`,
VsDom): `dk_recDel`, `dk_capDelete`, for any cap (CNode and TCB
`DomFrame`s), from `DK` lemmas of `finalise_cap`'s branches (mirroring
SpecFinFrames' `nkc_` lemmas) and the pre-fixed point of `rec_del` with
every outcome keeping the schedule (`lfp_le_prefixed`).
-/
import Fl4Proofs.P3.VsDomOps
import Fl4Proofs.P3.DelSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open Fl4Spec Classical

noncomputable section

/-! ## `DK`: `suspend` keeps the domain schedule -/


theorem dk_threadSet' (f : Tcb → Tcb) (t : ObjRef) : DK (threadSet (Z := Unit) f t) := by
  unfold threadSet; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_threadSet' _ _)

theorem dk_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : DK (threadGet (Z := Unit) f t) := by
  unfold threadGet; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_threadGet' _ _)

theorem dk_setThreadState' (t : ObjRef) (ts : ThreadState) : DK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setThreadState' _ _)

theorem dk_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    DK (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getSimpleKo' _ _)

theorem dk_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    DK (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setSimpleKo' _ _ _)

theorem dk_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef) :
    DK (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_updateSkObjRef' _ _ _ _)

theorem dk_getSchedContext' (q : ObjRef) : DK (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getSchedContext' _)

theorem dk_updateSchedContext' (q : ObjRef) (f : SchedContext → SchedContext) :
    DK (updateSchedContext (Z := Unit) q f) := by
  unfold updateSchedContext; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_updateSchedContext' _ _)

theorem dk_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : DK (asUser (Z := Unit) t u) := by
  unfold asUser; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_asUser' _ _)

theorem dk_replyUnlinkTcb' (t r : ObjRef) : DK (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_replyUnlinkTcb' _ _)

theorem dk_getThreadState' (t : ObjRef) : DK (getThreadState (Z := Unit) t) := by
  unfold getThreadState; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getThreadState' _)

theorem dk_cancelIpc' (t : ObjRef) : DK (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState blockedCancelIpc getBlockingObject tcbEpDequeue cancelSignal tcbNtfnDequeue
    replyRemoveTcb getReplyObjRef getSkObjRef
  dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_cancelIpc' _)

theorem dk_suspend' (t : ObjRef) : DK (suspend (Z := Unit) t) := by
  unfold suspend updateRestartPc tcbSchedAction getTcbQueue setTcbQueue tcbReleaseRemove
    schedContextCancelYieldTo getTcbObjRef getThreadState
  dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_suspend' _)


theorem dk_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) : DK (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getSkObjRef' _ _ _)

theorem dk_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : DK (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getScObjRef' _ _)

theorem dk_getIrqSlot' (irq : Irq) : DK (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getIrqSlot' _)

theorem dk_isFinalCap' (c : Cap) : DK (isFinalCap (Z := Unit) c) := by
  unfold isFinalCap; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_isFinalCap' _)

theorem dk_hwAsidInvalidate' (a : Asid) (v : ObjRef) : DK (hwAsidInvalidate (Z := Unit) a v) := by
  unfold hwAsidInvalidate; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_hwAsidInvalidate' _ _)

theorem dk_getCurrentCr3' : DK (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getCurrentCr3' )

theorem dk_setCurrentCr3' (c : Cr3) : DK (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setCurrentCr3' _)

theorem dk_setCurrentVspaceRoot' (v : ObjRef) (a : Asid) : DK (setCurrentVspaceRoot (Z := Unit) v a) := by
  unfold setCurrentVspaceRoot; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setCurrentVspaceRoot' _ _)

theorem dk_setVmRoot' (t : ObjRef) : DK (setVmRoot (Z := Unit) t) := by
  unfold setVmRoot; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setVmRoot' _)

theorem dk_freeIoportRange' (f l : IoPort) : DK (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_freeIoportRange' _ _)

theorem dk_setIrqState' (i : IrqState) (irq : Irq) : DK (setIrqState (Z := Unit) i irq) := by
  unfold setIrqState; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setIrqState' _ _)

theorem dk_deletedIrqHandler' (irq : Irq) : DK (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_deletedIrqHandler' _)

theorem dk_lookupIpcBuffer' (b : Bool) (t : ObjRef) : DK (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_lookupIpcBuffer' _ _)

theorem dk_zipWithMx' {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, DK (g a b)) :
    ∀ l1 l2, DK (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => dk_bind (h a b) (fun _ => dk_zipWithMx' h l1 l2)
  | [], _ => dk_pure' _
  | _ :: _, [] => dk_pure' _
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible refine dk_zipWithMx' (fun _ _ => ?_) _ _)

theorem dk_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : DK (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_storeWordOffs' _ _ _)

theorem dk_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : DK (setMrs (Z := Unit) t b m) := by
  unfold setMrs; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setMrs' _ _ _)

theorem dk_setMessageInfo' (t : ObjRef) (i : MessageInfo) : DK (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setMessageInfo' _ _)

theorem dk_archThreadSet' (f : ArchTcb → ArchTcb) (t : ObjRef) : DK (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_archThreadSet' _ _)

theorem dk_saveFpuState' (t : ObjRef) : DK (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_saveFpuState' _)

theorem dk_loadFpuState' (t : ObjRef) : DK (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_loadFpuState' _)

theorem dk_setX64CurrentFpuOwner' (o : Option ObjRef) : DK (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setX64CurrentFpuOwner' _)

theorem dk_switchLocalFpuOwner' (o : Option ObjRef) : DK (switchLocalFpuOwner (Z := Unit) o) := by
  unfold switchLocalFpuOwner; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_switchLocalFpuOwner' _)

theorem dk_getTcbQueue' (d : Domain) (p : Priority) : DK (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getTcbQueue' _ _)

theorem dk_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : DK (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setTcbQueue' _ _ _)

theorem dk_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) : DK (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_tcbSchedAction' _ _)

theorem dk_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : DK (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getTcbObjRef' _ _)

theorem dk_setSchedulerAction' (a : SchedulerAction) : DK (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setSchedulerAction' _)

theorem dk_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : DK (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getScRefillSufficient' _ _)

theorem dk_getScRefillReady' (sc : ObjRef) : DK (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getScRefillReady' _)

theorem dk_tcbReleaseRemove' (t : ObjRef) : DK (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_tcbReleaseRemove' _)

theorem dk_rescheduleRequired' : DK (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_rescheduleRequired' )

theorem dk_testReschedule' (t : ObjRef) : DK (testReschedule (Z := Unit) t) := by
  unfold testReschedule; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_testReschedule' _)

theorem dk_possibleSwitchTo' (t : ObjRef) : DK (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_possibleSwitchTo' _)

theorem dk_tcbEpDequeue' (t e : ObjRef) : DK (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_tcbEpDequeue' _ _)

theorem dk_tcbNtfnDequeue' (t n : ObjRef) : DK (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_tcbNtfnDequeue' _ _)

theorem dk_isRoundRobin' (sc : ObjRef) : DK (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_isRoundRobin' _)

theorem dk_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : DK (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_updateRefillHd' _ _)

theorem dk_getRefillHead' (sc : ObjRef) : DK (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getRefillHead' _)

theorem dk_refillPopHead' (sc : ObjRef) : DK (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_refillPopHead' _)

theorem dk_mergeOverlappingRefills' (sc : ObjRef) : DK (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_mergeOverlappingRefills' _)

theorem dk_refillHeadOverlappingLoop' (sc : ObjRef) : DK (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_refillHeadOverlappingLoop' _)

theorem dk_refillUnblockCheck' (sc : ObjRef) : DK (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_refillUnblockCheck' _)

theorem dk_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) : DK (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_ifCondRefillUnblockCheck' _ _ _)

theorem dk_ifSporadicCurScAssertRefillUnblockCheck' (o : Option ObjRef) : DK (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScAssertRefillUnblockCheck; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_ifSporadicCurScAssertRefillUnblockCheck' _)

theorem dk_restartThreadIfNoFault' (t : ObjRef) : DK (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_restartThreadIfNoFault' _)

theorem dk_removeAndRestartEpQueuedThread' (t e : ObjRef) : DK (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  unfold removeAndRestartEpQueuedThread; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_removeAndRestartEpQueuedThread' _ _)

theorem dk_removeAndRestartNtfnQueuedThread' (t n : ObjRef) : DK (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_removeAndRestartNtfnQueuedThread' _ _)

theorem dk_replyUnlinkSc' (sc r : ObjRef) : DK (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_replyUnlinkSc' _ _)

theorem dk_schedContextDonate' (sc t : ObjRef) : DK (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_schedContextDonate' _ _)

theorem dk_schedContextUpdateConsumed' (sc : ObjRef) : DK (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_schedContextUpdateConsumed' _)

theorem dk_replyFromKernel' (t : ObjRef) (x : Data × List Data) : DK (replyFromKernel (Z := Unit) t x) := by
  unfold replyFromKernel; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_replyFromKernel' _ _)

theorem dk_setConsumed' (sc t : ObjRef) : DK (setConsumed (Z := Unit) sc t) := by
  unfold setConsumed; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setConsumed' _ _)

theorem dk_schedContextCancelYieldTo' (t : ObjRef) : DK (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_schedContextCancelYieldTo' _)

theorem dk_fpuRelease' (t : ObjRef) : DK (fpuRelease (Z := Unit) t) := by
  unfold fpuRelease; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_fpuRelease' _)

theorem dk_deleteAsidPool' (b : Asid) (p : ObjRef) : DK (deleteAsidPool (Z := Unit) b p) := by
  unfold deleteAsidPool; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_deleteAsidPool' _ _)

theorem dk_deleteAsid' (a : Asid) (p : ObjRef) : DK (deleteAsid (Z := Unit) a p) := by
  unfold deleteAsid; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_deleteAsid' _ _)

theorem dk_archPostCapDeletion' (c : ArchCap) : DK (archPostCapDeletion (Z := Unit) c) := by
  unfold archPostCapDeletion; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_archPostCapDeletion' _)

theorem dk_postCapDeletion' (c : Cap) : DK (postCapDeletion (Z := Unit) c) := by
  unfold postCapDeletion; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_postCapDeletion' _)

theorem dk_emptySlot' (sl : CslotPtr) (c : Cap) : DK (emptySlot (Z := Unit) sl c) := by
  unfold emptySlot; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_emptySlot' _ _)

theorem dk_cancelAllIpc' (e : ObjRef) : DK (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_cancelAllIpc' _)

theorem dk_schedContextMaybeUnbindNtfn' (n : ObjRef) : DK (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_schedContextMaybeUnbindNtfn' _)

theorem dk_unbindMaybeNotification' (n : ObjRef) : DK (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_unbindMaybeNotification' _)

theorem dk_cancelAllSignals' (n : ObjRef) : DK (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_cancelAllSignals' _)

theorem dk_replyRemove' (t r : ObjRef) : DK (replyRemove (Z := Unit) t r) := by
  unfold replyRemove; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_replyRemove' _ _)

theorem dk_unbindNotification' (t : ObjRef) : DK (unbindNotification (Z := Unit) t) := by
  unfold unbindNotification; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_unbindNotification' _)

theorem dk_schedContextUnbindTcb' (sc : ObjRef) : DK (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_schedContextUnbindTcb' _)

theorem dk_completeYieldTo' (t : ObjRef) : DK (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_completeYieldTo' _)

theorem dk_unbindFromSc' (t : ObjRef) : DK (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_unbindFromSc' _)

theorem dk_schedContextUnbindAllTcbs' (sc : ObjRef) : DK (schedContextUnbindAllTcbs (Z := Unit) sc) := by
  unfold schedContextUnbindAllTcbs; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_schedContextUnbindAllTcbs' _)

theorem dk_schedContextUnbindNtfn' (sc : ObjRef) : DK (schedContextUnbindNtfn (Z := Unit) sc) := by
  unfold schedContextUnbindNtfn; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_schedContextUnbindNtfn' _)

theorem dk_schedContextUnbindReply' (sc : ObjRef) : DK (schedContextUnbindReply (Z := Unit) sc) := by
  unfold schedContextUnbindReply; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_schedContextUnbindReply' _)

theorem dk_schedContextUnbindYieldFrom' (sc : ObjRef) : DK (schedContextUnbindYieldFrom (Z := Unit) sc) := by
  unfold schedContextUnbindYieldFrom; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_schedContextUnbindYieldFrom' _)

theorem dk_schedContextSetInactive' (sc : ObjRef) : DK (schedContextSetInactive (Z := Unit) sc) := by
  unfold schedContextSetInactive; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_schedContextSetInactive' _)

theorem dk_prepareThreadDelete' (t : ObjRef) : DK (prepareThreadDelete (Z := Unit) t) := by
  unfold prepareThreadDelete; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_prepareThreadDelete' _)

theorem dk_archFinaliseCap' (c : ArchCap) (x : Bool) : DK (archFinaliseCap (Z := Unit) c x) := by
  unfold archFinaliseCap; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_archFinaliseCap' _ _)

theorem dk_fastFinalise' (c : Cap) (b : Bool) : DK (fastFinalise (Z := Unit) c b) := by
  unfold fastFinalise; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_fastFinalise' _ _)

theorem dk_capDeleteOne' (sl : CslotPtr) : DK (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_capDeleteOne' _)

theorem dk_deletingIrqHandler' (irq : Irq) : DK (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_deletingIrqHandler' _)

/-! ## `finalise_cap` -/

theorem dk_finaliseCap (c : Cap) (b : Bool) : DK (finaliseCap (Z := Unit) c b) := by
  cases c <;> unfold finaliseCap <;> dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_finaliseCap _ _)

/-! ## `rec_del` and `cap_delete` -/

theorem dk_capSwap' (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) : DK (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap setCdt; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_capSwap' _ _ _ _)

theorem dk_capSwapForDelete' (s1 s2 : CslotPtr) : DK (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_capSwapForDelete' _ _)

theorem dke_preemptionPoint' : DKE (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint orChoiceE updateTimeStamp getScActive; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dke_preemptionPoint')

/-- One step of `rec_del` keeps the schedule, its recursive calls keeping it. -/
theorem dk_recDelF {f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap))}
    (hrec : ∀ k, DK (f k)) (k : RecDelCall) : DKE (recDelF (Z := Unit) f k) := by
  have hrec' : ∀ k, DKE (ε := Unit) (f k : NonDetE (State Unit) Unit (Bool × Cap)) := hrec
  cases k with
  | cTEDeleteCall sl e => unfold recDelF withoutPreemption; dk_auto; all_goals exact hrec' _
  | finaliseSlotCall sl e => unfold recDelF withoutPreemption; dk_auto; all_goals exact hrec' _
  | reduceZombieCall c sl e =>
    unfold recDelF withoutPreemption
    split <;> dk_auto
    all_goals exact hrec' _

/-- **`rec_del` keeps the domain schedule.** -/
theorem dk_recDel (c : RecDelCall) : DKE (recDel (Z := Unit) c) := by
  intro σ x hx
  let f : RecDelCall → NonDet (State Unit) (Except Unit (Bool × Cap)) := fun _ t =>
    ({y | y.2.domainList = t.domainList ∧ y.2.domainStartIndex = t.domainStartIndex}, True)
  have hf : ∀ k t, RDF f k t ≤ f k t := fun k t =>
    ⟨fun y hy => dk_recDelF (f := f) (fun _ _ _ hz => hz) k t y hy, fun _ => trivial⟩
  exact (lfp_le_prefixed RDF f hf c σ).1 hx
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_recDel _)

/-- **`cap_delete` keeps the domain schedule.** -/
theorem dk_capDelete (sl : CslotPtr) : DKE (capDelete (Z := Unit) sl) := by
  unfold capDelete; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_capDelete _)

end

end Fl4Proofs.P3.Vs
