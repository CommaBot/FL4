/-
P3 (DESIGN.md §9), scheduler, g7c (KENTRY-PLAN g7c (a)): **the spec's
scheduler steps keep the CR3** (spec side only). `CRK := FK crF` (VsDom's
generic `FK`): every outcome keeps `x64_current_cr3`, the ASID table, the
global PML4 and the idle thread. ScFpuOwnK's `OWK` leaves for the cone of
`send_signal`, reproved for `crF` (generated from ScFpuOwnK by renaming:
none of those functions writes the four fields), and the scheduler's own
functions (`awaken`, `scAndTimer`, `lazyFpuRestore`, `archPrepareNextDomain`,
`nextDomain`). `crF_fires`: FL4's TCB timers (`Fires`) keep `crF`.
-/
import Fl4Proofs.P3.ScFpuOwnK
import Fl4Proofs.P3.ScSchedBsa
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open Fl4Spec Classical

noncomputable section

/-- The CR3, the ASID table, the global PML4 and the idle thread. -/
def crF (σ : State Unit) := (σ.archState.x64CurrentCr3, σ.archState.x64AsidTable, σ.archState.x64GlobalPml4,
  σ.idleThread, σ.archState.x64HugePages)

/-- Every outcome of `m` keeps `crF`. -/
abbrev CRK {α : Type} (m : NonDet (State Unit) α) : Prop := FK crF m

/-- An `CRK` lemma of a spec function (extended below, one rule per lemma). -/
syntax "crk_leaf" : tactic
macro_rules | `(tactic| crk_leaf) => `(tactic| fail "no crk_leaf")

macro "crk_auto" : tactic => `(tactic| repeat' (first | crk_leaf | dk_step0))

theorem crk_doMachineOp {α : Type} (mop : NonDet MachineState α) : CRK (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_doMachineOp _)

theorem crk_doExtendedOp (eop : DetExtMonad Unit) : CRK (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_doExtendedOp _)


theorem crk_setObject (p : ObjRef) (o : KernelObject) : CRK (setObject (Z := Unit) p o) := by
  unfold setObject; dk_auto0
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_setObject _ _)

theorem crk_setCap (c : Cap) (sl : CslotPtr) : CRK (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl; unfold setCap; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_setCap _ _)

theorem crk_getCap (sl : CslotPtr) : CRK (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_getCap _)


theorem crk_threadSet' (f : Tcb → Tcb) (t : ObjRef) : CRK (threadSet (Z := Unit) f t) := by
  unfold threadSet; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_threadSet' _ _)

theorem crk_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : CRK (threadGet (Z := Unit) f t) := by
  unfold threadGet; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_threadGet' _ _)

theorem crk_setThreadState' (t : ObjRef) (ts : ThreadState) : CRK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_setThreadState' _ _)

theorem crk_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    CRK (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_getSimpleKo' _ _)

theorem crk_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    CRK (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_setSimpleKo' _ _ _)

theorem crk_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef) :
    CRK (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_updateSkObjRef' _ _ _ _)

theorem crk_getSchedContext' (q : ObjRef) : CRK (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_getSchedContext' _)

theorem crk_updateSchedContext' (q : ObjRef) (f : SchedContext → SchedContext) :
    CRK (updateSchedContext (Z := Unit) q f) := by
  unfold updateSchedContext; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_updateSchedContext' _ _)

theorem crk_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : CRK (asUser (Z := Unit) t u) := by
  unfold asUser; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_asUser' _ _)

theorem crk_replyUnlinkTcb' (t r : ObjRef) : CRK (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_replyUnlinkTcb' _ _)

theorem crk_getThreadState' (t : ObjRef) : CRK (getThreadState (Z := Unit) t) := by
  unfold getThreadState; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_getThreadState' _)

theorem crk_cancelIpc' (t : ObjRef) : CRK (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState blockedCancelIpc getBlockingObject tcbEpDequeue cancelSignal tcbNtfnDequeue
    replyRemoveTcb getReplyObjRef getSkObjRef
  crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_cancelIpc' _)

theorem crk_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) : CRK (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_getSkObjRef' _ _ _)

theorem crk_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : CRK (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_getScObjRef' _ _)


theorem crk_getTcbQueue' (d : Domain) (p : Priority) : CRK (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_getTcbQueue' _ _)

theorem crk_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : CRK (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_setTcbQueue' _ _ _)

theorem crk_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) : CRK (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_tcbSchedAction' _ _)

theorem crk_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : CRK (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_getTcbObjRef' _ _)

theorem crk_setSchedulerAction' (a : SchedulerAction) : CRK (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_setSchedulerAction' _)

theorem crk_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : CRK (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_getScRefillSufficient' _ _)

theorem crk_getScRefillReady' (sc : ObjRef) : CRK (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_getScRefillReady' _)

theorem crk_tcbReleaseRemove' (t : ObjRef) : CRK (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_tcbReleaseRemove' _)

theorem crk_rescheduleRequired' : CRK (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_rescheduleRequired' )

theorem crk_testReschedule' (t : ObjRef) : CRK (testReschedule (Z := Unit) t) := by
  unfold testReschedule; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_testReschedule' _)

theorem crk_possibleSwitchTo' (t : ObjRef) : CRK (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_possibleSwitchTo' _)

theorem crk_tcbEpDequeue' (t e : ObjRef) : CRK (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_tcbEpDequeue' _ _)

theorem crk_tcbNtfnDequeue' (t n : ObjRef) : CRK (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_tcbNtfnDequeue' _ _)

theorem crk_isRoundRobin' (sc : ObjRef) : CRK (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_isRoundRobin' _)

theorem crk_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : CRK (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_updateRefillHd' _ _)

theorem crk_getRefillHead' (sc : ObjRef) : CRK (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_getRefillHead' _)

theorem crk_refillPopHead' (sc : ObjRef) : CRK (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_refillPopHead' _)

theorem crk_mergeOverlappingRefills' (sc : ObjRef) : CRK (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_mergeOverlappingRefills' _)

theorem crk_refillHeadOverlappingLoop' (sc : ObjRef) : CRK (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_refillHeadOverlappingLoop' _)

theorem crk_refillUnblockCheck' (sc : ObjRef) : CRK (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_refillUnblockCheck' _)

theorem crk_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) : CRK (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_ifCondRefillUnblockCheck' _ _ _)

theorem crk_ifSporadicCurScAssertRefillUnblockCheck' (o : Option ObjRef) : CRK (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScAssertRefillUnblockCheck; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_ifSporadicCurScAssertRefillUnblockCheck' _)

theorem crk_restartThreadIfNoFault' (t : ObjRef) : CRK (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_restartThreadIfNoFault' _)

theorem crk_removeAndRestartEpQueuedThread' (t e : ObjRef) : CRK (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  unfold removeAndRestartEpQueuedThread; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_removeAndRestartEpQueuedThread' _ _)

theorem crk_removeAndRestartNtfnQueuedThread' (t n : ObjRef) : CRK (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_removeAndRestartNtfnQueuedThread' _ _)

theorem crk_replyUnlinkSc' (sc r : ObjRef) : CRK (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_replyUnlinkSc' _ _)

theorem crk_schedContextDonate' (sc t : ObjRef) : CRK (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_schedContextDonate' _ _)

theorem crk_schedContextUpdateConsumed' (sc : ObjRef) : CRK (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_schedContextUpdateConsumed' _)

theorem crk_schedContextCancelYieldTo' (t : ObjRef) : CRK (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_schedContextCancelYieldTo' _)


theorem crk_orderedInsert' {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β)
    (R : β → β → Prop) : CRK (orderedInsert (Z := Unit) t ts f R) := by
  unfold orderedInsert; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_orderedInsert' _ _ _ _)

theorem crk_readyTimesAppend' (t : ObjRef) (q : List ObjRef) : CRK (readyTimesAppend (Z := Unit) t q) := by
  unfold readyTimesAppend; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_readyTimesAppend' _ _)

theorem crk_tcbReleaseEnqueue' (t : ObjRef) : CRK (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_tcbReleaseEnqueue' _)

theorem crk_tcbAppend' (t : ObjRef) (q : List ObjRef) : CRK (tcbAppend (Z := Unit) t q) := by
  unfold tcbAppend; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_tcbAppend' _ _)

theorem crk_postpone' (sc : ObjRef) : CRK (postpone (Z := Unit) sc) := by
  unfold postpone; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_postpone' _)

theorem crk_schedContextResume' (sc : ObjRef) : CRK (schedContextResume (Z := Unit) sc) := by
  unfold schedContextResume; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_schedContextResume' _)


theorem crk_maybeDonateSc' (tcbPtr ntfnPtr : ObjRef) : CRK (maybeDonateSc (Z := Unit) tcbPtr ntfnPtr) := by
  unfold maybeDonateSc; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_maybeDonateSc' _ _)

theorem crk_ifSporadicCurScTestRefillUnblockCheck' (o : Option ObjRef) :
    CRK (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScTestRefillUnblockCheck; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_ifSporadicCurScTestRefillUnblockCheck' _)

theorem crk_updateWaitingNtfn' (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) :
    CRK (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; crk_auto
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_updateWaitingNtfn' _ _ _)

/-- **`send_signal` keeps `crF`.** -/
theorem crk_sendSignal (n : ObjRef) (b : Badge) : CRK (sendSignal (Z := Unit) n b) := by
  unfold sendSignal; crk_auto


macro "crk_auto2" : tactic => `(tactic| repeat' (first | crk_leaf | dk_step0 | fk_unf | sched_unf))

theorem crk_tcbReleaseDequeue : CRK (tcbReleaseDequeue (Z := Unit)) := by
  unfold tcbReleaseDequeue; crk_auto2
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_tcbReleaseDequeue)

theorem crk_awaken : CRK (awaken (Z := Unit)) := by
  unfold awaken; crk_auto2
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_awaken)

theorem crk_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : CRK (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; crk_auto2
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_archThreadSet _ _)

theorem crk_saveFpuState (t : ObjRef) : CRK (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; crk_auto2
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_saveFpuState _)

theorem crk_loadFpuState (t : ObjRef) : CRK (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; crk_auto2
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_loadFpuState _)

theorem crk_setX64CurrentFpuOwner (o : Option ObjRef) : CRK (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner; crk_auto2
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_setX64CurrentFpuOwner _)

theorem crk_switchLocalFpuOwner (o : Option ObjRef) : CRK (switchLocalFpuOwner (Z := Unit) o) := by
  unfold switchLocalFpuOwner; crk_auto2
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_switchLocalFpuOwner _)

theorem crk_lazyFpuRestore (t : ObjRef) : CRK (lazyFpuRestore (Z := Unit) t) := by
  unfold lazyFpuRestore; crk_auto2
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_lazyFpuRestore _)

theorem crk_archPrepareNextDomain : CRK (archPrepareNextDomain (Z := Unit)) := by
  unfold archPrepareNextDomain; crk_auto2
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_archPrepareNextDomain)

set_option maxHeartbeats 2000000 in
theorem crk_nextDomain : CRK (nextDomain (Z := Unit)) := by
  unfold nextDomain; crk_auto2
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_nextDomain)

set_option maxHeartbeats 4000000 in
theorem crk_commitTime : CRK (commitTime (Z := Unit)) := by
  unfold commitTime; crk_auto2
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_commitTime)

set_option maxHeartbeats 4000000 in
theorem crk_switchSchedContext : CRK (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; crk_auto2
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_switchSchedContext)

set_option maxHeartbeats 2000000 in
theorem crk_setNextInterrupt : CRK (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; crk_auto2
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_setNextInterrupt)

theorem crk_scAndTimer : CRK (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; crk_auto2
macro_rules | `(tactic| crk_leaf) => `(tactic| with_reducible exact crk_scAndTimer)

end

end Fl4Proofs.P3.Vs

namespace Fl4Proofs.P3.Sched
open Fl4Spec

/-- **FL4's TCB timers keep `crF`** (`Fires`: notification signals and
`reprogram_timer` writes). -/
theorem crF_fires {σ σ1 : State Unit} (h : Fires σ σ1) : Vs.crF σ1 = Vs.crF σ := by
  induction h with
  | refl => rfl
  | tail _ hf ih =>
    obtain ⟨σa, ho, rfl⟩ := hf
    rcases ho with rfl | ⟨n, b, he⟩
    · exact ih
    · have := Vs.crk_sendSignal n b _ ((), σa) (by rw [he]; exact Set.mem_singleton _)
      exact this.trans ih

end Fl4Proofs.P3.Sched
