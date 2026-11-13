/-
Operations on scheduling contexts: refills, the release queue, binding,
yield-to and consumed time (MCS).

Ports `spec/abstract/SchedContext_A`.
-/
import Fl4Spec.IpcCancel

namespace Fl4Spec

open Classical

noncomputable section

section
variable {Z : Type} [StateExt Z]

/-- l4v: SchedContext_A.read_ready_time. -/
def readReadyTime (scPtr : ObjRef) : RMonad Z Time := do
  let head ← readRefillHead scPtr
  Lookup.oreturn head.rTime

/-- l4v: SchedContext_A.read_tcb_ready_time. -/
def readTcbReadyTime (tcbPtr : ObjRef) : RMonad Z Time := do
  let scPtrOpt ← threadRead Tcb.tcbSchedContext tcbPtr
  Lookup.oassert (scPtrOpt ≠ none)
  readReadyTime (the scPtrOpt)

/-- l4v: SchedContext_A.ready_times_append. -/
def readyTimesAppend (tptr : ObjRef) (qs : List ObjRef) : SMonad Z (List ObjRef) :=
  orderedInsert tptr qs readTcbReadyTime (· ≤ ·)

/-- l4v: SchedContext_A.tcb_release_enqueue: enqueue a TCB in the release
queue, sorted by the ready time of its scheduling context. -/
def tcbReleaseEnqueue (tcbPtr : ObjRef) : SMonad Z Unit := do
  let q ← NonDet.gets fun s : State Z => s.releaseQueue
  let q' ← readyTimesAppend tcbPtr q
  setReleaseQueue q'
  NonDet.when (q = [] ∨ the q'.head? ≠ the q.head?)
    (NonDet.modify fun s => { s with reprogramTimer := true })

/-- l4v: SchedContext_A.refill_size. -/
def refillSize (scPtr : ObjRef) : SMonad Z Nat := do
  let refills ← getRefills scPtr
  return refills.length

/-- l4v: SchedContext_A.refill_full. -/
def refillFull (scPtr : ObjRef) : SMonad Z Bool := do
  let sc ← getSchedContext scPtr
  return decide (sc.scRefills.length = sc.scRefillMax)

/-- l4v: SchedContext_A.refill_single. -/
def refillSingle (scPtr : ObjRef) : SMonad Z Bool := do
  let sz ← refillSize scPtr
  return decide (sz = 1)

end

/-- l4v: SchedContext_A.refills_sum. -/
def refillsSum (rf : List Refill) : Time := (rf.map Refill.rAmount).sum

section
variable {Z : Type} [StateExt Z]

/-- l4v: SchedContext_A.refill_sum. -/
def refillSum (scPtr : ObjRef) : SMonad Z Time := do
  let refills ← getRefills scPtr
  return refillsSum refills

end

/-- l4v: SchedContext_A.max_refills_cap. -/
def maxRefillsCap (cap : Cap) : Nat :=
  match cap with
  | .schedContextCap _ sz => maxNumRefills (minSchedContextBits + sz)
  | _ => 0

section
variable {Z : Type} [StateExt Z]

/-- l4v: SchedContext_A.set_refills. -/
def setRefills (scPtr : ObjRef) (refills : List Refill) : SMonad Z Unit :=
  setScObjRef scRefillsUpdate scPtr refills

/-- l4v: SchedContext_A.set_refill_hd. -/
def setRefillHd (scPtr : ObjRef) (new : Refill) : SMonad Z Unit := updateRefillHd scPtr fun _ => new

/-- l4v: SchedContext_A.update_refill_tl. -/
def updateRefillTl (scPtr : ObjRef) (f : Refill → Refill) : SMonad Z Unit :=
  updateSchedContext scPtr (scRefillsUpdate fun refills => refills.dropLast ++ [f (the refills.getLast?)])

/-- l4v: SchedContext_A.set_refill_tl. -/
def setRefillTl (scPtr : ObjRef) (new : Refill) : SMonad Z Unit := updateRefillTl scPtr fun _ => new

/-- l4v: SchedContext_A.refill_add_tail. -/
def refillAddTail (scPtr : ObjRef) (newRefill : Refill) : SMonad Z Unit :=
  updateSchedContext scPtr (scRefillsUpdate fun refills => refills ++ [newRefill])

/-- l4v: SchedContext_A.maybe_add_empty_tail. -/
def maybeAddEmptyTail (scPtr : ObjRef) : SMonad Z Unit := do
  let robin ← isRoundRobin scPtr
  NonDet.when robin <| do
    let head ← getRefillHead scPtr
    let emptyRefill ← pure { rTime := head.rTime, rAmount := 0 : Refill }
    refillAddTail scPtr emptyRefill

/-- l4v: SchedContext_A.refill_new. -/
def refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : SMonad Z Unit := do
  let curTime ← NonDet.gets fun s : State Z => s.curTime
  setScObjRef scPeriodUpdate scPtr period
  setScObjRef scBudgetUpdate scPtr budget
  setScObjRef scRefillMaxUpdate scPtr maxRefills
  let refill ← pure { rTime := curTime, rAmount := budget : Refill }
  setScObjRef scRefillsUpdate scPtr [refill]
  maybeAddEmptyTail scPtr

/-- l4v: SchedContext_A.schedule_used. -/
def scheduleUsed (scPtr : ObjRef) (new : Refill) : SMonad Z Unit := do
  let refills ← getRefills scPtr
  NonDet.assert (refills ≠ [])
  let tail ← getRefillTail scPtr
  if canMergeRefill tail new
  then updateRefillTl scPtr fun r => { r with rAmount := tail.rAmount + new.rAmount }
  else do
    let full ← refillFull scPtr
    if ¬full
    then refillAddTail scPtr new
    else do
      updateRefillTl scPtr fun r => { r with rTime := new.rTime - tail.rAmount }
      updateRefillTl scPtr fun r => { r with rAmount := tail.rAmount + new.rAmount }

/-- l4v: SchedContext_A.refill_budget_check_round_robin. -/
def refillBudgetCheckRoundRobin (usage : Ticks) : SMonad Z Unit := do
  let scPtr ← NonDet.gets fun s : State Z => s.curSc
  updateRefillHd scPtr fun refill => { refill with rAmount := refill.rAmount - usage }
  updateRefillTl scPtr fun refill => { refill with rAmount := refill.rAmount + usage }

/-- l4v: SchedContext_A.refill_head_insufficient. -/
def refillHeadInsufficient (scPtr : ObjRef) : RMonad Z Bool := do
  let head ← readRefillHead scPtr
  Lookup.oreturn (decide (head.rAmount < MIN_BUDGET))

/-- l4v: SchedContext_A.merge_nonoverlapping_head_refill. -/
def mergeNonoverlappingHeadRefill (scPtr : ObjRef) : SMonad Z Unit := do
  let oldHead ← refillPopHead scPtr
  updateRefillHd scPtr fun head => { head with rAmount := head.rAmount + oldHead.rAmount }
  updateRefillHd scPtr fun head => { head with rTime := head.rTime - oldHead.rAmount }

/-- l4v: SchedContext_A.head_insufficient_loop. -/
def headInsufficientLoop (scPtr : ObjRef) : SMonad Z Unit :=
  NonDet.whileLoop (fun _ s => the (refillHeadInsufficient scPtr s) = true)
    (fun _ => mergeNonoverlappingHeadRefill scPtr) ()

/-- l4v: SchedContext_A.head_refill_overrun. -/
def headRefillOverrun (scPtr : ObjRef) (usage : Ticks) : RMonad Z Bool := do
  let head ← readRefillHead scPtr
  Lookup.oreturn (decide (head.rAmount ≤ usage ∧ head.rTime < MAX_RELEASE_TIME))

/-- l4v: SchedContext_A.charge_entire_head_refill. -/
def chargeEntireHeadRefill (scPtr : ObjRef) (usage : Ticks) : SMonad Z Ticks := do
  let head ← getRefillHead scPtr
  let sc ← getSchedContext scPtr
  let single ← refillSingle scPtr
  if single
  then updateRefillHd scPtr fun r => { r with rTime := head.rTime + sc.scPeriod }
  else do
    let oldHead ← refillPopHead scPtr
    scheduleUsed scPtr { oldHead with rTime := oldHead.rTime + sc.scPeriod }
  return usage - head.rAmount

/-- l4v: SchedContext_A.handle_overrun. -/
def handleOverrun (scPtr : ObjRef) (usage : Ticks) : SMonad Z Ticks :=
  NonDet.whileLoop (fun usage s => the (headRefillOverrun scPtr usage s) = true)
    (fun usage => chargeEntireHeadRefill scPtr usage) usage

/-- l4v: SchedContext_A.refill_budget_check. -/
def refillBudgetCheck (usage : Ticks) : SMonad Z Unit := do
  let scPtr ← NonDet.gets fun s : State Z => s.curSc
  let robin ← isRoundRobin scPtr
  NonDet.assert (¬robin)
  let usage' ← handleOverrun scPtr usage
  let head ← getRefillHead scPtr
  NonDet.when (usage' > 0 ∧ head.rTime < MAX_RELEASE_TIME) <| do
    let sc ← getSchedContext scPtr
    let used ← pure { rTime := head.rTime + sc.scPeriod, rAmount := usage' : Refill }
    updateRefillHd scPtr fun r => { r with rAmount := head.rAmount - usage' }
    updateRefillHd scPtr fun r => { r with rTime := head.rTime + usage' }
    scheduleUsed scPtr used
  headInsufficientLoop scPtr

/-- l4v: SchedContext_A.refill_update. -/
def refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) :
    SMonad Z Unit := do
  updateSchedContext scPtr (scRefillsUpdate fun rfs => [the rfs.head?])
  setScObjRef scRefillMaxUpdate scPtr newMaxRefills
  setScObjRef scPeriodUpdate scPtr newPeriod
  setScObjRef scBudgetUpdate scPtr newBudget
  let ready ← getScRefillReady scPtr
  NonDet.when ready <| do
    let curTime ← NonDet.gets fun s : State Z => s.curTime
    updateRefillHd scPtr fun refill => { refill with rTime := curTime }
  let head ← getRefillHead scPtr
  if newBudget ≤ head.rAmount
  then do
    updateRefillHd scPtr fun refill => { refill with rAmount := newBudget }
    maybeAddEmptyTail scPtr
  else do
    let unused ← pure (newBudget - head.rAmount)
    let new ← pure { rTime := head.rTime + newPeriod, rAmount := unused : Refill }
    refillAddTail scPtr new

/-- l4v: SchedContext_A.postpone. -/
def postpone (scPtr : ObjRef) : SMonad Z Unit := do
  let tcbOpt ← getScObjRef SchedContext.scTcb scPtr
  let tcbPtr ← NonDet.assertOpt tcbOpt
  tcbSchedAction tcbSchedDequeue tcbPtr
  tcbReleaseEnqueue tcbPtr
  NonDet.modify fun s => { s with reprogramTimer := true }

/-- l4v: SchedContext_A.sched_context_resume: if the bound TCB is
schedulable but its head refill is not ready or not sufficient, move it to
the release queue. -/
def schedContextResume (scPtr : ObjRef) : SMonad Z Unit := do
  let sc ← getSchedContext scPtr
  let tptr ← NonDet.assertOpt sc.scTcb
  let sched ← NonDet.gets (schedulable tptr)
  NonDet.when sched <| do
    let ts ← threadGet Tcb.tcbState tptr
    let ready ← getScRefillReady scPtr
    let sufficient ← getScRefillSufficient scPtr 0
    NonDet.when (runnable ts ∧ scActive sc ∧ ¬(ready ∧ sufficient)) <| do
      -- C code also asserts that tptr is not in ready q (l4v comment)
      let d ← threadGet Tcb.tcbDomain tptr
      let prio ← threadGet Tcb.tcbPriority tptr
      let queue ← getTcbQueue d prio
      NonDet.assert (¬(tptr ∈ queue))
      postpone scPtr

/-! ### Consumed time -/

/-- l4v: SchedContext_A.sched_context_update_consumed. -/
def schedContextUpdateConsumed (scPtr : ObjRef) : SMonad Z Time := do
  let sc ← getSchedContext scPtr
  let consumed ← pure sc.scConsumed
  if maxTicksToUs ≤ consumed
  then do
    setScObjRef scConsumedUpdate scPtr (consumed - maxTicksToUs)
    return ticksToUs maxTicksToUs
  else do
    setScObjRef scConsumedUpdate scPtr 0
    return ticksToUs sc.scConsumed

/-- l4v: SchedContext_A.set_consumed. -/
def setConsumed (scPtr tcbPtr : ObjRef) : SMonad Z Unit := do
  let consumed ← schedContextUpdateConsumed scPtr
  replyFromKernel tcbPtr (0, wordsFromTime consumed)

/-- l4v: SchedContext_A.return_consumed. -/
def returnConsumed (scPtr : ObjRef) : SMonad Z (List Data) := do
  let consumed ← schedContextUpdateConsumed scPtr
  return wordsFromTime consumed

/-! ### Yield-to -/

/-- l4v: SchedContext_A.sched_context_cancel_yield_to. -/
def schedContextCancelYieldTo (thread : ObjRef) : SMonad Z Unit := do
  let ytOpt ← getTcbObjRef Tcb.tcbYieldTo thread
  NonDet.maybeM (fun scPtr => do
    setScObjRef scYieldFromUpdate scPtr none
    setTcbObjRef tcbYieldToUpdate thread none) ytOpt

/-- l4v: SchedContext_A.complete_yield_to. -/
def completeYieldTo (tcbPtr : ObjRef) : SMonad Z Unit := do
  let ytOpt ← getTcbObjRef Tcb.tcbYieldTo tcbPtr
  NonDet.maybeM (fun scPtr => do
    setConsumed scPtr tcbPtr
    schedContextCancelYieldTo tcbPtr) ytOpt

/-- l4v: SchedContext_A.sched_context_unbind_yield_from. -/
def schedContextUnbindYieldFrom (scPtr : ObjRef) : SMonad Z Unit := do
  let sc ← getSchedContext scPtr
  NonDet.maybeM completeYieldTo sc.scYieldFrom

/-! ### Binding a TCB to a scheduling context -/

/-- l4v: SchedContext_A.test_possible_switch_to. -/
def testPossibleSwitchTo (tcbPtr : ObjRef) : SMonad Z Unit := do
  let sched ← NonDet.gets (schedulable tcbPtr)
  NonDet.when sched <| possibleSwitchTo tcbPtr

/-- l4v: SchedContext_A.sched_context_bind_tcb. -/
def schedContextBindTcb (scPtr tcbPtr : ObjRef) : SMonad Z Unit := do
  setTcbObjRef tcbSchedContextUpdate tcbPtr (some scPtr)
  setScObjRef scTcbUpdate scPtr (some tcbPtr)
  ifSporadicActiveCurScTestRefillUnblockCheck (some scPtr)
  schedContextResume scPtr
  let sched ← NonDet.gets (schedulable tcbPtr)
  NonDet.when sched <| do
    tcbSchedAction tcbSchedEnqueue tcbPtr
    rescheduleRequired

/-- l4v: SchedContext_A.sched_context_set_inactive. -/
def schedContextSetInactive (scPtr : ObjRef) : SMonad Z Unit := do
  updateSchedContext scPtr (scRefillsUpdate fun _ => [])
  updateSchedContext scPtr (scRefillMaxUpdate fun _ => 0)
  updateSchedContext scPtr (scBudgetUpdate fun _ => 0)
  updateSchedContext scPtr (scSporadicUpdate fun _ => false)

/-- l4v: SchedContext_A.unbind_from_sc: unbind a TCB from its scheduling
context, if it has one. -/
def unbindFromSc (tcbPtr : ObjRef) : SMonad Z Unit := do
  let scPtrOpt ← getTcbObjRef Tcb.tcbSchedContext tcbPtr
  NonDet.maybeM schedContextUnbindTcb scPtrOpt
  NonDet.maybeM (fun scptr => do
    let sc ← getSchedContext scptr
    NonDet.maybeM completeYieldTo sc.scYieldFrom) scPtrOpt

/-- l4v: SchedContext_A.maybe_donate_sc. -/
def maybeDonateSc (tcbPtr ntfnPtr : ObjRef) : SMonad Z Unit := do
  let scOpt ← getTcbObjRef Tcb.tcbSchedContext tcbPtr
  NonDet.when (scOpt = none) <|
    NonDet.bind (getNtfnObjRef Notification.ntfnSc ntfnPtr) <| NonDet.maybeM fun scPtr => do
      let scTcb ← getScObjRef SchedContext.scTcb scPtr
      NonDet.when (scTcb = none) <| do
        schedContextDonate scPtr tcbPtr
        schedContextResume scPtr

/-- l4v: SchedContext_A.maybe_return_sc. -/
def maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : SMonad Z Unit := do
  let nscOpt ← getNtfnObjRef Notification.ntfnSc ntfnPtr
  let tscOpt ← getTcbObjRef Tcb.tcbSchedContext tcbPtr
  NonDet.when (nscOpt = tscOpt ∧ nscOpt ≠ none) <| do
    let scPtr ← NonDet.assertOpt nscOpt
    setTcbObjRef tcbSchedContextUpdate tcbPtr none
    setScObjRef scTcbUpdate scPtr none
    let ct ← NonDet.gets fun s : State Z => s.curThread
    NonDet.when (tcbPtr = ct) rescheduleRequired

/-- l4v: SchedContext_A.commit_time: charge the consumed time to the current
scheduling context. -/
def commitTime : SMonad Z Unit := do
  let csc ← NonDet.gets fun s : State Z => s.curSc
  let active ← getScActive csc
  NonDet.when (active ∧ csc ≠ idleScPtr) <| do
    let consumed ← NonDet.gets fun s : State Z => s.consumedTime
    NonDet.when (0 < consumed) <| do
      let robin ← isRoundRobin csc
      if robin
      then refillBudgetCheckRoundRobin consumed
      else refillBudgetCheck consumed
    updateSchedContext csc fun sc => { sc with scConsumed := sc.scConsumed + consumed }
  NonDet.modify fun s => { s with consumedTime := 0 }

/-! ### Global time -/

/-- l4v: SchedContext_A.update_restart_pc. -/
def updateRestartPc (threadPtr : ObjRef) : SMonad Z Unit :=
  asUser threadPtr (NonDet.bind (getRegister nextInstructionRegister) (setRegister faultRegister))

/-- l4v: SchedContext_A.suspend: cancel any pending operation of a thread and
make it `Inactive`. -/
def suspend (thread : ObjRef) : SMonad Z Unit := do
  cancelIpc thread
  let state ← getThreadState thread
  NonDet.when (state = .running) <| updateRestartPc thread
  tcbSchedAction tcbSchedDequeue thread
  tcbReleaseRemove thread
  schedContextCancelYieldTo thread
  setThreadState thread .inactive

end

end

end Fl4Spec
