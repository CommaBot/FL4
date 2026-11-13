/-
The scheduler, the release queue, timer reprogramming, and the user-level
scheduling context and domain invocations (MCS).

Ports `spec/abstract/Schedule_A`. Its `arch_requalify_consts` refer to
`Fl4Spec.X64.Arch`.
-/
import Fl4Spec.X64.Arch

namespace Fl4Spec

open Classical

noncomputable section

/-- l4v: Schedule_A.idle (`abbreviation`). -/
abbrev idle (st : ThreadState) : Prop := st = .idleThreadState

section
variable {Z : Type} [StateExt Z]

/-- l4v: Schedule_A.switch_to_thread: make a thread the current thread. -/
def switchToThread (t : ObjRef) : SMonad Z Unit := do
  let state ← NonDet.get
  NonDet.assert ((getTcb t : RMonad Z Tcb) state ≠ none)
  archSwitchToThread t
  tcbSchedAction tcbSchedDequeue t
  NonDet.modify fun s => { s with curThread := t }

/-- l4v: Schedule_A.guarded_switch_to: assert that a thread is schedulable
(ready and sufficient) and in the current domain before switching to it. -/
def guardedSwitchTo (thread : ObjRef) : SMonad Z Unit := do
  let scOpt ← threadGet Tcb.tcbSchedContext thread
  let _scp ← NonDet.assertOpt scOpt
  let sched ← NonDet.gets (schedulable thread)
  NonDet.assert sched
  -- l4v: to simplify the proofs of the invariants related to VCPUs and FPUs,
  -- assert that the thread switched to is in the current domain.
  let d ← NonDet.gets fun s : State Z => s.curDomain
  let nextDomain ← threadGet Tcb.tcbDomain thread
  NonDet.assert (nextDomain = d)
  switchToThread thread

/-- l4v: Schedule_A.switch_to_idle_thread. -/
def switchToIdleThread : SMonad Z Unit := do
  let thread ← NonDet.gets fun s : State Z => s.idleThread
  archSwitchToIdleThread
  NonDet.modify fun s => { s with curThread := thread }

end

/-- l4v: Schedule_A.domain_end_marker. -/
def domainEndMarker : Domain × DomainDuration := (0, 0)

section
variable {Z : Type} [StateExt Z]

/-- l4v: Schedule_A.next_domain. -/
def nextDomain : SMonad Z Unit := do
  NonDet.modify fun s =>
    let indexInc := s.domainIndex + 1
    let index' := if the s.domainList[indexInc]? = domainEndMarker
                  then s.domainStartIndex
                  else indexInc
    let domEntry := the s.domainList[index']?
    { s with domainIndex := index',
             curDomain := domEntry.1,
             domainTime := ucast 64 domEntry.2,
             reprogramTimer := true }
  doExtendedOp <| NonDet.modify fun s => workUnitsCompletedUpdate (fun _ => 0) s

/-- l4v: Schedule_A.dec_domain_time. -/
def decDomainTime : SMonad Z Unit := NonDet.modify fun s => { s with domainTime := s.domainTime - 1 }

/-- l4v: Schedule_A.set_next_interrupt: program the timer for the earliest of
the current budget expiry, the domain end, and the head of the release
queue. -/
def setNextInterrupt : SMonad Z Unit := do
  let curTm ← NonDet.gets fun s : State Z => s.curTime
  let curTh ← NonDet.gets fun s : State Z => s.curThread
  let scOpt ← getTcbObjRef Tcb.tcbSchedContext curTh
  let scPtr ← NonDet.assertOpt scOpt
  let ctHeadRefill ← getRefillHead scPtr
  let nextInterrupt ← pure (curTm + ctHeadRefill.rAmount)
  let nextInterrupt ←
    if numDomains > 1 then do
      let domainTm ← NonDet.gets fun s : State Z => s.domainTime
      pure (min nextInterrupt (curTm + domainTm))
    else
      pure nextInterrupt
  let rq ← NonDet.gets fun s : State Z => s.releaseQueue
  let nextInterrupt ← if rq = [] then pure nextInterrupt else do
    let rqscOpt ← getTcbObjRef Tcb.tcbSchedContext (the rq.head?)
    let rqscPtr ← NonDet.assertOpt rqscOpt
    let rlqHeadRefill ← getRefillHead rqscPtr
    pure (min rlqHeadRefill.rTime nextInterrupt)
  doMachineOp <| setDeadline (nextInterrupt - timerPrecision)

/-- l4v: Schedule_A.switch_sched_context. -/
def switchSchedContext : SMonad Z Unit := do
  let curSc ← NonDet.gets fun s : State Z => s.curSc
  let curTh ← NonDet.gets fun s : State Z => s.curThread
  let scOpt ← getTcbObjRef Tcb.tcbSchedContext curTh
  let scp ← NonDet.assertOpt scOpt
  let _sc' ← getSchedContext curSc
  NonDet.when (scp ≠ curSc) <| do
    NonDet.modify fun s => { s with reprogramTimer := true }
    ifConstantBandwidthRefillUnblockCheck (some scp)
  let reprogram ← NonDet.gets fun s : State Z => s.reprogramTimer
  NonDet.when reprogram <| commitTime
  NonDet.modify fun s => { s with curSc := scp }

/-- l4v: Schedule_A.sc_and_timer. -/
def scAndTimer : SMonad Z Unit := do
  switchSchedContext
  let reprogram ← NonDet.gets fun s : State Z => s.reprogramTimer
  NonDet.when reprogram <| do
    setNextInterrupt
    NonDet.modify fun s => { s with reprogramTimer := false }

/-- l4v: Schedule_A.read_tcb_refill_ready. -/
def readTcbRefillReady (t : ObjRef) : RMonad Z Bool := do
  let scOpt ← readTcbObjRef Tcb.tcbSchedContext t
  let scPtr ← Lookup.oassertOpt scOpt
  let ready ← readScRefillReady scPtr
  Lookup.oreturn ready

/-- l4v: Schedule_A.read_release_q_non_empty_and_ready. -/
def readReleaseQNonEmptyAndReady : RMonad Z Bool := do
  let rq ← Lookup.asks fun s : State Z => s.releaseQueue
  if rq = []
  then Lookup.oreturn false
  else readTcbRefillReady (the rq.head?)

/-- l4v: Schedule_A.tcb_release_dequeue. -/
def tcbReleaseDequeue : SMonad Z Unit := do
  let rq ← NonDet.gets fun s : State Z => s.releaseQueue
  NonDet.assert (rq ≠ [])
  tcbReleaseRemove (the rq.head?)
  possibleSwitchTo (the rq.head?)

/-- l4v: Schedule_A.awaken: release the threads at the head of the release
queue whose refills are ready. -/
def awaken : SMonad Z Unit :=
  NonDet.whileLoop (fun _ s => the (readReleaseQNonEmptyAndReady s) = true)
    (fun _ => tcbReleaseDequeue) ()

end

/-- l4v: Schedule_A.max_non_empty_queue. -/
def maxNonEmptyQueue (queues : Priority → ReadyQueue) : ReadyQueue :=
  queues (setMax {prio | queues prio ≠ []})

section
variable {Z : Type} [StateExt Z]

/-- l4v: Schedule_A.choose_thread. -/
def chooseThread : SMonad Z Unit := do
  let d ← NonDet.gets fun s : State Z => s.curDomain
  let queues ← NonDet.gets fun s : State Z => s.readyQueues d
  if ∀ prio, queues prio = []
  then switchToIdleThread
  else guardedSwitchTo (the (maxNonEmptyQueue queues).head?)

end

/-- l4v: Schedule_A.is_highest_prio: whether a priority is the highest among
the queued ready threads of a domain (trivially, if none are ready). -/
def isHighestPrio {Z : Type} (d : Domain) (p : Priority) (s : State Z) : Prop :=
  (∀ prio, s.readyQueues d prio = []) ∨ p ≥ setMax {prio | s.readyQueues d prio ≠ []}

section
variable {Z : Type} [StateExt Z]

/-- l4v: Schedule_A.schedule_switch_thread_fastfail. -/
def scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : SMonad Z Bool :=
  return decide (ct ≠ it → targetPrio < ctPrio)

/-- l4v: Schedule_A.schedule_choose_new_thread. -/
def scheduleChooseNewThread : SMonad Z Unit := do
  let domTime ← NonDet.gets fun s : State Z => s.domainTime
  NonDet.when (domTime = 0) <| do
    archPrepareNextDomain
    nextDomain
  chooseThread
  setSchedulerAction .resumeCurThread

/-- l4v: Schedule_A.check_domain_time. -/
def checkDomainTime : SMonad Z Unit := do
  let exp ← NonDet.gets isCurDomainExpired
  NonDet.when exp <| do
    NonDet.modify fun s => { s with reprogramTimer := true }
    rescheduleRequired

/-- l4v: Schedule_A.schedule_switch_thread_branch (`abbreviation (input)`). -/
abbrev scheduleSwitchThreadBranch (candidate ct : ObjRef) (ctSchdble : Bool) : SMonad Z Unit := do
  NonDet.when ctSchdble (tcbSchedAction tcbSchedEnqueue ct) -- schedulable
  let it ← NonDet.gets fun s : State Z => s.idleThread
  let targetPrio ← threadGet Tcb.tcbPriority candidate
  -- Infoflow does not like asking about the idle thread's priority or domain.
  let ctPrio ← if ct ≠ it then threadGet Tcb.tcbPriority ct else pure 0
  -- When to look at the bitmaps. This optimisation is used in the C fast
  -- path, but there we know cur_thread is not idle.
  let fastfail ← scheduleSwitchThreadFastfail ct it ctPrio targetPrio
  let curDom ← NonDet.gets fun s : State Z => s.curDomain
  let highest ← NonDet.gets fun s => decide (isHighestPrio curDom targetPrio s)
  if fastfail ∧ ¬highest
  then do -- Candidate is not best candidate, choose a new thread
    tcbSchedAction tcbSchedEnqueue candidate
    setSchedulerAction .chooseNewThread
    scheduleChooseNewThread
  else if ctSchdble ∧ ctPrio = targetPrio
  then do -- Current thread was runnable and candidate is not strictly better:
          -- want current thread to run next, so append the candidate to the
          -- end of the queue and choose again
    tcbSchedAction tcbSchedAppend candidate
    setSchedulerAction .chooseNewThread
    scheduleChooseNewThread
  else do
    guardedSwitchTo candidate
    -- Duplication assists in wp proof under different scheduler actions
    setSchedulerAction .resumeCurThread

/-- l4v: Schedule_A.schedule. -/
def schedule : SMonad Z Unit := do
  awaken
  checkDomainTime
  let ct ← NonDet.gets fun s : State Z => s.curThread
  let ctSchdble ← NonDet.gets (schedulable ct)
  let action ← NonDet.gets fun s : State Z => s.schedulerAction
  match action with
  | .resumeCurThread => pure ()
  | .chooseNewThread => do
      NonDet.when ctSchdble (tcbSchedAction tcbSchedEnqueue ct) -- schedulable
      scheduleChooseNewThread
  | .switchThread candidate => scheduleSwitchThreadBranch candidate ct ctSchdble
  scAndTimer

/-! ## User-level scheduling context invocations -/

/-- l4v: Schedule_A.sched_context_yield_to. -/
def schedContextYieldTo (scPtr : ObjRef) : SMonad Z (List Data) := do
  let scYfOpt ← getScObjRef SchedContext.scYieldFrom scPtr
  NonDet.when (scYfOpt ≠ none) <| do
    completeYieldTo (the scYfOpt) -- sc_yield_from = None
    let scYfOpt ← getScObjRef SchedContext.scYieldFrom scPtr
    NonDet.assert (scYfOpt = none)
  schedContextResume scPtr
  let returnNow ← (do
    let scTcbOpt ← getScObjRef SchedContext.scTcb scPtr
    let tcbPtr ← NonDet.assertOpt scTcbOpt
    let schedulable ← NonDet.gets (schedulable tcbPtr)
    if schedulable then do
      let ctPtr ← NonDet.gets fun s : State Z => s.curThread
      let prios ← threadGet Tcb.tcbPriority tcbPtr
      let ctPrios ← threadGet Tcb.tcbPriority ctPtr
      if prios < ctPrios
      then do
        tcbSchedAction tcbSchedDequeue tcbPtr
        tcbSchedAction tcbSchedEnqueue tcbPtr -- schedulable & dequeued & sufficient & ready
        pure true
      else do
        setTcbObjRef tcbYieldToUpdate ctPtr (some scPtr)
        setScObjRef scYieldFromUpdate scPtr (some ctPtr)
        tcbSchedAction tcbSchedDequeue tcbPtr
        tcbSchedAction tcbSchedEnqueue ctPtr
        tcbSchedAction tcbSchedEnqueue tcbPtr
        rescheduleRequired
        pure false
    else pure true : SMonad Z Bool)
  if returnNow then returnConsumed scPtr else return []

/-- l4v: Schedule_A.invoke_sched_context. -/
def invokeSchedContext (iv : SchedContextInvocation) : SMonad Z (List Data) :=
  match iv with
  | .invokeSchedContextConsumed scPtr => returnConsumed scPtr
  | .invokeSchedContextBind scPtr cap =>
    match cap with
    | .threadCap tcbPtr => do schedContextBindTcb scPtr tcbPtr; return []
    | .notificationCap ntfn _ _ => do schedContextBindNtfn scPtr ntfn; return []
    | _ => NonDet.fail
  | .invokeSchedContextUnbindObject scPtr cap =>
    match cap with
    | .threadCap _ => do schedContextUnbindTcb scPtr; return []
    | .notificationCap _ _ _ => do schedContextUnbindNtfn scPtr; return []
    | _ => NonDet.fail
  | .invokeSchedContextUnbind scPtr => do
    schedContextUnbindAllTcbs scPtr
    schedContextUnbindNtfn scPtr
    schedContextUnbindReply scPtr
    return []
  | .invokeSchedContextYieldTo scPtr => schedContextYieldTo scPtr

/-- l4v: Schedule_A.domain_schedule_configure. -/
def domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) :
    SMonad Z Unit :=
  NonDet.modify fun s => { s with domainList := s.domainList.set index (domain, duration) }

/-- l4v: Schedule_A.domain_set_start. -/
def domainSetStart (index : Nat) : SMonad Z Unit := do
  NonDet.modify fun s => { s with domainStartIndex := index }
  NonDet.modify fun s => { s with domainTime := 0 }
  -- Set the index such that after the increment in next_domain it points to
  -- the last domain schedule item, which is reserved to be an end marker.
  let domainListLen ← NonDet.gets fun s : State Z => s.domainList.length
  NonDet.modify fun s => { s with domainIndex := domainListLen - 2 }
  rescheduleRequired

end

end

end Fl4Spec
