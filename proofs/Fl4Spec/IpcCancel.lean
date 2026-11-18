/-
Cancelling IPC, scheduling-context bindings, reply stacks and endpoint
queues (MCS).

Ports `spec/abstract/IpcCancel_A`. Its `arch_requalify` lines refer to
`Fl4Spec.Retype` (ArchIpcCancel_A) and `Fl4Spec.Machine`. l4v imports
`Init_A` here only for `idle_sc_ptr`, which on RISCV64 `rt` lives in
`Machine_A`; here it is the state field `idleSc` (FL4 deviation: one idle SC
per core, see `AbstractState.idleSc`), so X64/Init_A is not needed. The lemma `sc_with_reply_def2` is not ported.
-/
import Fl4Spec.TcbAcc

namespace Fl4Spec

open Classical

noncomputable section

/-! ## Scheduling context accessors -/

section
variable {Z : Type} [StateExt Z]

/-- l4v: IpcCancel_A.sched_context_bind_ntfn. -/
def schedContextBindNtfn (sc ntfn : ObjRef) : SMonad Z Unit := do
  setNtfnObjRef ntfnScUpdate ntfn (some sc)
  setScObjRef scNtfnUpdate sc (some ntfn)

/-- l4v: IpcCancel_A.do_unbind_ntfn_sc (`abbreviation`): remove the binding
between a notification and a scheduling context. -/
abbrev doUnbindNtfnSc (ntfnptr scptr : ObjRef) : SMonad Z Unit := do
  setNtfnObjRef ntfnScUpdate ntfnptr none
  setScObjRef scNtfnUpdate scptr none

/-- l4v: IpcCancel_A.sched_context_unbind_ntfn. -/
def schedContextUnbindNtfn (scPtr : ObjRef) : SMonad Z Unit := do
  let ntfnOpt ← getScObjRef SchedContext.scNtfn scPtr
  NonDet.maybeM (fun ntfn => doUnbindNtfnSc ntfn scPtr) ntfnOpt

/-- l4v: IpcCancel_A.sched_context_maybe_unbind_ntfn. -/
def schedContextMaybeUnbindNtfn (ntfnPtr : ObjRef) : SMonad Z Unit := do
  let scOpt ← getNtfnObjRef Notification.ntfnSc ntfnPtr
  NonDet.maybeM (fun sc => doUnbindNtfnSc ntfnPtr sc) scOpt

/-- l4v: IpcCancel_A.sched_context_unbind_reply. Only the head reply points
to the scheduling context. -/
def schedContextUnbindReply (scPtr : ObjRef) : SMonad Z Unit := do
  let replies ← NonDet.liftM SchedContext.scReplies (getSchedContext scPtr)
  NonDet.unless (replies = []) <| do
    setReplyObjRef replyScUpdate (the replies.head?) none
    setScObjRef scRepliesUpdate scPtr []

/-- l4v: IpcCancel_A.sched_context_unbind_tcb: unbind a TCB from its
scheduling context, removing it from the scheduler. -/
def schedContextUnbindTcb (scPtr : ObjRef) : SMonad Z Unit := do
  let sc ← getSchedContext scPtr
  let tptr ← NonDet.assertOpt sc.scTcb
  let cur ← NonDet.gets fun s : State Z => s.curThread
  NonDet.when (tptr = cur) rescheduleRequired
  tcbSchedAction tcbSchedDequeue tptr
  tcbReleaseRemove tptr
  setTcbObjRef tcbSchedContextUpdate tptr none
  setScObjRef scTcbUpdate scPtr none

/-- l4v: IpcCancel_A.test_reschedule. -/
def testReschedule (fromTptr : ObjRef) : SMonad Z Unit := do
  let cur ← NonDet.gets fun s : State Z => s.curThread
  let action ← NonDet.gets fun s : State Z => s.schedulerAction
  let flag ← pure (match action with
    | .switchThread p => fromTptr = p
    | _ => False)
  NonDet.when (fromTptr = cur ∨ flag) rescheduleRequired

/-- l4v: IpcCancel_A.sched_context_donate: donate a scheduling context. -/
def schedContextDonate (scPtr tcbPtr : ObjRef) : SMonad Z Unit := do
  let fromOpt ← getScObjRef SchedContext.scTcb scPtr
  NonDet.when (fromOpt ≠ none) <| do
    let fromTptr ← NonDet.assertOpt fromOpt
    tcbSchedAction tcbSchedDequeue fromTptr
    tcbReleaseRemove fromTptr
    setTcbObjRef tcbSchedContextUpdate fromTptr none
    testReschedule fromTptr
  setScObjRef scTcbUpdate scPtr (some tcbPtr)
  setTcbObjRef tcbSchedContextUpdate tcbPtr (some scPtr)

/-- l4v: IpcCancel_A.reply_unlink_sc: unbind a reply from its scheduling
context. -/
def replyUnlinkSc (scPtr replyPtr : ObjRef) : SMonad Z Unit := do
  let scReplies ← NonDet.liftM SchedContext.scReplies (getSchedContext scPtr)
  let reply ← getReply replyPtr
  if the scReplies.head? = replyPtr
  then do -- if it is the head
    -- only the head of the list should point to the sc
    NonDet.assert (reply.replySc = some scPtr)
    updateSchedContext scPtr (scRepliesUpdate List.tail) -- pop the head
    match scReplies.tail with
    | [] => pure ()
    | r' :: _ => setReplyObjRef replyScUpdate r' (some scPtr) -- fix up the refs
    setReplyObjRef replyScUpdate replyPtr none -- set reply_sc to None
  else do
    -- only the head of the list should point to the sc
    NonDet.assert (reply.replySc = none)
    -- take until the (first and only) occurrence of reply_ptr
    updateSchedContext scPtr (scRepliesUpdate (List.takeWhile fun r => decide (r ≠ replyPtr)))

/-- l4v: IpcCancel_A.reply_unlink_tcb: unbind a reply from its TCB. -/
def replyUnlinkTcb (t r : ObjRef) : SMonad Z Unit := do
  let reply ← getReply r
  NonDet.assert (reply.replyTcb = some t)
  let ts ← getThreadState t
  NonDet.assert (ts = .blockedOnReply r ∨ ∃ ep d, ts = .blockedOnReceive ep (some r) d)
  setReplyObjRef replyTcbUpdate r none
  setThreadState t .inactive

end

/-- l4v: IpcCancel_A.sc_with_reply: the scheduling context whose reply stack
holds `r` (`the_pred_option`, i.e. `partial_inv P True`). -/
def scWithReply {Z : Type} (r : ObjRef) (s : State Z) : Option ObjRef :=
  partialInv (fun scPtr => decide (∃ sc n, s.kheap scPtr = some (.schedContext sc n) ∧
    r ∈ sc.scReplies)) true

section
variable {Z : Type} [StateExt Z]

/-- l4v: IpcCancel_A.reply_remove: remove a reply object from the call
stack. The caller must be `BlockedOnReply`; it is `Inactive` on return. -/
def replyRemove (caller r : ObjRef) : SMonad Z Unit := do
  let reply ← getReply r
  NonDet.assert (reply.replyTcb = some caller)
  let rScOpt ← NonDet.gets (scWithReply r)
  match rScOpt with
  | none => pure ()
  | some scPtr => do
    let replies ← NonDet.liftM SchedContext.scReplies (getSchedContext scPtr)
    let callerSc ← getTcbObjRef Tcb.tcbSchedContext caller
    -- drop the head or cut off the stack
    replyUnlinkSc scPtr r
    NonDet.when (the replies.head? = r ∧ callerSc = none) <| schedContextDonate scPtr caller
  -- FIXME RT: check the C code! (l4v comment)
  replyUnlinkTcb caller r

/-- l4v: IpcCancel_A.reply_remove_tcb: remove a `BlockedOnReply` thread and
the reply it is blocked on from the call stack. -/
def replyRemoveTcb (tptr rptr : ObjRef) : SMonad Z Unit := do
  let ts ← getThreadState tptr
  NonDet.assert (ts = .blockedOnReply rptr)
  let scPtrOpt ← NonDet.gets (scWithReply rptr)
  match scPtrOpt with
  | none => pure ()
  | some scPtr => do
    let scReplies ← NonDet.liftM SchedContext.scReplies (getSchedContext scPtr)
    -- The reply only refers to the scheduling context if it is at the head
    -- of the reply queue.
    let replySc ← getReplyObjRef Reply.replySc rptr
    NonDet.assert (if the scReplies.head? = rptr then replySc = some scPtr else replySc = none)
    -- Drop this reply and all subsequent replies from the call stack. All the
    -- associated caller threads become stuck.
    updateSchedContext scPtr (scRepliesUpdate (List.takeWhile fun r => decide (r ≠ rptr)))
    -- A no-op if the reply is not at the head of the queue.
    setReplyObjRef replyScUpdate rptr none
  -- This leaves the caller thread Inactive.
  replyUnlinkTcb tptr rptr

/-- l4v: IpcCancel_A.no_reply_in_ts. -/
def noReplyInTs (tptr : ObjRef) : SMonad Z Bool := do
  let st ← getThreadState tptr
  match st with
  | .blockedOnReceive _ r _ => return decide (r = none)
  | .blockedOnReply _ => return false
  | _ => return true

/-- l4v: IpcCancel_A.bind_sc_reply. -/
def bindScReply (scPtr replyPtr : ObjRef) : SMonad Z Unit := do
  let scReplies ← NonDet.liftM SchedContext.scReplies (getSchedContext scPtr)
  -- unlink head reply and sc before pushing
  match scReplies with
  | [] => pure ()
  | r :: _ => setReplyObjRef replyScUpdate r none
  -- push new head reply
  setScObjRef scRepliesUpdate scPtr (replyPtr :: scReplies)
  -- link new head reply to sc
  setReplyObjRef replyScUpdate replyPtr (some scPtr)

/-- l4v: IpcCancel_A.reply_push: push a reply object onto the call stack. -/
def replyPush (caller callee replyPtr : ObjRef) (canDonate : Bool) : SMonad Z Unit := do
  let scCaller ← getTcbObjRef Tcb.tcbSchedContext caller
  let scCallee ← getTcbObjRef Tcb.tcbSchedContext callee
  -- link reply and tcb
  setReplyObjRef replyTcbUpdate replyPtr (some caller)
  setThreadState caller (.blockedOnReply replyPtr)
  NonDet.when (scCaller ≠ none ∧ scCallee = none ∧ canDonate) <| do
    bindScReply (the scCaller) replyPtr
    schedContextDonate (the scCaller) callee

end

/-! ## Endpoint and notification queues -/

/-- l4v: IpcCancel_A.update_ep_queue. -/
def updateEpQueue : Endpoint → List ObjRef → Bool → Endpoint
  | .recvEP _, q', _ => .recvEP q'
  | .sendEP _, q', _ => .sendEP q'
  | .idleEP, q', isRecv => if isRecv then .recvEP q' else .sendEP q'

/-- l4v: IpcCancel_A.ntfn_queue_of (`abbreviation`). -/
abbrev ntfnQueueOf (notification : Notification) : List ObjRef := notification.ntfnObj.ntfnQueue

/-- l4v: IpcCancel_A.update_ntfn_queue (`primrec (nonexhaustive)`). -/
def updateNtfnQueue : Ntfn → List ObjRef → Ntfn
  | .waitingNtfn _, q' => .waitingNtfn q'
  | _, _ => undefined

/-- l4v: IpcCancel_A.ep_blocked: the endpoint a thread is blocked on. -/
def epBlocked (ts : ThreadState) : Option ObjRef :=
  match ts with
  | .blockedOnReceive r _ _ => some r
  | .blockedOnSend r _ => some r
  | _ => none

/-- l4v: IpcCancel_A.ntfn_blocked: the notification a thread is blocked on. -/
def ntfnBlocked (ts : ThreadState) : Option ObjRef :=
  match ts with
  | .blockedOnNotification r => some r
  | _ => none

/-- Isabelle list `removeAll x xs` (`filter (λy. x ≠ y) xs`). -/
def removeAll {α : Type} [DecidableEq α] (x : α) (xs : List α) : List α := xs.filter fun y => x ≠ y

section
variable {Z : Type} [StateExt Z]

/-- l4v: IpcCancel_A.tcb_ep_dequeue. -/
def tcbEpDequeue (tptr epPtr : ObjRef) : SMonad Z Unit := do
  let ep ← getEndpoint epPtr
  let q ← pure ep.epQueue
  NonDet.assert (tptr ∈ q)
  let q' ← pure (removeAll tptr q)
  let ep' ← pure (match q' with
    | [] => Endpoint.idleEP
    | _ => updateEpQueue ep q' true)
  setEndpoint epPtr ep'

/-- l4v: IpcCancel_A.tcb_ntfn_dequeue. -/
def tcbNtfnDequeue (tptr ntfnPtr : ObjRef) : SMonad Z Unit := do
  let notification ← getNotification ntfnPtr
  let q ← pure (ntfnQueueOf notification)
  NonDet.assert (tptr ∈ q)
  let q' ← pure (removeAll tptr q)
  let notification' ← pure (ntfnObjUpdate (fun _ => match q' with
      | [] => Ntfn.idleNtfn
      | _ => Ntfn.waitingNtfn q')
    notification)
  setNotification ntfnPtr notification'

/-- l4v: IpcCancel_A.ordered_insert: insert `t` into `ts`, which is sorted
by the values of `f` in the order `R`. -/
def orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Z β)
    (R : β → β → Prop) : SMonad Z (List α) := do
  let val ← NonDet.getsThe (f t)
  let vals ← NonDet.mapM (fun t' => NonDet.getsThe (f t')) ts
  let zip ← pure (ts.zip vals)
  let zip' ← pure (zip.takeWhile (fun (_, val') => decide (R val' val))
                   ++ [(t, val)]
                   ++ zip.dropWhile (fun (_, val') => decide (R val' val)))
  return zip'.map Prod.fst

/-- l4v: IpcCancel_A.tcb_append. -/
def tcbAppend (tptr : ObjRef) (qs : List ObjRef) : SMonad Z (List ObjRef) :=
  orderedInsert tptr qs (threadRead Tcb.tcbPriority) (· ≥ ·)

/-- l4v: IpcCancel_A.tcb_ep_append. -/
def tcbEpAppend (tptr epPtr : ObjRef) (isRecv : Bool) : SMonad Z Unit := do
  let ep ← getEndpoint epPtr
  let q ← pure ep.epQueue
  let q' ← tcbAppend tptr q
  setEndpoint epPtr (updateEpQueue ep q' isRecv)

/-- l4v: IpcCancel_A.tcb_ntfn_append. -/
def tcbNtfnAppend (tptr ntfnPtr : ObjRef) : SMonad Z Unit := do
  let notification ← getNotification ntfnPtr
  let qs ← pure (ntfnQueueOf notification)
  let qs' ← tcbAppend tptr qs
  setNotification ntfnPtr { notification with ntfnObj := .waitingNtfn qs' }

/-- l4v: IpcCancel_A.reorder_ep: bring an endpoint queue back into priority
order. -/
def reorderEp (epPtr tptr : ObjRef) : SMonad Z Unit := do
  let ep ← getEndpoint epPtr
  NonDet.assert (ep ≠ .idleEP)
  let qs ← pure ep.epQueue
  NonDet.assert (qs ≠ [])
  let qs' ← pure (removeAll tptr qs)
  let qs'' ← tcbAppend tptr qs'
  setEndpoint epPtr (updateEpQueue ep qs'' true)

end

/-- Isabelle datatype discriminator `is_WaitingNtfn`. -/
def Ntfn.isWaitingNtfn : Ntfn → Bool
  | .waitingNtfn _ => true
  | _ => false

section
variable {Z : Type} [StateExt Z]

/-- l4v: IpcCancel_A.reorder_ntfn: bring a notification queue back into
priority order. -/
def reorderNtfn (ntfnPtr tptr : ObjRef) : SMonad Z Unit := do
  let ntfn ← getNotification ntfnPtr
  NonDet.assert (ntfn.ntfnObj.isWaitingNtfn = true)
  let qs ← pure (ntfnQueueOf ntfn)
  NonDet.assert (qs ≠ [])
  let qs' ← pure (removeAll tptr qs)
  let qs'' ← tcbAppend tptr qs'
  setNotification ntfnPtr { ntfn with ntfnObj := .waitingNtfn qs'' }

/-- l4v: IpcCancel_A.set_priority: set a new priority for a TCB. -/
def setPriority (tptr : ObjRef) (prio : Priority) : SMonad Z Unit := do
  let ts ← getThreadState tptr
  if runnable ts then do
    let d ← threadGet Tcb.tcbDomain tptr
    let p ← threadGet Tcb.tcbPriority tptr
    let queue ← getTcbQueue d p
    let cur ← NonDet.gets fun s : State Z => s.curThread
    if tptr ∈ queue ∨ tptr = cur then do
      tcbSchedAction tcbSchedDequeue tptr
      threadSetPriority tptr prio
      tcbSchedAction tcbSchedEnqueue tptr
      rescheduleRequired
    else
      threadSetPriority tptr prio
  else do
    threadSetPriority tptr prio
    NonDet.maybeM (fun ep => reorderEp ep tptr) (epBlocked ts)
    NonDet.maybeM (fun ntfn => reorderNtfn ntfn tptr) (ntfnBlocked ts)

/-- l4v: IpcCancel_A.restart_thread_if_no_fault. -/
def restartThreadIfNoFault (t : ObjRef) : SMonad Z Unit := do
  let fault ← threadGet Tcb.tcbFault t
  if fault = none
  then do
    setThreadState t .restart
    let scOpt ← getTcbObjRef Tcb.tcbSchedContext t
    ifSporadicCurScAssertRefillUnblockCheck scOpt
    possibleSwitchTo t
  else setThreadState t .inactive

/-- l4v: IpcCancel_A.remove_and_restart_ep_queued_thread. -/
def removeAndRestartEpQueuedThread (t epptr : ObjRef) : SMonad Z Unit := do
  tcbEpDequeue t epptr
  let st ← getThreadState t
  let replyOpt ← pure (if isBlockedOnReceive st then replyObject st else none)
  NonDet.maybeM (replyUnlinkTcb t) replyOpt
  restartThreadIfNoFault t

/-- l4v: IpcCancel_A.cancel_all_ipc: cancel all message operations of the
threads queued on an endpoint; they restart and reattempt the operation. -/
def cancelAllIpc (epptr : ObjRef) : SMonad Z Unit := do
  let ep ← getEndpoint epptr
  match ep with
  | .idleEP => return ()
  | _ => do
    let queue ← pure ep.epQueue
    NonDet.mapMx (fun t => removeAndRestartEpQueuedThread t epptr) queue
    rescheduleRequired

end

/-- l4v: IpcCancel_A.blocking_ipc_badge (`primrec (nonexhaustive)`): the badge
of a thread waiting to send. -/
def blockingIpcBadge : ThreadState → Badge
  | .blockedOnSend _ payload => payload.senderBadge
  | _ => undefined

section
variable {Z : Type} [StateExt Z]

/-- l4v: IpcCancel_A.remove_and_restart_badged_thread. -/
def removeAndRestartBadgedThread (t epptr : ObjRef) (badge : Badge) : SMonad Z Unit := do
  let st ← getThreadState t
  NonDet.when (blockingIpcBadge st = badge) (do
    tcbEpDequeue t epptr
    restartThreadIfNoFault t)

/-- l4v: IpcCancel_A.cancel_badged_sends: cancel the sends queued on an
endpoint with a given badge. -/
def cancelBadgedSends (epptr : ObjRef) (badge : Badge) : SMonad Z Unit := do
  let ep ← getEndpoint epptr
  match ep with
  | .sendEP queue => do
      NonDet.mapMx (fun t => removeAndRestartBadgedThread t epptr badge) queue
      rescheduleRequired
  | _ => return ()

/-- l4v: IpcCancel_A.do_unbind_notification (`abbreviation`). -/
abbrev doUnbindNotification (ntfnptr tcbptr : ObjRef) : SMonad Z Unit := do
  setNtfnObjRef ntfnBoundTcbUpdate ntfnptr none
  setTcbObjRef tcbBoundNotificationUpdate tcbptr none

/-- l4v: IpcCancel_A.unbind_notification. -/
def unbindNotification (tcb : ObjRef) : SMonad Z Unit := do
  let ntfnptr ← getTcbObjRef Tcb.tcbBoundNotification tcb
  NonDet.maybeM (fun nptr => doUnbindNotification nptr tcb) ntfnptr

/-- l4v: IpcCancel_A.unbind_maybe_notification. -/
def unbindMaybeNotification (ntfnptr : ObjRef) : SMonad Z Unit := do
  let tptr ← getNtfnObjRef Notification.ntfnBoundTcb ntfnptr
  NonDet.maybeM (fun t => doUnbindNotification ntfnptr t) tptr

/-- l4v: IpcCancel_A.remove_and_restart_ntfn_queued_thread. -/
def removeAndRestartNtfnQueuedThread (t ntfnptr : ObjRef) : SMonad Z Unit := do
  tcbNtfnDequeue t ntfnptr
  setThreadState t .restart
  let scOpt ← getTcbObjRef Tcb.tcbSchedContext t
  ifSporadicCurScAssertRefillUnblockCheck scOpt
  possibleSwitchTo t

/-- l4v: IpcCancel_A.cancel_all_signals: cancel the waits queued on a
notification. -/
def cancelAllSignals (ntfnptr : ObjRef) : SMonad Z Unit := do
  let ntfn ← getNotification ntfnptr
  match ntfn.ntfnObj with
  | .waitingNtfn queue => do
      NonDet.mapMx (fun t => removeAndRestartNtfnQueuedThread t ntfnptr) queue
      rescheduleRequired
  | _ => return ()

/-- l4v: IpcCancel_A.get_blocking_object: the endpoint of a thread waiting
for a transfer in either direction. -/
def getBlockingObject (state : ThreadState) : SMonad Z ObjRef := NonDet.assertOpt (epBlocked state)

/-- l4v: IpcCancel_A.blocked_cancel_ipc. -/
def blockedCancelIpc (state : ThreadState) (tptr : ObjRef) (replyOpt : Option ObjRef) :
    SMonad Z Unit := do
  let epptr ← getBlockingObject state
  tcbEpDequeue tptr epptr
  match replyOpt with
  | none => pure ()
  | some r => replyUnlinkTcb tptr r
  setThreadState tptr .inactive

/-- l4v: IpcCancel_A.sched_context_unbind_all_tcbs: unbind the TCB, if there
is one (l4v: "FIXME RT: remove check on whether sc_ptr ~= idle_sc_ptr",
VER-1413). -/
def schedContextUnbindAllTcbs (scPtr : ObjRef) : SMonad Z Unit := do
  let sc ← getSchedContext scPtr
  let isc ← NonDet.gets fun s : State Z => s.idleSc
  NonDet.when (sc.scTcb ≠ none ∧ scPtr ≠ isc) <| schedContextUnbindTcb scPtr

end

/-- l4v: IpcCancel_A.cap_irq_opt. -/
def capIrqOpt (cap : Cap) : Option Irq :=
  match cap with
  | .irqHandlerCap irq => some irq
  | _ => none

/-- l4v: IpcCancel_A.cap_irqs (`set_option`). -/
def capIrqs (cap : Cap) : Set Irq := {irq | capIrqOpt cap = some irq}

/-- l4v: IpcCancel_A.gen_obj_ref: a generic reference to an object, used in
finalisation to decide whether caps refer to the same object. -/
inductive GenObjRef where
  | objRef (r : ObjRef)
  | iRQRef (irq : Irq)
  | archRef (r : ArchGenObjRef)
deriving DecidableEq, Repr, Inhabited

/-- l4v: IpcCancel_A.arch_cap_set_map. -/
def archCapSetMap {α : Type} (f : ArchCap → Set α) (cap : Cap) : Set α :=
  match cap with
  | .archObjectCap acap => f acap
  | _ => ∅

/-- l4v: IpcCancel_A.arch_gen_refs (`abbreviation`). -/
abbrev archGenRefs : Cap → Set ArchGenObjRef := archCapSetMap archGenObjRefs

/-- l4v: IpcCancel_A.gen_obj_refs. -/
def genObjRefs (c : Cap) : Set GenObjRef :=
  GenObjRef.objRef '' objRefs c ∪ GenObjRef.iRQRef '' capIrqs c ∪ GenObjRef.archRef '' archGenRefs c

/-- l4v: IpcCancel_A.cap_cleanup_opt. -/
def capCleanupOpt (c : Cap) : Cap :=
  match c with
  | .irqHandlerCap _ => c
  | .archObjectCap acap => archCapCleanupOpt acap
  | _ => .nullCap

/-- l4v: IpcCancel_A.is_final_cap': whether the cap is the last one to its
object in the system. -/
def isFinalCap' {Z : Type} [StateExt Z] (cap : Cap) (s : State Z) : Prop :=
  ∃ cref, {cref | ∃ cap', ((getCap cref : SMonad Z Cap) s).1 = {(cap', s)} ∧
    genObjRefs cap ∩ genObjRefs cap' ≠ ∅} = {cref}

section
variable {Z : Type} [StateExt Z]

/-- l4v: IpcCancel_A.is_final_cap. -/
def isFinalCap (cap : Cap) : SMonad Z Bool := NonDet.gets fun s => decide (isFinalCap' cap s)

/-- l4v: IpcCancel_A.deleted_irq_handler: after an IRQ handler cap is
deleted. -/
def deletedIrqHandler (irq : Irq) : SMonad Z Unit := setIrqState .irqInactive irq

/-- l4v: IpcCancel_A.post_cap_deletion: after a cap is deleted. -/
def postCapDeletion (cap : Cap) : SMonad Z Unit :=
  match cap with
  | .irqHandlerCap irq => deletedIrqHandler irq
  | .archObjectCap acap => archPostCapDeletion acap
  | _ => return ()

/-- l4v: IpcCancel_A.empty_slot: empty a slot whose cap is already
finalised. -/
def emptySlot (slot : CslotPtr) (cleanupInfo : Cap) : SMonad Z Unit := do
  let cap ← getCap slot
  if cap = .nullCap then
    return ()
  else do
    let slotP ← NonDet.gets fun s : State Z => s.cdt slot
    let cdt ← NonDet.gets fun s : State Z => s.cdt
    let parent ← pure (cdt slot)
    setCdt (Function.update (fun p => if cdt p = some slot then parent else cdt p) slot none)
    doExtendedOp (emptySlotExt slot slotP)
    setOriginal slot false
    setCap .nullCap slot
    postCapDeletion cleanupInfo

/-- l4v: IpcCancel_A.cancel_signal: cancel a thread's wait on a
notification. -/
def cancelSignal (threadptr ntfnptr : ObjRef) : SMonad Z Unit := do
  tcbNtfnDequeue threadptr ntfnptr
  setThreadState threadptr .inactive

/-- l4v: IpcCancel_A.cancel_ipc: cancel any message operation a thread is
waiting on. -/
def cancelIpc (tptr : ObjRef) : SMonad Z Unit := do
  let state ← getThreadState tptr
  threadSet (fun tcb => { tcb with tcbFault := none }) tptr
  match state with
  | .blockedOnSend _ _ => blockedCancelIpc state tptr none
  | .blockedOnReceive _ reply _ => blockedCancelIpc state tptr reply
  | .blockedOnNotification event => cancelSignal tptr event
  | .blockedOnReply reply => replyRemoveTcb tptr reply
  | _ => return ()

end

end

end Fl4Spec
