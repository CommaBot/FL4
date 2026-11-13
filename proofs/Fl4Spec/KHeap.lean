/-
Access to the kernel heap and the scheduler state (MCS).

Ports, in theory order:
- `spec/abstract/KHeap_A`;
- `spec/abstract/X64/ArchVSpaceAcc_A` (the VT-d accessors there are
  commented out in l4v, `FIXME x64-vtd`, and not ported: no IOMMU).

KHeap_A's lemmas (`tcb_of_Some`, `proj_inj_ep`, ...) are not ported.
-/
import Fl4Spec.Deterministic

namespace Fl4Spec

open Classical

noncomputable section

/-! ## Projections from the kernel heap -/

/-- l4v: KHeap_A.tcb_of. -/
def tcbOf (ko : KernelObject) : Option Tcb :=
  match ko with
  | .tcb tcb => some tcb
  | _ => none

/-- l4v: KHeap_A.tcbs_of_kh. -/
def tcbsOfKh {R : Type} (kh : R → Option KernelObject) : R → Option Tcb := optMap kh tcbOf

/-- l4v: KHeap_A.tcbs_of (`abbreviation`). -/
abbrev tcbsOf {Z : Type} (s : State Z) : ObjRef → Option Tcb := tcbsOfKh s.kheap

/-- l4v: KHeap_A.sc_fields_of. -/
def scFieldsOf (ko : KernelObject) : Option (SchedContext × Nat) :=
  match ko with
  | .schedContext sc n => some (sc, n)
  | _ => none

/-- l4v: KHeap_A.scs_fields_of (`abbreviation`). -/
abbrev scsFieldsOf {Z : Type} (s : State Z) : ObjRef → Option (SchedContext × Nat) :=
  optMap s.kheap scFieldsOf

/-- l4v: KHeap_A.sc_of. -/
def scOf (ko : KernelObject) : Option SchedContext :=
  match ko with
  | .schedContext sc _ => some sc
  | _ => none

/-- l4v: KHeap_A.scs_of_kh. -/
def scsOfKh {R : Type} (kh : R → Option KernelObject) : R → Option SchedContext := optMap kh scOf

/-- l4v: KHeap_A.scs_of (`abbreviation`). -/
abbrev scsOf {Z : Type} (s : State Z) : ObjRef → Option SchedContext := scsOfKh s.kheap

/-- l4v: KHeap_A.sc_sizes_of (`abbreviation`). -/
abbrev scSizesOf {Z : Type} (s : State Z) : ObjRef → Option Nat := optMapSome (scsFieldsOf s) Prod.snd

/-- l4v: KHeap_A.cnode_of. -/
def cnodeOf (ko : KernelObject) : Option (Nat × CnodeContents) :=
  match ko with
  | .cnode sz cnode => some (sz, cnode)
  | _ => none

/-- l4v: KHeap_A.cnodes_of (`abbreviation`). -/
abbrev cnodesOf {Z : Type} (s : State Z) : ObjRef → Option (Nat × CnodeContents) :=
  optMap s.kheap cnodeOf

/-- l4v: KHeap_A.cnode_sizes_of (`abbreviation`). -/
abbrev cnodeSizesOf {Z : Type} (s : State Z) : ObjRef → Option Nat := optMapSome (cnodesOf s) Prod.fst

/-- l4v: KHeap_A.cnode_contents_of (`abbreviation`). -/
abbrev cnodeContentsOf {Z : Type} (s : State Z) : ObjRef → Option CnodeContents :=
  optMapSome (cnodesOf s) Prod.snd

/-! ## General object access -/

/-- l4v: KHeap_A.r_monad: the kernel reader option monad. -/
abbrev RMonad (Z α : Type) := Lookup (State Z) α

section
variable {Z : Type} [StateExt Z]

/-- l4v: KHeap_A.read_object. -/
def readObject (ptr : ObjRef) : RMonad Z KernelObject := fun s => s.kheap ptr

/-- l4v: KHeap_A.get_object. -/
def getObject (ptr : ObjRef) : SMonad Z KernelObject := NonDet.getsThe (readObject ptr)

/-- l4v: KHeap_A.set_object. -/
def setObject (ptr : ObjRef) (obj : KernelObject) : SMonad Z Unit := do
  let kobj ← getObject ptr
  NonDet.assert (aType kobj = aType obj)
  let s ← NonDet.get
  NonDet.put { s with kheap := Function.update s.kheap ptr (some obj) }

/-! ## TCBs -/

/-- l4v: KHeap_A.get_tcb. -/
def getTcb (tcbRef : ObjRef) : RMonad Z Tcb := fun state =>
  match readObject tcbRef state with
  | none => none
  | some kobj => match kobj with
    | .tcb tcb => some tcb
    | _ => none

/-- l4v: KHeap_A.thread_read. -/
def threadRead {α : Type} (f : Tcb → α) (tptr : ObjRef) : RMonad Z α :=
  Lookup.oliftM f (getTcb tptr)

/-- l4v: KHeap_A.thread_get. -/
def threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : SMonad Z α := do
  let tcb ← NonDet.getsThe (getTcb tptr)
  return f tcb

/-- l4v: KHeap_A.thread_set. -/
def threadSet (f : Tcb → Tcb) (tptr : ObjRef) : SMonad Z Unit := do
  let tcb ← NonDet.getsThe (getTcb tptr)
  setObject tptr (.tcb (f tcb))

/-- l4v: KHeap_A.arch_thread_get. -/
def archThreadGet {α : Type} (f : ArchTcb → α) (tptr : ObjRef) : SMonad Z α := do
  let tcb ← NonDet.getsThe (getTcb tptr)
  return f tcb.tcbArch

/-- l4v: KHeap_A.arch_thread_set. -/
def archThreadSet (f : ArchTcb → ArchTcb) (tptr : ObjRef) : SMonad Z Unit := do
  let tcb ← NonDet.getsThe (getTcb tptr)
  setObject tptr (.tcb { tcb with tcbArch := f tcb.tcbArch })

/-- l4v: KHeap_A.read_thread_state. -/
def readThreadState (ref : ObjRef) : RMonad Z ThreadState := threadRead Tcb.tcbState ref

/-- l4v: KHeap_A.get_thread_state. -/
def getThreadState (ref : ObjRef) : SMonad Z ThreadState := threadGet Tcb.tcbState ref

/-- l4v: KHeap_A.read_tcb_obj_ref. -/
def readTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : RMonad Z (Option ObjRef) :=
  threadRead f ref

/-- l4v: KHeap_A.get_tcb_obj_ref. -/
def getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : SMonad Z (Option ObjRef) :=
  threadGet f ref

/-- l4v: KHeap_A.set_tcb_obj_ref (`abbreviation (input)`): `f` is a record
field update such as `tcb_sched_context_update`. -/
abbrev setTcbObjRef (f : (Option ObjRef → Option ObjRef) → Tcb → Tcb) (ref : ObjRef)
    (new : Option ObjRef) : SMonad Z Unit :=
  threadSet (f fun _ => new) ref

/-! ## Simple kernel objects (endpoints, notifications, replies) -/

/-- l4v: KHeap_A.is_simple_type (`abbreviation`). -/
abbrev isSimpleType (ob : KernelObject) : Prop := aType ob ∈ ({.aEndpoint, .aNTFN, .aReply} : Set AType)

/-- l4v: KHeap_A.get_simple_ko. -/
def getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) : SMonad Z α := do
  let kobj ← getObject ptr
  NonDet.assert (isSimpleType kobj)
  match partialInv f kobj with
  | some e => return e
  | _ => NonDet.fail

/-- l4v: KHeap_A.set_simple_ko. -/
def setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (ptr : ObjRef) (ep : α) :
    SMonad Z Unit := do
  let obj ← getObject ptr
  NonDet.assert (isSimpleType obj)
  NonDet.assert (partialInv f obj ≠ none)
  setObject ptr (f ep)

/-- l4v: KHeap_A.get_endpoint (`abbreviation`). -/
abbrev getEndpoint : ObjRef → SMonad Z Endpoint := getSimpleKo KernelObject.endpoint
/-- l4v: KHeap_A.set_endpoint (`abbreviation`). -/
abbrev setEndpoint : ObjRef → Endpoint → SMonad Z Unit := setSimpleKo KernelObject.endpoint
/-- l4v: KHeap_A.get_notification (`abbreviation`). -/
abbrev getNotification : ObjRef → SMonad Z Notification := getSimpleKo KernelObject.notification
/-- l4v: KHeap_A.set_notification (`abbreviation`). -/
abbrev setNotification : ObjRef → Notification → SMonad Z Unit :=
  setSimpleKo KernelObject.notification

end

/-- l4v: KHeap_A.ntfn_set_bound_tcb (`abbreviation`). -/
abbrev ntfnSetBoundTcb (ntfn : Notification) (t : Option ObjRef) : Notification :=
  { ntfn with ntfnBoundTcb := t }

/-- l4v: KHeap_A.ntfn_set_obj (`abbreviation`). -/
abbrev ntfnSetObj (ntfn : Notification) (a : Ntfn) : Notification := { ntfn with ntfnObj := a }

section
variable {Z : Type} [StateExt Z]

/-! ## IRQ state and slot -/

/-- l4v: KHeap_A.get_irq_state. -/
def getIrqState (irq : Irq) : SMonad Z IrqState := NonDet.gets fun s => s.interruptStates irq

/-- l4v: KHeap_A.set_irq_state. -/
def setIrqState (state : IrqState) (irq : Irq) : SMonad Z Unit := do
  NonDet.modify fun s => { s with interruptStates := Function.update s.interruptStates irq state }
  doMachineOp (maskInterrupt (state = .irqInactive) irq)

/-- l4v: KHeap_A.get_irq_slot. -/
def getIrqSlot (irq : Irq) : SMonad Z CslotPtr := NonDet.gets fun st => (st.interruptIrqNode irq, [])

/-! ## Reply objects -/

/-- l4v: KHeap_A.get_reply (`abbreviation`). -/
abbrev getReply : ObjRef → SMonad Z Reply := getSimpleKo KernelObject.reply
/-- l4v: KHeap_A.set_reply (`abbreviation`). -/
abbrev setReply : ObjRef → Reply → SMonad Z Unit := setSimpleKo KernelObject.reply

/-- l4v: KHeap_A.get_reply_tcb (`abbreviation`). -/
abbrev getReplyTcb (r : ObjRef) : SMonad Z (Option ObjRef) := NonDet.liftM Reply.replyTcb (getReply r)

/-! ## Scheduling contexts -/

/-- l4v: KHeap_A.read_sched_context. -/
def readSchedContext (ptr : ObjRef) : RMonad Z SchedContext := do
  let kobj ← readObject ptr
  match kobj with
  | .schedContext sc _ => Lookup.oreturn sc
  | _ => Lookup.ofail

/-- l4v: KHeap_A.get_sched_context. -/
def getSchedContext (ptr : ObjRef) : SMonad Z SchedContext := do
  let kobj ← getObject ptr
  match kobj with
  | .schedContext sc _ => return sc
  | _ => NonDet.fail

/-- l4v: KHeap_A.read_sc_obj_ref. -/
def readScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : RMonad Z (Option ObjRef) :=
  Lookup.oliftM f (readSchedContext ref)

/-- l4v: KHeap_A.get_sc_obj_ref. -/
def getScObjRef (f : SchedContext → Option ObjRef) (ref : ObjRef) : SMonad Z (Option ObjRef) := do
  let sc ← getSchedContext ref
  return f sc

/-- l4v: KHeap_A.set_sched_context (`abbreviation`). -/
abbrev setSchedContext (ptr : ObjRef) (sc : SchedContext) (n : Nat) : SMonad Z Unit :=
  setObject ptr (.schedContext sc n)

/-- l4v: KHeap_A.update_sched_context: update the scheduling context in
place, keeping its size. -/
def updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : SMonad Z Unit := do
  let obj ← getObject ptr
  match obj with
  | .schedContext sc n => setSchedContext ptr (f sc) n
  | _ => NonDet.fail

/-- l4v: KHeap_A.set_sc_obj_ref (`abbreviation`): `f` is a record field
update such as `sc_tcb_update`. -/
abbrev setScObjRef {α : Type} (f : (α → α) → SchedContext → SchedContext) (ref : ObjRef) (new : α) :
    SMonad Z Unit :=
  updateSchedContext ref (f fun _ => new)

end

/-- l4v: KHeap_A.active_sc. -/
def activeSc (refillMax : Nat) : Bool := decide (0 < refillMax)

/-- l4v: KHeap_A.sc_active (`abbreviation`). -/
abbrev scActive (sc : SchedContext) : Bool := activeSc sc.scRefillMax

section
variable {Z : Type} [StateExt Z]

/-- l4v: KHeap_A.read_sc_active. -/
def readScActive (scPtr : ObjRef) : RMonad Z Bool := do
  let sc ← readSchedContext scPtr
  Lookup.oreturn (scActive sc)

/-- l4v: KHeap_A.get_sc_active. -/
def getScActive (scPtr : ObjRef) : SMonad Z Bool := NonDet.getsThe (readScActive scPtr)

/-- l4v: KHeap_A.in_release_queue. -/
def inReleaseQueue (tcbPtr : ObjRef) : State Z → Bool := fun s => decide (tcbPtr ∈ s.releaseQueue)

/-- l4v: KHeap_A.schedulable. -/
def schedulable (t : ObjRef) (s : State Z) : Bool :=
  decide (optPred (fun st => runnable st = true) (optMapSome (tcbsOf s) Tcb.tcbState) t
    ∧ optPred (fun sc => scActive sc = true)
        (optMap (optMap (tcbsOf s) Tcb.tcbSchedContext) (scsOf s)) t
    ∧ t ∉ s.releaseQueue)

/-- l4v: KHeap_A.ct_schedulable (`abbreviation`). -/
abbrev ctSchedulable (s : State Z) : Bool := schedulable s.curThread s

end

/-! ## Refill checks -/

/-- l4v: KHeap_A.refill_hd (`abbreviation`, `hd (sc_refills sc)`). -/
abbrev refillHd (sc : SchedContext) : Refill := the sc.scRefills.head?

/-- l4v: KHeap_A.refill_tl (`abbreviation`, `last (sc_refills sc)`). -/
abbrev refillTl (sc : SchedContext) : Refill := the sc.scRefills.getLast?

section
variable {Z : Type} [StateExt Z]

/-- l4v: KHeap_A.get_refills. -/
def getRefills (scPtr : ObjRef) : SMonad Z (List Refill) := do
  let sc ← getSchedContext scPtr
  return sc.scRefills

/-- l4v: KHeap_A.read_refill_head. -/
def readRefillHead (scPtr : ObjRef) : RMonad Z Refill := do
  let sc ← readSchedContext scPtr
  Lookup.oassert (sc.scRefills ≠ [])
  Lookup.oreturn (refillHd sc)

/-- l4v: KHeap_A.get_refill_head. -/
def getRefillHead (scPtr : ObjRef) : SMonad Z Refill := NonDet.getsThe (readRefillHead scPtr)

/-- l4v: KHeap_A.read_refill_tail. -/
def readRefillTail (scPtr : ObjRef) : RMonad Z Refill := do
  let sc ← readSchedContext scPtr
  Lookup.oassert (sc.scRefills ≠ [])
  Lookup.oreturn (refillTl sc)

/-- l4v: KHeap_A.get_refill_tail. -/
def getRefillTail (scPtr : ObjRef) : SMonad Z Refill := NonDet.getsThe (readRefillTail scPtr)

end

/-- l4v: KHeap_A.refill_capacity. -/
def refillCapacity (usage : Time) (refill : Refill) : Time :=
  if refill.rAmount < usage then 0 else refill.rAmount - usage

section
variable {Z : Type} [StateExt Z]

/-- l4v: KHeap_A.read_sc_refill_capacity. -/
def readScRefillCapacity (scPtr : ObjRef) (usage : Ticks) : RMonad Z Ticks := do
  let refillHead ← readRefillHead scPtr
  Lookup.oreturn (refillCapacity usage refillHead)

/-- l4v: KHeap_A.get_sc_refill_capacity. -/
def getScRefillCapacity (scPtr : ObjRef) (usage : Ticks) : SMonad Z Ticks :=
  NonDet.getsThe (readScRefillCapacity scPtr usage)

end

/-- l4v: KHeap_A.refill_sufficient. -/
def refillSufficient (usage : Time) (refill : Refill) : Bool :=
  decide (MIN_BUDGET ≤ refillCapacity usage refill)

section
variable {Z : Type} [StateExt Z]

/-- l4v: KHeap_A.read_sc_refill_sufficient. -/
def readScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : RMonad Z Bool := do
  let head ← readRefillHead scPtr
  Lookup.oreturn (refillSufficient usage head)

/-- l4v: KHeap_A.get_sc_refill_sufficient. -/
def getScRefillSufficient (scPtr : ObjRef) (usage : Ticks) : SMonad Z Bool :=
  NonDet.getsThe (readScRefillSufficient scPtr usage)

end

/-- l4v: KHeap_A.refill_ready'. -/
def refillReady' (usage curtime : Time) (refill : Refill) : Bool :=
  decide (refill.rTime + usage ≤ curtime)

/-- l4v: KHeap_A.refill_ready (`abbreviation`). -/
abbrev refillReady : Time → Refill → Bool := refillReady' 0

section
variable {Z : Type} [StateExt Z]

/-- l4v: KHeap_A.read_sc_refill_ready. -/
def readScRefillReady (scPtr : ObjRef) : RMonad Z Bool := do
  let refillHead ← readRefillHead scPtr
  let curTime ← Lookup.asks fun s : State Z => s.curTime
  Lookup.oreturn (refillReady curTime refillHead)

/-- l4v: KHeap_A.get_sc_refill_ready. -/
def getScRefillReady (scPtr : ObjRef) : SMonad Z Bool := NonDet.getsThe (readScRefillReady scPtr)

end

/-- l4v: KHeap_A.sc_released. -/
def scReleased (curtime : Time) (sc : SchedContext) : Bool :=
  scActive sc && refillReady curtime (refillHd sc)

section
variable {Z : Type} [StateExt Z]

/-- l4v: KHeap_A.read_sc_released. -/
def readScReleased (scPtr : ObjRef) : RMonad Z Bool := do
  let active ← readScActive scPtr
  if active then readScRefillReady scPtr else Lookup.oreturn false

/-- l4v: KHeap_A.get_sc_released. -/
def getScReleased (scPtr : ObjRef) : SMonad Z Bool := NonDet.getsThe (readScReleased scPtr)

/-! ## Scheduler queues and actions -/

/-- l4v: KHeap_A.get_tcb_queue. -/
def getTcbQueue (d : Domain) (prio : Priority) : SMonad Z ReadyQueue := do
  let queues ← NonDet.gets fun s : State Z => s.readyQueues
  return queues d prio

/-- l4v: KHeap_A.set_tcb_queue. -/
def setTcbQueue (d : Domain) (prio : Priority) (queue : ReadyQueue) : SMonad Z Unit :=
  NonDet.modify fun es => { es with readyQueues :=
    fun d' p => if d' = d ∧ p = prio then queue else es.readyQueues d' p }

/-- l4v: KHeap_A.tcb_sched_action. -/
def tcbSchedAction (action : ObjRef → List ObjRef → List ObjRef) (thread : ObjRef) :
    SMonad Z Unit := do
  let d ← threadGet Tcb.tcbDomain thread
  let prio ← threadGet Tcb.tcbPriority thread
  let queue ← getTcbQueue d prio
  let queue' ← pure (action thread queue)
  setTcbQueue d prio queue'

/-- l4v: KHeap_A.is_blocked. -/
def isBlocked (thread : ObjRef) : SMonad Z Bool :=
  NonDet.liftM ipcQueuedThreadState (getThreadState thread)

end

/-- l4v: KHeap_A.tcb_sched_enqueue. -/
def tcbSchedEnqueue (thread : ObjRef) (queue : List ObjRef) : List ObjRef :=
  if thread ∉ queue then thread :: queue else queue

/-- l4v: KHeap_A.tcb_sched_append. -/
def tcbSchedAppend (thread : ObjRef) (queue : List ObjRef) : List ObjRef :=
  if thread ∉ queue then queue ++ [thread] else queue

/-- l4v: KHeap_A.tcb_sched_dequeue. -/
def tcbSchedDequeue (thread : ObjRef) (queue : List ObjRef) : List ObjRef :=
  queue.filter fun x => thread ≠ x

section
variable {Z : Type} [StateExt Z]

/-- l4v: KHeap_A.set_release_queue (`abbreviation`). -/
abbrev setReleaseQueue (queue : List ObjRef) : SMonad Z Unit :=
  NonDet.modify fun s => { s with releaseQueue := queue }

/-- l4v: KHeap_A.tcb_release_remove. -/
def tcbReleaseRemove (tcbPtr : ObjRef) : SMonad Z Unit := do
  let qs ← NonDet.gets fun s : State Z => s.releaseQueue
  NonDet.when (qs ≠ [] ∧ the qs.head? = tcbPtr) <|
    NonDet.modify fun s => { s with reprogramTimer := true }
  let qs' ← pure (tcbSchedDequeue tcbPtr qs)
  setReleaseQueue qs'

/-- l4v: KHeap_A.set_scheduler_action. -/
def setSchedulerAction (action : SchedulerAction) : SMonad Z Unit :=
  NonDet.modify fun es => { es with schedulerAction := action }

/-- l4v: KHeap_A.thread_set_priority. -/
def threadSetPriority (tptr : ObjRef) (prio : Priority) : SMonad Z Unit :=
  threadSet (fun tcb => { tcb with tcbPriority := prio }) tptr

/-- l4v: KHeap_A.thread_set_domain. -/
def threadSetDomain (tptr : ObjRef) (domain : Domain) : SMonad Z Unit :=
  threadSet (fun tcb => { tcb with tcbDomain := domain }) tptr

/-- l4v: KHeap_A.reschedule_required. -/
def rescheduleRequired : SMonad Z Unit := do
  let action ← NonDet.gets fun s : State Z => s.schedulerAction
  match action with
  | .switchThread t => do
      let sched ← NonDet.gets (schedulable t)
      NonDet.when sched <| do
        let scOpt ← threadGet Tcb.tcbSchedContext t
        let scp ← NonDet.assertOpt scOpt
        let sufficient ← getScRefillSufficient scp 0
        let ready ← getScRefillReady scp
        NonDet.assert (sufficient && ready)
        tcbSchedAction tcbSchedEnqueue t
  | _ => pure ()
  setSchedulerAction .chooseNewThread

/-- l4v: KHeap_A.possible_switch_to. -/
def possibleSwitchTo (target : ObjRef) : SMonad Z Unit := do
  let scOpt ← getTcbObjRef Tcb.tcbSchedContext target
  let inq ← NonDet.gets (inReleaseQueue target)
  NonDet.when (scOpt ≠ none ∧ ¬inq) <| do
    let curDom ← NonDet.gets fun s : State Z => s.curDomain
    let targetDom ← threadGet Tcb.tcbDomain target
    let action ← NonDet.gets fun s : State Z => s.schedulerAction
    -- not in release queue & active_sc
    if targetDom ≠ curDom then
      tcbSchedAction tcbSchedEnqueue target -- not in cur_domain
    else if action ≠ .resumeCurThread then do
      rescheduleRequired
      tcbSchedAction tcbSchedEnqueue target
    else setSchedulerAction (.switchThread target)

/-- l4v: KHeap_A.schedule_tcb. -/
def scheduleTcb (tcbPtr : ObjRef) : SMonad Z Unit := do
  let cur ← NonDet.gets fun s : State Z => s.curThread
  let schedAct ← NonDet.gets fun s : State Z => s.schedulerAction
  let schedulable ← NonDet.gets (schedulable tcbPtr)
  NonDet.when (tcbPtr = cur ∧ schedAct = .resumeCurThread ∧ ¬schedulable) rescheduleRequired

/-- l4v: KHeap_A.set_thread_state_act. -/
def setThreadStateAct (tcbPtr : ObjRef) : SMonad Z Unit := do
  let cur ← NonDet.gets fun s : State Z => s.curThread
  let schedAct ← NonDet.gets fun s : State Z => s.schedulerAction
  let schedulable ← NonDet.gets (schedulable tcbPtr)
  NonDet.when (tcbPtr = cur ∧ schedAct = .resumeCurThread ∧ ¬schedulable) <|
    setSchedulerAction .chooseNewThread

/-- l4v: KHeap_A.set_thread_state. -/
def setThreadState (ref : ObjRef) (ts : ThreadState) : SMonad Z Unit := do
  threadSet (fun tcb => { tcb with tcbState := ts }) ref
  setThreadStateAct ref

/-- l4v: KHeap_A.set_mcpriority. -/
def setMcpriority (ref : ObjRef) (mcp : Priority) : SMonad Z Unit :=
  threadSet (fun tcb => { tcb with tcbMcpriority := mcp }) ref

/-! ## `obj_ref` fields of notifications, scheduling contexts and replies -/

/-- l4v: KHeap_A.get_sk_obj_ref. -/
def getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef)
    (ref : ObjRef) : SMonad Z (Option ObjRef) := do
  let sc ← getSimpleKo C ref
  return f sc

/-- l4v: KHeap_A.update_sk_obj_ref. -/
def updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) :
    SMonad Z Unit := do
  let sc ← getSimpleKo C ref
  setSimpleKo C ref (f (fun _ => new) sc)

/-- l4v: KHeap_A.get_reply_obj_ref (`abbreviation`). -/
abbrev getReplyObjRef (update : Reply → Option ObjRef) (ref : ObjRef) : SMonad Z (Option ObjRef) :=
  getSkObjRef KernelObject.reply update ref

/-- l4v: KHeap_A.set_reply_obj_ref (`abbreviation`). -/
abbrev setReplyObjRef (update : (Option ObjRef → Option ObjRef) → Reply → Reply) (ref : ObjRef)
    (new : Option ObjRef) : SMonad Z Unit :=
  updateSkObjRef KernelObject.reply update ref new

/-- l4v: KHeap_A.get_ntfn_obj_ref (`abbreviation`). -/
abbrev getNtfnObjRef (update : Notification → Option ObjRef) (ref : ObjRef) :
    SMonad Z (Option ObjRef) :=
  getSkObjRef KernelObject.notification update ref

/-- l4v: KHeap_A.set_ntfn_obj_ref (`abbreviation`). -/
abbrev setNtfnObjRef (update : (Option ObjRef → Option ObjRef) → Notification → Notification)
    (ref : ObjRef) (new : Option ObjRef) : SMonad Z Unit :=
  updateSkObjRef KernelObject.notification update ref new

/-- l4v: KHeap_A.is_irq_active: whether an IRQ is in use. -/
def isIrqActive (irq : Irq) : SMonad Z Bool :=
  NonDet.liftM (fun st => decide (st ≠ .irqInactive)) (getIrqState irq)

/-- l4v: KHeap_A.set_flags. -/
def setFlags (ref : ObjRef) (flags : TcbFlags) : SMonad Z Unit :=
  threadSet (fun tcb => { tcb with tcbFlags := flags }) ref

/-! ## User context -/

/-- l4v: KHeap_A.as_user: run a user monad on the context of a thread. -/
def asUser {α : Type} (tptr : ObjRef) (f : UserMonad α) : SMonad Z α := do
  let tcb ← NonDet.getsThe (getTcb tptr)
  let uc ← pure (archTcbContextGet tcb.tcbArch)
  let (a, uc') ← NonDet.selectF (f uc)
  let newTcb ← pure { tcb with tcbArch := archTcbContextSet uc' tcb.tcbArch }
  setObject tptr (.tcb newTcb)
  return a

/-- l4v: KHeap_A.throw_on_false: raise `ex` if the property does not
hold. -/
def throwOnFalse {ε : Type} (ex : ε) (f : SMonad Z Bool) : NonDetE (State Z) ε Unit := do
  let v ← NonDetE.liftE f
  NonDetE.unlessE v (NonDetE.throwError ex)

/-! ## Preemption -/

/-- l4v: KHeap_A.is_cur_domain_expired. -/
def isCurDomainExpired : State Z → Bool := fun s => decide (numDomains > 1 ∧ s.domainTime = 0)

/-- l4v: KHeap_A.update_time_stamp: update the current and consumed time. -/
def updateTimeStamp : SMonad Z Unit := do
  let previousTime ← NonDet.gets fun s : State Z => s.curTime
  let currentTime ← doMachineOp getCurrentTime
  let consumed ← pure (currentTime - previousTime)
  NonDet.modify fun s => { s with curTime := currentTime }
  NonDet.modify fun s => { s with consumedTime := s.consumedTime + consumed }
  let domainTime ← NonDet.gets fun s : State Z => s.domainTime
  NonDet.when (numDomains > 1) <|
    if consumed + MIN_BUDGET ≥ domainTime
    then NonDet.modify fun s => { s with domainTime := 0 }
    else NonDet.modify fun s => { s with domainTime := domainTime - consumed }

/-- l4v: KHeap_A.preemption_point: allow preemption at this point. -/
def preemptionPoint : PMonad Z Unit := do
  NonDetE.liftE (doExtendedOp updateWorkUnits)
  orChoiceE workUnitsLimitReached
    (do NonDetE.liftE (doExtendedOp resetWorkUnits)
        NonDetE.liftE updateTimeStamp
        let irqOpt ← NonDetE.liftE (doMachineOp (getActiveIRQ true))
        let exp ← NonDetE.liftE (NonDet.gets isCurDomainExpired)
        let curSc ← NonDetE.liftE (NonDet.gets fun s : State Z => s.curSc)
        let consumed ← NonDetE.liftE (NonDet.gets fun s : State Z => s.consumedTime)
        let active ← NonDetE.liftE (getScActive curSc)
        let sufficient ← NonDetE.liftE (NonDet.gets (readScRefillSufficient curSc consumed))
        NonDetE.whenE (irqOpt ≠ none ∨ exp ∨ ¬(active ∧ sufficient = some true))
          (NonDetE.throwError ()))
    (NonDetE.returnOk ())

end

/-! ## ArchVSpaceAcc_A: encodings -/

/-- l4v: ArchVSpaceAcc_A.X64_A.asid_high_bits_of: the high bits of a virtual
ASID. -/
def asidHighBitsOf (asid : Asid) : AsidHighIndex := ucast asidHighLen (asid >>> asidLowBits)

/-- l4v: ArchVSpaceAcc_A.X64_A.asid_low_bits_of: the low bits of a virtual
ASID. -/
def asidLowBitsOf (asid : Asid) : AsidLowIndex := ucast asidLowLen asid

/-! ## ArchVSpaceAcc_A: kernel heap accessors -/

/-- l4v: ArchVSpaceAcc_A.X64_A.aobjs_of (`locale_abbrev`). -/
abbrev aobjsOf {Z : Type} (s : State Z) : ObjRef → Option ArchKernelObj := optMap s.kheap aobjOf

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchVSpaceAcc_A.X64_A.get_asid_pool. -/
def getAsidPool (ptr : ObjRef) : SMonad Z (AsidLowIndex → Option ObjRef) := do
  let kobj ← getObject ptr
  match kobj with
  | .archObj (.asidPool pool) => return pool
  | _ => NonDet.fail

/-- l4v: ArchVSpaceAcc_A.X64_A.set_asid_pool. -/
def setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : SMonad Z Unit :=
  setObject ptr (.archObj (.asidPool pool))

/-- l4v: ArchVSpaceAcc_A.X64_A.get_pd. -/
def getPd (ptr : ObjRef) : SMonad Z (BitVec 9 → PDE) := do
  let kobj ← getObject ptr
  match kobj with
  | .archObj (.pageDirectory pd) => return pd
  | _ => NonDet.fail

/-- l4v: ArchVSpaceAcc_A.X64_A.set_pd. -/
def setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : SMonad Z Unit :=
  setObject ptr (.archObj (.pageDirectory pd))

/-- l4v: ArchVSpaceAcc_A.X64_A.get_pde: the PDE at a pointer into kernel
memory. -/
def getPde (ptr : ObjRef) : SMonad Z PDE := do
  let base ← pure (ptr &&& ~~~(mask pdBits))
  let offset ← pure ((ptr &&& mask pdBits) >>> wordSizeBits)
  let pd ← getPd base
  return pd (ucast 9 offset)

/-- l4v: ArchVSpaceAcc_A.X64_A.store_pde. -/
def storePde (p : ObjRef) (pde : PDE) : SMonad Z Unit := do
  let base ← pure (p &&& ~~~(mask pdBits))
  let offset ← pure ((p &&& mask pdBits) >>> wordSizeBits)
  let pd ← getPd base
  let pd' ← pure (Function.update pd (ucast 9 offset) pde)
  setPd base pd'

/-- l4v: ArchVSpaceAcc_A.X64_A.get_pt. -/
def getPt (ptr : ObjRef) : SMonad Z (BitVec 9 → PTE) := do
  let kobj ← getObject ptr
  match kobj with
  | .archObj (.pageTable pt) => return pt
  | _ => NonDet.fail

/-- l4v: ArchVSpaceAcc_A.X64_A.set_pt. -/
def setPt (ptr : ObjRef) (pt : BitVec 9 → PTE) : SMonad Z Unit :=
  setObject ptr (.archObj (.pageTable pt))

/-- l4v: ArchVSpaceAcc_A.X64_A.get_pte: the PTE at a pointer into kernel
memory. -/
def getPte (ptr : ObjRef) : SMonad Z PTE := do
  let base ← pure (ptr &&& ~~~(mask ptBits))
  let offset ← pure ((ptr &&& mask ptBits) >>> wordSizeBits)
  let pt ← getPt base
  return pt (ucast 9 offset)

/-- l4v: ArchVSpaceAcc_A.X64_A.store_pte. -/
def storePte (p : ObjRef) (pte : PTE) : SMonad Z Unit := do
  let base ← pure (p &&& ~~~(mask ptBits))
  let offset ← pure ((p &&& mask ptBits) >>> wordSizeBits)
  let pt ← getPt base
  let pt' ← pure (Function.update pt (ucast 9 offset) pte)
  setPt base pt'

/-- l4v: ArchVSpaceAcc_A.X64_A.get_pdpt. -/
def getPdpt (ptr : ObjRef) : SMonad Z (BitVec 9 → PDPTE) := do
  let kobj ← getObject ptr
  match kobj with
  | .archObj (.pdPointerTable pt) => return pt
  | _ => NonDet.fail

/-- l4v: ArchVSpaceAcc_A.X64_A.set_pdpt. -/
def setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : SMonad Z Unit :=
  setObject ptr (.archObj (.pdPointerTable pt))

/-- l4v: ArchVSpaceAcc_A.X64_A.get_pdpte: the PDPTE at a pointer into kernel
memory. -/
def getPdpte (ptr : ObjRef) : SMonad Z PDPTE := do
  let base ← pure (ptr &&& ~~~(mask pdptBits))
  let offset ← pure ((ptr &&& mask pdptBits) >>> wordSizeBits)
  let pt ← getPdpt base
  return pt (ucast 9 offset)

/-- l4v: ArchVSpaceAcc_A.X64_A.store_pdpte. -/
def storePdpte (p : ObjRef) (pte : PDPTE) : SMonad Z Unit := do
  let base ← pure (p &&& ~~~(mask pdptBits))
  let offset ← pure ((p &&& mask pdptBits) >>> wordSizeBits)
  let pt ← getPdpt base
  let pt' ← pure (Function.update pt (ucast 9 offset) pte)
  setPdpt base pt'

/-- l4v: ArchVSpaceAcc_A.X64_A.get_pml4. -/
def getPml4 (ptr : ObjRef) : SMonad Z (BitVec 9 → PML4E) := do
  let kobj ← getObject ptr
  match kobj with
  | .archObj (.pageMapL4 pt) => return pt
  | _ => NonDet.fail

/-- l4v: ArchVSpaceAcc_A.X64_A.set_pml4. -/
def setPml4 (ptr : ObjRef) (pt : BitVec 9 → PML4E) : SMonad Z Unit :=
  setObject ptr (.archObj (.pageMapL4 pt))

/-- l4v: ArchVSpaceAcc_A.X64_A.get_pml4e: the PML4E at a pointer into kernel
memory. -/
def getPml4e (ptr : ObjRef) : SMonad Z PML4E := do
  let base ← pure (ptr &&& ~~~(mask pml4Bits))
  let offset ← pure ((ptr &&& mask pml4Bits) >>> wordSizeBits)
  let pt ← getPml4 base
  return pt (ucast 9 offset)

/-- l4v: ArchVSpaceAcc_A.X64_A.store_pml4e. -/
def storePml4e (p : ObjRef) (pte : PML4E) : SMonad Z Unit := do
  let base ← pure (p &&& ~~~(mask pml4Bits))
  let offset ← pure ((p &&& mask pml4Bits) >>> wordSizeBits)
  let pt ← getPml4 base
  let pt' ← pure (Function.update pt (ucast 9 offset) pte)
  setPml4 base pt'

end

/-! ## ArchVSpaceAcc_A: basic operations -/

/-- l4v: ArchVSpaceAcc_A.X64_A.get_pt_index. -/
def getPtIndex (vptr : VSpaceRef) : Word := (vptr >>> ptShiftBits) &&& mask ptTranslationBits

/-- l4v: ArchVSpaceAcc_A.X64_A.get_pd_index. -/
def getPdIndex (vptr : VSpaceRef) : Word := (vptr >>> pdShiftBits) &&& mask ptTranslationBits

/-- l4v: ArchVSpaceAcc_A.X64_A.get_pdpt_index. -/
def getPdptIndex (vptr : VSpaceRef) : Word := (vptr >>> pdptShiftBits) &&& mask ptTranslationBits

/-- l4v: ArchVSpaceAcc_A.X64_A.get_pml4_index. -/
def getPml4Index (vptr : VSpaceRef) : Word := (vptr >>> pml4ShiftBits) &&& mask ptTranslationBits

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchVSpaceAcc_A.X64_A.copy_global_mappings: copy the kernel window
mappings (from `pptr_base` up) into a new PML4. -/
def copyGlobalMappings (newPm : ObjRef) : SMonad Z Unit := do
  let globalPm ← NonDet.gets fun s : State Z => s.archState.x64GlobalPml4
  let base ← pure (getPml4Index pptr_base)
  let pmeBits ← pure wordSizeBits
  let pmSize ← pure ((1 : Word) <<< ptTranslationBits)
  NonDet.mapMx (fun index : Word => do
      let offset ← pure (index <<< pmeBits)
      let pme ← getPml4e (globalPm + offset)
      storePml4e (newPm + offset) pme)
    (uptoEnum base (pmSize - 1))

end

/-- l4v: ArchVSpaceAcc_A.X64_A.lookup_pml4_slot. -/
def lookupPml4Slot (pm : ObjRef) (vptr : VSpaceRef) : ObjRef :=
  let pmIndex := getPml4Index vptr
  pm + (pmIndex <<< wordSizeBits)

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchVSpaceAcc_A.X64_A.lookup_pdpt_slot. -/
def lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : LFMonad Z ObjRef := do
  let pml4Slot ← NonDetE.returnOk (lookupPml4Slot pd vptr)
  let pml4e ← NonDetE.liftE (getPml4e pml4Slot)
  match pml4e with
  | .pdPointerTablePML4E tab _ _ => do
      let pd ← NonDetE.returnOk (ptrFromPAddr tab)
      let pdIndex ← NonDetE.returnOk (getPdptIndex vptr)
      let pdSlot ← NonDetE.returnOk (pd + (pdIndex <<< wordSizeBits))
      NonDetE.returnOk pdSlot
  | _ => NonDetE.throwError (.missingCapability pml4ShiftBits)

end

/-- l4v: ArchVSpaceAcc_A.X64_A.lookup_pdpt_slot_no_fail: `lookup_pdpt_slot`
when the PDPT is already known. -/
def lookupPdptSlotNoFail (pdpt : ObjRef) (vptr : VSpaceRef) : ObjRef :=
  pdpt + (getPdptIndex vptr <<< wordSizeBits)

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchVSpaceAcc_A.X64_A.lookup_pd_slot: the PDE slot for a virtual
address. -/
def lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : LFMonad Z ObjRef := do
  let pdptSlot ← lookupPdptSlot pd vptr
  let pdpte ← NonDetE.liftE (getPdpte pdptSlot)
  match pdpte with
  | .pageDirectoryPDPTE tab _ _ => do
      let pd ← NonDetE.returnOk (ptrFromPAddr tab)
      let pdIndex ← NonDetE.returnOk (getPdIndex vptr)
      let pdSlot ← NonDetE.returnOk (pd + (pdIndex <<< wordSizeBits))
      NonDetE.returnOk pdSlot
  | _ => NonDetE.throwError (.missingCapability pdptShiftBits)

end

/-- l4v: ArchVSpaceAcc_A.X64_A.lookup_pd_slot_no_fail: `lookup_pd_slot`
when the PD is already known. -/
def lookupPdSlotNoFail (pd : ObjRef) (vptr : VSpaceRef) : ObjRef :=
  pd + (getPdIndex vptr <<< wordSizeBits)

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchVSpaceAcc_A.X64_A.lookup_pt_slot: the PTE slot for a virtual
address; fails if the address is mapped by a large or huge page. -/
def lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : LFMonad Z ObjRef := do
  let pdSlot ← lookupPdSlot vspace vptr
  let pde ← NonDetE.liftE (getPde pdSlot)
  match pde with
  | .pageTablePDE ptab _ _ => do
      let pt ← NonDetE.returnOk (ptrFromPAddr ptab)
      let ptIndex ← NonDetE.returnOk (getPtIndex vptr)
      let ptSlot ← NonDetE.returnOk (pt + (ptIndex <<< wordSizeBits))
      NonDetE.returnOk ptSlot
  | _ => NonDetE.throwError (.missingCapability pdShiftBits)

end

/-- l4v: ArchVSpaceAcc_A.X64_A.lookup_pt_slot_no_fail: `lookup_pt_slot`
when the PT is already known. -/
def lookupPtSlotNoFail (pt : ObjRef) (vptr : VSpaceRef) : ObjRef :=
  pt + (getPtIndex vptr <<< wordSizeBits)

-- ArchVSpaceAcc_A's VT-d accessors (get_iopt ... lookup_io_pt_slot) are
-- commented out in l4v (`FIXME x64-vtd`); not ported (no IOMMU).

end

end Fl4Spec
