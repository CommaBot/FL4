/-
The top-level system call interface: the kernel entry point `callKernel`
(MCS, x86-64).

Ports, in theory order:
- the `Event` and `Syscall` types of `spec/design/skel/Event_H` (Haskell
  `SEL4/API/Syscall.lhs`, `ONLY Event Syscall`);
- `spec/abstract/X64/Hypervisor_A` (imports Exceptions_A; X64 without VT-x
  has no hypervisor faults, `handle_hypervisor_fault` does nothing);
- `spec/abstract/Syscall_A` (imports Event_H, Decode_A, Init_A,
  Hypervisor_A).
-/
import Fl4Spec.Decode
import Fl4Spec.Init

namespace Fl4Spec

open Classical

noncomputable section

/-! ## Event_H (Haskell SEL4/API/Syscall.lhs) -/

/-- l4v: Event_H.syscall (Haskell `Syscall`). -/
inductive Syscall where
  | sysCall
  | sysReplyRecv
  | sysNBSendRecv
  | sysNBSendWait
  | sysSend
  | sysNBSend
  | sysRecv
  | sysYield
  | sysNBRecv
  | sysWait
  | sysNBWait
deriving DecidableEq, Repr, Inhabited

/-- l4v: Event_H.event (Haskell `Event`): the events the kernel reacts to.
The Haskell `Int` of `UnknownSyscall` is Isabelle `nat`. -/
inductive Event where
  | syscallEvent (call : Syscall)
  | unknownSyscall (n : Nat)
  | userLevelFault (w1 w2 : Word)
  | interrupt
  | vmFaultEvent (faultType : VMFaultType)
  | hypervisorEvent (hypFaultType : HypFaultType)
deriving DecidableEq, Repr, Inhabited

section
variable {Z : Type} [StateExt Z]

/-! ## Hypervisor_A -/

/-- l4v: Hypervisor_A.X64_A.handle_hypervisor_fault. -/
def handleHypervisorFault : Word → HypFaultType → SMonad Z Unit
  | _thread, .x64NoHypFaults => return ()

/-! ## Syscall_A: generic system call structure -/

/-- l4v: Syscall_A.syscall: run a system call in three phases; the first may
fault, the second may fail with an error, the third may be preempted. -/
def syscall {α β γ : Type} (mFault : FMonad Z α) (hFault : Fault → SMonad Z γ)
    (mError : α → SEMonad Z β) (hError : SyscallError → SMonad Z γ)
    (mFinalise : β → PMonad Z γ) : PMonad Z γ := do
  let rFault ← withoutPreemption <| ExceptT.run mFault
  match rFault with
  | .error f => withoutPreemption <| hFault f
  | .ok a => do
    let rError ← withoutPreemption <| ExceptT.run (mError a)
    match rError with
    | .error e => withoutPreemption <| hError e
    | .ok b => mFinalise b

/-! ## Syscall_A: system call entry point -/

/-- l4v: Syscall_A.perform_invocation: perform a decoded invocation. -/
def performInvocation : Bool → Bool → Bool → Invocation → PMonad Z (List Data)
  | _, _, _, .invokeUntyped i => do
    invokeUntyped i
    NonDetE.returnOk []
  | block, call, canDonate, .invokeEndpoint ep badge canGrant canGrantReply =>
    withoutPreemption <| do
      let thread ← NonDet.gets fun s : State Z => s.curThread
      sendIpc block call badge canGrant canGrantReply canDonate thread ep
      return []
  | _, _, _, .invokeNotification ep badge => do
    withoutPreemption <| sendSignal ep badge
    NonDetE.returnOk []
  | _, _, _, .invokeTCB i => invokeTcb i
  | _, _, _, .invokeDomain domInv =>
    NonDetE.liftE (do
      invokeDomain domInv
      return [])
  | _, _, _, .invokeReply reply grant =>
    NonDetE.liftE (do
      let sender ← NonDet.gets fun s : State Z => s.curThread
      doReplyTransfer sender reply grant
      return [])
  | _, _, _, .invokeCNode i => do
    invokeCnode i
    NonDetE.returnOk []
  | _, _, _, .invokeIRQControl i => do
    invokeIrqControl i
    NonDetE.returnOk []
  | _, _, _, .invokeIRQHandler i => do
    NonDetE.liftE <| invokeIrqHandler i
    NonDetE.returnOk []
  | _, _, _, .invokeSchedContext i =>
    withoutPreemption (invokeSchedContext i)
  | _, _, _, .invokeSchedControl i => do
    NonDetE.liftE <| invokeSchedControlConfigureFlags i
    NonDetE.returnOk []
  | _, _, _, .invokeArchObject i =>
    archPerformInvocation i

/-- l4v: Syscall_A.get_cap_reg: a cptr from a register of the current
thread. -/
def getCapReg (reg : Register) : SMonad Z CapRef := do
  let ct ← NonDet.gets fun s : State Z => s.curThread
  NonDet.liftM dataToCptr <| asUser ct <| getRegister reg

/-- l4v: Syscall_A.handle_invocation: look up, decode and perform an
invocation of the cap at `cptr`. -/
def handleInvocation (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) :
    PMonad Z Unit := do
  let thread ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.curThread
  let info ← withoutPreemption <| getMessageInfo thread
  syscall
    (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <|
                         lookupCapAndSlot thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer))
    (fun fault => NonDet.when blocking <| handleFault thread fault)
    (fun (slot, cap, extracaps, buffer) => do
          let args ← NonDetE.liftE <| getMrs thread buffer info
          decodeInvocation firstPhase info.miLabel args cptr slot cap extracaps buffer)
    (fun err => NonDet.when calling <|
          replyFromKernel thread <| msgFromSyscallError err)
    (fun oper => do
          withoutPreemption <| setThreadState thread .restart
          let reply ← performInvocation blocking calling canDonate oper
          withoutPreemption <| do
              let state ← getThreadState thread
              match state with
              | .restart => do
                NonDet.when calling <|
                  replyFromKernel thread (0, reply)
                setThreadState thread .running
              | _ => return ())

/-- l4v: Syscall_A.handle_yield: charge the rest of the head refill and
yield. -/
def handleYield : SMonad Z Unit := do
  let curSc ← NonDet.gets fun s : State Z => s.curSc
  let sc ← getSchedContext curSc
  let consumed ← NonDet.gets fun s : State Z => s.consumedTime
  let head ← getRefillHead curSc
  chargeBudget head.rAmount false
  setScObjRef scConsumedUpdate curSc (sc.scConsumed + consumed)

/-- l4v: Syscall_A.handle_send. -/
def handleSend (bl : Bool) : PMonad Z Unit := do
  let cptr ← NonDetE.liftE <| getCapReg cap_register
  handleInvocation false bl false false cptr

/-- l4v: Syscall_A.handle_call. -/
def handleCall : PMonad Z Unit := do
  let cptr ← NonDetE.liftE <| getCapReg cap_register
  handleInvocation true true true false cptr

/-- l4v: Syscall_A.lookup_reply: the reply cap named in the reply
register. -/
def lookupReply : FMonad Z Cap := do
  let cref ← NonDetE.liftE <| getCapReg replyRegister
  let ct ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.curThread
  let cap ← capFaultOnFailure (ofBl cref) true <| lookupCap ct cref
  if isReplyCap cap
  then NonDetE.returnOk cap
  else NonDetE.throwError <| .capFault (ofBl cref) true (.missingCapability 0)

/-- l4v: Syscall_A.handle_recv: receive on the endpoint or notification
named in the cap register. -/
def handleRecv (isBlocking canReply : Bool) : SMonad Z Unit := do
  let thread ← NonDet.gets fun s : State Z => s.curThread

  let epCptr ← NonDet.liftM dataToCptr <| asUser thread <|
                 getRegister cap_register

  NonDetE.catch (show FMonad Z Unit from do
      let epCap ← capFaultOnFailure (ofBl epCptr) true (lookupCap thread epCptr)

      let flt : FMonad Z Unit :=
        NonDetE.throwError <| .capFault (ofBl epCptr) true (.missingCapability 0)
      match epCap with
      | .endpointCap _ref _badge rights =>
        if AllowRecv ∈ rights
        then do
          let replyCap ← if canReply then lookupReply else NonDetE.returnOk .nullCap
          NonDetE.liftE <| receiveIpc thread epCap isBlocking replyCap
        else flt
      | .notificationCap ref _badge rights =>
        (if AllowRecv ∈ rights
         then do
           let boundTCB ← NonDetE.liftE <| getNtfnObjRef Notification.ntfnBoundTcb ref
           if boundTCB = some thread ∨ boundTCB = none
           then NonDetE.liftE <| receiveSignal thread epCap isBlocking
           else flt
         else flt)
      | _ => flt)
    (handleFault thread)

/-! ## Syscall_A: top-level event handling -/

/-- l4v: Syscall_A.handle_event: update the time, check the budget and
dispatch the event. -/
def handleEvent : Event → PMonad Z Unit
  | .syscallEvent call => do
    NonDetE.liftE updateTimeStamp
    let restart ← NonDetE.liftE checkBudgetRestart
    NonDetE.whenE restart (match call with
      | .sysSend => handleSend true
      | .sysNBSend => handleSend false
      | .sysCall => handleCall
      | .sysRecv => withoutPreemption <| handleRecv true true
      | .sysYield => withoutPreemption handleYield
      | .sysReplyRecv => do
        let replyCptr ← withoutPreemption <| getCapReg replyRegister
        handleInvocation false false true true replyCptr
        withoutPreemption <| handleRecv true true
      | .sysNBSendRecv => do
        let dest ← withoutPreemption <| getCapReg nbsendRecvDest
        handleInvocation false false true true dest
        withoutPreemption <| handleRecv true true
      | .sysNBSendWait => do
        let replyCptr ← withoutPreemption <| getCapReg replyRegister
        handleInvocation false false true true replyCptr
        withoutPreemption <| handleRecv true false
      | .sysWait => withoutPreemption <| handleRecv true false
      | .sysNBWait => withoutPreemption <| handleRecv false false
      | .sysNBRecv => withoutPreemption <| handleRecv false true)
  | .unknownSyscall n => withoutPreemption <| do
    updateTimeStamp
    let restart ← checkBudgetRestart
    NonDet.when restart <| do
      let thread ← NonDet.gets fun s : State Z => s.curThread
      handleFault thread <| .unknownSyscallException <| BitVec.ofNat 64 n
  | .userLevelFault w1 w2 => withoutPreemption <| do
    updateTimeStamp
    let restart ← checkBudgetRestart
    NonDet.when restart <| do
      let thread ← NonDet.gets fun s : State Z => s.curThread
      handleFault thread <| .userException (w1 &&& mask 32) (w2 &&& mask 28)
  | .interrupt => withoutPreemption <| do
    updateTimeStamp
    let _ ← checkBudget
    maybeHandleInterrupt false
  | .vmFaultEvent faultType => withoutPreemption <| do
    updateTimeStamp
    let restart ← checkBudgetRestart
    NonDet.when restart <| do
      let thread ← NonDet.gets fun s : State Z => s.curThread
      NonDetE.catch (handleVmFault thread faultType) (handleFault thread)
  | .hypervisorEvent hypfaultType => withoutPreemption <| do
    updateTimeStamp
    let restart ← checkBudgetRestart
    NonDet.when restart <| do
      let thread ← NonDet.gets fun s : State Z => s.curThread
      handleHypervisorFault thread hypfaultType

/-! ## Syscall_A: kernel entry point -/

/-- l4v: Syscall_A.preemption_path: on preemption, charge the budget and
handle the pending interrupt. -/
def preemptionPath : SMonad Z Unit := do
  let ct ← NonDet.gets fun s : State Z => s.curThread
  let sched ← NonDet.gets (schedulable ct)
  if sched then do
    let _ ← checkBudget
    pure ()
  else do
    let csc ← NonDet.gets fun s : State Z => s.curSc
    let active ← getScActive csc
    if active
    then do
      let consumed ← NonDet.gets fun s : State Z => s.consumedTime
      chargeBudget consumed false
    else NonDet.modify fun s : State Z => { s with consumedTime := 0 }
  maybeHandleInterrupt true

/-- l4v: Syscall_A.call_kernel: the kernel entry point. Handle the event
(on preemption, take the preemption path), schedule, and switch to the
chosen thread. Isabelle's `<handle>` is `handleE`; its `unit + unit` result
is discarded. -/
def callKernel (ev : Event) : SMonad Z Unit := do
  let _ ← ExceptT.run <| NonDetE.handleE (handleEvent ev) (fun _ => withoutPreemption preemptionPath)
  schedule
  activateThread

end

end

end Fl4Spec
