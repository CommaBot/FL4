/-
Thread control: x86-64 register sanitising and FPU hooks, TCB invocations,
message register copying, domains, and arch fault messages (MCS).

Ports, in theory order:
- `spec/abstract/X64/ArchTcb_A` (imports only FPU_A in l4v);
- `spec/abstract/Tcb_A`;
- `spec/abstract/X64/ArchFault_A`.
-/
import Fl4Spec.Schedule

namespace Fl4Spec

open Classical

noncomputable section

/-! ## ArchTcb_A -/

/-- l4v: ArchTcb_A.X64_A.sanitise_or_flags. -/
def sanitiseOrFlags : Word := (1 <<< 1) ||| (1 <<< 9)

/-- l4v: ArchTcb_A.X64_A.sanitise_and_flags. -/
def sanitiseAndFlags : Word :=
  mask 12 &&& ~~~((1 : Word) <<< 8) &&& ~~~((1 : Word) <<< 3) &&& ~~~((1 : Word) <<< 5)

/-- l4v: ArchTcb_A.X64_A.sanitise_register: keep user-written instruction
pointers and segment bases canonical and the user-writable FLAGS bits in
range. -/
def sanitiseRegister (_t : Bool) (r : Register) (v : Word) : Word :=
  let val := if r = .faultIP ∨ r = .nextIP ∨ r = .fsBase ∨ r = .gsBase
             then if v > 0x00007fffffffffff ∧ v < 0xffff800000000000 then 0 else v
             else v
  if r = .flags then (val ||| sanitiseOrFlags) &&& sanitiseAndFlags else val

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchTcb_A.X64_A.arch_get_sanitise_register_info. -/
def archGetSanitiseRegisterInfo (_t : ObjRef) : SMonad Z Bool := return false

/-- l4v: ArchTcb_A.X64_A.arch_post_modify_registers. -/
def archPostModifyRegisters (cur t : ObjRef) : SMonad Z Unit :=
  NonDet.when (t ≠ cur) <| asUser t <| setRegister .errorRegister 0

/-- l4v: ArchTcb_A.X64_A.arch_post_set_flags (inline in the C
`invokeSetFlags`). -/
def archPostSetFlags (t : ObjRef) (flags : TcbFlags) : SMonad Z Unit := do
  let cur ← NonDet.gets fun s : State Z => s.curThread
  if TcbFlag.fpuDisabled ∈ flags
  then fpuRelease t
  else NonDet.when (t = cur) (lazyFpuRestore t)

/-- l4v: ArchTcb_A.X64_A.arch_prepare_set_domain. -/
def archPrepareSetDomain (t : ObjRef) (newDom : Domain) : SMonad Z Unit := do
  let curDomain ← NonDet.gets fun s : State Z => s.curDomain
  NonDet.when (curDomain ≠ newDom) <| fpuRelease t

/-! ## Tcb_A: activating threads -/

/-- l4v: Tcb_A.restart: reactivate a thread that is not running. -/
def restart (thread : ObjRef) : SMonad Z Unit := do
  let state ← getThreadState thread
  let scOpt ← getTcbObjRef Tcb.tcbSchedContext thread
  NonDet.when (¬runnable state ∧ ¬idle state) <| do
    cancelIpc thread
    setThreadState thread .restart
    ifSporadicCurScTestRefillUnblockCheck scOpt
    NonDet.maybeM schedContextResume scOpt
    testPossibleSwitchTo thread

/-- l4v: Tcb_A.activate_thread: before returning to user mode, a restarted
thread's program counter is set back to the operation it was performing. -/
def activateThread : SMonad Z Unit := do
  let thread ← NonDet.gets fun s : State Z => s.curThread
  let ytOpt ← getTcbObjRef Tcb.tcbYieldTo thread
  NonDet.when (ytOpt ≠ none) <| completeYieldTo thread
  let state ← getThreadState thread
  match state with
  | .running => return ()
  | .restart => do
      let pc ← asUser thread getRestartPC
      asUser thread <| setNextPC pc
      setThreadState thread .running
  | .idleThreadState => archActivateIdleThread thread
  | _ => NonDet.fail

/-! ## Tcb_A: thread message formats -/

/-- l4v: Tcb_A.load_word_offs. -/
def loadWordOffs (ptr : ObjRef) (offs : Nat) : SMonad Z Word :=
  doMachineOp <| loadWord (ptr + BitVec.ofNat 64 (offs * wordSize))

/-- l4v: Tcb_A.load_word_offs_word. -/
def loadWordOffsWord (ptr : ObjRef) (offs : Data) : SMonad Z Word :=
  doMachineOp <| loadWord (ptr + offs * BitVec.ofNat 64 wordSize)

/-- l4v: Tcb_A.copy_mrs: copy message registers from one thread to another. -/
def copyMrs (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef)
    (n : LengthType) : SMonad Z LengthType := do
  let hardwareMrs ← pure (msg_registers.take (unat n))
  let _ ← NonDet.mapM (fun r => do
      let v ← asUser sender <| getRegister r
      asUser receiver <| setRegister r v) hardwareMrs
  let bufMrs ← match sbuf, rbuf with
    | some sbPtr, some rbPtr =>
        NonDet.mapM (fun x => do
            let v ← loadWordOffs sbPtr x
            storeWordOffs rbPtr x v)
          (List.range' (msg_registers.length + 1) (unat n + 1 - (msg_registers.length + 1)))
    | _, _ => pure []
  return min n (natToLen (hardwareMrs.length + bufMrs.length))

end

/-- l4v: Tcb_A.get_tcb_ctable_ptr. -/
def getTcbCtablePtr (tcbRef : ObjRef) : CslotPtr := (tcbRef, tcbCnodeIndex 0)

/-- l4v: Tcb_A.get_tcb_vtable_ptr. -/
def getTcbVtablePtr (tcbRef : ObjRef) : CslotPtr := (tcbRef, tcbCnodeIndex 1)

/-- l4v: Tcb_A.get_tcb_fault_handler_ptr. -/
def getTcbFaultHandlerPtr (tcbRef : ObjRef) : CslotPtr := (tcbRef, tcbCnodeIndex 3)

/-- l4v: Tcb_A.get_tcb_timeout_handler_ptr. -/
def getTcbTimeoutHandlerPtr (tcbRef : ObjRef) : CslotPtr := (tcbRef, tcbCnodeIndex 4)

section
variable {Z : Type} [StateExt Z]

/-- l4v: Tcb_A.option_update_thread. -/
def optionUpdateThread {α : Type} (thread : ObjRef) (fn : α → Tcb → Tcb) : Option α → SMonad Z Unit
  | none => return ()
  | some v => threadSet (fn v) thread

/-- l4v: Tcb_A.check_cap_at: run `m` only if a related cap is still at the
slot (before `cap_insert`, in case the would-be parent was moved or
deleted). -/
def checkCapAt (cap : Cap) (slot : CslotPtr) (m : SMonad Z Unit) : SMonad Z Unit := do
  let cap' ← getCap slot
  NonDet.when (sameObjectAs cap cap') m

/-- l4v: Tcb_A.bind_notification. -/
def bindNotification (tcbptr ntfnptr : ObjRef) : SMonad Z Unit := do
  setNtfnObjRef ntfnBoundTcbUpdate ntfnptr (some tcbptr)
  setTcbObjRef tcbBoundNotificationUpdate tcbptr (some ntfnptr)

/-- l4v: Tcb_A.install_tcb_cap. -/
def installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) :
    PMonad Z Unit :=
  match slotOpt with
  | none => NonDetE.returnOk ()
  | some (newCap, srcSlot) => do
    capDelete (target, tcbCnodeIndex n)
    NonDetE.unlessE (newCap = .nullCap) <|
      NonDetE.liftE <| checkCapAt newCap srcSlot
        <| checkCapAt (.threadCap target) slot
        <| capInsert newCap srcSlot (target, tcbCnodeIndex n)

/-- l4v: Tcb_A.install_tcb_frame_cap. -/
def installTcbFrameCap (target : ObjRef) (slot : CslotPtr)
    (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : PMonad Z Unit :=
  match buffer with
  | none => NonDetE.returnOk ()
  | some (ptr, frame) => do
    capDelete (target, tcbCnodeIndex 2)
    NonDetE.liftE <| threadSet (fun t => { t with tcbIpcBuffer := ptr }) target
    NonDetE.liftE <| match frame with
      | none => return ()
      | some (newCap, srcSlot) =>
          checkCapAt newCap srcSlot
            <| checkCapAt (.threadCap target) slot
            <| capInsert newCap srcSlot (target, tcbCnodeIndex 2)
    let cur ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.curThread
    NonDetE.liftE <| NonDet.when (target = cur) rescheduleRequired

/-- l4v: Tcb_A.invoke_tcb: suspend, resume or reconfigure a thread, or copy
registers into, out of or between threads. -/
def invokeTcb : TcbInvocation → PMonad Z (List Data)
  | .suspend thread => NonDetE.liftE (do suspend thread; return [])
  | .resume thread => NonDetE.liftE (do restart thread; return [])
  | .threadControlCaps target slot faultHandler timeoutHandler croot vroot buffer => do
      installTcbCap target slot 3 faultHandler
      installTcbCap target slot 4 timeoutHandler
      installTcbCap target slot 0 croot
      installTcbCap target slot 1 vroot
      installTcbFrameCap target slot buffer
      NonDetE.returnOk []
  | .threadControlSched target slot faultHandler mcp priority sc => do
      installTcbCap target slot 3 faultHandler
      NonDetE.liftE <| NonDet.maybeM (fun (newmcp, _) => setMcpriority target newmcp) mcp
      NonDetE.liftE <| NonDet.maybeM (fun (prio, _) => setPriority target prio) priority
      NonDetE.liftE <| NonDet.maybeM (fun scopt =>
          match scopt with
          | none => do
              let scPtrOpt ← getTcbObjRef Tcb.tcbSchedContext target
              let scPtr ← NonDet.assertOpt scPtrOpt
              schedContextUnbindTcb scPtr
          | some scPtr => schedContextBindTcb scPtr target) sc
      NonDetE.returnOk []
  | .copyRegisters dest src suspendSource resumeTarget transferFrame transferInteger _transferArch =>
      NonDetE.liftE <| do
        NonDet.when suspendSource <| suspend src
        NonDet.when resumeTarget <| restart dest
        let sanitiseInfo ← archGetSanitiseRegisterInfo dest
        NonDet.when transferFrame <| do
          NonDet.mapMx (fun r => do
              let v ← asUser src <| getRegister r
              asUser dest <| setRegister r (sanitiseRegister sanitiseInfo r v)) frame_registers
          let pc ← asUser dest getRestartPC
          asUser dest <| setNextPC pc
        NonDet.when transferInteger <|
          NonDet.mapMx (fun r => do
              let v ← asUser src <| getRegister r
              asUser dest <| setRegister r (sanitiseRegister sanitiseInfo r v)) gpRegisters
        let cur ← NonDet.gets fun s : State Z => s.curThread
        archPostModifyRegisters cur dest
        NonDet.when (dest = cur) rescheduleRequired
        return []
  | .readRegisters src suspendSource n _arch =>
      NonDetE.liftE <| do
        NonDet.when suspendSource <| suspend src
        let _self ← NonDet.gets fun s : State Z => s.curThread
        let regs ← pure ((frame_registers ++ gp_registers).take (unat n))
        asUser src <| NonDet.mapM getRegister regs
  | .writeRegisters dest resumeTarget values _arch =>
      NonDetE.liftE <| do
        let self ← NonDet.gets fun s : State Z => s.curThread
        let b ← archGetSanitiseRegisterInfo dest
        asUser dest <| do
          let _ ← NonDet.zipWithM (fun r v => setRegister r (sanitiseRegister b r v))
            (frameRegisters ++ gpRegisters) values
          let pc ← getRestartPC
          setNextPC pc
        archPostModifyRegisters self dest
        NonDet.when resumeTarget <| restart dest
        NonDet.when (dest = self) rescheduleRequired
        return []
  | .notificationControl tcb (some ntfnptr) =>
      NonDetE.liftE <| do
        bindNotification tcb ntfnptr
        return []
  | .notificationControl tcb none =>
      NonDetE.liftE <| do
        unbindNotification tcb
        return []
  | .setTLSBase tcb tlsBase =>
      NonDetE.liftE <| do
        let sanitiseInfo ← archGetSanitiseRegisterInfo tcb
        asUser tcb <|
          setRegister tlsBaseRegister (sanitiseRegister sanitiseInfo tlsBaseRegister tlsBase)
        let cur ← NonDet.gets fun s : State Z => s.curThread
        NonDet.when (tcb = cur) rescheduleRequired
        return []
  | .setFlags tcb clearFlags setFlags =>
      NonDetE.liftE <| do
        let flags ← threadGet Tcb.tcbFlags tcb
        let newFlags ← pure (flags \ clearFlags ∪ setFlags)
        Fl4Spec.setFlags tcb newFlags
        archPostSetFlags tcb newFlags
        return [tcbFlagsToWord newFlags]

/-! ## Tcb_A: domains -/

/-- l4v: Tcb_A.set_domain. -/
def setDomain (tptr : ObjRef) (newDom : Domain) : SMonad Z Unit := do
  let cur ← NonDet.gets fun s : State Z => s.curThread
  tcbSchedAction tcbSchedDequeue tptr
  threadSetDomain tptr newDom
  let sched ← NonDet.gets (schedulable tptr)
  NonDet.when sched <| tcbSchedAction tcbSchedEnqueue tptr -- schedulable and dequeued
  NonDet.when (tptr = cur) rescheduleRequired

/-- l4v: Tcb_A.invoke_set_domain. -/
def invokeSetDomain (thread : ObjRef) (domain : Domain) : SMonad Z Unit := do
  archPrepareSetDomain thread domain
  setDomain thread domain

/-- l4v: Tcb_A.invoke_domain. -/
def invokeDomain (domInv : DomainInvocation) : SMonad Z Unit :=
  match domInv with
  | .invokeDomainSet thread domain => invokeSetDomain thread domain
  | .invokeDomainScheduleSetStart index => domainSetStart index
  | .invokeDomainScheduleConfigure index domain duration =>
      domainScheduleConfigure index domain duration

/-- l4v: Tcb_A.get_mrs: all the message registers, from the register file
and the IPC buffer. -/
def getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : SMonad Z (List Message) := do
  let context ← threadGet (archTcbGetRegisters ∘ Tcb.tcbArch) thread
  let cpuMrs ← pure (msg_registers.map context)
  let bufMrs ← match buf with
    | none => pure []
    | some pptr =>
        NonDet.mapM (fun x => loadWordOffs pptr x)
          (List.range' (msg_registers.length + 1) (msgMaxLength + 1 - (msg_registers.length + 1)))
  return (cpuMrs ++ bufMrs).take (unat info.miLength)

/-! ## ArchFault_A -/

/-- l4v: ArchFault_A.X64_A.make_arch_fault_msg. rt X64 gap: the X64 theory
on `rt` has the non-MCS label 5; with `CONFIG_KERNEL_MCS` the C kernel's
x86 `seL4_Fault_VMFault` tag is 6 (after `Timeout`, 5), as in RISCV64 `rt`
`make_arch_fault_msg`. -/
def makeArchFaultMsg : ArchFault → ObjRef → SMonad Z (Data × List Data)
  | .vmFault vptr archData, thread => do
    let pc ← asUser thread getRestartPC
    return (6, pc :: vptr :: archData)

/-- l4v: ArchFault_A.X64_A.handle_arch_fault_reply. -/
def handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) :
    SMonad Z Bool :=
  return true

end

end

end Fl4Spec
