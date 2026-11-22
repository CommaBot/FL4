/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization,
VMEnter, the VCPU check and the notification and scheduler interaction**
(proofs/VIRT-PLAN.md §5.3).

* `vmEnter t` (FL4 `vcpu::enter`, the `SysVMEnter` unknown syscall of a
  thread with a VCPU, after FL4's budget check): MR0..2 from the message
  registers (even without an IPC buffer) staged sanitized
  (`VcpuState.enter`), the exit record emptied; then, as seL4's
  `c_handle_syscall` (`CONFIG_VTX`), an active bound notification
  completes the VMEnter at once (`completeSignal`, message info
  `SEL4_VMENTER_RESULT_NOTIF` = 0, the message registers left as the
  caller sent them), otherwise the thread becomes `runningVM`.
  -- FL4 code differs until V2 (FL4 enters `runningVM`, then its `check`
  reports 30 MRs with the badge).
* `vmCheck t` (FL4 `vcpu::check`, before every guest entry and after every
  VM exit): a `runningVM` thread with a pending exit gets `vmReport t 0`;
  else an active bound notification (signalled from another core) becomes
  idle and ends the VMEnter by `vmNotifyComplete` (seL4
  `VMCheckBoundNotification` and `Arch_leaveVMAsyncTransfer`: `Running`,
  the badge, MR0..2 := the guest's RIP, controls and injection, message
  info 0); else a thread without VCPU gets `vmReport t 0`.
  -- FL4 code differs until V2 (FL4's `report` writes all 30 MRs).
* `sendSignalV onCore` (seL4 `sendSignal` with `CONFIG_VTX`): an idle
  notification bound to a `runningVM` thread on this core completes the
  VMEnter at once (`vmNotifyComplete`, then MCS donation, `possibleSwitchTo`
  and the sporadic refill check, as seL4); on another core it becomes
  active (the ported `sendSignal`) and that core's next `vmCheck` delivers
  it. -- FL4 code differs until V1 (FL4 always takes the second branch).
  The spec's state has no thread affinity (l4v is uniprocessor), so the
  kernel entry takes it as a parameter `onCore : ObjRef → Bool` (FL4: the
  TCB's affinity is the current core), fixed for the entry.
* Every caller of `send_signal` in the extended kernel uses `sendSignalV`:
  `handleInterruptV`, the notification invocation (`Ext/VirtDispatch`), the
  TCB timers (`fl4AwakenV`).
* `activateThreadV`: l4v's `activate_thread` with seL4's `RunningVM`
  case (nothing to do; the ported function fails on it).
* The scheduler: `runningVM` is `runnable` (ported); the ported
  `end_timeslice` already raises no timeout fault for a `runningVM` thread
  (FL4 `sched.rs` `end_timeslice`, FINDING V8, decision of 2026-11-21:
  FL4's behaviour is kept; PORTING.md "FL4 differences").

The ported modules are not changed.
-/
import Fl4Spec.Ext.VirtFinalise
import Fl4Spec.Ext.Timer

namespace Fl4Spec

noncomputable section
open Classical

/-- FL4's `SysVMEnter` (-23) as l4v's unknown-syscall number: the 64-bit
word FL4 reports in the unknown-syscall fault (`number as u64`). -/
def fl4SysVMEnterNum : Nat := 2 ^ 64 - 23

section
variable {Z : Type} [StateExt Z]

/-- The end of a VMEnter by a notification (seL4 `setThreadState
Running`, the badge register, `Arch_leaveVMAsyncTransfer` =
`vcpu_sysvmenter_reply_to_user`: MR0..2 := the guest's current RIP, entry
controls and event injection, message info 0). -/
def vmNotifyComplete (t : ObjRef) (badge : Word) : SMonad Z Unit := do
  setThreadState t .running
  asUser t (setRegister badge_register badge)
  let vo ← getTcbVcpu t
  match vo with
  | some v => do
    let st ← getVcpu v
    let buf ← lookupIpcBuffer true t
    let _ ← setMrs t buf [st.entryIp virtKind, st.entryCtl virtKind, st.entryIntr virtKind]
    pure ()
  | none => pure ()
  asUser t (setRegister msg_info_register 0)

/-- **seL4 `sendSignal` with `CONFIG_VTX`** (module docstring). -/
def sendSignalV (onCore : ObjRef → Bool) (ntfnptr : ObjRef) (badge : Badge) : SMonad Z Unit := do
  let ntfn ← getNotification ntfnptr
  match ntfn.ntfnObj, ntfn.ntfnBoundTcb with
  | .idleNtfn, some tcb => do
    let st ← getThreadState tcb
    -- FL4 code differs until V1 (FL4: always the ported branch, plus a stall).
    if st = .runningVM ∧ onCore tcb = true then do
      vmNotifyComplete tcb badge
      maybeDonateSc tcb ntfnptr
      let sched ← NonDet.gets (schedulable tcb)
      NonDet.when sched <| possibleSwitchTo tcb
      let scOpt ← getTcbObjRef Tcb.tcbSchedContext tcb
      NonDet.maybeM (fun scp => do
          let active ← getScActive scp
          NonDet.when active <| do
            let sc ← getSchedContext scp
            let ntfnScp ← getNtfnObjRef Notification.ntfnSc ntfnptr
            let curScPtr ← NonDet.gets fun s : State Z => s.curSc
            NonDet.when (scOpt = ntfnScp ∧ sc.scSporadic ∧ scp ≠ curScPtr) <| refillUnblockCheck scp)
        scOpt
    else sendSignal ntfnptr badge
  | _, _ => sendSignal ntfnptr badge

/-- l4v `Interrupt_A.handle_interrupt` with `sendSignalV`. -/
def handleInterruptV (onCore : ObjRef → Bool) (irq : Irq) : SMonad Z Unit :=
  if irq > maxIRQ then doMachineOp (do
    maskInterrupt true irq
    ackInterrupt irq)
  else do
    let st ← getIrqState irq
    match st with
    | .irqSignal => do
      let slot ← getIrqSlot irq
      let cap ← getCap slot
      NonDet.when (isNtfnCap cap ∧ AllowSend ∈ capRights cap) <|
        sendSignalV onCore (objRefOf cap) (capEpBadge cap)
      archMaskIrqSignal irq
    | .irqTimer => do
      doMachineOp ackDeadlineIRQ
      NonDet.modify fun s : State Z => { s with reprogramTimer := true }
    | .irqInactive => NonDet.fail
    | .irqReserved => handleReservedIrq irq
    doMachineOp <| ackInterrupt irq

/-- l4v `maybe_handle_interrupt` with `handleInterruptV`. -/
def maybeHandleInterruptV (onCore : ObjRef → Bool) (inKernel : Bool) : SMonad Z Unit := do
  let irqOpt ← doMachineOp <| getActiveIRQ inKernel
  match irqOpt with
  | none => handleSpuriousIrq
  | some irq => handleInterruptV onCore irq

/-- `Ext/Timer`'s `fl4TimerSignal` with `sendSignalV`. -/
def fl4TimerSignalV (onCore : ObjRef → Bool) (σ σ' : State Z) : Prop :=
  ∃ n b, sendSignalV onCore n b σ = ({((), σ')}, False)

/-- `Ext/Timer`'s `fl4TimerFire` with `fl4TimerSignalV`. -/
def fl4TimerFireV (onCore : ObjRef → Bool) (σ σ' : State Z) : Prop :=
  ∃ σ1, (σ1 = σ ∨ fl4TimerSignalV onCore σ σ1) ∧ σ' = { σ1 with reprogramTimer := true }

/-- `Ext/Timer`'s `fl4Awaken` with `fl4TimerFireV`. -/
def fl4AwakenV (onCore : ObjRef → Bool) : SMonad Z Unit :=
  fun σ => ({p | Relation.ReflTransGen (fl4TimerFireV onCore) σ p.2}, False)

/-- **VMEnter** (module docstring). -/
def vmEnter (t : ObjRef) : SMonad Z Unit := do
  let vo ← getTcbVcpu t
  match vo with
  | none => asUser t (setRegister msg_info_register 0)
  | some v => do
    let ip ← asUser t (getRegister (the msg_registers[0]?))
    let ctl ← asUser t (getRegister (the msg_registers[1]?))
    let intr ← asUser t (getRegister (the msg_registers[2]?))
    vcpuUpdate v fun st => st.enter virtKind ip ctl intr
    let nOpt ← getTcbObjRef Tcb.tcbBoundNotification t
    let active ← match nOpt with
      | some n => do
        let ntfn ← getNotification n
        pure (match ntfn.ntfnObj with
          | .activeNtfn _ => true
          | _ => false)
      | none => pure false
    -- FL4 code differs until V2 (FL4: `runningVM`, then `check` reports
    -- 30 MRs with the badge).
    match nOpt, active with
    | some n, true => do
      completeSignal n t
      asUser t (setRegister msg_info_register 0)
    | _, _ => setThreadState t .runningVM

/-- **The VCPU check** (FL4 `vcpu::check`; module docstring). -/
def vmCheck (t : ObjRef) : SMonad Z Unit := do
  let st ← getThreadState t
  NonDet.when (st = .runningVM) <| do
    let vo ← getTcbVcpu t
    let pending ← match vo with
      | some v => do
        let s ← getVcpu v
        pure s.exit.pending
      | none => pure false
    if pending then vmReport t 0
    else do
      let nOpt ← getTcbObjRef Tcb.tcbBoundNotification t
      let nb ← match nOpt with
        | some n => do
          let ntfn ← getNotification n
          pure (match ntfn.ntfnObj with
            | .activeNtfn b => some (n, ntfn, b)
            | _ => none)
        | none => pure none
      match nb with
      | some (n, ntfn, b) => do
        -- FL4 code differs until V2 (FL4: `report` of 30 MRs).
        setNotification n <| ntfnObjUpdate (fun _ => .idleNtfn) ntfn
        vmNotifyComplete t b
        let cur ← NonDet.gets fun s : State Z => s.curThread
        NonDet.when (t ≠ cur) <| possibleSwitchTo t
      | none => NonDet.when (vo = none) <| vmReport t 0

/-- l4v `Tcb_A.activate_thread` with seL4's `RunningVM` case (C
`activateThread`: nothing to do). -/
def activateThreadV : SMonad Z Unit := do
  let thread ← NonDet.gets fun s : State Z => s.curThread
  let ytOpt ← getTcbObjRef Tcb.tcbYieldTo thread
  NonDet.when (ytOpt ≠ none) <| completeYieldTo thread
  let state ← getThreadState thread
  match state with
  | .running => return ()
  | .runningVM => return ()
  | .restart => do
      let pc ← asUser thread getRestartPC
      asUser thread <| setNextPC pc
      setThreadState thread .running
  | .idleThreadState => archActivateIdleThread thread
  | _ => NonDet.fail

end

end

end Fl4Spec
