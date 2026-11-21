/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization,
the kernel entry and exit** (proofs/VIRT-PLAN.md §5.3, §7).

`Ext/Entry`'s `fl4HandleSyscall`, `fl4HandleEvent`, `fl4CallKernel` and
`fl4KernelEntrySyscall`, with

* the extended dispatcher `fl4HandleInvocationV` (`Ext/VirtDispatch`);
* `SysVMEnter` (an unknown syscall in l4v, `fl4SysVMEnterNum`): when
  `virtKind ≠ none` and the caller has a VCPU (FL4
  `handle_unknown_syscall`), FL4's `budget_ok` (`update_timestamp`,
  `check_budget_restart`) and, if it passes, `vmEnter`; otherwise l4v's
  unknown-syscall fault, as before. (seL4's `c_handle_syscall` enters
  without charging the budget: FINDING V9.)
* interrupts through `handleInterruptV` (also on the preemption path),
  and the TCB timers through `fl4AwakenV`, so every signal is
  `sendSignalV`;
* `activateThreadV` for `activate_thread`;
* the kernel exit's VCPU check (FL4 `kernel/entry.rs` `exit`: the current
  thread, if `runningVM`, is checked under the serial gate before the
  guest is entered): `vmCheck` of the current thread after activation.

`fl4VcpuExitV onCore irq stalled` is the entry after a guest step (FL4
`syscall.rs` `handle_vcpu_exit`, reached from the trusted layer's
`vm::run`): unless the thread was stalled by another core,
`update_timestamp`, `vmCheck` of the current thread, `check_budget`; then
the host interrupt the exit accepted, if any; then the scheduler and the
exit as for every entry. A guest step is `GuestStep` (`Ext/VirtGuest`),
taken when the current thread is `runningVM` after the exit's check.

`onCore` (`Ext/VirtEntry`) says which threads run on this core.

The ported modules are not changed.
-/
import Fl4Spec.Ext.VirtDispatch
import Fl4Spec.Ext.Entry

namespace Fl4Spec

noncomputable section
open Classical

section
variable {Z : Type} [StateExt Z]

/-- `fl4HandleSyscall` with `fl4HandleInvocationV`. -/
def fl4HandleSyscallV (onCore : ObjRef → Bool) (rep : Bool) : Syscall → PMonad Z Unit
  | .sysSend => do
    let cptr ← NonDetE.liftE <| getCapReg cap_register
    fl4HandleInvocationV onCore rep false true false false cptr
  | .sysNBSend => do
    let cptr ← NonDetE.liftE <| getCapReg cap_register
    fl4HandleInvocationV onCore rep false false false false cptr
  | .sysCall => do
    let cptr ← NonDetE.liftE <| getCapReg cap_register
    fl4HandleInvocationV onCore rep true true true false cptr
  | .sysRecv => withoutPreemption <| handleRecv true true
  | .sysYield => withoutPreemption handleYield
  | .sysReplyRecv => do
    let replyCptr ← withoutPreemption <| getCapReg replyRegister
    fl4HandleInvocationV onCore rep false false true true replyCptr
    withoutPreemption <| handleRecv true true
  | .sysNBSendRecv => do
    let dest ← withoutPreemption <| getCapReg nbsendRecvDest
    fl4HandleInvocationV onCore rep false false true true dest
    withoutPreemption <| handleRecv true true
  | .sysNBSendWait => do
    let replyCptr ← withoutPreemption <| getCapReg replyRegister
    fl4HandleInvocationV onCore rep false false true true replyCptr
    withoutPreemption <| handleRecv true false
  | .sysWait => withoutPreemption <| handleRecv true false
  | .sysNBWait => withoutPreemption <| handleRecv false false
  | .sysNBRecv => withoutPreemption <| handleRecv false true

/-- FL4's `SysVMEnter` branch of `handle_unknown_syscall` applies. -/
def isVmEnterCall (n : Nat) (σ : State Z) : Bool :=
  decide (n = fl4SysVMEnterNum ∧ virtKind ≠ .none ∧ (tcbVcpuOf σ σ.curThread).isSome)

/-- `fl4HandleEvent` with the extended dispatcher, `SysVMEnter` and
`handleInterruptV` (module docstring). -/
def fl4HandleEventV (onCore : ObjRef → Bool) (rep : Bool) : Event → PMonad Z Unit
  | .syscallEvent call => do
    NonDetE.liftE updateTimeStamp
    let restart ← NonDetE.liftE checkBudgetRestart
    NonDetE.whenE restart (fl4HandleSyscallV onCore rep call)
  | .unknownSyscall n => do
    let vm ← NonDetE.liftE <| NonDet.gets (isVmEnterCall n)
    if vm then withoutPreemption <| do
      updateTimeStamp
      let restart ← checkBudgetRestart
      let thread ← NonDet.gets fun s : State Z => s.curThread
      NonDet.when restart <| vmEnter thread
    else handleEvent (.unknownSyscall n)
  | .interrupt => withoutPreemption <| do
    updateTimeStamp
    let _ ← checkBudget
    maybeHandleInterruptV onCore false
  | ev => handleEvent ev

/-- l4v `Syscall_A.preemption_path` with `maybeHandleInterruptV`. -/
def preemptionPathV (onCore : ObjRef → Bool) : SMonad Z Unit := do
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
  maybeHandleInterruptV onCore true

/-- The common tail of every entry: TCB timers, `schedule`,
`activateThreadV`, and the exit's VCPU check of the current thread (FL4
`kernel/entry.rs` `exit`). -/
def fl4KernelExitV (onCore : ObjRef → Bool) : SMonad Z Unit := do
  fl4AwakenV onCore
  schedule
  activateThreadV
  let ct ← NonDet.gets fun s : State Z => s.curThread
  vmCheck ct

/-- **`fl4CallKernel` with the virtualization extension** (module
docstring). -/
def fl4CallKernelV (onCore : ObjRef → Bool) (rep : Bool) (ev : Event) : SMonad Z Unit := do
  let _ ← ExceptT.run <| NonDetE.handleE (fl4HandleEventV onCore rep ev)
    (fun _ => withoutPreemption (preemptionPathV onCore))
  fl4KernelExitV onCore

/-- The syscall entry (`fl4KernelEntrySyscall`) of the extended kernel. -/
def fl4KernelEntrySyscallV (onCore : ObjRef → Bool) (rep : Bool) (c : Syscall) : SMonad Z Unit := do
  let ct ← NonDet.gets fun s : State Z => s.curThread
  fl4SyscallFaultIP ct
  fl4CallKernelV onCore rep (.syscallEvent c)

/-- **The entry after a guest step** (FL4 `handle_vcpu_exit`; module
docstring). -/
def fl4VcpuExitV (onCore : ObjRef → Bool) (irq : Option Irq) (stalled : Bool) : SMonad Z Unit := do
  NonDet.unless stalled <| do
    updateTimeStamp
    let ct ← NonDet.gets fun s : State Z => s.curThread
    vmCheck ct
    let _ ← checkBudget
    pure ()
  match irq with
  | some i => handleInterruptV onCore i
  | none => pure ()
  fl4KernelExitV onCore

end

end

end Fl4Spec
