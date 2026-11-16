/-
FL4 differences (PORTING.md, "FL4 differences"): **the error reply with
seL4's `CONFIG_KERNEL_INVOCATION_REPORT_ERROR_IPC`**.

FL4's `KERNEL_INVOCATION_REPORT_ERROR_IPC` (fl4-abi's generated config, set
in the debug profile like seL4's debug option, off in l4v's verified
configuration) makes `reply_error` (syscall.rs) also write the debug word of
a caller with an IPC buffer, word `DEBUG_MESSAGE_START + 1` of the buffer with
its low 8 bits cleared, and count it in the reply's length.

The ported modules are not changed. `fl4ReplyFromKernelError reportError` is
the error reply: l4v's `reply_from_kernel` when `reportError` is false
(`fl4ReplyFromKernelError_false`, by `rfl`), and with the debug word and the
longer length when it is set. `fl4HandleInvocationR reportError` is
`fl4HandleInvocation` (Ext/Invocation) with this error reply
(`fl4HandleInvocationR_false`).
-/
import Fl4Spec.Ext.Invocation

namespace Fl4Spec

open Classical

noncomputable section

section
variable {Z : Type} [StateExt Z]

/-- seL4's `DEBUG_MESSAGE_START` (FL4's `syscall::DEBUG_MESSAGE_START`). -/
def debugMessageStart : Nat := 6

/-- The error reply (see the module docstring): `reply_from_kernel`, and with
`reportError` and an IPC buffer, the debug word and one more word in the
length. -/
def fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : SMonad Z Unit :=
  if reportError then do
    let (label, msg) ← pure x
    let buf ← lookupIpcBuffer true thread
    asUser thread (setRegister badge_register 0)
    let len ← setMrs thread buf msg
    match buf with
    | some p => do
      let w ← loadWordOffs p (debugMessageStart + 1)
      storeWordOffs p (debugMessageStart + 1) (w &&& ~~~255)
      setMessageInfo thread ⟨len + 1, 0, 0, label⟩
    | none => setMessageInfo thread ⟨len, 0, 0, label⟩
  else replyFromKernel thread x

/-- Without the debug option, the error reply is l4v's. -/
theorem fl4ReplyFromKernelError_false (thread : ObjRef) (x : Data × List Data) :
    fl4ReplyFromKernelError (Z := Z) false thread x = replyFromKernel thread x := rfl

/-- `fl4HandleInvocation` with the error reply `fl4ReplyFromKernelError`. -/
def fl4HandleInvocationR (reportError : Bool) (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) :
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
          fl4DecodeInvocation firstPhase info.miLabel args cptr slot cap extracaps buffer)
    (fun err => NonDet.when calling <|
          fl4ReplyFromKernelError reportError thread <| msgFromSyscallError err)
    (fun oper => do
          withoutPreemption <| setThreadState thread .restart
          let reply ← fl4PerformInvocation blocking calling canDonate oper
          withoutPreemption <| do
              let state ← getThreadState thread
              match state with
              | .restart => do
                NonDet.when calling <|
                  replyFromKernel thread (0, reply)
                setThreadState thread .running
              | _ => return ())

/-- Without the debug option, `fl4HandleInvocationR` is `fl4HandleInvocation`. -/
theorem fl4HandleInvocationR_false (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) :
    fl4HandleInvocationR (Z := Z) false calling blocking canDonate firstPhase cptr =
      fl4HandleInvocation calling blocking canDonate firstPhase cptr := rfl

end

end

end Fl4Spec
