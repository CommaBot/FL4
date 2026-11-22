/-
FL4 differences (PORTING.md, "FL4 differences"): **the invocation
dispatcher**.

`fl4DecodeInvocation` and `fl4PerformInvocation` are l4v's
`decode_invocation` (Decode_A) and `perform_invocation` (Syscall_A) with
exactly four substitutions, FL4's untyped, IRQControl, arch and TCB
functions:

1. untyped caps: `fl4DecodeUntypedInvocation` and `fl4InvokeUntyped`
   (4 KiB TCBs, `Ext/TcbSize`) for `decode_untyped_invocation` and
   `invoke_untyped`;
2. the IRQControl cap: `decodeFl4IrqControl` and `invokeFl4IrqControl`
   (`Ext/IrqControl`) for `decode_irq_control_invocation` and
   `invoke_irq_control`. The l4h label `IRQIssueIRQHandlerIOAPICRemapped` is
   not an l4v label; its number is FL4's (`fl4RemappedLabel`).
3. arch caps: `fl4ArchDecodeInvocation` and `fl4ArchPerformInvocation` for
   `arch_decode_invocation` and `arch_perform_invocation` (ArchDecode_A,
   Arch_A). They are l4v's, except that the l4h VSpace labels go to the
   `Ext/VSpace` decoders and invocations: `X64PML4Flush` on a PML4 cap
   (`decodePml4Flush`, `performPml4Flush`), `Page_DeriveSubframe` and
   `Page_TestAndClearAccessed` on a frame cap (`decodeDeriveSubframe`,
   `performDeriveSubframe`; `decodeTestAndClearAccessed`,
   `performTestAndClearAccessed`), and the FL4 extension `X86PML4FrameBatch`
   on a PML4 cap (`decodeFrameBatch`, `performFrameBatch`, `Ext/FrameBatch`;
   no seL4 counterpart). These labels are not l4v labels either:
   their numbers are FL4's (`fl4Pml4FlushLabel`, `fl4DeriveSubframeLabel`,
   `fl4TestAndClearLabel`, `fl4FrameBatchLabel`).

4. thread caps: `fl4DecodeTcbInvocation` for `decode_tcb_invocation`,
   which is l4v's except for FL4's TCB extensions (`Ext/Tcb`): the label
   `TCBSetFlags` goes to FL4's `decodeFl4SetFlags`, and the extension
   labels (seL4's debug API, l4h's FPU transfer and timer), at FL4's
   numbers (`fl4TcbExtLabelNum`), to their decoders
   (`decodeFl4TcbExt`); their invocations are `invokeFl4TCB`
   (`invokeFl4Tcb`).

`fl4HandleInvocation` is l4v's `handle_invocation` (Syscall_A) with this
dispatcher.

So the invocation type `Fl4Invocation` is l4v's `invocation` with
`InvokeIRQControl` carrying `Fl4IrqControlInvocation` and
`InvokeArchObject` carrying `Fl4ArchInvocation` (l4v's arch invocations and
the l4h ones). Every other cap goes to l4v's decoders and invocations,
unchanged.

The ported modules are not changed.
-/
import Fl4Spec.Syscall
import Fl4Spec.Ext.TcbSize
import Fl4Spec.Ext.IrqControl
import Fl4Spec.Ext.VSpace
import Fl4Spec.Ext.Tcb
import Fl4Spec.Ext.FrameBatch

namespace Fl4Spec

noncomputable section
open Classical

/-- l4h: the label number of `IRQIssueIRQHandlerIOAPICRemapped`
(`fl4_abi::label`, PORTING.md "Invocation label numbers"), past every
number of `InvocationLabel.fl4Numbering`. -/
def fl4RemappedLabel : Nat := 72

/-- Whether a message label is the remapped IOAPIC label. -/
def isFl4RemappedLabel (label : Data) : Bool := decide (dataToNat label = fl4RemappedLabel)

/-- l4h: the label number of `X64PML4Flush` (FL4's `X86PML4Flush`). -/
def fl4Pml4FlushLabel : Nat := 46
/-- l4h: the label number of `X86PageDeriveSubframe`. -/
def fl4DeriveSubframeLabel : Nat := 57
/-- l4h: the label number of `X86PageTestAndClearAccessed`. -/
def fl4TestAndClearLabel : Nat := 58

/-- The label number of an FL4 TCB extension label (FL4's ABI numbers:
seL4's debug API, then after `TCBSetTLSBase`/`TCBSetFlags` the FPU and
timer labels). -/
def fl4TcbExtLabelNum : Fl4TcbExtLabel → Nat
  | .setBreakpoint => 16
  | .getBreakpoint => 17
  | .unsetBreakpoint => 18
  | .configureSingleStepping => 19
  | .readFpu => 22
  | .writeFpu => 23
  | .setTimer => 24

/-- The FL4 TCB extension label of a message label not in l4v's
enumeration, if any. -/
def fl4TcbExtLabelOf (label : Data) : Option Fl4TcbExtLabel :=
  if genInvocationType label = .invalidInvocation then
    [Fl4TcbExtLabel.setBreakpoint, .getBreakpoint, .unsetBreakpoint, .configureSingleStepping, .readFpu,
      .writeFpu, .setTimer].find? fun l => decide (dataToNat label = fl4TcbExtLabelNum l)
  else none

/-- FL4's arch invocations: l4v's, and the l4h VSpace ones. -/
inductive Fl4ArchInvocation where
  | spec (i : ArchInvocation)
  | pml4Flush (i : Fl4Pml4Invocation)
  | deriveSubframe (i : Fl4SubframeInvocation)
  | testAndClearAccessed (slot : ObjRef)
  /-- FL4 extension (no l4v counterpart): `X86PML4FrameBatch` (`Ext/FrameBatch`). -/
  | frameBatch (i : Fl4FrameBatchInvocation)
deriving Inhabited

/-- l4v's `invocation` (Invocations_A) with FL4's IRQControl and arch
invocations. -/
inductive Fl4Invocation where
  | invokeUntyped (i : UntypedInvocation)
  | invokeEndpoint (ep : ObjRef) (badge : Word) (canGrant canGrantReply : Bool)
  | invokeNotification (ntfn : ObjRef) (badge : Word)
  | invokeReply (reply : ObjRef) (canGrant : Bool)
  | invokeTCB (i : TcbInvocation)
  | invokeFl4TCB (i : Fl4TcbInvocation)
  | invokeDomain (i : DomainInvocation)
  | invokeSchedContext (i : SchedContextInvocation)
  | invokeSchedControl (i : SchedControlInvocation)
  | invokeCNode (i : CnodeInvocation)
  | invokeIRQControl (i : Fl4IrqControlInvocation)
  | invokeIRQHandler (i : IrqHandlerInvocation)
  | invokeArchObject (i : Fl4ArchInvocation)
deriving Inhabited

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchDecode_A.X64_A.arch_decode_invocation, with the l4h VSpace
labels. -/
def fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr)
    (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : SEMonad Z Fl4ArchInvocation :=
  match cap with
  | .pml4Cap _ _ =>
    if dataToNat label = fl4Pml4FlushLabel
    then NonDetE.liftME Fl4ArchInvocation.pml4Flush <| decodePml4Flush cap
    else if dataToNat label = fl4FrameBatchLabel
    then NonDetE.liftME Fl4ArchInvocation.frameBatch <| decodeFrameBatch args cap extraCaps
    else NonDetE.liftME Fl4ArchInvocation.spec <| archDecodeInvocation label args xSlot cte cap extraCaps
  | .pageCap _ _ _ _ _ _ =>
    if dataToNat label = fl4DeriveSubframeLabel
    then NonDetE.liftME Fl4ArchInvocation.deriveSubframe <| decodeDeriveSubframe args cte cap extraCaps
    else if dataToNat label = fl4TestAndClearLabel
    then NonDetE.liftME Fl4ArchInvocation.testAndClearAccessed <| decodeTestAndClearAccessed cap
    else NonDetE.liftME Fl4ArchInvocation.spec <| archDecodeInvocation label args xSlot cte cap extraCaps
  | _ => NonDetE.liftME Fl4ArchInvocation.spec <| archDecodeInvocation label args xSlot cte cap extraCaps

/-- l4v: Arch_A.X64_A.arch_perform_invocation, with the l4h VSpace
invocations. -/
def fl4ArchPerformInvocation : Fl4ArchInvocation → PMonad Z (List Data)
  | .spec i => archPerformInvocation i
  | .pml4Flush i => NonDetE.liftE <| archNoReturn <| performPml4Flush i
  | .deriveSubframe i => NonDetE.liftE <| archNoReturn <| performDeriveSubframe i
  | .testAndClearAccessed slot => NonDetE.liftE <| performTestAndClearAccessed slot
  | .frameBatch i => NonDetE.liftE <| performFrameBatch i

/-- l4v: Decode_A.decode_tcb_invocation, with FL4's TCB extensions
(`Ext/Tcb`): FL4's `SetFlags`, and the extension labels. -/
def fl4DecodeTcbInvocation (label : Data) (args : List Data) (cap : Cap) (slot : CslotPtr)
    (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : SEMonad Z Fl4Invocation :=
  if genInvocationType label = .tcbSetFlags then
    NonDetE.liftME Fl4Invocation.invokeFl4TCB <| decodeFl4SetFlags args (objRefOf cap)
  else match fl4TcbExtLabelOf label with
    | some l => NonDetE.liftME Fl4Invocation.invokeFl4TCB <| decodeFl4TcbExt l args (objRefOf cap) excaps buffer
    | none => NonDetE.liftME Fl4Invocation.invokeTCB <| decodeTcbInvocation label args cap slot excaps

/-- l4v: Decode_A.decode_invocation, with FL4's untyped, IRQControl, TCB and
arch decoders. -/
def fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef)
    (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    SEMonad Z Fl4Invocation :=
  match cap with
  | .endpointCap ptr badge rights =>
    if AllowSend ∈ rights then
      NonDetE.returnOk <| .invokeEndpoint ptr badge (decide (Rights.allowGrant ∈ rights))
        (decide (Rights.allowGrantReply ∈ rights))
    else NonDetE.throwError <| .invalidCapability 0
  | .notificationCap ptr badge rights =>
    if AllowSend ∈ rights then
      NonDetE.returnOk <| .invokeNotification ptr badge
    else NonDetE.throwError <| .invalidCapability 0
  | .replyCap reply rights =>
    NonDetE.returnOk <| .invokeReply reply (decide (Rights.allowGrant ∈ rights))
  | .irqControlCap =>
    NonDetE.liftME Fl4Invocation.invokeIRQControl
      <| decodeFl4IrqControl (isFl4RemappedLabel label) label args slot (excaps.map Prod.fst)
  | .irqHandlerCap irq =>
    NonDetE.liftME Fl4Invocation.invokeIRQHandler
      <| decodeIrqHandlerInvocation label irq excaps
  | .threadCap _ptr =>
    if firstPhase
    then NonDetE.throwError <| .invalidCapability 0
    else fl4DecodeTcbInvocation label args cap slot excaps buffer
  | .domainCap =>
    if firstPhase
    then NonDetE.throwError <| .invalidCapability 0
    else NonDetE.liftME Fl4Invocation.invokeDomain <| decodeDomainInvocation label args excaps
  | .schedContextCap sc _sz =>
    if firstPhase
    then NonDetE.throwError <| .invalidCapability 0
    else NonDetE.liftME Fl4Invocation.invokeSchedContext <|
      decodeSchedContextInvocation label sc (excaps.map Prod.fst)
  | .schedControlCap =>
    if firstPhase
    then NonDetE.throwError <| .invalidCapability 0
    else NonDetE.liftME Fl4Invocation.invokeSchedControl <|
      decodeSchedControlInvocationFlags label args (excaps.map Prod.fst)
  | .cnodeCap _ptr _bits _ =>
    if firstPhase
    then NonDetE.throwError <| .invalidCapability 0
    else NonDetE.liftME Fl4Invocation.invokeCNode <|
      decodeCnodeInvocation label args cap (excaps.map Prod.fst)
  | .untypedCap _dev _ptr _sz _fi =>
    NonDetE.liftME Fl4Invocation.invokeUntyped <|
      fl4DecodeUntypedInvocation label args slot cap (excaps.map Prod.fst)
  | .archObjectCap archCap =>
    NonDetE.liftME Fl4Invocation.invokeArchObject <|
      fl4ArchDecodeInvocation label args capIndex slot archCap excaps
  | _ =>
    NonDetE.throwError <| .invalidCapability 0

/-- l4v: Syscall_A.perform_invocation, with FL4's untyped, IRQControl and
arch invocations. -/
def fl4PerformInvocation : Bool → Bool → Bool → Fl4Invocation → PMonad Z (List Data)
  | _, _, _, .invokeUntyped i => do
    fl4InvokeUntyped i
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
  | _, _, _, .invokeFl4TCB i => invokeFl4Tcb i
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
    invokeFl4IrqControl i
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
    fl4ArchPerformInvocation i

/-- l4v: Syscall_A.handle_invocation, with FL4's dispatcher
(`fl4DecodeInvocation`, `fl4PerformInvocation`). -/
def fl4HandleInvocation (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) :
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
          replyFromKernel thread <| msgFromSyscallError err)
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

end

end

end Fl4Spec
