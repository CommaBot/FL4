/-
FL4 differences (PORTING.md, "FL4 differences"): **the invocation
dispatcher**.

`fl4DecodeInvocation` and `fl4PerformInvocation` are l4v's
`decode_invocation` (Decode_A) and `perform_invocation` (Syscall_A) with
exactly two substitutions, FL4's untyped and IRQControl functions:

1. untyped caps: `fl4DecodeUntypedInvocation` and `fl4InvokeUntyped`
   (4 KiB TCBs, `Ext/TcbSize`) for `decode_untyped_invocation` and
   `invoke_untyped`;
2. the IRQControl cap: `decodeFl4IrqControl` and `invokeFl4IrqControl`
   (`Ext/IrqControl`) for `decode_irq_control_invocation` and
   `invoke_irq_control`. The l4h label `IRQIssueIRQHandlerIOAPICRemapped` is
   not an l4v label; it is the first label number past l4v's
   (`fl4RemappedLabel`, the length of `invocation_label`'s enumeration).

So the invocation type `Fl4Invocation` is l4v's `invocation` with
`InvokeIRQControl` carrying `Fl4IrqControlInvocation`. Every other cap goes
to l4v's decoders and invocations, unchanged.

The ported modules are not changed.
-/
import Fl4Spec.Syscall
import Fl4Spec.Ext.TcbSize
import Fl4Spec.Ext.IrqControl

namespace Fl4Spec

noncomputable section
open Classical

/-- l4h: the label number of `IRQIssueIRQHandlerIOAPICRemapped`, the first
past l4v's `invocation_label` enumeration. -/
def fl4RemappedLabel : Nat := InvocationLabel.enum.length

/-- Whether a message label is the remapped IOAPIC label. -/
def isFl4RemappedLabel (label : Data) : Bool := decide (dataToNat label = fl4RemappedLabel)

/-- l4v's `invocation` (Invocations_A) with FL4's IRQControl invocations. -/
inductive Fl4Invocation where
  | invokeUntyped (i : UntypedInvocation)
  | invokeEndpoint (ep : ObjRef) (badge : Word) (canGrant canGrantReply : Bool)
  | invokeNotification (ntfn : ObjRef) (badge : Word)
  | invokeReply (reply : ObjRef) (canGrant : Bool)
  | invokeTCB (i : TcbInvocation)
  | invokeDomain (i : DomainInvocation)
  | invokeSchedContext (i : SchedContextInvocation)
  | invokeSchedControl (i : SchedControlInvocation)
  | invokeCNode (i : CnodeInvocation)
  | invokeIRQControl (i : Fl4IrqControlInvocation)
  | invokeIRQHandler (i : IrqHandlerInvocation)
  | invokeArchObject (i : ArchInvocation)
deriving Inhabited

section
variable {Z : Type} [StateExt Z]

/-- l4v: Decode_A.decode_invocation, with FL4's untyped and IRQControl
decoders. -/
def fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef)
    (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) :
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
    else NonDetE.liftME Fl4Invocation.invokeTCB <| decodeTcbInvocation label args cap slot excaps
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
      archDecodeInvocation label args capIndex slot archCap excaps
  | _ =>
    NonDetE.throwError <| .invalidCapability 0

/-- l4v: Syscall_A.perform_invocation, with FL4's untyped and IRQControl
invocations. -/
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
    archPerformInvocation i

end

end

end Fl4Spec
