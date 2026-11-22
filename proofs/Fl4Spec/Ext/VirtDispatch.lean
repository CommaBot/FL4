/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization,
the extended invocation dispatcher** (proofs/VIRT-PLAN.md §5, §10).

`fl4DecodeInvocationV` wraps `Ext/Invocation`'s `fl4DecodeInvocation`
(unchanged): it routes, in FL4's dispatch order,

* VCPU caps to `decodeVcpuInvocation` (`Ext/VirtVcpu`; the ported
  `arch_decode_invocation` fails on them);
* EPT caps to `decodeEptInvocation` (`Ext/VirtEptInv`; likewise);
* frame caps: label `X86PageMapEPT` to `decodePageMapEpt`; an EPT-mapped
  frame's `X86PageMap` to `InvalidCapability 0` and its `X86PageUnmap` to
  the guest unmap (FL4 `decode_frame`);
* ASID pool caps: `X86ASIDPoolAssign` of an unmapped EPT root to
  `decodeEptAsidPoolAssign`;
* thread caps (second phase): `TCBSetEPTRoot` to `decodeSetEptRoot`
  (`Ext/VirtFinalise`);
* untyped caps: the VT-x gate of `fl4DecodeUntypedInvocationV`, then
  the ported decoder;

and everything else to `fl4DecodeInvocation`. `fl4PerformInvocationV`
performs the new invocations and, for the ported ones, substitutes the
virtualization-aware operations: `fl4InvokeUntypedV` (VCPU init),
`sendSignalV` (notification send), `invokeTcbV` and `invokeCnodeV`
(finalisation hooks); the rest is `fl4PerformInvocation`.
`fl4HandleInvocationV` is `fl4HandleInvocationR` with this dispatcher.

The ported modules are not changed.
-/
import Fl4Spec.Ext.VirtEntry
import Fl4Spec.Ext.ReplyError

namespace Fl4Spec

noncomputable section
open Classical

/-- The invocations of the extended kernel. -/
inductive Fl4InvocationV where
  | base (i : Fl4Invocation)
  | vcpu (i : VcpuInvocation)
  | ept (i : EptInvocation)
  | setEptRoot (i : SetEptRootInvocation)
deriving Inhabited

section
variable {Z : Type} [StateExt Z]

/-- Whether an extra-cap list starts with an unmapped EPT root. -/
def startsWithEptRoot : List (Cap × CslotPtr) → Bool
  | (.archObjectCap (.eptCap _ 0 none), _) :: _ => true
  | _ => false

/-- **The extended decoder** (module docstring). -/
def fl4DecodeInvocationV (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef)
    (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    SEMonad Z Fl4InvocationV :=
  let base : SEMonad Z Fl4InvocationV :=
    NonDetE.liftME Fl4InvocationV.base <|
      fl4DecodeInvocation firstPhase label args capIndex slot cap excaps buffer
  match cap with
  | .archObjectCap (.vcpuCap v) =>
    NonDetE.liftME Fl4InvocationV.vcpu <| decodeVcpuInvocation label args v excaps
  | .archObjectCap (.eptCap p l m) =>
    NonDetE.liftME Fl4InvocationV.ept <| decodeEptInvocation label args slot (.eptCap p l m) excaps
  | .archObjectCap (.pageCap dev p R mt sz m) =>
    if dataToNat label = fl4PageMapEptLabel then
      NonDetE.liftME Fl4InvocationV.ept <| decodePageMapEpt args slot (.pageCap dev p R mt sz m) excaps
    else if mt = .vmEptMap ∧ m.isSome ∧ invocationType label = .archInvocationLabel .x64PageMap then
      NonDetE.throwError (.invalidCapability 0)
    else if mt = .vmEptMap ∧ m.isSome ∧ invocationType label = .archInvocationLabel .x64PageUnmap then
      NonDetE.returnOk (.ept (.frameUnmap (.pageCap dev p R mt sz m) slot))
    else base
  | .archObjectCap (.asidPoolCap p b) =>
    if invocationType label = .archInvocationLabel .x64ASIDPoolAssign ∧ startsWithEptRoot excaps then
      NonDetE.liftME Fl4InvocationV.ept <| decodeEptAsidPoolAssign p b (the excaps.head?).2
    else base
  | .threadCap t =>
    if ¬ firstPhase ∧ dataToNat label = fl4SetEptRootLabel then
      NonDetE.liftME Fl4InvocationV.setEptRoot <| decodeSetEptRoot t excaps
    else base
  | .untypedCap _ _ _ _ =>
    -- `fl4DecodeUntypedInvocationV`, written around `base`.
    if untypedVtxGate label args (excaps.map Prod.fst) then NonDetE.throwError (.invalidArgument 0)
    else base
  | _ => base

/-- **The extended invocations** (module docstring). -/
def fl4PerformInvocationV (onCore : ObjRef → Bool) : Bool → Bool → Bool → Fl4InvocationV →
    PMonad Z (List Data)
  | _, _, _, .base (.invokeUntyped i) => do
    fl4InvokeUntypedV i
    NonDetE.returnOk []
  | _, _, _, .base (.invokeNotification ep badge) => do
    withoutPreemption <| sendSignalV onCore ep badge
    NonDetE.returnOk []
  | _, _, _, .base (.invokeTCB i) => invokeTcbV i
  | _, _, _, .base (.invokeCNode i) => do
    invokeCnodeV i
    NonDetE.returnOk []
  | block, call, canDonate, .base i => fl4PerformInvocation block call canDonate i
  | _, _, _, .vcpu i => NonDetE.liftE <| performVcpuInvocation i
  | _, _, _, .ept i => NonDetE.liftE (do
      performEptInvocation i
      return [])
  | _, _, _, .setEptRoot i => do
    invokeSetEptRoot i
    NonDetE.returnOk []

/-- `fl4HandleInvocationR` (`Ext/ReplyError`) with the extended
dispatcher. -/
def fl4HandleInvocationV (onCore : ObjRef → Bool) (reportError : Bool)
    (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : PMonad Z Unit := do
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
          fl4DecodeInvocationV firstPhase info.miLabel args cptr slot cap extracaps buffer)
    (fun err => NonDet.when calling <|
          fl4ReplyFromKernelError reportError thread <| msgFromSyscallError err)
    (fun oper => do
          withoutPreemption <| setThreadState thread .restart
          let reply ← fl4PerformInvocationV onCore blocking calling canDonate oper
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
