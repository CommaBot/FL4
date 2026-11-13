/-
Basic types of the seL4 abstract specification (MCS, x86-64).

Ports, in theory order:
- `spec/abstract/CapRights_A`;
- `spec/abstract/VMRights_A`;
- `spec/abstract/ExceptionTypes_A`;
- `spec/design/skel/X64/ArchInvocationLabels_H` and
  `spec/design/skel/InvocationLabels_H` (from the Haskell
  `SEL4/API/InvocationLabels/X64.lhs` and `SEL4/API/InvocationLabels.lhs`);
  `ArchLabelFuns_H` is empty on X64;
- `spec/abstract/InvocationLabels_A`.
-/
import Fl4Spec.Machine

namespace Fl4Spec

open Classical

noncomputable section

/-! ## CapRights_A -/

/-- l4v: CapRights_A.rights. -/
inductive Rights where
  | allowRead
  | allowWrite
  | allowGrant
  | allowGrantReply
deriving DecidableEq, Repr, Inhabited

/-- l4v: CapRights_A.AllowSend. -/
def AllowSend : Rights := .allowWrite
/-- l4v: CapRights_A.AllowRecv. -/
def AllowRecv : Rights := .allowRead
/-- l4v: CapRights_A.CanModify. -/
def CanModify : Rights := .allowWrite

/-- l4v: CapRights_A.cap_rights. -/
abbrev CapRights := Set Rights

/-- l4v: CapRights_A.all_rights. -/
def allRights : CapRights := Set.univ

/-! ## VMRights_A -/

/-- l4v: VMRights_A.vm_rights. -/
abbrev VMRights := CapRights

/-- l4v: VMRights_A.vm_kernel_only. -/
def vmKernelOnly : VMRights := ∅
/-- l4v: VMRights_A.vm_read_only. -/
def vmReadOnly : VMRights := {.allowRead}
/-- l4v: VMRights_A.vm_read_write. -/
def vmReadWrite : VMRights := {.allowRead, .allowWrite}

/-- l4v: VMRights_A.valid_vm_rights. -/
def validVmRights : Set VMRights := {vmReadWrite, vmReadOnly, vmKernelOnly}

/-- l4v: VMRights_A.validate_vm_rights: the largest permitted subset. -/
def validateVmRights (rs : VMRights) : VMRights :=
  if Rights.allowRead ∈ rs
  then if Rights.allowWrite ∈ rs then vmReadWrite else vmReadOnly
  else vmKernelOnly

/-- l4v: VMRights_A.mask_vm_rights. -/
def maskVmRights (V : VMRights) (R : CapRights) : VMRights := validateVmRights (V ∩ R)

/-! ## ExceptionTypes_A -/

/-- l4v: ExceptionTypes_A.lookup_failure. -/
inductive LookupFailure where
  | invalidRoot
  | missingCapability (bits : Nat)
  | depthMismatch (bitsLeft bitsFound : Nat)
  | guardMismatch (bitsLeft : Nat) (guard : List Bool)
deriving DecidableEq, Repr, Inhabited

/-- l4v: ExceptionTypes_A.fault. -/
inductive Fault where
  | capFault (addr : ObjRef) (inReceivePhase : Bool) (lf : LookupFailure)
  | unknownSyscallException (n : Data)
  | userException (number code : Data)
  | timeout (badge : Data)
  | archFault (af : ArchFault)
deriving DecidableEq, Repr, Inhabited

/-- l4v: ExceptionTypes_A.syscall_error. -/
inductive SyscallError where
  | invalidArgument (n : Nat)
  | invalidCapability (n : Nat)
  | illegalOperation
  | rangeError (minv maxv : Data)
  | alignmentError
  | failedLookup (sourceIsDest : Bool) (lf : LookupFailure)
  | truncatedMessage
  | deleteFirst
  | revokeFirst
  | notEnoughMemory (n : Data)
deriving DecidableEq, Repr, Inhabited

/-- l4v: ExceptionTypes_A.msg_from_lookup_failure. -/
def msgFromLookupFailure : LookupFailure → List Data
  | .invalidRoot => [1]
  | .missingCapability n => [2, BitVec.ofNat 64 n]
  | .depthMismatch n m => [3, BitVec.ofNat 64 n, BitVec.ofNat 64 m]
  | .guardMismatch n g => [4, BitVec.ofNat 64 n, ofBl g, BitVec.ofNat 64 g.length]

/-- l4v: ExceptionTypes_A.msg_from_syscall_error. -/
def msgFromSyscallError : SyscallError → Data × List Data
  | .invalidArgument n => (1, [BitVec.ofNat 64 n])
  | .invalidCapability n => (2, [BitVec.ofNat 64 n])
  | .illegalOperation => (3, [])
  | .rangeError minv maxv => (4, [minv, maxv])
  | .alignmentError => (5, [])
  | .failedLookup s lf => (6, [if s then 1 else 0] ++ msgFromLookupFailure lf)
  | .truncatedMessage => (7, [])
  | .deleteFirst => (8, [])
  | .revokeFirst => (9, [])
  | .notEnoughMemory n => (10, [n])

/-! ## ArchInvocationLabels_H (Haskell SEL4/API/InvocationLabels/X64.lhs) -/

/-- l4v: ArchInvocationLabels_H.X64_H.arch_invocation_label. The IO page
table labels (`X64IOPageTableMap`, `X64IOPageTableUnmap`, `X64PageMapIO`)
are commented out in the Haskell spec too (no IOMMU). -/
inductive ArchInvocationLabel where
  | x64PDPTMap
  | x64PDPTUnmap
  | x64PageDirectoryMap
  | x64PageDirectoryUnmap
  | x64PageTableMap
  | x64PageTableUnmap
  | x64PageMap
  | x64PageUnmap
  | x64PageGetAddress
  | x64ASIDControlMakePool
  | x64ASIDPoolAssign
  | x64IOPortControlIssue
  | x64IOPortIn8
  | x64IOPortIn16
  | x64IOPortIn32
  | x64IOPortOut8
  | x64IOPortOut16
  | x64IOPortOut32
  | x64IRQIssueIRQHandlerIOAPIC
  | x64IRQIssueIRQHandlerMSI
deriving DecidableEq, Repr, Inhabited

open ArchInvocationLabel in
/-- l4v: ArchInvocationLabels_H.X64_H.enum_arch_invocation_label (the
derived `Enum` order). -/
def ArchInvocationLabel.enum : List ArchInvocationLabel :=
  [x64PDPTMap, x64PDPTUnmap, x64PageDirectoryMap, x64PageDirectoryUnmap, x64PageTableMap,
   x64PageTableUnmap, x64PageMap, x64PageUnmap, x64PageGetAddress, x64ASIDControlMakePool,
   x64ASIDPoolAssign, x64IOPortControlIssue, x64IOPortIn8, x64IOPortIn16, x64IOPortIn32,
   x64IOPortOut8, x64IOPortOut16, x64IOPortOut32, x64IRQIssueIRQHandlerIOAPIC,
   x64IRQIssueIRQHandlerMSI]

/-! ## InvocationLabels_H (Haskell SEL4/API/InvocationLabels.lhs) -/

/-- l4v: InvocationLabels_H.gen_invocation_labels. -/
inductive GenInvocationLabels where
  | invalidInvocation
  | untypedRetype
  | tcbReadRegisters
  | tcbWriteRegisters
  | tcbCopyRegisters
  | tcbConfigure
  | tcbSetPriority
  | tcbSetMCPriority
  | tcbSetSchedParams
  | tcbSetTimeoutEndpoint
  | tcbSetIPCBuffer
  | tcbSetSpace
  | tcbSuspend
  | tcbResume
  | tcbBindNotification
  | tcbUnbindNotification
  | tcbSetTLSBase
  | tcbSetFlags
  | cnodeRevoke
  | cnodeDelete
  | cnodeCancelBadgedSends
  | cnodeCopy
  | cnodeMint
  | cnodeMove
  | cnodeMutate
  | cnodeRotate
  | irqIssueIRQHandler
  | irqAckIRQ
  | irqSetIRQHandler
  | irqClearIRQHandler
  | domainSetSet
  | domainScheduleConfigure
  | domainScheduleSetStart
  | schedControlConfigureFlags
  | schedContextBind
  | schedContextUnbind
  | schedContextUnbindObject
  | schedContextConsumed
  | schedContextYieldTo
deriving DecidableEq, Repr, Inhabited

open GenInvocationLabels in
/-- l4v: InvocationLabels_H.enum_gen_invocation_labels (the derived `Enum`
order). -/
def GenInvocationLabels.enum : List GenInvocationLabels :=
  [invalidInvocation, untypedRetype, tcbReadRegisters, tcbWriteRegisters, tcbCopyRegisters,
   tcbConfigure, tcbSetPriority, tcbSetMCPriority, tcbSetSchedParams, tcbSetTimeoutEndpoint,
   tcbSetIPCBuffer, tcbSetSpace, tcbSuspend, tcbResume, tcbBindNotification,
   tcbUnbindNotification, tcbSetTLSBase, tcbSetFlags, cnodeRevoke, cnodeDelete,
   cnodeCancelBadgedSends, cnodeCopy, cnodeMint, cnodeMove, cnodeMutate, cnodeRotate,
   irqIssueIRQHandler, irqAckIRQ, irqSetIRQHandler, irqClearIRQHandler, domainSetSet,
   domainScheduleConfigure, domainScheduleSetStart, schedControlConfigureFlags,
   schedContextBind, schedContextUnbind, schedContextUnbindObject, schedContextConsumed,
   schedContextYieldTo]

/-- l4v: InvocationLabels_H.invocation_label. -/
inductive InvocationLabel where
  | genInvocationLabel (l : GenInvocationLabels)
  | archInvocationLabel (l : ArchInvocationLabel)
deriving DecidableEq, Repr, Inhabited

/-- l4v: InvocationLabels_H.enum_invocation_label: the generic labels, then
the arch labels (Haskell `Enum InvocationLabel`, numbered
`apiMax + 1 + fromEnum a` for arch label `a`). -/
def InvocationLabel.enum : List InvocationLabel :=
  GenInvocationLabels.enum.map .genInvocationLabel ++
  ArchInvocationLabel.enum.map .archInvocationLabel

/-- l4v: Enumeration.fromEnum on `invocation_label`: the position in
`enum`. -/
def InvocationLabel.fromEnum (l : InvocationLabel) : Nat := InvocationLabel.enum.idxOf l

/-- l4v: Enumeration.toEnum on `invocation_label`: `enum ! n` (unspecified
past the end). -/
def InvocationLabel.toEnum (n : Nat) : InvocationLabel := the (InvocationLabel.enum[n]?)

/-! ## InvocationLabels_A -/

/-- l4v: InvocationLabels_A.invocation_type. -/
def invocationType (x : Data) : InvocationLabel :=
  if ∃ v : InvocationLabel, v.fromEnum = dataToNat x
  then InvocationLabel.toEnum (dataToNat x)
  else .genInvocationLabel .invalidInvocation

/-- l4v: InvocationLabels_A.gen_invocation_type. -/
def genInvocationType (x : Data) : GenInvocationLabels :=
  match invocationType x with
  | .genInvocationLabel l => l
  | .archInvocationLabel _ => .invalidInvocation

end

end Fl4Spec
