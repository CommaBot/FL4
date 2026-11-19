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

open GenInvocationLabels ArchInvocationLabel in
/-- **FL4 deviation: FL4's label numbers** (PORTING.md, "Invocation label
numbers"). Entry `n` is the label FL4's ABI numbers `n` (`fl4_abi::label`,
generated by `crates/fl4-abi/build.rs` from `interfaces/object-api*.xml`, the
x86-64 build with the hardware debug API), `none` where FL4's label is not
an l4v label: seL4's debug API (16..19), FL4's TCB FPU and timer labels
(22..24), `X86PML4Flush` (46), the VCPU MSR labels (49, 50),
`X86PageDeriveSubframe`, `X86PageTestAndClearAccessed` (57, 58),
`X86PageMapEPT` (60); every number from 72 on (the remapped IOAPIC label,
the VCPU and EPT labels, `TCBSetEPTRoot`, `UntypedRetypeShared`) is past the
list. The l4v labels keep l4v's relative order (`enum`'s), with gaps. -/
def InvocationLabel.fl4Numbering : List (Option InvocationLabel) :=
  [some (.genInvocationLabel invalidInvocation), some (.genInvocationLabel untypedRetype),
   some (.genInvocationLabel tcbReadRegisters), some (.genInvocationLabel tcbWriteRegisters),
   some (.genInvocationLabel tcbCopyRegisters), some (.genInvocationLabel tcbConfigure),
   some (.genInvocationLabel tcbSetPriority), some (.genInvocationLabel tcbSetMCPriority),
   some (.genInvocationLabel tcbSetSchedParams), some (.genInvocationLabel tcbSetTimeoutEndpoint),
   some (.genInvocationLabel tcbSetIPCBuffer), some (.genInvocationLabel tcbSetSpace),
   some (.genInvocationLabel tcbSuspend), some (.genInvocationLabel tcbResume),
   some (.genInvocationLabel tcbBindNotification), some (.genInvocationLabel tcbUnbindNotification),
   none, none, none, none,
   some (.genInvocationLabel tcbSetTLSBase), some (.genInvocationLabel tcbSetFlags),
   none, none, none,
   some (.genInvocationLabel cnodeRevoke), some (.genInvocationLabel cnodeDelete),
   some (.genInvocationLabel cnodeCancelBadgedSends), some (.genInvocationLabel cnodeCopy),
   some (.genInvocationLabel cnodeMint), some (.genInvocationLabel cnodeMove),
   some (.genInvocationLabel cnodeMutate), some (.genInvocationLabel cnodeRotate),
   some (.genInvocationLabel irqIssueIRQHandler), some (.genInvocationLabel irqAckIRQ),
   some (.genInvocationLabel irqSetIRQHandler), some (.genInvocationLabel irqClearIRQHandler),
   some (.genInvocationLabel domainSetSet), some (.genInvocationLabel domainScheduleConfigure),
   some (.genInvocationLabel domainScheduleSetStart), some (.genInvocationLabel schedControlConfigureFlags),
   some (.genInvocationLabel schedContextBind), some (.genInvocationLabel schedContextUnbind),
   some (.genInvocationLabel schedContextUnbindObject), some (.genInvocationLabel schedContextConsumed),
   some (.genInvocationLabel schedContextYieldTo),
   none,
   some (.archInvocationLabel x64PDPTMap), some (.archInvocationLabel x64PDPTUnmap),
   none, none,
   some (.archInvocationLabel x64PageDirectoryMap), some (.archInvocationLabel x64PageDirectoryUnmap),
   some (.archInvocationLabel x64PageTableMap), some (.archInvocationLabel x64PageTableUnmap),
   some (.archInvocationLabel x64PageMap), some (.archInvocationLabel x64PageUnmap),
   none, none,
   some (.archInvocationLabel x64PageGetAddress),
   none,
   some (.archInvocationLabel x64ASIDControlMakePool), some (.archInvocationLabel x64ASIDPoolAssign),
   some (.archInvocationLabel x64IOPortControlIssue), some (.archInvocationLabel x64IOPortIn8),
   some (.archInvocationLabel x64IOPortIn16), some (.archInvocationLabel x64IOPortIn32),
   some (.archInvocationLabel x64IOPortOut8), some (.archInvocationLabel x64IOPortOut16),
   some (.archInvocationLabel x64IOPortOut32), some (.archInvocationLabel x64IRQIssueIRQHandlerIOAPIC),
   some (.archInvocationLabel x64IRQIssueIRQHandlerMSI)]

/-- l4v: Enumeration.fromEnum on `invocation_label`; FL4: the label's FL4
number, its position in `fl4Numbering` (l4v: its position in `enum`). -/
def InvocationLabel.fromEnum (l : InvocationLabel) : Nat := InvocationLabel.fl4Numbering.idxOf (some l)

/-- l4v: Enumeration.toEnum on `invocation_label`; FL4: the label FL4
numbers `n` (unspecified at a number with no l4v label; l4v: `enum ! n`). -/
def InvocationLabel.toEnum (n : Nat) : InvocationLabel := the ((InvocationLabel.fl4Numbering[n]?).bind id)

/-! ## InvocationLabels_A -/

/-- l4v: InvocationLabels_A.invocation_type (with FL4's numbers:
`fromEnum`, `toEnum`). -/
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
