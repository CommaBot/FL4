/-
The arguments of the kernel object invocations (MCS, x86-64).

Ports, in theory order:
- `spec/abstract/X64/ArchInvocation_A`;
- `spec/abstract/Invocations_A`.

Omitted (no IOMMU): the `PageIOMap` case of `page_invocation`, the
`io_pt_invocation` datatype and the `InvokeIOPT` case of `arch_invocation`
are commented out in l4v (VT-d) and not ported.

The datatypes hold caps, which have no decidable equality (rights are
sets), so they derive only `Inhabited`.
-/
import Fl4Spec.Structures

namespace Fl4Spec

open Classical

noncomputable section

/-! ## ArchInvocation_A -/

/-- l4v: ArchInvocation_A.X64_A.pdpt_invocation. -/
inductive PdptInvocation where
  | pdptMap (cap : Cap) (slot : CslotPtr) (pml4e : PML4E) (pml4Slot : ObjRef) (vspace : ObjRef)
  | pdptUnmap (cap : Cap) (slot : CslotPtr)
deriving Inhabited

/-- l4v: ArchInvocation_A.X64_A.page_directory_invocation. -/
inductive PageDirectoryInvocation where
  | pageDirectoryMap (cap : Cap) (slot : CslotPtr) (pdpte : PDPTE) (pdptSlot : ObjRef)
      (vspace : ObjRef)
  | pageDirectoryUnmap (cap : Cap) (slot : CslotPtr)
deriving Inhabited

/-- l4v: ArchInvocation_A.X64_A.page_table_invocation. -/
inductive PageTableInvocation where
  | pageTableMap (cap : Cap) (slot : CslotPtr) (pde : PDE) (pdSlot : ObjRef) (vspace : ObjRef)
  | pageTableUnmap (cap : Cap) (slot : CslotPtr)
deriving Inhabited

/-- l4v: ArchInvocation_A.X64_A.asid_control_invocation. -/
inductive AsidControlInvocation where
  | makePool (frame : ObjRef) (slot : CslotPtr) (parent : CslotPtr) (base : Asid)
deriving DecidableEq, Repr, Inhabited

/-- l4v: ArchInvocation_A.X64_A.asid_pool_invocation. -/
inductive AsidPoolInvocation where
  | assign (asid : Asid) (poolPtr : ObjRef) (ctSlot : CslotPtr)
deriving DecidableEq, Repr, Inhabited

/-- l4v: ArchInvocation_A.X64_A.page_invocation. The `PageIOMap` case is
commented out in l4v (no IOMMU). -/
inductive PageInvocation where
  | pageMap (pageMapCap : Cap) (pageMapCtSlot : CslotPtr) (pageMapEntries : VMPageEntry × ObjRef)
      (pageMapVspace : ObjRef)
  | pageUnmap (pageUnmapCap : ArchCap) (pageUnmapCapSlot : CslotPtr)
  | pageGetAddr (pageGetPaddr : ObjRef)
deriving Inhabited

/-- l4v: ArchInvocation_A.X64_A.page_map_cap (selector). -/
def PageInvocation.pageMapCap : PageInvocation → Cap
  | .pageMap c _ _ _ => c
  | _ => undefined
/-- l4v: ArchInvocation_A.X64_A.page_map_ct_slot (selector). -/
def PageInvocation.pageMapCtSlot : PageInvocation → CslotPtr
  | .pageMap _ s _ _ => s
  | _ => undefined
/-- l4v: ArchInvocation_A.X64_A.page_map_entries (selector). -/
def PageInvocation.pageMapEntries : PageInvocation → VMPageEntry × ObjRef
  | .pageMap _ _ e _ => e
  | _ => undefined
/-- l4v: ArchInvocation_A.X64_A.page_map_vspace (selector). -/
def PageInvocation.pageMapVspace : PageInvocation → ObjRef
  | .pageMap _ _ _ v => v
  | _ => undefined
/-- l4v: ArchInvocation_A.X64_A.page_unmap_cap (selector). -/
def PageInvocation.pageUnmapCap : PageInvocation → ArchCap
  | .pageUnmap c _ => c
  | _ => undefined
/-- l4v: ArchInvocation_A.X64_A.page_unmap_cap_slot (selector). -/
def PageInvocation.pageUnmapCapSlot : PageInvocation → CslotPtr
  | .pageUnmap _ s => s
  | _ => undefined
/-- l4v: ArchInvocation_A.X64_A.page_get_paddr (selector). -/
def PageInvocation.pageGetPaddr : PageInvocation → ObjRef
  | .pageGetAddr p => p
  | _ => undefined

/-- l4v: ArchInvocation_A.X64_A.io_port_invocation_data. -/
inductive IoPortInvocationData where
  | ioPortIn8
  | ioPortIn16
  | ioPortIn32
  | ioPortOut8 (w : Word8)
  | ioPortOut16 (w : Word16)
  | ioPortOut32 (w : Word32)
deriving DecidableEq, Repr, Inhabited

/-- l4v: ArchInvocation_A.X64_A.io_port_invocation. -/
inductive IoPortInvocation where
  | ioPortInvocation (port : IoPort) (data : IoPortInvocationData)
deriving DecidableEq, Repr, Inhabited

/-- l4v: ArchInvocation_A.X64_A.io_port_control_invocation. -/
inductive IoPortControlInvocation where
  | ioPortControlInvocation (first last : IoPort) (destSlot controlSlot : CslotPtr)
deriving DecidableEq, Repr, Inhabited

-- l4v ArchInvocation_A.io_pt_invocation is commented out (VT-d); not ported.

/-- l4v: ArchInvocation_A.X64_A.arch_invocation. The `InvokeIOPT` case is
commented out in l4v (no IOMMU). -/
inductive ArchInvocation where
  | invokePageTable (i : PageTableInvocation)
  | invokePageDirectory (i : PageDirectoryInvocation)
  | invokePDPT (i : PdptInvocation)
  | invokePage (i : PageInvocation)
  | invokeASIDControl (i : AsidControlInvocation)
  | invokeASIDPool (i : AsidPoolInvocation)
  | invokeIOPort (i : IoPortInvocation)
  | invokeIOPortControl (i : IoPortControlInvocation)
deriving Inhabited

/-- l4v: ArchInvocation_A.X64_A.arch_copy_register_sets. -/
inductive ArchCopyRegisterSets where
  | x64NoExtraRegisters
deriving DecidableEq, Repr, Inhabited

/-- l4v: ArchInvocation_A.X64_A.ArchDefaultExtraRegisters. -/
def ArchDefaultExtraRegisters : ArchCopyRegisterSets := .x64NoExtraRegisters

/-- l4v: ArchInvocation_A.X64_A.arch_irq_control_invocation. -/
inductive ArchIrqControlInvocation where
  | issueIRQHandlerIOAPIC (irq : Irq) (dest src : CslotPtr) (ioapic pin level polarity vector : Word)
  | issueIRQHandlerMSI (irq : Irq) (dest src : CslotPtr) (bus dev func handle : Word)
deriving DecidableEq, Repr, Inhabited

/-! ## Invocations_A -/

/-- l4v: Invocations_A.cnode_invocation. -/
inductive CnodeInvocation where
  | insertCall (cap : Cap) (src dest : CslotPtr)
  | moveCall (cap : Cap) (src dest : CslotPtr)
  | revokeCall (slot : CslotPtr)
  | deleteCall (slot : CslotPtr)
  | rotateCall (cap1 cap2 : Cap) (slot1 slot2 slot3 : CslotPtr)
  | cancelBadgedSendsCall (cap : Cap)
deriving Inhabited

/-- l4v: Invocations_A.untyped_invocation. -/
inductive UntypedInvocation where
  | retype (srcSlot : CslotPtr) (reset : Bool) (base retypeBase : ObjRef) (newType : ApiObjectType)
      (objSz : Nat) (slots : List CslotPtr) (isDevice : Bool)
deriving DecidableEq, Repr, Inhabited

/-- l4v: Invocations_A.tcb_invocation. -/
inductive TcbInvocation where
  | writeRegisters (dest : Word) (resume : Bool) (values : List Word) (arch : ArchCopyRegisterSets)
  | readRegisters (src : Word) (suspend : Bool) (n : Word) (arch : ArchCopyRegisterSets)
  | copyRegisters (dest src : Word) (suspendSource resumeTarget transferFrame transferInteger : Bool)
      (arch : ArchCopyRegisterSets)
  | threadControlCaps (tcTarget : Word) (tcSlot : CslotPtr)
      (tcNewFaultHandler : Option (Cap × CslotPtr))
      (tcNewTimeoutHandler : Option (Cap × CslotPtr))
      (tcNewCroot : Option (Cap × CslotPtr))
      (tcNewVroot : Option (Cap × CslotPtr))
      (tcNewBuffer : Option (VSpaceRef × Option (Cap × CslotPtr)))
  | threadControlSched (tcTarget : Word) (tcSlot : CslotPtr)
      (tcNewFaultHandler : Option (Cap × CslotPtr))
      (tcNewMcpriority : Option (Word8 × ObjRef))
      (tcNewPriority : Option (Word8 × ObjRef))
      (tcNewSc : Option (Option ObjRef))
  | suspend (t : ObjRef)
  | resume (t : ObjRef)
  | notificationControl (t : ObjRef) (ntfn : Option ObjRef)
  | setTLSBase (t : ObjRef) (base : Word)
  | setFlags (t : ObjRef) (clear set : TcbFlags)
deriving Inhabited

/-- l4v: Invocations_A.tc_target (selector of two constructors). -/
def TcbInvocation.tcTarget : TcbInvocation → Word
  | .threadControlCaps t _ _ _ _ _ _ => t
  | .threadControlSched t _ _ _ _ _ => t
  | _ => undefined
/-- l4v: Invocations_A.tc_slot (selector of two constructors). -/
def TcbInvocation.tcSlot : TcbInvocation → CslotPtr
  | .threadControlCaps _ s _ _ _ _ _ => s
  | .threadControlSched _ s _ _ _ _ => s
  | _ => undefined
/-- l4v: Invocations_A.tc_new_fault_handler (selector of two constructors). -/
def TcbInvocation.tcNewFaultHandler : TcbInvocation → Option (Cap × CslotPtr)
  | .threadControlCaps _ _ f _ _ _ _ => f
  | .threadControlSched _ _ f _ _ _ => f
  | _ => undefined
/-- l4v: Invocations_A.tc_new_timeout_handler (selector). -/
def TcbInvocation.tcNewTimeoutHandler : TcbInvocation → Option (Cap × CslotPtr)
  | .threadControlCaps _ _ _ t _ _ _ => t
  | _ => undefined
/-- l4v: Invocations_A.tc_new_croot (selector). -/
def TcbInvocation.tcNewCroot : TcbInvocation → Option (Cap × CslotPtr)
  | .threadControlCaps _ _ _ _ c _ _ => c
  | _ => undefined
/-- l4v: Invocations_A.tc_new_vroot (selector). -/
def TcbInvocation.tcNewVroot : TcbInvocation → Option (Cap × CslotPtr)
  | .threadControlCaps _ _ _ _ _ v _ => v
  | _ => undefined
/-- l4v: Invocations_A.tc_new_buffer (selector). -/
def TcbInvocation.tcNewBuffer : TcbInvocation → Option (VSpaceRef × Option (Cap × CslotPtr))
  | .threadControlCaps _ _ _ _ _ _ b => b
  | _ => undefined
/-- l4v: Invocations_A.tc_new_mcpriority (selector). -/
def TcbInvocation.tcNewMcpriority : TcbInvocation → Option (Word8 × ObjRef)
  | .threadControlSched _ _ _ m _ _ => m
  | _ => undefined
/-- l4v: Invocations_A.tc_new_priority (selector). -/
def TcbInvocation.tcNewPriority : TcbInvocation → Option (Word8 × ObjRef)
  | .threadControlSched _ _ _ _ p _ => p
  | _ => undefined
/-- l4v: Invocations_A.tc_new_sc (selector). -/
def TcbInvocation.tcNewSc : TcbInvocation → Option (Option ObjRef)
  | .threadControlSched _ _ _ _ _ sc => sc
  | _ => undefined

/-- l4v: Invocations_A.sched_context_invocation. -/
inductive SchedContextInvocation where
  | invokeSchedContextConsumed (scPtr : ObjRef)
  | invokeSchedContextBind (scPtr : ObjRef) (cap : Cap)
  | invokeSchedContextUnbindObject (scPtr : ObjRef) (cap : Cap)
  | invokeSchedContextUnbind (scPtr : ObjRef)
  | invokeSchedContextYieldTo (scPtr : ObjRef)
deriving Inhabited

/-- l4v: Invocations_A.sched_control_invocation. -/
inductive SchedControlInvocation where
  | invokeSchedControlConfigureFlags (scPtr : ObjRef) (budget period : Ticks) (refills : Nat)
      (badge : Badge) (flags : Data)
deriving DecidableEq, Repr, Inhabited

/-- l4v: Invocations_A.irq_control_invocation. -/
inductive IrqControlInvocation where
  | irqControl (irq : Irq) (handlerSlot controlSlot : CslotPtr)
  | archIRQControl (i : ArchIrqControlInvocation)
deriving DecidableEq, Repr, Inhabited

/-- l4v: Invocations_A.irq_handler_invocation. -/
inductive IrqHandlerInvocation where
  | aCKIrq (irq : Irq)
  | setIRQHandler (irq : Irq) (cap : Cap) (slot : CslotPtr)
  | clearIRQHandler (irq : Irq)
deriving Inhabited

/-- l4v: Invocations_A.domain_invocation. -/
inductive DomainInvocation where
  | invokeDomainSet (domThread : ObjRef) (domDomain : Domain)
  | invokeDomainScheduleSetStart (domIndex : Nat)
  | invokeDomainScheduleConfigure (domIndex : Nat) (domDomain : Domain)
      (domDuration : DomainDuration)
deriving DecidableEq, Repr, Inhabited

/-- l4v: Invocations_A.dom_thread (selector). -/
def DomainInvocation.domThread : DomainInvocation → ObjRef
  | .invokeDomainSet t _ => t
  | _ => undefined
/-- l4v: Invocations_A.dom_domain (selector of two constructors). -/
def DomainInvocation.domDomain : DomainInvocation → Domain
  | .invokeDomainSet _ d => d
  | .invokeDomainScheduleConfigure _ d _ => d
  | _ => undefined
/-- l4v: Invocations_A.dom_index (selector of two constructors). -/
def DomainInvocation.domIndex : DomainInvocation → Nat
  | .invokeDomainScheduleSetStart i => i
  | .invokeDomainScheduleConfigure i _ _ => i
  | _ => undefined
/-- l4v: Invocations_A.dom_duration (selector). -/
def DomainInvocation.domDuration : DomainInvocation → DomainDuration
  | .invokeDomainScheduleConfigure _ _ d => d
  | _ => undefined

/-- l4v: Invocations_A.invocation. -/
inductive Invocation where
  | invokeUntyped (i : UntypedInvocation)
  | invokeEndpoint (ep : ObjRef) (badge : Word) (canGrant canGrantReply : Bool)
  | invokeNotification (ntfn : ObjRef) (badge : Word)
  | invokeReply (reply : ObjRef) (canGrant : Bool)
  | invokeTCB (i : TcbInvocation)
  | invokeDomain (i : DomainInvocation)
  | invokeSchedContext (i : SchedContextInvocation)
  | invokeSchedControl (i : SchedControlInvocation)
  | invokeCNode (i : CnodeInvocation)
  | invokeIRQControl (i : IrqControlInvocation)
  | invokeIRQHandler (i : IrqHandlerInvocation)
  | invokeArchObject (i : ArchInvocation)
deriving Inhabited

end

end Fl4Spec
