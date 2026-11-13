/-
Top-level x86-64 definitions: arch IRQ control, thread switch hooks, and the
ASID, paging and IO port invocations (MCS).

Ports `spec/abstract/X64/Arch_A`. rt X64 gap: l4v `rt` has X64 Arch_A
import TcbAcc_A (the non-MCS import graph), although it uses `cap_insert`
and `max_free_index_update` from CSpace_A; it imports CSpace_A here, as
RISCV64 `rt` Arch_A does. The `PageIOMap` case of `perform_page_invocation`
is commented out in l4v (no IOMMU).
-/
import Fl4Spec.CSpace

namespace Fl4Spec

open Classical

noncomputable section

/-- l4v: Arch_A.X64_A.page_bits. -/
def page_bits : Nat := pageBits

section
variable {Z : Type} [StateExt Z]

/-- l4v: Arch_A.X64_A.update_irq_state (on any `abstract_state_scheme`; here on
the kernel state). -/
def updateIrqState (irq : Irq) (irqState : X64IRQState) : SMonad Z Unit := do
  let irqStates ← NonDet.gets fun s : State Z => s.archState.x64IrqState
  NonDet.modify fun s =>
    { s with archState := { s.archState with x64IrqState := Function.update irqStates irq irqState } }

/-- l4v: Arch_A.X64_A.arch_invoke_irq_control. -/
def archInvokeIrqControl (aic : ArchIrqControlInvocation) : PMonad Z Unit :=
  match aic with
  | .issueIRQHandlerIOAPIC irq dest src ioapic pin level polarity vector => withoutPreemption (do
      doMachineOp <| ioapicMapPinToVector ioapic pin level polarity vector
      let irqState ← pure (X64IRQState.irqIOAPIC (ioapic &&& mask 5) (pin &&& mask 5) (level &&& 1)
        (polarity &&& 1) true)
      updateIrqState irq irqState
      setIrqState .irqSignal (IRQ irq)
      capInsert (.irqHandlerCap (IRQ irq)) src dest)
  | .issueIRQHandlerMSI irq dest src bus dev func handle => withoutPreemption (do
      let irqState ← pure (X64IRQState.irqMSI (bus &&& mask 8) (dev &&& mask 5) (func &&& mask 3)
        (handle &&& mask 32))
      updateIrqState irq irqState
      setIrqState .irqSignal (IRQ irq)
      capInsert (.irqHandlerCap (IRQ irq)) src dest)

/-- l4v: Arch_A.X64_A.arch_switch_to_thread: switch to a thread's address
space and FPU context. -/
def archSwitchToThread (t : ObjRef) : SMonad Z Unit := do
  setVmRoot t
  lazyFpuRestore t

/-- l4v: Arch_A.X64_A.arch_switch_to_idle_thread. -/
def archSwitchToIdleThread : SMonad Z Unit := do
  let thread ← NonDet.gets fun s : State Z => s.idleThread
  setVmRoot thread

/-- l4v: Arch_A.X64_A.arch_prepare_next_domain. -/
def archPrepareNextDomain : SMonad Z Unit := switchLocalFpuOwner none

/-- l4v: Arch_A.X64_A.arch_activate_idle_thread. -/
def archActivateIdleThread (_t : ObjRef) : SMonad Z Unit := return ()

/-- l4v: Arch_A.X64_A.store_asid_pool_entry. -/
def storeAsidPoolEntry (poolPtr : ObjRef) (asid : Asid) (pml4base : Option ObjRef) :
    SMonad Z Unit := do
  let pool ← getAsidPool poolPtr
  let pool' ← pure (Function.update pool (asidLowBitsOf asid) pml4base)
  setAsidPool poolPtr pool'

/-- l4v: Arch_A.X64_A.perform_asid_control_invocation: create a new ASID pool,
a cap to it, and connect it to the global ASID table. -/
def performAsidControlInvocation (iv : AsidControlInvocation) : SMonad Z Unit :=
  match iv with
  | .makePool frame slot parent base => do
    deleteObjects frame page_bits
    let pcap ← getCap parent
    setCap (maxFreeIndexUpdate pcap) parent
    let _ ← retypeRegion frame 1 0 (.archObject .asidPoolObj) false
    capInsert (.archObjectCap (.asidPoolCap frame base)) parent slot
    NonDet.assert (asidLowBitsOf base = 0)
    let asidTable ← NonDet.gets fun s : State Z => s.archState.x64AsidTable
    let asidTable' ← pure (Function.update asidTable (asidHighBitsOf base) (some frame))
    NonDet.modify fun s => { s with archState := { s.archState with x64AsidTable := asidTable' } }

/-- l4v: Arch_A.X64_A.perform_asid_pool_invocation: assign a virtual ASID to
a PML4. -/
def performAsidPoolInvocation (iv : AsidPoolInvocation) : SMonad Z Unit :=
  match iv with
  | .assign asid poolPtr ctSlot => do
    let pml4Cap ← getCap ctSlot
    match pml4Cap with
    | .archObjectCap (.pml4Cap pml4Base _) => do
        setCap (.archObjectCap (.pml4Cap pml4Base (some asid))) ctSlot
        storeAsidPoolEntry poolPtr asid (some pml4Base)
    | _ => NonDet.fail

/-- l4v: Arch_A.X64_A.pte_check_if_mapped. -/
def pteCheckIfMapped (slot : ObjRef) : SMonad Z Bool := do
  let pt ← getPte slot
  return decide (pt ≠ .invalidPTE)

/-- l4v: Arch_A.X64_A.pde_check_if_mapped. -/
def pdeCheckIfMapped (slot : ObjRef) : SMonad Z Bool := do
  let pd ← getPde slot
  return decide (pd ≠ .invalidPDE)

/-- l4v: Arch_A.X64_A.perform_page_invocation_unmap. -/
def performPageInvocationUnmap (cap : ArchCap) (ctSlot : CslotPtr) : SMonad Z Unit :=
  match cap with
  | .pageCap _ base _ _ sz mapped => do
    match mapped with
    | some (asid, vaddr) => unmapPage sz asid vaddr base
    | none => pure ()
    let cap ← NonDet.liftM Cap.theArchCap (getCap ctSlot)
    setCap (.archObjectCap (updateMapData cap none (some .vmNoMap))) ctSlot
  | _ => NonDet.fail

/-- l4v: Arch_A.X64_A.perform_page_invocation: the Page cap confers the
authority to map, unmap and flush a page. -/
def performPageInvocation (iv : PageInvocation) : SMonad Z (List Data) :=
  match iv with
  | .pageMap cap ctSlot entries vspace => do
    setCap cap ctSlot
    match entries with
    | (.vmPTE pte, slot) => storePte slot pte
    | (.vmPDE pde, slot) => storePde slot pde
    | (.vmPDPTE pdpte, slot) => storePdpte slot pdpte
    let asid ← match cap with
      | .archObjectCap (.pageCap _ _ _ _ _ (some (as, _))) => pure as
      | _ => NonDet.fail
    invalidatePageStructureCacheAsid (addrFromPPtr vspace) asid
    return []
  | .pageUnmap cap ctSlot =>
    match cap with
    | .pageCap _ _ _ mapType _ mapped => do
      match mapped with
      | some _ =>
          match mapType with
          | .vmVSpaceMap => performPageInvocationUnmap cap ctSlot
          | _ => NonDet.fail
      | none => pure ()
      return []
    | _ => NonDet.fail
  | .pageGetAddr ptr => return [addrFromPPtr ptr]

/-- l4v: Arch_A.X64_A.perform_page_table_invocation. -/
def performPageTableInvocation (iv : PageTableInvocation) : SMonad Z Unit :=
  match iv with
  | .pageTableMap cap ctSlot pde pdSlot vspace => do
    setCap cap ctSlot
    storePde pdSlot pde
    let asid ← match cap with
      | .archObjectCap (.pageTableCap _ (some (as, _))) => pure as
      | _ => NonDet.fail
    invalidatePageStructureCacheAsid (addrFromPPtr vspace) asid
  | .pageTableUnmap (.archObjectCap (.pageTableCap p mappedAddress)) ctSlot => do
    match mappedAddress with
    | some (asid, vaddr) => do
      unmapPageTable asid vaddr p
      let pteBits ← pure wordSizeBits
      let slots ← pure (uptoEnumStep p (p + ((1 : Word) <<< pteBits)) (p + ((1 : Word) <<< ptBits) - 1))
      NonDet.mapMx (fun slot => storePte slot .invalidPTE) slots
    | none => pure ()
    let cap ← NonDet.liftM Cap.theArchCap (getCap ctSlot)
    setCap (.archObjectCap (updateMapData cap none none)) ctSlot
  | _ => NonDet.fail

/-- l4v: Arch_A.X64_A.perform_page_directory_invocation. -/
def performPageDirectoryInvocation (iv : PageDirectoryInvocation) : SMonad Z Unit :=
  match iv with
  | .pageDirectoryMap cap ctSlot pdpte pdptSlot vspace => do
    setCap cap ctSlot
    storePdpte pdptSlot pdpte
    let asid ← match cap with
      | .archObjectCap (.pageDirectoryCap _ (some (as, _))) => pure as
      | _ => NonDet.fail
    invalidatePageStructureCacheAsid (addrFromPPtr vspace) asid
  | .pageDirectoryUnmap (.archObjectCap (.pageDirectoryCap p mappedAddress)) ctSlot => do
    match mappedAddress with
    | some (asid, vaddr) => do
      unmapPd asid vaddr p
      let pdeBits ← pure wordSizeBits
      let slots ← pure (uptoEnumStep p (p + ((1 : Word) <<< pdeBits)) (p + ((1 : Word) <<< pdBits) - 1))
      NonDet.mapMx (fun slot => storePde slot .invalidPDE) slots
    | none => pure ()
    let cap ← NonDet.liftM Cap.theArchCap (getCap ctSlot)
    setCap (.archObjectCap (updateMapData cap none none)) ctSlot
  | _ => NonDet.fail

/-- l4v: Arch_A.X64_A.perform_pdpt_invocation. -/
def performPdptInvocation (iv : PdptInvocation) : SMonad Z Unit :=
  match iv with
  | .pdptMap cap ctSlot pml4e pml4Slot vspace => do
    setCap cap ctSlot
    storePml4e pml4Slot pml4e
    let asid ← match cap with
      | .archObjectCap (.pdPointerTableCap _ (some (as, _))) => pure as
      | _ => NonDet.fail
    invalidatePageStructureCacheAsid (addrFromPPtr vspace) asid
  | .pdptUnmap (.archObjectCap (.pdPointerTableCap p mappedAddress)) ctSlot => do
    match mappedAddress with
    | some (asid, vaddr) => do
      unmapPdpt asid vaddr p
      let pdeptBits ← pure wordSizeBits
      let slots ← pure (uptoEnumStep p (p + ((1 : Word) <<< pdeptBits)) (p + ((1 : Word) <<< pdptBits) - 1))
      NonDet.mapMx (fun slot => storePdpte slot .invalidPDPTE) slots
    | none => pure ()
    let cap ← NonDet.liftM Cap.theArchCap (getCap ctSlot)
    setCap (.archObjectCap (updateMapData cap none none)) ctSlot
  | _ => NonDet.fail

/-- l4v: Arch_A.X64_A.port_out. -/
def portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) : SMonad Z (List Data) := do
  doMachineOp (f w)
  return []

/-- l4v: Arch_A.X64_A.port_in. -/
def portIn (f : MachineMonad Data) : SMonad Z (List Data) := do
  let res ← doMachineOp f
  return [res]

/-- l4v: Arch_A.X64_A.perform_io_port_invocation. -/
def performIoPortInvocation (i : IoPortInvocation) : SMonad Z (List Data) :=
  match i with
  | .ioPortInvocation port portData =>
    match portData with
    | .ioPortIn8 => portIn (in8 port)
    | .ioPortIn16 => portIn (in16 port)
    | .ioPortIn32 => portIn (in32 port)
    | .ioPortOut8 w => portOut (out8 port) w
    | .ioPortOut16 w => portOut (out16 port) w
    | .ioPortOut32 w => portOut (out32 port) w

/-- l4v: Arch_A.X64_A.perform_ioport_control_invocation. -/
def performIoportControlInvocation (i : IoPortControlInvocation) : SMonad Z Unit :=
  match i with
  | .ioPortControlInvocation f l destSlot controlSlot => do
    setIoportMask f l true
    let _c ← pure (Cap.archObjectCap (.ioPortCap f l))
    capInsert (.archObjectCap (.ioPortCap f l)) controlSlot destSlot

/-- l4v: Arch_A.X64_A.arch_no_return (`abbreviation`). -/
abbrev archNoReturn (oper : SMonad Z Unit) : SMonad Z (List Data) := do
  oper
  return []

/-- l4v: Arch_A.X64_A.arch_perform_invocation: the top-level dispatcher of
x64-specific system calls. -/
def archPerformInvocation (i : ArchInvocation) : PMonad Z (List Data) :=
  NonDetE.liftE <|
    match i with
    | .invokePageTable oper => archNoReturn <| performPageTableInvocation oper
    | .invokePageDirectory oper => archNoReturn <| performPageDirectoryInvocation oper
    | .invokePDPT oper => archNoReturn <| performPdptInvocation oper
    | .invokePage oper => performPageInvocation oper
    | .invokeASIDControl oper => archNoReturn <| performAsidControlInvocation oper
    | .invokeASIDPool oper => archNoReturn <| performAsidPoolInvocation oper
    | .invokeIOPort oper => performIoPortInvocation oper
    | .invokeIOPortControl oper => archNoReturn <| performIoportControlInvocation oper

end

end

end Fl4Spec
