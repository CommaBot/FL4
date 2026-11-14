/-
FL4 differences (PORTING.md, "FL4 differences"): **IRQControl**.

1. `IRQIssueIRQHandler` without IOAPICs. l4v X64 rejects it
   (`arch_check_irq` throws `IllegalOperation`; x86 IRQs are issued through
   the IOAPIC or MSI labels). FL4 accepts it when the machine has no IOAPIC
   (legacy PIC, seL4's `Arch_checkIRQ` for x86 without an IOAPIC), for the
   ISA IRQs 0..15.
2. l4h: `X86IRQIssueIRQHandlerIOAPICRemapped`, an IOAPIC handler whose pin
   is routed through the IOMMU's interrupt remapping table. Its decode is
   the IOAPIC one with an eighth argument, the remapping-table handle
   (< 2^16); its invocation programs the pin through the remapping table
   (`ioapicMapPinToVectorRemapped`, a machine operation like
   `ioapicMapPinToVector`).

The ported modules are not changed. `decodeIrqControlInvocationWith` is
`decode_irq_control_invocation` with `arch_check_irq` as a parameter (the
port is the instance `archCheckIrq`, by `rfl`), `fl4ArchCheckIrq` is FL4's.
`decodeFl4IrqControl` adds the remapped label; `invokeFl4IrqControl` is
`invoke_irq_control` with the remapped case.
-/
import Fl4Spec.Decode

namespace Fl4Spec

noncomputable section
open Classical

/-- l4h: program an IOAPIC pin through the interrupt remapping table. -/
opaque ioapicMapPinToVectorRemappedImpl : Word → Word → Word → Word → Word → Word → MachineRestMonad Unit

/-- l4h: `ioapicMapPinToVector` through the interrupt remapping table. -/
def ioapicMapPinToVectorRemapped (ioapic pin level polarity vector handle : Word) : MachineMonad Unit :=
  machineOpLift (ioapicMapPinToVectorRemappedImpl ioapic pin level polarity vector handle)

/-- FL4's IRQControl invocations: l4v's, and the remapped IOAPIC handler. -/
inductive Fl4IrqControlInvocation where
  | spec (i : IrqControlInvocation)
  | ioapicRemapped (irq : Irq) (dest src : CslotPtr) (ioapic pin level polarity vector handle : Word)

section
variable {Z : Type} [StateExt Z]

/-- FL4's `arch_check_irq`: the ISA IRQs through the legacy PIC when there
is no IOAPIC, else (as l4v) `IllegalOperation`. -/
def fl4ArchCheckIrq (irq : Data) : SEMonad Z Unit := do
  let n ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.archState.x64NumIoapics
  if n = 0 then NonDetE.whenE (irq > 15) (NonDetE.throwError (.rangeError 0 15))
  else NonDetE.throwError .illegalOperation

/-- `decode_irq_control_invocation` with `arch_check_irq` as a parameter. -/
def decodeIrqControlInvocationWith (check : Data → SEMonad Z Unit) (label : Data) (args : List Data)
    (srcSlot : CslotPtr) (cps : List Cap) : SEMonad Z IrqControlInvocation :=
  (if genInvocationType label = .irqIssueIRQHandler
    then if args.length ≥ 3 ∧ cps.length ≥ 1
      then
        let irqWord := the args[0]?
        let index := the args[1]?
        let depth := the args[2]?
        let cnode := the cps[0]?
        let irq : Irq := ucast 8 irqWord
        do
          check irqWord
          let irqActive ← NonDetE.liftE <| isIrqActive irq
          NonDetE.whenE irqActive <| NonDetE.throwError .revokeFirst

          let destSlot ← lookupTargetSlot
                 cnode (dataToCptr index) (unat depth)
          ensureEmpty destSlot

          NonDetE.returnOk <| .irqControl irq destSlot srcSlot
      else NonDetE.throwError .truncatedMessage
    else NonDetE.liftME IrqControlInvocation.archIRQControl <|
      archDecodeIrqControlInvocation label args srcSlot cps)

theorem decodeIrqControlInvocationWith_archCheckIrq :
    decodeIrqControlInvocationWith (Z := Z) archCheckIrq = decodeIrqControlInvocation := rfl

/-- l4h: the decode of `X86IRQIssueIRQHandlerIOAPICRemapped`: the IOAPIC
decode, with the remapping-table handle (argument 7). -/
def decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) :
    SEMonad Z Fl4IrqControlInvocation :=
  if args.length ≥ 8 ∧ cps.length ≥ 1
  then
    let preIrq := the args[6]?
    let index := the args[0]?
    let depth := the args[1]?
    let cnode := the cps[0]?
    let irqv : Irq := ucast 8 preIrq + minUserIRQ
    let ioapic := the args[2]?
    let pin := the args[3]?
    let level := the args[4]?
    let polarity := the args[5]?
    let handle := the args[7]?
    let vector : Word := ucast 64 irqv + irqIntOffset
    do
      NonDetE.whenE (preIrq > ucast 64 (maxUserIRQ - minUserIRQ)) <|
        NonDetE.throwError (.rangeError 0 (ucast 64 (maxUserIRQ - minUserIRQ)))
      let irqActive ← NonDetE.liftE <| isIrqActive irqv
      NonDetE.whenE irqActive <| NonDetE.throwError .revokeFirst
      let destSlot ← lookupTargetSlot cnode (dataToCptr index) (unat depth)
      ensureEmpty destSlot
      let numIOAPICs ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.archState.x64NumIoapics
      let ioapicNirqs ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.archState.x64IoapicNirqs
      NonDetE.whenE (numIOAPICs = 0) <| NonDetE.throwError .illegalOperation
      NonDetE.whenE (ioapic > numIOAPICs - 1) <| NonDetE.throwError (.rangeError 0 (numIOAPICs - 1))
      NonDetE.whenE (pin > ucast 64 (ioapicNirqs ioapic - 1)) <|
        NonDetE.throwError (.rangeError 0 (ucast 64 (ioapicNirqs ioapic - 1)))
      NonDetE.whenE (level > 1) <| NonDetE.throwError (.rangeError 0 1)
      NonDetE.whenE (polarity > 1) <| NonDetE.throwError (.rangeError 0 1)
      NonDetE.whenE (handle ≥ 0x10000) <| NonDetE.throwError (.rangeError 0 0xffff)
      NonDetE.returnOk <| .ioapicRemapped irqv destSlot srcSlot ioapic pin level polarity vector handle
  else NonDetE.throwError .truncatedMessage

/-- FL4's IRQControl decode: the remapped label, or l4v's with FL4's
`arch_check_irq`. -/
def decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr)
    (cps : List Cap) : SEMonad Z Fl4IrqControlInvocation :=
  if remapped then decodeIrqControlRemapped args srcSlot cps
  else NonDetE.liftME Fl4IrqControlInvocation.spec <|
    decodeIrqControlInvocationWith fl4ArchCheckIrq label args srcSlot cps

/-- FL4's `invoke_irq_control`. -/
def invokeFl4IrqControl : Fl4IrqControlInvocation → PMonad Z Unit
  | .spec i => invokeIrqControl i
  | .ioapicRemapped irq dest src ioapic pin level polarity vector handle => withoutPreemption (do
      doMachineOp <| ioapicMapPinToVectorRemapped ioapic pin level polarity vector handle
      let irqState ← pure (X64IRQState.irqIOAPIC (ioapic &&& mask 5) (pin &&& mask 5) (level &&& 1)
        (polarity &&& 1) true)
      updateIrqState irq irqState
      setIrqState .irqSignal (IRQ irq)
      capInsert (.irqHandlerCap (IRQ irq)) src dest)

end

end

end Fl4Spec
