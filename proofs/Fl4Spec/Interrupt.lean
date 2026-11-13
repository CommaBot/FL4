/-
Interrupt handling: IRQ control and handler invocations, and the delivery
of interrupts (MCS, x86-64).

Ports, in theory order:
- `spec/abstract/X64/ArchInterrupt_A` (imports Ipc_A);
- `spec/abstract/Interrupt_A`.

The X64 ArchInterrupt_A on `rt` has the same definitions as RISCV64 `rt`'s
(only the machine operations differ: x86 masks the IRQ line where RISCV64
completes the PLIC claim).
-/
import Fl4Spec.Ipc

namespace Fl4Spec

open Classical

noncomputable section

section
variable {Z : Type} [StateExt Z]

/-! ## ArchInterrupt_A -/

/-- l4v: ArchInterrupt_A.X64_A.handle_reserved_irq. -/
def handleReservedIrq (_irq : Irq) : SMonad Z Unit := return ()

/-- l4v: ArchInterrupt_A.X64_A.arch_invoke_irq_handler. -/
def archInvokeIrqHandler : IrqHandlerInvocation → SMonad Z Unit
  | .aCKIrq irq => doMachineOp <| maskInterrupt false irq
  | _ => return ()

/-- l4v: ArchInterrupt_A.X64_A.arch_mask_irq_signal. -/
def archMaskIrqSignal (irq : Irq) : SMonad Z Unit := doMachineOp <| maskInterrupt true irq

/-- l4v: ArchInterrupt_A.X64_A.handle_spurious_irq. -/
def handleSpuriousIrq : SMonad Z Unit := return ()

/-! ## Interrupt_A -/

/-- l4v: Interrupt_A.invoke_irq_control: create an IRQ handler cap, or an
arch-specific IRQ control action. -/
def invokeIrqControl : IrqControlInvocation → PMonad Z Unit
  | .irqControl irq handlerSlot controlSlot =>
    NonDetE.liftE (do
      setIrqState .irqSignal irq
      capInsert (.irqHandlerCap irq) controlSlot handlerSlot)
  | .archIRQControl invok => archInvokeIrqControl invok

/-- l4v: Interrupt_A.invoke_irq_handler: acknowledge an IRQ, or set or clear
the notification cap in its slot. -/
def invokeIrqHandler : IrqHandlerInvocation → SMonad Z Unit
  | .aCKIrq irq => archInvokeIrqHandler (.aCKIrq irq)
  | .setIRQHandler irq cap slot => do
    let irqSlot ← getIrqSlot irq
    capDeleteOne irqSlot
    capInsert cap slot irqSlot
  | .clearIRQHandler irq => do
    let irqSlot ← getIrqSlot irq
    capDeleteOne irqSlot

/-- l4v: Interrupt_A.handle_interrupt: signal the notification of an IRQ, or
note a timer interrupt. -/
def handleInterrupt (irq : Irq) : SMonad Z Unit :=
  if irq > maxIRQ then doMachineOp (do
    maskInterrupt true irq
    ackInterrupt irq)
  else do
    let st ← getIrqState irq
    match st with
    | .irqSignal => do
      let slot ← getIrqSlot irq
      let cap ← getCap slot
      NonDet.when (isNtfnCap cap ∧ AllowSend ∈ capRights cap) <|
        sendSignal (objRefOf cap) (capEpBadge cap)
      archMaskIrqSignal irq
    | .irqTimer => do
      doMachineOp ackDeadlineIRQ
      NonDet.modify fun s : State Z => { s with reprogramTimer := true }
    | .irqInactive => NonDet.fail -- not meant to be able to get IRQs from inactive lines
    | .irqReserved => handleReservedIrq irq
    doMachineOp <| ackInterrupt irq

/-- l4v: Interrupt_A.maybe_handle_interrupt. -/
def maybeHandleInterrupt (inKernel : Bool) : SMonad Z Unit := do
  let irqOpt ← doMachineOp <| getActiveIRQ inKernel
  match irqOpt with
  | none => handleSpuriousIrq
  | some irq => handleInterrupt irq

end

end

end Fl4Spec
