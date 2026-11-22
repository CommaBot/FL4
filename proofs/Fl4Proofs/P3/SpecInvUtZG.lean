/- g5g: `IKH (HU U)` (the cap half of untyped_ranges_zero) for the spec functions of the syscall entry
that write caps and need no carried fact (g5c's SpecInvIoPortsG renamed, without the untyped performs;
the leaves of SpecInvUtZW/Y): the IRQ control issues, the ASID pool, IPC with cap transfer, the fault and
timeout paths, budget charging, the preemption path, DeriveSubframe. -/
import Fl4Proofs.P3.SpecInvUtZY
open Classical

namespace Fl4Proofs.P3.SInvUZ
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {U : UtSet}


theorem hu_archInvokeIrqControl (aic : ArchIrqControlInvocation) : IKHE (HU U) (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_archInvokeIrqControl _)

theorem hu_performAsidPoolInvocation (iv : AsidPoolInvocation) : IKH (HU U) (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_performAsidPoolInvocation _)

theorem hu_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : IKH (HU U) (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_doIpcTransfer _ _ _ _ _)

theorem hu_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : IKH (HU U) (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_sendIpc _ _ _ _ _ _ _ _)

theorem hu_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : IKH (HU U) (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_sendFaultIpc _ _ _ _)

theorem hu_handleTimeout (tptr : ObjRef) (ex : Fault) : IKH (HU U) (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_handleTimeout _ _)

theorem hu_endTimeslice (canTimeout : Bool) : IKH (HU U) (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_endTimeslice _)

theorem hu_chargeBudget (consumed : Ticks) (canTimeout : Bool) : IKH (HU U) (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_chargeBudget _ _)

theorem hu_checkBudget  : IKH (HU U) (checkBudget (Z := Unit)) := by
  unfold checkBudget; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_checkBudget)

theorem hu_checkBudgetRestart  : IKH (HU U) (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_checkBudgetRestart)

theorem hu_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : IKH (HU U) (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_doReplyTransfer _ _ _)

theorem hu_performDeriveSubframe (iv : Fl4SubframeInvocation) : IKH (HU U) (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_performDeriveSubframe _)

theorem hu_handleFault (thread : ObjRef) (ex : Fault) : IKH (HU U) (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_handleFault _ _)

set_option maxHeartbeats 4000000 in
theorem hu_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    IKH (HU U) (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_receiveIpc _ _ _ _)

theorem hu_handleRecv (isBlocking canReply : Bool) : IKH (HU U) (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_handleRecv _ _)

theorem hu_handleYield  : IKH (HU U) (handleYield (Z := Unit)) := by
  unfold handleYield; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_handleYield)

theorem hu_invokeIrqControl (a0 : IrqControlInvocation) : IKHE (HU U) (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_invokeIrqControl _)

theorem hu_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : IKHE (HU U) (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_invokeFl4IrqControl _)

theorem hu_preemptionPath  : IKH (HU U) (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hu_preemptionPath)

end

end Fl4Proofs.P3.SInvUZ
