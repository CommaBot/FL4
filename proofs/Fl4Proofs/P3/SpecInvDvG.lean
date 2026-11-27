/- s26 (SpecInvUtZG with the device flag, `HUD U`); was g5g: `IKH (HUD U)` (the cap half of untyped_ranges_zero) for the spec functions of the syscall entry
that write caps and need no carried fact (g5c's SpecInvIoPortsG renamed, without the untyped performs;
the leaves of SpecInvUtZW/Y): the IRQ control issues, the ASID pool, IPC with cap transfer, the fault and
timeout paths, budget charging, the preemption path, DeriveSubframe. -/
import Fl4Proofs.P3.SpecInvDvY
open Classical

namespace Fl4Proofs.P3.SInvDV
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {U : UtSetD}


theorem hd_archInvokeIrqControl (aic : ArchIrqControlInvocation) : IKHE (HUD U) (archInvokeIrqControl (Z := Unit) aic) := by
  unfold archInvokeIrqControl; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_archInvokeIrqControl _)

theorem hd_performAsidPoolInvocation (iv : AsidPoolInvocation) : IKH (HUD U) (performAsidPoolInvocation (Z := Unit) iv) := by
  unfold performAsidPoolInvocation; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_performAsidPoolInvocation _)

theorem hd_doIpcTransfer (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : IKH (HUD U) (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_doIpcTransfer _ _ _ _ _)

theorem hd_sendIpc (block call : Bool) (badge : Badge) (canGrant canGrantReply canDonate : Bool) (thread epptr : ObjRef) : IKH (HUD U) (sendIpc (Z := Unit) block call badge canGrant canGrantReply canDonate thread epptr) := by
  unfold sendIpc; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_sendIpc _ _ _ _ _ _ _ _)

theorem hd_sendFaultIpc (tptr : ObjRef) (handlerCap : Cap) (fault : Fault) (canDonate : Bool) : IKH (HUD U) (sendFaultIpc (Z := Unit) tptr handlerCap fault canDonate) := by
  unfold sendFaultIpc; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_sendFaultIpc _ _ _ _)

theorem hd_handleTimeout (tptr : ObjRef) (ex : Fault) : IKH (HUD U) (handleTimeout (Z := Unit) tptr ex) := by
  unfold handleTimeout; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_handleTimeout _ _)

theorem hd_endTimeslice (canTimeout : Bool) : IKH (HUD U) (endTimeslice (Z := Unit) canTimeout) := by
  unfold endTimeslice; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_endTimeslice _)

theorem hd_chargeBudget (consumed : Ticks) (canTimeout : Bool) : IKH (HUD U) (chargeBudget (Z := Unit) consumed canTimeout) := by
  unfold chargeBudget; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_chargeBudget _ _)

theorem hd_checkBudget  : IKH (HUD U) (checkBudget (Z := Unit)) := by
  unfold checkBudget; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_checkBudget)

theorem hd_checkBudgetRestart  : IKH (HUD U) (checkBudgetRestart (Z := Unit)) := by
  unfold checkBudgetRestart; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_checkBudgetRestart)

theorem hd_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : IKH (HUD U) (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_doReplyTransfer _ _ _)

theorem hd_performDeriveSubframe (iv : Fl4SubframeInvocation) : IKH (HUD U) (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_performDeriveSubframe _)

theorem hd_handleFault (thread : ObjRef) (ex : Fault) : IKH (HUD U) (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_handleFault _ _)

set_option maxHeartbeats 4000000 in
theorem hd_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    IKH (HUD U) (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_receiveIpc _ _ _ _)

theorem hd_handleRecv (isBlocking canReply : Bool) : IKH (HUD U) (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_handleRecv _ _)

theorem hd_handleYield  : IKH (HUD U) (handleYield (Z := Unit)) := by
  unfold handleYield; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_handleYield)

theorem hd_invokeIrqControl (a0 : IrqControlInvocation) : IKHE (HUD U) (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_invokeIrqControl _)

theorem hd_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : IKHE (HUD U) (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_invokeFl4IrqControl _)

theorem hd_preemptionPath  : IKH (HUD U) (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; hv_auto
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hd_preemptionPath)

end

end Fl4Proofs.P3.SInvDV
