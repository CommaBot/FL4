/- s26: the object half `OBK O` of device `valid_untyped`, part 6 (SpecInvUtZK6 renamed; see SpecInvDvK1). -/
import Fl4Proofs.P3.SpecInvDvK5
open Classical

namespace Fl4Proofs.P3.SInvDV
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {OS : ObSet}



theorem ob_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : OBK OS (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_updateWaitingNtfn _ _ _)

theorem ob_sendSignal (ntfnptr : ObjRef) (badge : Badge) : OBK OS (sendSignal (Z := Unit) ntfnptr badge) := by
  unfold sendSignal; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_sendSignal _ _)

theorem ob_fl4Awaken : OBK OS (fl4Awaken (Z := Unit)) := by
  intro σ hσ x hx
  obtain ⟨u, s'⟩ := x
  have hx' : fl4TimerFires σ s' := hx
  clear hx
  induction hx' with
  | refl => exact hσ
  | tail _ hst ih =>
    obtain ⟨σ1, h1, rfl⟩ := hst
    rcases h1 with rfl | ⟨n, bd, hs⟩
    · exact ih
    · exact ob_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_fl4Awaken)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem ob_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    OBKE OS (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem ob_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : OBKE OS (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem ob_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : OBK OS (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_initArchObjects _ _ _ _ _ _)

theorem ob_resetUntypedCap (srcSlot : CslotPtr) : OBKE OS (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_resetUntypedCap _)

theorem ob_invokeCnode (i : CnodeInvocation) : OBKE OS (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_invokeCnode _)

theorem ob_threadSetDomain (tptr : ObjRef) (domain : Domain) : OBK OS (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_threadSetDomain _ _)

theorem ob_setDomain (tptr : ObjRef) (newDom : Domain) : OBK OS (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setDomain _ _)

theorem ob_invokeSetDomain (thread : ObjRef) (domain : Domain) : OBK OS (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_invokeSetDomain _ _)

theorem ob_invokeDomain (domInv : DomainInvocation) : OBK OS (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_invokeDomain _)

theorem ob_invokeIrqControl (a0 : IrqControlInvocation) : OBKE OS (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_invokeIrqControl _)

theorem ob_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : OBKE OS (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_invokeFl4IrqControl _)

theorem ob_invokeIrqHandler (a0 : IrqHandlerInvocation) : OBK OS (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_invokeIrqHandler _)

theorem ob_returnConsumed (scPtr : ObjRef) : OBK OS (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_returnConsumed _)

theorem ob_schedContextBindNtfn (sc ntfn : ObjRef) : OBK OS (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_schedContextBindNtfn _ _)

theorem ob_schedContextBindTcb (scPtr tcbPtr : ObjRef) : OBK OS (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_schedContextBindTcb _ _)

theorem ob_schedContextYieldTo (scPtr : ObjRef) : OBK OS (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_schedContextYieldTo _)

theorem ob_invokeSchedContext (iv : SchedContextInvocation) : OBK OS (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_invokeSchedContext _)

theorem ob_maybeAddEmptyTail (scPtr : ObjRef) : OBK OS (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_maybeAddEmptyTail _)

theorem ob_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : OBK OS (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_refillNew _ _ _ _)

theorem ob_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : OBK OS (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_refillUpdate _ _ _ _)

theorem ob_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : OBK OS (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_invokeSchedControlConfigureFlags _)

theorem ob_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : OBKE OS (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_installTcbCap _ _ _ _)

theorem ob_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : OBKE OS (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_installTcbFrameCap _ _ _)

theorem ob_setFlags (ref : ObjRef) (flags : TcbFlags) : OBK OS (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setFlags _ _)

theorem ob_setMcpriority (ref : ObjRef) (mcp : Priority) : OBK OS (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setMcpriority _ _)

theorem ob_reorderEp (epPtr tptr : ObjRef) : OBK OS (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_reorderEp _ _)

theorem ob_reorderNtfn (ntfnPtr tptr : ObjRef) : OBK OS (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_reorderNtfn _ _)

theorem ob_threadSetPriority (tptr : ObjRef) (prio : Priority) : OBK OS (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_threadSetPriority _ _)

theorem ob_setPriority (tptr : ObjRef) (prio : Priority) : OBK OS (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setPriority _ _)

theorem ob_invokeTcb (a0 : TcbInvocation) : OBKE OS (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_invokeTcb _)

theorem ob_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : OBK OS (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_fl4ReplyFromKernelError _ _ _)

theorem ob_handleNoFault (tptr : ObjRef) : OBK OS (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_handleNoFault _)

theorem ob_handleFault (thread : ObjRef) (ex : Fault) : OBK OS (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_handleFault _ _)

theorem ob_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : OBKE OS mFault) (h_hFault : ∀ x0, OBK OS (hFault x0)) (h_mError : ∀ x0, OBKE OS (mError x0)) (h_hError : ∀ x0, OBK OS (hError x0)) (h_mFinalise : ∀ x0, OBKE OS (mFinalise x0)) : OBKE OS (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; ob_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible refine ob_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem ob_getCapReg (reg : Register) : OBK OS (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getCapReg _)

theorem ob_lookupReply  : OBKE OS (lookupReply (Z := Unit)) := by
  unfold lookupReply; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_lookupReply)

theorem ob_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : OBK OS (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_maybeReturnSc _ _)

theorem ob_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : OBK OS (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_receiveIpcBlocked _ _ _ _)

set_option maxHeartbeats 4000000 in
theorem ob_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    OBK OS (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_receiveIpc _ _ _ _)

theorem ob_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : OBK OS (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_tcbNtfnAppend _ _)

theorem ob_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : OBK OS (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_receiveSignalBlocked _ _ _)

theorem ob_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : OBK OS (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_receiveSignal _ _ _)

theorem ob_handleRecv (isBlocking canReply : Bool) : OBK OS (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_handleRecv _ _)

theorem ob_handleYield  : OBK OS (handleYield (Z := Unit)) := by
  unfold handleYield; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_handleYield)

theorem ob_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : OBK OS (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_handleHypervisorFault _ _)

theorem ob_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : OBKE OS (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_handleVmFault _ _)

theorem ob_handleReservedIrq (_irq : Irq) : OBK OS (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_handleReservedIrq _)

theorem ob_handleInterrupt (irq : Irq) : OBK OS (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_handleInterrupt _)

theorem ob_handleSpuriousIrq  : OBK OS (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_handleSpuriousIrq)

theorem ob_maybeHandleInterrupt (inKernel : Bool) : OBK OS (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_maybeHandleInterrupt _)

theorem ob_preemptionPath  : OBK OS (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_preemptionPath)

theorem ob_fl4SyscallFaultIP (thread : ObjRef) : OBK OS (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_fl4SyscallFaultIP _)

end

end Fl4Proofs.P3.SInvDV
