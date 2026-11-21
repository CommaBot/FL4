/- sg1: idle-thread frame lemmas `IoK t` (ut7's SpecInvUtNK6 renamed; see SpecInvSgI1). -/
import Fl4Proofs.P3.SpecInvIoK5
open Classical

namespace Fl4Proofs.P3.SInvIo
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : IoPort → Bool}

theorem iok_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : IoK N (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_updateWaitingNtfn _ _ _)

theorem iok_sendSignal (ntfnptr : ObjRef) (badge : Badge) : IoK N (sendSignal (Z := Unit) ntfnptr badge) := by
  unfold sendSignal; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_sendSignal _ _)

theorem iok_fl4Awaken : IoK N (fl4Awaken (Z := Unit)) := by
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
    · exact iok_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_fl4Awaken)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem iok_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    IoKE N (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem iok_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : IoKE N (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem iok_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : IoK N (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_initArchObjects _ _ _ _ _ _)

theorem iok_resetUntypedCap (srcSlot : CslotPtr) : IoKE N (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_resetUntypedCap _)

theorem iok_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : IoKE N (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_invokeUntypedWith _ _)

theorem iok_threadSetDomain (tptr : ObjRef) (domain : Domain) : IoK N (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_threadSetDomain _ _)

theorem iok_setDomain (tptr : ObjRef) (newDom : Domain) : IoK N (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_setDomain _ _)

theorem iok_invokeSetDomain (thread : ObjRef) (domain : Domain) : IoK N (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_invokeSetDomain _ _)

theorem iok_invokeDomain (domInv : DomainInvocation) : IoK N (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_invokeDomain _)

theorem iok_invokeIrqControl (a0 : IrqControlInvocation) : IoKE N (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_invokeIrqControl _)

theorem iok_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : IoKE N (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_invokeFl4IrqControl _)

theorem iok_invokeFl4Tcb (a0 : Fl4TcbInvocation) : IoKE N (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_invokeFl4Tcb _)

theorem iok_returnConsumed (scPtr : ObjRef) : IoK N (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_returnConsumed _)

theorem iok_schedContextBindNtfn (sc ntfn : ObjRef) : IoK N (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_schedContextBindNtfn _ _)

theorem iok_schedContextBindTcb (scPtr tcbPtr : ObjRef) : IoK N (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_schedContextBindTcb _ _)

theorem iok_schedContextYieldTo (scPtr : ObjRef) : IoK N (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_schedContextYieldTo _)

theorem iok_invokeSchedContext (iv : SchedContextInvocation) : IoK N (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_invokeSchedContext _)

theorem iok_maybeAddEmptyTail (scPtr : ObjRef) : IoK N (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_maybeAddEmptyTail _)

theorem iok_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : IoK N (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_refillNew _ _ _ _)

theorem iok_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : IoK N (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_refillUpdate _ _ _ _)

theorem iok_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : IoK N (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_invokeSchedControlConfigureFlags _)

theorem iok_setFlags (ref : ObjRef) (flags : TcbFlags) : IoK N (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_setFlags _ _)

theorem iok_setMcpriority (ref : ObjRef) (mcp : Priority) : IoK N (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_setMcpriority _ _)

theorem iok_reorderEp (epPtr tptr : ObjRef) : IoK N (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_reorderEp _ _)

theorem iok_reorderNtfn (ntfnPtr tptr : ObjRef) : IoK N (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_reorderNtfn _ _)

theorem iok_threadSetPriority (tptr : ObjRef) (prio : Priority) : IoK N (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_threadSetPriority _ _)

theorem iok_setPriority (tptr : ObjRef) (prio : Priority) : IoK N (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_setPriority _ _)

theorem iok_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : IoK N (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_fl4ReplyFromKernelError _ _ _)

theorem iok_handleNoFault (tptr : ObjRef) : IoK N (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_handleNoFault _)

theorem iok_handleFault (thread : ObjRef) (ex : Fault) : IoK N (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_handleFault _ _)

theorem iok_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : IoKE N mFault) (h_hFault : ∀ x0, IoK N (hFault x0)) (h_mError : ∀ x0, IoKE N (mError x0)) (h_hError : ∀ x0, IoK N (hError x0)) (h_mFinalise : ∀ x0, IoKE N (mFinalise x0)) : IoKE N (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; iok_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible refine iok_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem iok_getCapReg (reg : Register) : IoK N (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_getCapReg _)

theorem iok_lookupReply  : IoKE N (lookupReply (Z := Unit)) := by
  unfold lookupReply; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_lookupReply)

theorem iok_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : IoK N (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_maybeReturnSc _ _)

theorem iok_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : IoK N (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_receiveIpcBlocked _ _ _ _)

set_option maxHeartbeats 4000000 in
theorem iok_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    IoK N (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_receiveIpc _ _ _ _)

theorem iok_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : IoK N (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_tcbNtfnAppend _ _)

theorem iok_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : IoK N (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_receiveSignalBlocked _ _ _)

theorem iok_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : IoK N (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_receiveSignal _ _ _)

theorem iok_handleRecv (isBlocking canReply : Bool) : IoK N (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_handleRecv _ _)

theorem iok_handleYield  : IoK N (handleYield (Z := Unit)) := by
  unfold handleYield; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_handleYield)

theorem iok_invokeUntyped (ui : UntypedInvocation) : IoKE N (invokeUntyped (Z := Unit) ui) := by
  unfold invokeUntyped; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_invokeUntyped _)

theorem iok_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : IoK N (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_handleHypervisorFault _ _)

theorem iok_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : IoKE N (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_handleVmFault _ _)

theorem iok_handleReservedIrq (_irq : Irq) : IoK N (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_handleReservedIrq _)

theorem iok_handleInterrupt (irq : Irq) : IoK N (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_handleInterrupt _)

theorem iok_handleSpuriousIrq  : IoK N (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_handleSpuriousIrq)

theorem iok_maybeHandleInterrupt (inKernel : Bool) : IoK N (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_maybeHandleInterrupt _)

theorem iok_preemptionPath  : IoK N (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_preemptionPath)

theorem iok_fl4SyscallFaultIP (thread : ObjRef) : IoK N (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_fl4SyscallFaultIP _)

end

end Fl4Proofs.P3.SInvIo
