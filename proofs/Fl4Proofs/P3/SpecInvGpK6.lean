/- s27: global-PML4 frame lemmas `GpK g` (sg1's SpecInvSgI6 renamed; see SpecInvGpK1). -/
import Fl4Proofs.P3.SpecInvGpK5
open Classical

namespace Fl4Proofs.P3.SInvGp
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem gpk_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : GpK N (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_updateWaitingNtfn _ _ _)

theorem gpk_sendSignal (ntfnptr : ObjRef) (badge : Badge) : GpK N (sendSignal (Z := Unit) ntfnptr badge) := by
  unfold sendSignal; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_sendSignal _ _)

theorem gpk_fl4Awaken : GpK N (fl4Awaken (Z := Unit)) := by
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
    · exact gpk_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fl4Awaken)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem gpk_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    GpKE N (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem gpk_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : GpKE N (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem gpk_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : GpK N (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_initArchObjects _ _ _ _ _ _)

theorem gpk_resetUntypedCap (srcSlot : CslotPtr) : GpKE N (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_resetUntypedCap _)

theorem gpk_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : GpKE N (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_invokeUntypedWith _ _)

theorem gpk_invokeCnode (i : CnodeInvocation) : GpKE N (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_invokeCnode _)

theorem gpk_threadSetDomain (tptr : ObjRef) (domain : Domain) : GpK N (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_threadSetDomain _ _)

theorem gpk_setDomain (tptr : ObjRef) (newDom : Domain) : GpK N (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setDomain _ _)

theorem gpk_invokeSetDomain (thread : ObjRef) (domain : Domain) : GpK N (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_invokeSetDomain _ _)

theorem gpk_invokeDomain (domInv : DomainInvocation) : GpK N (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_invokeDomain _)

theorem gpk_invokeIrqControl (a0 : IrqControlInvocation) : GpKE N (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_invokeIrqControl _)

theorem gpk_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : GpKE N (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_invokeFl4IrqControl _)

theorem gpk_invokeFl4Tcb (a0 : Fl4TcbInvocation) : GpKE N (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_invokeFl4Tcb _)

theorem gpk_invokeIrqHandler (a0 : IrqHandlerInvocation) : GpK N (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_invokeIrqHandler _)

theorem gpk_returnConsumed (scPtr : ObjRef) : GpK N (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_returnConsumed _)

theorem gpk_schedContextBindNtfn (sc ntfn : ObjRef) : GpK N (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_schedContextBindNtfn _ _)

theorem gpk_schedContextBindTcb (scPtr tcbPtr : ObjRef) : GpK N (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_schedContextBindTcb _ _)

theorem gpk_schedContextYieldTo (scPtr : ObjRef) : GpK N (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_schedContextYieldTo _)

theorem gpk_invokeSchedContext (iv : SchedContextInvocation) : GpK N (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_invokeSchedContext _)

theorem gpk_maybeAddEmptyTail (scPtr : ObjRef) : GpK N (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_maybeAddEmptyTail _)

theorem gpk_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : GpK N (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_refillNew _ _ _ _)

theorem gpk_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : GpK N (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_refillUpdate _ _ _ _)

theorem gpk_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : GpK N (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_invokeSchedControlConfigureFlags _)

theorem gpk_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : GpKE N (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_installTcbCap _ _ _ _)

theorem gpk_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : GpKE N (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_installTcbFrameCap _ _ _)

theorem gpk_setFlags (ref : ObjRef) (flags : TcbFlags) : GpK N (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setFlags _ _)

theorem gpk_setMcpriority (ref : ObjRef) (mcp : Priority) : GpK N (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setMcpriority _ _)

theorem gpk_reorderEp (epPtr tptr : ObjRef) : GpK N (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_reorderEp _ _)

theorem gpk_reorderNtfn (ntfnPtr tptr : ObjRef) : GpK N (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_reorderNtfn _ _)

theorem gpk_threadSetPriority (tptr : ObjRef) (prio : Priority) : GpK N (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_threadSetPriority _ _)

theorem gpk_setPriority (tptr : ObjRef) (prio : Priority) : GpK N (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setPriority _ _)

theorem gpk_invokeTcb (a0 : TcbInvocation) : GpKE N (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_invokeTcb _)

theorem gpk_fl4PerformInvocation (a0 : Bool) (a1 : Bool) (a2 : Bool) (a3 : Fl4Invocation) : GpKE N (fl4PerformInvocation (Z := Unit) a0 a1 a2 a3) := by
  unfold fl4PerformInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fl4PerformInvocation _ _ _ _)

theorem gpk_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : GpK N (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fl4ReplyFromKernelError _ _ _)

theorem gpk_handleNoFault (tptr : ObjRef) : GpK N (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_handleNoFault _)

theorem gpk_handleFault (thread : ObjRef) (ex : Fault) : GpK N (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_handleFault _ _)

theorem gpk_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : GpKE N mFault) (h_hFault : ∀ x0, GpK N (hFault x0)) (h_mError : ∀ x0, GpKE N (mError x0)) (h_hError : ∀ x0, GpK N (hError x0)) (h_mFinalise : ∀ x0, GpKE N (mFinalise x0)) : GpKE N (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; gpk_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible refine gpk_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem gpk_fl4HandleInvocationR (reportError : Bool) (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : GpKE N (fl4HandleInvocationR (Z := Unit) reportError calling blocking canDonate firstPhase cptr) := by
  unfold fl4HandleInvocationR; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fl4HandleInvocationR _ _ _ _ _ _)

theorem gpk_getCapReg (reg : Register) : GpK N (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getCapReg _)

theorem gpk_lookupReply  : GpKE N (lookupReply (Z := Unit)) := by
  unfold lookupReply; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_lookupReply)

theorem gpk_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : GpK N (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_maybeReturnSc _ _)

theorem gpk_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : GpK N (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_receiveIpcBlocked _ _ _ _)

set_option maxHeartbeats 4000000 in
theorem gpk_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    GpK N (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_receiveIpc _ _ _ _)

theorem gpk_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : GpK N (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_tcbNtfnAppend _ _)

theorem gpk_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : GpK N (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_receiveSignalBlocked _ _ _)

theorem gpk_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : GpK N (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_receiveSignal _ _ _)

theorem gpk_handleRecv (isBlocking canReply : Bool) : GpK N (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_handleRecv _ _)

theorem gpk_handleYield  : GpK N (handleYield (Z := Unit)) := by
  unfold handleYield; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_handleYield)

theorem gpk_fl4HandleSyscall (rep : Bool) (a0 : Syscall) : GpKE N (fl4HandleSyscall (Z := Unit) rep a0) := by
  unfold fl4HandleSyscall; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fl4HandleSyscall _ _)

theorem gpk_invokeUntyped (ui : UntypedInvocation) : GpKE N (invokeUntyped (Z := Unit) ui) := by
  unfold invokeUntyped; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_invokeUntyped _)

theorem gpk_performInvocation (a0 : Bool) (a1 : Bool) (a2 : Bool) (a3 : Invocation) : GpKE N (performInvocation (Z := Unit) a0 a1 a2 a3) := by
  unfold performInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_performInvocation _ _ _ _)

theorem gpk_handleInvocation (calling blocking canDonate firstPhase : Bool) (cptr : CapRef) : GpKE N (handleInvocation (Z := Unit) calling blocking canDonate firstPhase cptr) := by
  unfold handleInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_handleInvocation _ _ _ _ _)

theorem gpk_handleCall  : GpKE N (handleCall (Z := Unit)) := by
  unfold handleCall; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_handleCall)

theorem gpk_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : GpK N (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_handleHypervisorFault _ _)

theorem gpk_handleSend (bl : Bool) : GpKE N (handleSend (Z := Unit) bl) := by
  unfold handleSend; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_handleSend _)

theorem gpk_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : GpKE N (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_handleVmFault _ _)

theorem gpk_handleReservedIrq (_irq : Irq) : GpK N (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_handleReservedIrq _)

theorem gpk_handleInterrupt (irq : Irq) : GpK N (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_handleInterrupt _)

theorem gpk_handleSpuriousIrq  : GpK N (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_handleSpuriousIrq)

theorem gpk_maybeHandleInterrupt (inKernel : Bool) : GpK N (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_maybeHandleInterrupt _)

theorem gpk_handleEvent (a0 : Event) : GpKE N (handleEvent (Z := Unit) a0) := by
  unfold handleEvent; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_handleEvent _)

theorem gpk_fl4HandleEvent (rep : Bool) (a0 : Event) : GpKE N (fl4HandleEvent (Z := Unit) rep a0) := by
  unfold fl4HandleEvent; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fl4HandleEvent _ _)

theorem gpk_preemptionPath  : GpK N (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_preemptionPath)

theorem gpk_fl4CallKernel (rep : Bool) (ev : Event) : GpK N (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fl4CallKernel _ _)

theorem gpk_fl4SyscallFaultIP (thread : ObjRef) : GpK N (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fl4SyscallFaultIP _)

theorem gpk_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) : GpK N (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fl4KernelEntrySyscall _ _)

end

end Fl4Proofs.P3.SInvGp
