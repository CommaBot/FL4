/- virt gen 4: the object-type family `TYK`, part 6 (SpecInvDvK6 with `aType` for `objBits`, proofs/scratch/virt/mkty2.py; see VirtTyK1). -/
import Fl4Proofs.P3.VirtTyK5
open Classical

namespace Fl4Proofs.P3.SInvTY
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {OS : TySet}



theorem ty_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : TYK OS (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_updateWaitingNtfn _ _ _)

theorem ty_sendSignal (ntfnptr : ObjRef) (badge : Badge) : TYK OS (sendSignal (Z := Unit) ntfnptr badge) := by
  unfold sendSignal; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_sendSignal _ _)

theorem ty_fl4Awaken : TYK OS (fl4Awaken (Z := Unit)) := by
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
    · exact ty_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_fl4Awaken)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem ty_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    TYKE OS (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem ty_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : TYKE OS (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem ty_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : TYK OS (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_initArchObjects _ _ _ _ _ _)

theorem ty_resetUntypedCap (srcSlot : CslotPtr) : TYKE OS (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_resetUntypedCap _)

theorem ty_invokeCnode (i : CnodeInvocation) : TYKE OS (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_invokeCnode _)

theorem ty_threadSetDomain (tptr : ObjRef) (domain : Domain) : TYK OS (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_threadSetDomain _ _)

theorem ty_setDomain (tptr : ObjRef) (newDom : Domain) : TYK OS (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setDomain _ _)

theorem ty_invokeSetDomain (thread : ObjRef) (domain : Domain) : TYK OS (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_invokeSetDomain _ _)

theorem ty_invokeDomain (domInv : DomainInvocation) : TYK OS (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_invokeDomain _)

theorem ty_invokeIrqControl (a0 : IrqControlInvocation) : TYKE OS (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_invokeIrqControl _)

theorem ty_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : TYKE OS (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_invokeFl4IrqControl _)

theorem ty_invokeIrqHandler (a0 : IrqHandlerInvocation) : TYK OS (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_invokeIrqHandler _)

theorem ty_returnConsumed (scPtr : ObjRef) : TYK OS (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_returnConsumed _)

theorem ty_schedContextBindNtfn (sc ntfn : ObjRef) : TYK OS (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_schedContextBindNtfn _ _)

theorem ty_schedContextBindTcb (scPtr tcbPtr : ObjRef) : TYK OS (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_schedContextBindTcb _ _)

theorem ty_schedContextYieldTo (scPtr : ObjRef) : TYK OS (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_schedContextYieldTo _)

theorem ty_invokeSchedContext (iv : SchedContextInvocation) : TYK OS (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_invokeSchedContext _)

theorem ty_maybeAddEmptyTail (scPtr : ObjRef) : TYK OS (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_maybeAddEmptyTail _)

theorem ty_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : TYK OS (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_refillNew _ _ _ _)

theorem ty_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : TYK OS (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_refillUpdate _ _ _ _)

theorem ty_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : TYK OS (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_invokeSchedControlConfigureFlags _)

theorem ty_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : TYKE OS (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_installTcbCap _ _ _ _)

theorem ty_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : TYKE OS (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_installTcbFrameCap _ _ _)

theorem ty_setFlags (ref : ObjRef) (flags : TcbFlags) : TYK OS (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setFlags _ _)

theorem ty_setMcpriority (ref : ObjRef) (mcp : Priority) : TYK OS (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setMcpriority _ _)

theorem ty_reorderEp (epPtr tptr : ObjRef) : TYK OS (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_reorderEp _ _)

theorem ty_reorderNtfn (ntfnPtr tptr : ObjRef) : TYK OS (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_reorderNtfn _ _)

theorem ty_threadSetPriority (tptr : ObjRef) (prio : Priority) : TYK OS (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_threadSetPriority _ _)

theorem ty_setPriority (tptr : ObjRef) (prio : Priority) : TYK OS (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setPriority _ _)

theorem ty_invokeTcb (a0 : TcbInvocation) : TYKE OS (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_invokeTcb _)

theorem ty_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : TYK OS (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_fl4ReplyFromKernelError _ _ _)

theorem ty_handleNoFault (tptr : ObjRef) : TYK OS (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_handleNoFault _)

theorem ty_handleFault (thread : ObjRef) (ex : Fault) : TYK OS (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_handleFault _ _)

theorem ty_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : TYKE OS mFault) (h_hFault : ∀ x0, TYK OS (hFault x0)) (h_mError : ∀ x0, TYKE OS (mError x0)) (h_hError : ∀ x0, TYK OS (hError x0)) (h_mFinalise : ∀ x0, TYKE OS (mFinalise x0)) : TYKE OS (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; ty_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible refine ty_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem ty_getCapReg (reg : Register) : TYK OS (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getCapReg _)

theorem ty_lookupReply  : TYKE OS (lookupReply (Z := Unit)) := by
  unfold lookupReply; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_lookupReply)

theorem ty_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : TYK OS (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_maybeReturnSc _ _)

theorem ty_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : TYK OS (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_receiveIpcBlocked _ _ _ _)

set_option maxHeartbeats 4000000 in
theorem ty_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    TYK OS (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_receiveIpc _ _ _ _)

theorem ty_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : TYK OS (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_tcbNtfnAppend _ _)

theorem ty_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : TYK OS (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_receiveSignalBlocked _ _ _)

theorem ty_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : TYK OS (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_receiveSignal _ _ _)

theorem ty_handleRecv (isBlocking canReply : Bool) : TYK OS (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_handleRecv _ _)

theorem ty_handleYield  : TYK OS (handleYield (Z := Unit)) := by
  unfold handleYield; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_handleYield)

theorem ty_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : TYK OS (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_handleHypervisorFault _ _)

theorem ty_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : TYKE OS (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_handleVmFault _ _)

theorem ty_handleReservedIrq (_irq : Irq) : TYK OS (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_handleReservedIrq _)

theorem ty_handleInterrupt (irq : Irq) : TYK OS (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_handleInterrupt _)

theorem ty_handleSpuriousIrq  : TYK OS (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_handleSpuriousIrq)

theorem ty_maybeHandleInterrupt (inKernel : Bool) : TYK OS (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_maybeHandleInterrupt _)

theorem ty_preemptionPath  : TYK OS (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_preemptionPath)

theorem ty_fl4SyscallFaultIP (thread : ObjRef) : TYK OS (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_fl4SyscallFaultIP _)

end

end Fl4Proofs.P3.SInvTY
