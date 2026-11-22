/- g5g: the memory half `YK D F` of untyped_ranges_zero, part 6 (sg1's SpecInvSgI6 renamed; see SpecInvUtZK1). -/
import Fl4Proofs.P3.SpecInvUtZK5
open Classical

namespace Fl4Proofs.P3.SInvUZ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {PD : PgSet} {FS : Set Nat}


theorem yk_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : YK PD FS (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_updateWaitingNtfn _ _ _)

theorem yk_sendSignal (ntfnptr : ObjRef) (badge : Badge) : YK PD FS (sendSignal (Z := Unit) ntfnptr badge) := by
  unfold sendSignal; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_sendSignal _ _)

theorem yk_fl4Awaken : YK PD FS (fl4Awaken (Z := Unit)) := by
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
    · exact yk_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_fl4Awaken)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem yk_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    YKE PD FS (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem yk_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : YKE PD FS (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem yk_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : YK PD FS (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_initArchObjects _ _ _ _ _ _)

theorem yk_resetUntypedCap (srcSlot : CslotPtr) : YKE PD FS (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_resetUntypedCap _)

theorem yk_invokeCnode (i : CnodeInvocation) : YKE PD FS (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_invokeCnode _)

theorem yk_threadSetDomain (tptr : ObjRef) (domain : Domain) : YK PD FS (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_threadSetDomain _ _)

theorem yk_setDomain (tptr : ObjRef) (newDom : Domain) : YK PD FS (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setDomain _ _)

theorem yk_invokeSetDomain (thread : ObjRef) (domain : Domain) : YK PD FS (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_invokeSetDomain _ _)

theorem yk_invokeDomain (domInv : DomainInvocation) : YK PD FS (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_invokeDomain _)

theorem yk_invokeIrqControl (a0 : IrqControlInvocation) : YKE PD FS (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_invokeIrqControl _)

theorem yk_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : YKE PD FS (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_invokeFl4IrqControl _)

theorem yk_invokeIrqHandler (a0 : IrqHandlerInvocation) : YK PD FS (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_invokeIrqHandler _)

theorem yk_returnConsumed (scPtr : ObjRef) : YK PD FS (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_returnConsumed _)

theorem yk_schedContextBindNtfn (sc ntfn : ObjRef) : YK PD FS (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_schedContextBindNtfn _ _)

theorem yk_schedContextBindTcb (scPtr tcbPtr : ObjRef) : YK PD FS (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_schedContextBindTcb _ _)

theorem yk_schedContextYieldTo (scPtr : ObjRef) : YK PD FS (schedContextYieldTo (Z := Unit) scPtr) := by
  unfold schedContextYieldTo; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_schedContextYieldTo _)

theorem yk_invokeSchedContext (iv : SchedContextInvocation) : YK PD FS (invokeSchedContext (Z := Unit) iv) := by
  unfold invokeSchedContext; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_invokeSchedContext _)

theorem yk_maybeAddEmptyTail (scPtr : ObjRef) : YK PD FS (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_maybeAddEmptyTail _)

theorem yk_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : YK PD FS (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_refillNew _ _ _ _)

theorem yk_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : YK PD FS (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_refillUpdate _ _ _ _)

theorem yk_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : YK PD FS (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_invokeSchedControlConfigureFlags _)

theorem yk_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : YKE PD FS (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_installTcbCap _ _ _ _)

theorem yk_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : YKE PD FS (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_installTcbFrameCap _ _ _)

theorem yk_setFlags (ref : ObjRef) (flags : TcbFlags) : YK PD FS (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setFlags _ _)

theorem yk_setMcpriority (ref : ObjRef) (mcp : Priority) : YK PD FS (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setMcpriority _ _)

theorem yk_reorderEp (epPtr tptr : ObjRef) : YK PD FS (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_reorderEp _ _)

theorem yk_reorderNtfn (ntfnPtr tptr : ObjRef) : YK PD FS (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_reorderNtfn _ _)

theorem yk_threadSetPriority (tptr : ObjRef) (prio : Priority) : YK PD FS (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_threadSetPriority _ _)

theorem yk_setPriority (tptr : ObjRef) (prio : Priority) : YK PD FS (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setPriority _ _)

theorem yk_invokeTcb (a0 : TcbInvocation) : YKE PD FS (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_invokeTcb _)

theorem yk_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : YK PD FS (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_fl4ReplyFromKernelError _ _ _)

theorem yk_handleNoFault (tptr : ObjRef) : YK PD FS (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_handleNoFault _)

theorem yk_handleFault (thread : ObjRef) (ex : Fault) : YK PD FS (handleFault (Z := Unit) thread ex) := by
  unfold handleFault; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_handleFault _ _)

theorem yk_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : YKE PD FS mFault) (h_hFault : ∀ x0, YK PD FS (hFault x0)) (h_mError : ∀ x0, YKE PD FS (mError x0)) (h_hError : ∀ x0, YK PD FS (hError x0)) (h_mFinalise : ∀ x0, YKE PD FS (mFinalise x0)) : YKE PD FS (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; yk_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible refine yk_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

theorem yk_getCapReg (reg : Register) : YK PD FS (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getCapReg _)

theorem yk_lookupReply  : YKE PD FS (lookupReply (Z := Unit)) := by
  unfold lookupReply; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_lookupReply)

theorem yk_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : YK PD FS (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_maybeReturnSc _ _)

theorem yk_receiveIpcBlocked (isBlocking : Bool) (thread epptr : ObjRef) (reply : Option ObjRef) : YK PD FS (receiveIpcBlocked (Z := Unit) isBlocking thread epptr reply) := by
  unfold receiveIpcBlocked; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_receiveIpcBlocked _ _ _ _)

set_option maxHeartbeats 4000000 in
theorem yk_receiveIpc (thread : ObjRef) (cap : Cap) (isBlocking : Bool) (replyCap : Cap) :
    YK PD FS (receiveIpc (Z := Unit) thread cap isBlocking replyCap) := by
  unfold receiveIpc; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_receiveIpc _ _ _ _)

theorem yk_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : YK PD FS (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_tcbNtfnAppend _ _)

theorem yk_receiveSignalBlocked (thread ntfnptr : ObjRef) (isBlocking : Bool) : YK PD FS (receiveSignalBlocked (Z := Unit) thread ntfnptr isBlocking) := by
  unfold receiveSignalBlocked; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_receiveSignalBlocked _ _ _)

theorem yk_receiveSignal (thread : ObjRef) (cap : Cap) (isBlocking : Bool) : YK PD FS (receiveSignal (Z := Unit) thread cap isBlocking) := by
  unfold receiveSignal; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_receiveSignal _ _ _)

theorem yk_handleRecv (isBlocking canReply : Bool) : YK PD FS (handleRecv (Z := Unit) isBlocking canReply) := by
  unfold handleRecv; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_handleRecv _ _)

theorem yk_handleYield  : YK PD FS (handleYield (Z := Unit)) := by
  unfold handleYield; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_handleYield)

theorem yk_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : YK PD FS (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_handleHypervisorFault _ _)

theorem yk_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : YKE PD FS (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_handleVmFault _ _)

theorem yk_handleReservedIrq (_irq : Irq) : YK PD FS (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_handleReservedIrq _)

theorem yk_handleInterrupt (irq : Irq) : YK PD FS (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_handleInterrupt _)

theorem yk_handleSpuriousIrq  : YK PD FS (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_handleSpuriousIrq)

theorem yk_maybeHandleInterrupt (inKernel : Bool) : YK PD FS (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_maybeHandleInterrupt _)

theorem yk_preemptionPath  : YK PD FS (preemptionPath (Z := Unit)) := by
  unfold preemptionPath; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_preemptionPath)

theorem yk_fl4SyscallFaultIP (thread : ObjRef) : YK PD FS (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_fl4SyscallFaultIP _)

end

end Fl4Proofs.P3.SInvUZ
