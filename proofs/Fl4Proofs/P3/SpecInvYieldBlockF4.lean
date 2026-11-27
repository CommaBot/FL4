/- iolay gen 5: YieldBlock frame lemmas, part 4: SpecInvYieldScopeF4's generated lemmas (gen.py `ys` mode, skip list
proofs/scratch/invA/skipYS.txt) for the strengthened invariant, without the functions that reach a blocking writer
(proofs/scratch/invA/skipYB.txt; hand-proved in SpecInvYieldBlockH). -/
import Fl4Proofs.P3.SpecInvYieldBlockF3
import Fl4Proofs.P3.SpecInvFbK
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {L : List ObjRef}

theorem yb_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : YBKE L (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeSchedContextUnbindObject _ _)

theorem yb_decodeSchedContextYieldTo (scPtr : ObjRef) : YBKE L (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeSchedContextYieldTo _)

theorem yb_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : YBKE L (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeSchedContextInvocation _ _ _)

theorem yb_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : YBKE L (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeSchedControlInvocationFlags _ _ _)

theorem yb_rangeCheck (v minV maxV : Word) : YBKE L (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_rangeCheck _ _ _)

theorem yb_decodeSetFlags (args : List Data) (cap : Cap) : YBKE L (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeSetFlags _ _)

theorem yb_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : YBKE L (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeSetIpcBuffer _ _ _ _)

theorem yb_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : YBKE L (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeSetMcpriority _ _ _ _)

theorem yb_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : YBKE L (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeSetPriority _ _ _ _)

theorem yb_isBlocked (thread : ObjRef) : YBK L (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_isBlocked _)

theorem yb_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : YBKE L (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeUpdateSc _ _ _)

theorem yb_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : YBKE L (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeSetSchedParams _ _ _ _)

theorem yb_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : YBKE L (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeSetSpace _ _ _ _)

theorem yb_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : YBKE L (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeSetTimeoutEp _ _ _)

theorem yb_decodeSetTlsBase (args : List Data) (cap : Cap) : YBKE L (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeSetTlsBase _ _)

theorem yb_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : YBKE L (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeTcbConfigure _ _ _ _)

theorem yb_decodeUnbindNotification (cap : Cap) : YBKE L (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem yb_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : YBKE L (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeTcbInvocation _ _ _ _ _)

theorem yb_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : YBKE L (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeUntypedInvocation _ _ _ _ _)

theorem yb_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : YBKE L (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeInvocation _ _ _ _ _ _ _ _)

theorem yb_decodePml4Flush (cap : ArchCap) : YBKE L (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodePml4Flush _)

theorem yb_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : YBKE L (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_frameMappingSlot _ _ _ _)

theorem yb_decodeTestAndClearAccessed (cap : ArchCap) : YBKE L (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeTestAndClearAccessed _)

theorem yb_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : YBKE L (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem yb_doNbrecvFailedTransfer (thread : ObjRef) : YBK L (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_doNbrecvFailedTransfer _)

theorem yb_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : YBK L (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getMrs _ _ _)

theorem yb_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : YBK L (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_handleArchFaultReply _ _ _ _)

theorem yb_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : YBK L (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_handleFaultReply _ _ _ _)

theorem yb_testPossibleSwitchTo (tcbPtr : ObjRef) : YBK L (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_testPossibleSwitchTo _)

theorem yb_restart (thread : ObjRef) : YBK L (restart (Z := Unit) thread) := by
  unfold restart; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_restart _)

theorem yb_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : YBK L (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_domainScheduleConfigure _ _ _)

theorem yb_setNextInterrupt  : YBK L (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setNextInterrupt)

theorem yb_switchSchedContext  : YBK L (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_switchSchedContext)

theorem yb_scAndTimer  : YBK L (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_scAndTimer)

theorem yb_scheduleChooseNewThread  : YBK L (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_scheduleChooseNewThread)

theorem yb_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : YBK L (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_scheduleSwitchThreadFastfail _ _ _ _)

theorem yb_schedule  : YBK L (schedule (Z := Unit)) := by
  unfold schedule; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_schedule)

theorem yb_domainSetStart (index : Nat) : YBK L (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_domainSetStart _)

theorem yb_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : YBKE L (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem yb_performDeriveSubframe (iv : Fl4SubframeInvocation) : YBK L (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_performDeriveSubframe _)

theorem yb_performPml4Flush (a0 : Fl4Pml4Invocation) : YBK L (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_performPml4Flush _)

theorem yb_performTestAndClearAccessed (_slot : ObjRef) : YBK L (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_performTestAndClearAccessed _)

/-- fb-spec-2: one `X86PML4FrameBatch` entry (no recursion). -/
theorem yb_fbEntry (b : Fl4FrameBatchInvocation) (w : Data × Data × Data) : YBKE L (fbEntry (Z := Unit) b w) := by
  unfold fbEntry; yb_auto

/-- fb-spec-2: the batch (`Fl4Proofs.P3.SInv.ik_performFrameBatch`). -/
theorem yb_performFrameBatch (b : Fl4FrameBatchInvocation) : YBK L (performFrameBatch (Z := Unit) b) :=
  Fl4Proofs.P3.SInv.ik_performFrameBatch (fun w => yb_fbEntry b w) (yb_flushAll _ _)
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_performFrameBatch _)

theorem yb_fl4ArchPerformInvocation (a0 : Fl4ArchInvocation) : YBKE L (fl4ArchPerformInvocation (Z := Unit) a0) := by
  unfold fl4ArchPerformInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_fl4ArchPerformInvocation _)

theorem yb_updateWaitingNtfn (ntfnptr : ObjRef) (queue : List ObjRef) (badge : Badge) : YBK L (updateWaitingNtfn (Z := Unit) ntfnptr queue badge) := by
  unfold updateWaitingNtfn; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_updateWaitingNtfn _ _ _)

theorem yb_sendSignal (ntfnptr : ObjRef) (badge : Badge) : YBK L (sendSignal (Z := Unit) ntfnptr badge) := by
  unfold sendSignal; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_sendSignal _ _)

theorem yb_fl4Awaken : YBK L (fl4Awaken (Z := Unit)) := by
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
    · exact yb_sendSignal n bd _ ih ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_fl4Awaken)

/-- On a thread cap (`fl4DecodeInvocation`'s thread branch). -/
theorem yb_fl4DecodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    YBKE L (fl4DecodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs buffer) := by
  unfold fl4DecodeTcbInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_fl4DecodeTcbInvocation _ _ _ _ _ _)

theorem yb_fl4DecodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (buffer : Option ObjRef) : YBKE L (fl4DecodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps buffer) := by
  unfold fl4DecodeInvocation; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_fl4DecodeInvocation _ _ _ _ _ _ _ _)

theorem yb_fl4ReplyFromKernelError (reportError : Bool) (thread : ObjRef) (x : Data × List Data) : YBK L (fl4ReplyFromKernelError (Z := Unit) reportError thread x) := by
  unfold fl4ReplyFromKernelError; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_fl4ReplyFromKernelError _ _ _)

theorem yb_fl4SyscallFaultIP (thread : ObjRef) : YBK L (fl4SyscallFaultIP (Z := Unit) thread) := by
  unfold fl4SyscallFaultIP; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_fl4SyscallFaultIP _)

theorem yb_getCapReg (reg : Register) : YBK L (getCapReg (Z := Unit) reg) := by
  unfold getCapReg; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_getCapReg _)

theorem yb_handleNoFault (tptr : ObjRef) : YBK L (handleNoFault (Z := Unit) tptr) := by
  unfold handleNoFault; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_handleNoFault _)

theorem yb_handleHypervisorFault (a0 : Word) (a1 : HypFaultType) : YBK L (handleHypervisorFault (Z := Unit) a0 a1) := by
  unfold handleHypervisorFault; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_handleHypervisorFault _ _)

theorem yb_handleReservedIrq (_irq : Irq) : YBK L (handleReservedIrq (Z := Unit) _irq) := by
  unfold handleReservedIrq; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_handleReservedIrq _)

theorem yb_handleInterrupt (irq : Irq) : YBK L (handleInterrupt (Z := Unit) irq) := by
  unfold handleInterrupt; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_handleInterrupt _)

theorem yb_handleSpuriousIrq  : YBK L (handleSpuriousIrq (Z := Unit)) := by
  unfold handleSpuriousIrq; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_handleSpuriousIrq)

theorem yb_handleVmFault (thread : ObjRef) (faultType : VMFaultType) : YBKE L (handleVmFault (Z := Unit) thread faultType) := by
  unfold handleVmFault; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_handleVmFault _ _)

theorem yb_initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat) (_objSz : Nat) (refs : List ObjRef) : YBK L (initArchObjects (Z := Unit) newType _isDevice _ptr _numObjects _objSz refs) := by
  unfold initArchObjects; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_initArchObjects _ _ _ _ _ _)

theorem yb_installTcbCap (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) : YBKE L (installTcbCap (Z := Unit) target slot n slotOpt) := by
  unfold installTcbCap; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_installTcbCap _ _ _ _)

theorem yb_installTcbFrameCap (target : ObjRef) (slot : CslotPtr) (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : YBKE L (installTcbFrameCap (Z := Unit) target slot buffer) := by
  unfold installTcbFrameCap; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_installTcbFrameCap _ _ _)

theorem yb_invokeCnode (i : CnodeInvocation) : YBKE L (invokeCnode (Z := Unit) i) := by
  unfold invokeCnode; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_invokeCnode _)

theorem yb_threadSetDomain (tptr : ObjRef) (domain : Domain) : YBK L (threadSetDomain (Z := Unit) tptr domain) := by
  unfold threadSetDomain; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_threadSetDomain _ _)

theorem yb_setDomain (tptr : ObjRef) (newDom : Domain) : YBK L (setDomain (Z := Unit) tptr newDom) := by
  unfold setDomain; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setDomain _ _)

theorem yb_invokeSetDomain (thread : ObjRef) (domain : Domain) : YBK L (invokeSetDomain (Z := Unit) thread domain) := by
  unfold invokeSetDomain; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_invokeSetDomain _ _)

theorem yb_invokeDomain (domInv : DomainInvocation) : YBK L (invokeDomain (Z := Unit) domInv) := by
  unfold invokeDomain; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_invokeDomain _)

theorem yb_invokeIrqControl (a0 : IrqControlInvocation) : YBKE L (invokeIrqControl (Z := Unit) a0) := by
  unfold invokeIrqControl; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_invokeIrqControl _)

theorem yb_invokeFl4IrqControl (a0 : Fl4IrqControlInvocation) : YBKE L (invokeFl4IrqControl (Z := Unit) a0) := by
  unfold invokeFl4IrqControl; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_invokeFl4IrqControl _)

theorem yb_invokeFl4Tcb (a0 : Fl4TcbInvocation) : YBKE L (invokeFl4Tcb (Z := Unit) a0) := by
  unfold invokeFl4Tcb; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_invokeFl4Tcb _)

theorem yb_invokeIrqHandler (a0 : IrqHandlerInvocation) : YBK L (invokeIrqHandler (Z := Unit) a0) := by
  unfold invokeIrqHandler; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_invokeIrqHandler _)

theorem yb_maybeAddEmptyTail (scPtr : ObjRef) : YBK L (maybeAddEmptyTail (Z := Unit) scPtr) := by
  unfold maybeAddEmptyTail; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_maybeAddEmptyTail _)

theorem yb_refillNew (scPtr : ObjRef) (maxRefills : Nat) (budget period : Ticks) : YBK L (refillNew (Z := Unit) scPtr maxRefills budget period) := by
  unfold refillNew; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_refillNew _ _ _ _)

theorem yb_refillUpdate (scPtr : ObjRef) (newPeriod newBudget : Ticks) (newMaxRefills : Nat) : YBK L (refillUpdate (Z := Unit) scPtr newPeriod newBudget newMaxRefills) := by
  unfold refillUpdate; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_refillUpdate _ _ _ _)

theorem yb_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) : YBK L (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_invokeSchedControlConfigureFlags _)

theorem yb_schedContextBindTcb (scPtr tcbPtr : ObjRef) : YBK L (schedContextBindTcb (Z := Unit) scPtr tcbPtr) := by
  unfold schedContextBindTcb; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_schedContextBindTcb _ _)

theorem yb_setFlags (ref : ObjRef) (flags : TcbFlags) : YBK L (setFlags (Z := Unit) ref flags) := by
  unfold setFlags; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setFlags _ _)

theorem yb_setMcpriority (ref : ObjRef) (mcp : Priority) : YBK L (setMcpriority (Z := Unit) ref mcp) := by
  unfold setMcpriority; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setMcpriority _ _)

theorem yb_reorderEp (epPtr tptr : ObjRef) : YBK L (reorderEp (Z := Unit) epPtr tptr) := by
  unfold reorderEp; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_reorderEp _ _)

theorem yb_reorderNtfn (ntfnPtr tptr : ObjRef) : YBK L (reorderNtfn (Z := Unit) ntfnPtr tptr) := by
  unfold reorderNtfn; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_reorderNtfn _ _)

theorem yb_threadSetPriority (tptr : ObjRef) (prio : Priority) : YBK L (threadSetPriority (Z := Unit) tptr prio) := by
  unfold threadSetPriority; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_threadSetPriority _ _)

theorem yb_setPriority (tptr : ObjRef) (prio : Priority) : YBK L (setPriority (Z := Unit) tptr prio) := by
  unfold setPriority; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_setPriority _ _)

theorem yb_invokeTcb (a0 : TcbInvocation) : YBKE L (invokeTcb (Z := Unit) a0) := by
  unfold invokeTcb; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_invokeTcb _)

theorem yb_resetUntypedCap (srcSlot : CslotPtr) : YBKE L (resetUntypedCap (Z := Unit) srcSlot) := by
  unfold resetUntypedCap; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_resetUntypedCap _)

theorem yb_invokeUntyped (ui : UntypedInvocation) : YBKE L (invokeUntyped (Z := Unit) ui) := by
  unfold invokeUntyped; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_invokeUntyped _)

theorem yb_invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : YBKE L (invokeUntypedWith (Z := Unit) bitsApi ui) := by
  unfold invokeUntypedWith; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_invokeUntypedWith _ _)

theorem yb_lookupReply  : YBKE L (lookupReply (Z := Unit)) := by
  unfold lookupReply; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_lookupReply)

theorem yb_maybeHandleInterrupt (inKernel : Bool) : YBK L (maybeHandleInterrupt (Z := Unit) inKernel) := by
  unfold maybeHandleInterrupt; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_maybeHandleInterrupt _)

theorem yb_maybeReturnSc (ntfnPtr tcbPtr : ObjRef) : YBK L (maybeReturnSc (Z := Unit) ntfnPtr tcbPtr) := by
  unfold maybeReturnSc; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_maybeReturnSc _ _)

theorem yb_tcbNtfnAppend (tptr ntfnPtr : ObjRef) : YBK L (tcbNtfnAppend (Z := Unit) tptr ntfnPtr) := by
  unfold tcbNtfnAppend; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_tcbNtfnAppend _ _)

theorem yb_returnConsumed (scPtr : ObjRef) : YBK L (returnConsumed (Z := Unit) scPtr) := by
  unfold returnConsumed; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_returnConsumed _)

theorem yb_schedContextBindNtfn (sc ntfn : ObjRef) : YBK L (schedContextBindNtfn (Z := Unit) sc ntfn) := by
  unfold schedContextBindNtfn; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact yb_schedContextBindNtfn _ _)

theorem yb_syscall {α β γ : Type} (mFault : FMonad Unit α) (hFault : Fault → SMonad Unit γ) (mError : α → SEMonad Unit β) (hError : SyscallError → SMonad Unit γ) (mFinalise : β → PMonad Unit γ) (h_mFault : YBKE L mFault) (h_hFault : ∀ x0, YBK L (hFault x0)) (h_mError : ∀ x0, YBKE L (mError x0)) (h_hError : ∀ x0, YBK L (hError x0)) (h_mFinalise : ∀ x0, YBKE L (mFinalise x0)) : YBKE L (syscall (Z := Unit) mFault hFault mError hError mFinalise) := by
  unfold syscall; yb_auto
  all_goals first | exact h_mFault | exact h_hFault _ | exact h_mError _ | exact h_hError _ | exact h_mFinalise _
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible refine yb_syscall _ _ _ _ _ ?_ (fun _ => ?_) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_))

end

end Fl4Proofs.P3.SInv
