/- sg1: idle-thread frame lemmas `IoK t` (ut7's SpecInvUtNK5 renamed; see SpecInvSgI1). -/
import Fl4Proofs.P3.SpecInvIoK4
open Classical

namespace Fl4Proofs.P3.SInvIo
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : IoPort → Bool}

theorem iok_subframeNode (nodeCap : Cap) (index depth : Data) : IoKE N (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_subframeNode _ _ _)

theorem iok_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : IoKE N (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeDeriveSubframe _ _ _ _)

theorem iok_decodeDomainScheduleConfigure (args : List Data) : IoKE N (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeDomainScheduleConfigure _)

theorem iok_decodeDomainScheduleSetStart (args : List Data) : IoKE N (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeDomainScheduleSetStart _)

theorem iok_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : IoKE N (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeDomainSet _ _)

theorem iok_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : IoKE N (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeDomainInvocation _ _ _)

theorem iok_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : IoK N (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_fl4GetMr _ _ _)

theorem iok_fl4Arg (buf : Option ObjRef) (i : Nat) : IoKE N (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_fl4Arg _ _)

theorem iok_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : IoKE N (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeFl4ConfigureSingleStepping _ _)

theorem iok_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : IoKE N (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeFl4FpuTransfer _ _ _ _)

theorem iok_fl4CheckBpNum (bp : Data) : IoKE N (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_fl4CheckBpNum _)

theorem iok_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : IoKE N (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeFl4GetBreakpoint _ _)

theorem iok_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, IoKE N (check x0)) : IoKE N (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; iok_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible refine iok_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem iok_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : IoKE N (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeIrqControlRemapped _ _ _)

theorem iok_fl4ArchCheckIrq (irq : Data) : IoKE N (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_fl4ArchCheckIrq _)

theorem iok_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : IoKE N (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeFl4IrqControl _ _ _ _ _)

theorem iok_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : IoKE N (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeFl4SetBreakpoint _ _)

theorem iok_decodeFl4SetFlags (args : List Data) (t : ObjRef) : IoKE N (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeFl4SetFlags _ _)

theorem iok_decodeFl4SetTimer (args : List Data) (t : ObjRef) : IoKE N (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeFl4SetTimer _ _)

theorem iok_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : IoKE N (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeFl4UnsetBreakpoint _ _)

theorem iok_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : IoKE N (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeFl4TcbExt _ _ _ _ _)

theorem iok_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : IoKE N (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeIrqControlInvocation _ _ _ _)

theorem iok_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : IoKE N (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeIrqHandlerInvocation _ _ _)

theorem iok_getScReleased (scPtr : ObjRef) : IoK N (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_getScReleased _)

theorem iok_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : IoKE N (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeSchedContextBind _ _)

theorem iok_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : IoKE N (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeSchedContextUnbindObject _ _)

theorem iok_decodeSchedContextYieldTo (scPtr : ObjRef) : IoKE N (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeSchedContextYieldTo _)

theorem iok_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : IoKE N (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeSchedContextInvocation _ _ _)

theorem iok_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : IoKE N (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeSchedControlInvocationFlags _ _ _)

theorem iok_rangeCheck (v minV maxV : Word) : IoKE N (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_rangeCheck _ _ _)

theorem iok_decodeSetFlags (args : List Data) (cap : Cap) : IoKE N (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeSetFlags _ _)

theorem iok_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : IoKE N (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeSetIpcBuffer _ _ _ _)

theorem iok_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IoKE N (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeSetMcpriority _ _ _ _)

theorem iok_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IoKE N (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeSetPriority _ _ _ _)

theorem iok_isBlocked (thread : ObjRef) : IoK N (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_isBlocked _)

theorem iok_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : IoKE N (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeUpdateSc _ _ _)

theorem iok_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IoKE N (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeSetSchedParams _ _ _ _)

theorem iok_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : IoKE N (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeSetSpace _ _ _ _)

theorem iok_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IoKE N (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeSetTimeoutEp _ _ _)

theorem iok_decodeSetTlsBase (args : List Data) (cap : Cap) : IoKE N (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeSetTlsBase _ _)

theorem iok_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : IoKE N (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeTcbConfigure _ _ _ _)

theorem iok_decodeUnbindNotification (cap : Cap) : IoKE N (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem iok_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : IoKE N (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeTcbInvocation _ _ _ _ _)

theorem iok_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : IoKE N (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeUntypedInvocation _ _ _ _ _)

theorem iok_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : IoKE N (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeInvocation _ _ _ _ _ _ _ _)

theorem iok_decodePml4Flush (cap : ArchCap) : IoKE N (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodePml4Flush _)

theorem iok_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : IoKE N (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_frameMappingSlot _ _ _ _)

theorem iok_decodeTestAndClearAccessed (cap : ArchCap) : IoKE N (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeTestAndClearAccessed _)

theorem iok_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : IoKE N (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem iok_doNbrecvFailedTransfer (thread : ObjRef) : IoK N (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_doNbrecvFailedTransfer _)

theorem iok_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : IoK N (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_getMrs _ _ _)

theorem iok_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : IoK N (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_handleArchFaultReply _ _ _ _)

theorem iok_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : IoK N (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_handleFaultReply _ _ _ _)

theorem iok_testPossibleSwitchTo (tcbPtr : ObjRef) : IoK N (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_testPossibleSwitchTo _)

theorem iok_restart (thread : ObjRef) : IoK N (restart (Z := Unit) thread) := by
  unfold restart; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_restart _)

theorem iok_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : IoK N (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_doReplyTransfer _ _ _)

theorem iok_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : IoK N (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_domainScheduleConfigure _ _ _)

theorem iok_setNextInterrupt  : IoK N (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_setNextInterrupt)

theorem iok_switchSchedContext  : IoK N (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_switchSchedContext)

theorem iok_scAndTimer  : IoK N (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_scAndTimer)

theorem iok_scheduleChooseNewThread  : IoK N (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_scheduleChooseNewThread)

theorem iok_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : IoK N (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_scheduleSwitchThreadFastfail _ _ _ _)

theorem iok_schedule  : IoK N (schedule (Z := Unit)) := by
  unfold schedule; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_schedule)

theorem iok_domainSetStart (index : Nat) : IoK N (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_domainSetStart _)

theorem iok_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : IoKE N (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem iok_performDeriveSubframe (iv : Fl4SubframeInvocation) : IoK N (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_performDeriveSubframe _)

theorem iok_performPml4Flush (a0 : Fl4Pml4Invocation) : IoK N (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_performPml4Flush _)

theorem iok_performTestAndClearAccessed (_slot : ObjRef) : IoK N (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; iok_auto
macro_rules | `(tactic| iok_leaf) => `(tactic| with_reducible exact iok_performTestAndClearAccessed _)

end

end Fl4Proofs.P3.SInvIo
