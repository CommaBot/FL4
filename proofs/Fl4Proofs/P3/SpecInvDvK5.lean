/- s26: the object half `OBK O` of device `valid_untyped`, part 5 (SpecInvUtZK5 renamed; see SpecInvDvK1). -/
import Fl4Proofs.P3.SpecInvDvK4
open Classical

namespace Fl4Proofs.P3.SInvDV
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {OS : ObSet}



theorem ob_subframeNode (nodeCap : Cap) (index depth : Data) : OBKE OS (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_subframeNode _ _ _)

theorem ob_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : OBKE OS (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeDeriveSubframe _ _ _ _)

theorem ob_decodeDomainScheduleConfigure (args : List Data) : OBKE OS (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeDomainScheduleConfigure _)

theorem ob_decodeDomainScheduleSetStart (args : List Data) : OBKE OS (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeDomainScheduleSetStart _)

theorem ob_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : OBKE OS (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeDomainSet _ _)

theorem ob_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : OBKE OS (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeDomainInvocation _ _ _)

theorem ob_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : OBK OS (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_fl4GetMr _ _ _)

theorem ob_fl4Arg (buf : Option ObjRef) (i : Nat) : OBKE OS (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_fl4Arg _ _)

theorem ob_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : OBKE OS (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeFl4ConfigureSingleStepping _ _)

theorem ob_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : OBKE OS (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeFl4FpuTransfer _ _ _ _)

theorem ob_fl4CheckBpNum (bp : Data) : OBKE OS (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_fl4CheckBpNum _)

theorem ob_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : OBKE OS (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeFl4GetBreakpoint _ _)

theorem ob_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, OBKE OS (check x0)) : OBKE OS (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; ob_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible refine ob_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem ob_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : OBKE OS (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeIrqControlRemapped _ _ _)

theorem ob_fl4ArchCheckIrq (irq : Data) : OBKE OS (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_fl4ArchCheckIrq _)

theorem ob_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : OBKE OS (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeFl4IrqControl _ _ _ _ _)

theorem ob_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : OBKE OS (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeFl4SetBreakpoint _ _)

theorem ob_decodeFl4SetFlags (args : List Data) (t : ObjRef) : OBKE OS (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeFl4SetFlags _ _)

theorem ob_decodeFl4SetTimer (args : List Data) (t : ObjRef) : OBKE OS (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeFl4SetTimer _ _)

theorem ob_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : OBKE OS (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeFl4UnsetBreakpoint _ _)

theorem ob_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : OBKE OS (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeFl4TcbExt _ _ _ _ _)

theorem ob_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : OBKE OS (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeIrqControlInvocation _ _ _ _)

theorem ob_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : OBKE OS (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeIrqHandlerInvocation _ _ _)

theorem ob_getScReleased (scPtr : ObjRef) : OBK OS (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getScReleased _)

theorem ob_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : OBKE OS (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeSchedContextBind _ _)

theorem ob_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : OBKE OS (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeSchedContextUnbindObject _ _)

theorem ob_decodeSchedContextYieldTo (scPtr : ObjRef) : OBKE OS (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeSchedContextYieldTo _)

theorem ob_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : OBKE OS (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeSchedContextInvocation _ _ _)

theorem ob_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : OBKE OS (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeSchedControlInvocationFlags _ _ _)

theorem ob_rangeCheck (v minV maxV : Word) : OBKE OS (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_rangeCheck _ _ _)

theorem ob_decodeSetFlags (args : List Data) (cap : Cap) : OBKE OS (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeSetFlags _ _)

theorem ob_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : OBKE OS (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeSetIpcBuffer _ _ _ _)

theorem ob_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : OBKE OS (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeSetMcpriority _ _ _ _)

theorem ob_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : OBKE OS (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeSetPriority _ _ _ _)

theorem ob_isBlocked (thread : ObjRef) : OBK OS (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_isBlocked _)

theorem ob_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : OBKE OS (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeUpdateSc _ _ _)

theorem ob_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : OBKE OS (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeSetSchedParams _ _ _ _)

theorem ob_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : OBKE OS (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeSetSpace _ _ _ _)

theorem ob_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : OBKE OS (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeSetTimeoutEp _ _ _)

theorem ob_decodeSetTlsBase (args : List Data) (cap : Cap) : OBKE OS (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeSetTlsBase _ _)

theorem ob_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : OBKE OS (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeTcbConfigure _ _ _ _)

theorem ob_decodeUnbindNotification (cap : Cap) : OBKE OS (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem ob_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : OBKE OS (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeTcbInvocation _ _ _ _ _)

theorem ob_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : OBKE OS (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeUntypedInvocation _ _ _ _ _)

theorem ob_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : OBKE OS (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeInvocation _ _ _ _ _ _ _ _)

theorem ob_decodePml4Flush (cap : ArchCap) : OBKE OS (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodePml4Flush _)

theorem ob_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : OBKE OS (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_frameMappingSlot _ _ _ _)

theorem ob_decodeTestAndClearAccessed (cap : ArchCap) : OBKE OS (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeTestAndClearAccessed _)

theorem ob_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : OBKE OS (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem ob_doNbrecvFailedTransfer (thread : ObjRef) : OBK OS (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_doNbrecvFailedTransfer _)

theorem ob_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : OBK OS (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getMrs _ _ _)

theorem ob_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : OBK OS (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_handleArchFaultReply _ _ _ _)

theorem ob_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : OBK OS (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_handleFaultReply _ _ _ _)

theorem ob_testPossibleSwitchTo (tcbPtr : ObjRef) : OBK OS (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_testPossibleSwitchTo _)

theorem ob_restart (thread : ObjRef) : OBK OS (restart (Z := Unit) thread) := by
  unfold restart; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_restart _)

theorem ob_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : OBK OS (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_doReplyTransfer _ _ _)

theorem ob_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : OBK OS (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_domainScheduleConfigure _ _ _)

theorem ob_setNextInterrupt  : OBK OS (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setNextInterrupt)

theorem ob_switchSchedContext  : OBK OS (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_switchSchedContext)

theorem ob_scAndTimer  : OBK OS (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_scAndTimer)

theorem ob_scheduleChooseNewThread  : OBK OS (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_scheduleChooseNewThread)

theorem ob_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : OBK OS (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_scheduleSwitchThreadFastfail _ _ _ _)

theorem ob_schedule  : OBK OS (schedule (Z := Unit)) := by
  unfold schedule; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_schedule)

theorem ob_domainSetStart (index : Nat) : OBK OS (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_domainSetStart _)

theorem ob_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : OBKE OS (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem ob_performDeriveSubframe (iv : Fl4SubframeInvocation) : OBK OS (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_performDeriveSubframe _)

theorem ob_performPml4Flush (a0 : Fl4Pml4Invocation) : OBK OS (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_performPml4Flush _)

theorem ob_performTestAndClearAccessed (_slot : ObjRef) : OBK OS (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_performTestAndClearAccessed _)

end

end Fl4Proofs.P3.SInvDV
