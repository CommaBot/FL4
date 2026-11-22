/- s27: global-PML4 frame lemmas `GpK g` (sg1's SpecInvSgI5 renamed; see SpecInvGpK1). -/
import Fl4Proofs.P3.SpecInvGpK4
open Classical

namespace Fl4Proofs.P3.SInvGp
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {N : ObjRef}

theorem gpk_subframeNode (nodeCap : Cap) (index depth : Data) : GpKE N (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_subframeNode _ _ _)

theorem gpk_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : GpKE N (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeDeriveSubframe _ _ _ _)

theorem gpk_decodeDomainScheduleConfigure (args : List Data) : GpKE N (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeDomainScheduleConfigure _)

theorem gpk_decodeDomainScheduleSetStart (args : List Data) : GpKE N (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeDomainScheduleSetStart _)

theorem gpk_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : GpKE N (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeDomainSet _ _)

theorem gpk_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : GpKE N (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeDomainInvocation _ _ _)

theorem gpk_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : GpK N (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fl4GetMr _ _ _)

theorem gpk_fl4Arg (buf : Option ObjRef) (i : Nat) : GpKE N (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fl4Arg _ _)

theorem gpk_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : GpKE N (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeFl4ConfigureSingleStepping _ _)

theorem gpk_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : GpKE N (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeFl4FpuTransfer _ _ _ _)

theorem gpk_fl4CheckBpNum (bp : Data) : GpKE N (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fl4CheckBpNum _)

theorem gpk_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : GpKE N (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeFl4GetBreakpoint _ _)

theorem gpk_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, GpKE N (check x0)) : GpKE N (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; gpk_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible refine gpk_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem gpk_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : GpKE N (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeIrqControlRemapped _ _ _)

theorem gpk_fl4ArchCheckIrq (irq : Data) : GpKE N (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fl4ArchCheckIrq _)

theorem gpk_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : GpKE N (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeFl4IrqControl _ _ _ _ _)

theorem gpk_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : GpKE N (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeFl4SetBreakpoint _ _)

theorem gpk_decodeFl4SetFlags (args : List Data) (t : ObjRef) : GpKE N (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeFl4SetFlags _ _)

theorem gpk_decodeFl4SetTimer (args : List Data) (t : ObjRef) : GpKE N (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeFl4SetTimer _ _)

theorem gpk_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : GpKE N (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeFl4UnsetBreakpoint _ _)

theorem gpk_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : GpKE N (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeFl4TcbExt _ _ _ _ _)

theorem gpk_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : GpKE N (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeIrqControlInvocation _ _ _ _)

theorem gpk_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : GpKE N (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeIrqHandlerInvocation _ _ _)

theorem gpk_getScReleased (scPtr : ObjRef) : GpK N (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getScReleased _)

theorem gpk_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : GpKE N (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeSchedContextBind _ _)

theorem gpk_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : GpKE N (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeSchedContextUnbindObject _ _)

theorem gpk_decodeSchedContextYieldTo (scPtr : ObjRef) : GpKE N (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeSchedContextYieldTo _)

theorem gpk_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : GpKE N (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeSchedContextInvocation _ _ _)

theorem gpk_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : GpKE N (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeSchedControlInvocationFlags _ _ _)

theorem gpk_rangeCheck (v minV maxV : Word) : GpKE N (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_rangeCheck _ _ _)

theorem gpk_decodeSetFlags (args : List Data) (cap : Cap) : GpKE N (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeSetFlags _ _)

theorem gpk_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : GpKE N (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeSetIpcBuffer _ _ _ _)

theorem gpk_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : GpKE N (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeSetMcpriority _ _ _ _)

theorem gpk_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : GpKE N (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeSetPriority _ _ _ _)

theorem gpk_isBlocked (thread : ObjRef) : GpK N (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_isBlocked _)

theorem gpk_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : GpKE N (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeUpdateSc _ _ _)

theorem gpk_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : GpKE N (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeSetSchedParams _ _ _ _)

theorem gpk_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : GpKE N (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeSetSpace _ _ _ _)

theorem gpk_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : GpKE N (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeSetTimeoutEp _ _ _)

theorem gpk_decodeSetTlsBase (args : List Data) (cap : Cap) : GpKE N (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeSetTlsBase _ _)

theorem gpk_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : GpKE N (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeTcbConfigure _ _ _ _)

theorem gpk_decodeUnbindNotification (cap : Cap) : GpKE N (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem gpk_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : GpKE N (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeTcbInvocation _ _ _ _ _)

theorem gpk_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : GpKE N (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeUntypedInvocation _ _ _ _ _)

theorem gpk_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : GpKE N (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeInvocation _ _ _ _ _ _ _ _)

theorem gpk_decodePml4Flush (cap : ArchCap) : GpKE N (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodePml4Flush _)

theorem gpk_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : GpKE N (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_frameMappingSlot _ _ _ _)

theorem gpk_decodeTestAndClearAccessed (cap : ArchCap) : GpKE N (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeTestAndClearAccessed _)

theorem gpk_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : GpKE N (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem gpk_doNbrecvFailedTransfer (thread : ObjRef) : GpK N (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_doNbrecvFailedTransfer _)

theorem gpk_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : GpK N (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getMrs _ _ _)

theorem gpk_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : GpK N (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_handleArchFaultReply _ _ _ _)

theorem gpk_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : GpK N (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_handleFaultReply _ _ _ _)

theorem gpk_testPossibleSwitchTo (tcbPtr : ObjRef) : GpK N (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_testPossibleSwitchTo _)

theorem gpk_restart (thread : ObjRef) : GpK N (restart (Z := Unit) thread) := by
  unfold restart; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_restart _)

theorem gpk_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : GpK N (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_doReplyTransfer _ _ _)

theorem gpk_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : GpK N (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_domainScheduleConfigure _ _ _)

theorem gpk_setNextInterrupt  : GpK N (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setNextInterrupt)

theorem gpk_switchSchedContext  : GpK N (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_switchSchedContext)

theorem gpk_scAndTimer  : GpK N (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_scAndTimer)

theorem gpk_scheduleChooseNewThread  : GpK N (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_scheduleChooseNewThread)

theorem gpk_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : GpK N (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_scheduleSwitchThreadFastfail _ _ _ _)

theorem gpk_schedule  : GpK N (schedule (Z := Unit)) := by
  unfold schedule; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_schedule)

theorem gpk_domainSetStart (index : Nat) : GpK N (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_domainSetStart _)

theorem gpk_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : GpKE N (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem gpk_performDeriveSubframe (iv : Fl4SubframeInvocation) : GpK N (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_performDeriveSubframe _)

theorem gpk_performPml4Flush (a0 : Fl4Pml4Invocation) : GpK N (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_performPml4Flush _)

theorem gpk_performTestAndClearAccessed (_slot : ObjRef) : GpK N (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_performTestAndClearAccessed _)

theorem gpk_fl4ArchPerformInvocation (a0 : Fl4ArchInvocation) : GpKE N (fl4ArchPerformInvocation (Z := Unit) a0) := by
  unfold fl4ArchPerformInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_fl4ArchPerformInvocation _)
end

end Fl4Proofs.P3.SInvGp
