/- g5g: the memory half `YK D F` of untyped_ranges_zero, part 5 (sg1's SpecInvSgI5 renamed; see SpecInvUtZK1). -/
import Fl4Proofs.P3.SpecInvUtZK4
open Classical

namespace Fl4Proofs.P3.SInvUZ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {PD : PgSet} {FS : Set Nat}


theorem yk_subframeNode (nodeCap : Cap) (index depth : Data) : YKE PD FS (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_subframeNode _ _ _)

theorem yk_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : YKE PD FS (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeDeriveSubframe _ _ _ _)

theorem yk_decodeDomainScheduleConfigure (args : List Data) : YKE PD FS (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeDomainScheduleConfigure _)

theorem yk_decodeDomainScheduleSetStart (args : List Data) : YKE PD FS (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeDomainScheduleSetStart _)

theorem yk_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : YKE PD FS (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeDomainSet _ _)

theorem yk_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : YKE PD FS (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeDomainInvocation _ _ _)

theorem yk_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : YK PD FS (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_fl4GetMr _ _ _)

theorem yk_fl4Arg (buf : Option ObjRef) (i : Nat) : YKE PD FS (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_fl4Arg _ _)

theorem yk_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : YKE PD FS (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeFl4ConfigureSingleStepping _ _)

theorem yk_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : YKE PD FS (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeFl4FpuTransfer _ _ _ _)

theorem yk_fl4CheckBpNum (bp : Data) : YKE PD FS (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_fl4CheckBpNum _)

theorem yk_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : YKE PD FS (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeFl4GetBreakpoint _ _)

theorem yk_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, YKE PD FS (check x0)) : YKE PD FS (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; yk_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible refine yk_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem yk_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : YKE PD FS (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeIrqControlRemapped _ _ _)

theorem yk_fl4ArchCheckIrq (irq : Data) : YKE PD FS (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_fl4ArchCheckIrq _)

theorem yk_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : YKE PD FS (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeFl4IrqControl _ _ _ _ _)

theorem yk_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : YKE PD FS (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeFl4SetBreakpoint _ _)

theorem yk_decodeFl4SetFlags (args : List Data) (t : ObjRef) : YKE PD FS (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeFl4SetFlags _ _)

theorem yk_decodeFl4SetTimer (args : List Data) (t : ObjRef) : YKE PD FS (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeFl4SetTimer _ _)

theorem yk_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : YKE PD FS (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeFl4UnsetBreakpoint _ _)

theorem yk_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : YKE PD FS (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeFl4TcbExt _ _ _ _ _)

theorem yk_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : YKE PD FS (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeIrqControlInvocation _ _ _ _)

theorem yk_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : YKE PD FS (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeIrqHandlerInvocation _ _ _)

theorem yk_getScReleased (scPtr : ObjRef) : YK PD FS (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getScReleased _)

theorem yk_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : YKE PD FS (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeSchedContextBind _ _)

theorem yk_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : YKE PD FS (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeSchedContextUnbindObject _ _)

theorem yk_decodeSchedContextYieldTo (scPtr : ObjRef) : YKE PD FS (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeSchedContextYieldTo _)

theorem yk_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : YKE PD FS (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeSchedContextInvocation _ _ _)

theorem yk_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : YKE PD FS (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeSchedControlInvocationFlags _ _ _)

theorem yk_rangeCheck (v minV maxV : Word) : YKE PD FS (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_rangeCheck _ _ _)

theorem yk_decodeSetFlags (args : List Data) (cap : Cap) : YKE PD FS (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeSetFlags _ _)

theorem yk_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : YKE PD FS (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeSetIpcBuffer _ _ _ _)

theorem yk_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : YKE PD FS (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeSetMcpriority _ _ _ _)

theorem yk_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : YKE PD FS (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeSetPriority _ _ _ _)

theorem yk_isBlocked (thread : ObjRef) : YK PD FS (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_isBlocked _)

theorem yk_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : YKE PD FS (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeUpdateSc _ _ _)

theorem yk_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : YKE PD FS (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeSetSchedParams _ _ _ _)

theorem yk_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : YKE PD FS (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeSetSpace _ _ _ _)

theorem yk_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : YKE PD FS (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeSetTimeoutEp _ _ _)

theorem yk_decodeSetTlsBase (args : List Data) (cap : Cap) : YKE PD FS (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeSetTlsBase _ _)

theorem yk_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : YKE PD FS (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeTcbConfigure _ _ _ _)

theorem yk_decodeUnbindNotification (cap : Cap) : YKE PD FS (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem yk_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : YKE PD FS (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeTcbInvocation _ _ _ _ _)

theorem yk_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : YKE PD FS (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeUntypedInvocation _ _ _ _ _)

theorem yk_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : YKE PD FS (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeInvocation _ _ _ _ _ _ _ _)

theorem yk_decodePml4Flush (cap : ArchCap) : YKE PD FS (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodePml4Flush _)

theorem yk_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : YKE PD FS (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_frameMappingSlot _ _ _ _)

theorem yk_decodeTestAndClearAccessed (cap : ArchCap) : YKE PD FS (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeTestAndClearAccessed _)

theorem yk_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : YKE PD FS (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem yk_doNbrecvFailedTransfer (thread : ObjRef) : YK PD FS (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_doNbrecvFailedTransfer _)

theorem yk_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : YK PD FS (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getMrs _ _ _)

theorem yk_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : YK PD FS (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_handleArchFaultReply _ _ _ _)

theorem yk_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : YK PD FS (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_handleFaultReply _ _ _ _)

theorem yk_testPossibleSwitchTo (tcbPtr : ObjRef) : YK PD FS (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_testPossibleSwitchTo _)

theorem yk_restart (thread : ObjRef) : YK PD FS (restart (Z := Unit) thread) := by
  unfold restart; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_restart _)

theorem yk_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : YK PD FS (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_doReplyTransfer _ _ _)

theorem yk_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : YK PD FS (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_domainScheduleConfigure _ _ _)

theorem yk_setNextInterrupt  : YK PD FS (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setNextInterrupt)

theorem yk_switchSchedContext  : YK PD FS (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_switchSchedContext)

theorem yk_scAndTimer  : YK PD FS (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_scAndTimer)

theorem yk_scheduleChooseNewThread  : YK PD FS (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_scheduleChooseNewThread)

theorem yk_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : YK PD FS (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_scheduleSwitchThreadFastfail _ _ _ _)

theorem yk_schedule  : YK PD FS (schedule (Z := Unit)) := by
  unfold schedule; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_schedule)

theorem yk_domainSetStart (index : Nat) : YK PD FS (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_domainSetStart _)

theorem yk_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : YKE PD FS (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem yk_performDeriveSubframe (iv : Fl4SubframeInvocation) : YK PD FS (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_performDeriveSubframe _)

theorem yk_performPml4Flush (a0 : Fl4Pml4Invocation) : YK PD FS (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_performPml4Flush _)

theorem yk_performTestAndClearAccessed (_slot : ObjRef) : YK PD FS (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_performTestAndClearAccessed _)

end

end Fl4Proofs.P3.SInvUZ
