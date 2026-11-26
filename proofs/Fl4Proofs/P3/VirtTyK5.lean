/- virt gen 4: the object-type family `TYK`, part 5 (SpecInvDvK5 with `aType` for `objBits`, proofs/scratch/virt/mkty2.py; see VirtTyK1). -/
import Fl4Proofs.P3.VirtTyK4
open Classical

namespace Fl4Proofs.P3.SInvTY
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {OS : TySet}



theorem ty_subframeNode (nodeCap : Cap) (index depth : Data) : TYKE OS (subframeNode (Z := Unit) nodeCap index depth) := by
  unfold subframeNode; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_subframeNode _ _ _)

theorem ty_decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap) (excaps : List (Cap × CslotPtr)) : TYKE OS (decodeDeriveSubframe (Z := Unit) args cte cap excaps) := by
  unfold decodeDeriveSubframe; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeDeriveSubframe _ _ _ _)

theorem ty_decodeDomainScheduleConfigure (args : List Data) : TYKE OS (decodeDomainScheduleConfigure (Z := Unit) args) := by
  unfold decodeDomainScheduleConfigure; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeDomainScheduleConfigure _)

theorem ty_decodeDomainScheduleSetStart (args : List Data) : TYKE OS (decodeDomainScheduleSetStart (Z := Unit) args) := by
  unfold decodeDomainScheduleSetStart; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeDomainScheduleSetStart _)

theorem ty_decodeDomainSet (args : List Data) (excs : List (Cap × CslotPtr)) : TYKE OS (decodeDomainSet (Z := Unit) args excs) := by
  unfold decodeDomainSet; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeDomainSet _ _)

theorem ty_decodeDomainInvocation (label : Data) (args : List Data) (excs : List (Cap × CslotPtr)) : TYKE OS (decodeDomainInvocation (Z := Unit) label args excs) := by
  unfold decodeDomainInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeDomainInvocation _ _ _)

theorem ty_fl4GetMr (t : ObjRef) (buf : Option ObjRef) (i : Nat) : TYK OS (fl4GetMr (Z := Unit) t buf i) := by
  unfold fl4GetMr; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_fl4GetMr _ _ _)

theorem ty_fl4Arg (buf : Option ObjRef) (i : Nat) : TYKE OS (fl4Arg (Z := Unit) buf i) := by
  unfold fl4Arg; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_fl4Arg _ _)

theorem ty_decodeFl4ConfigureSingleStepping (buf : Option ObjRef) (t : ObjRef) : TYKE OS (decodeFl4ConfigureSingleStepping (Z := Unit) buf t) := by
  unfold decodeFl4ConfigureSingleStepping; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeFl4ConfigureSingleStepping _ _)

theorem ty_decodeFl4FpuTransfer (toFrame : Bool) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) : TYKE OS (decodeFl4FpuTransfer (Z := Unit) toFrame args t excaps) := by
  unfold decodeFl4FpuTransfer; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeFl4FpuTransfer _ _ _ _)

theorem ty_fl4CheckBpNum (bp : Data) : TYKE OS (fl4CheckBpNum (Z := Unit) bp) := by
  unfold fl4CheckBpNum; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_fl4CheckBpNum _)

theorem ty_decodeFl4GetBreakpoint (buf : Option ObjRef) (t : ObjRef) : TYKE OS (decodeFl4GetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4GetBreakpoint; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeFl4GetBreakpoint _ _)

theorem ty_decodeIrqControlInvocationWith (check : Data → SEMonad Unit Unit) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) (h_check : ∀ x0, TYKE OS (check x0)) : TYKE OS (decodeIrqControlInvocationWith (Z := Unit) check label args srcSlot cps) := by
  unfold decodeIrqControlInvocationWith; ty_auto
  all_goals first | exact h_check _
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible refine ty_decodeIrqControlInvocationWith _ _ _ _ _ (fun _ => ?_))

theorem ty_decodeIrqControlRemapped (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : TYKE OS (decodeIrqControlRemapped (Z := Unit) args srcSlot cps) := by
  unfold decodeIrqControlRemapped; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeIrqControlRemapped _ _ _)

theorem ty_fl4ArchCheckIrq (irq : Data) : TYKE OS (fl4ArchCheckIrq (Z := Unit) irq) := by
  unfold fl4ArchCheckIrq; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_fl4ArchCheckIrq _)

theorem ty_decodeFl4IrqControl (remapped : Bool) (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : TYKE OS (decodeFl4IrqControl (Z := Unit) remapped label args srcSlot cps) := by
  unfold decodeFl4IrqControl; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeFl4IrqControl _ _ _ _ _)

theorem ty_decodeFl4SetBreakpoint (buf : Option ObjRef) (t : ObjRef) : TYKE OS (decodeFl4SetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4SetBreakpoint; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeFl4SetBreakpoint _ _)

theorem ty_decodeFl4SetFlags (args : List Data) (t : ObjRef) : TYKE OS (decodeFl4SetFlags (Z := Unit) args t) := by
  unfold decodeFl4SetFlags; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeFl4SetFlags _ _)

theorem ty_decodeFl4SetTimer (args : List Data) (t : ObjRef) : TYKE OS (decodeFl4SetTimer (Z := Unit) args t) := by
  unfold decodeFl4SetTimer; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeFl4SetTimer _ _)

theorem ty_decodeFl4UnsetBreakpoint (buf : Option ObjRef) (t : ObjRef) : TYKE OS (decodeFl4UnsetBreakpoint (Z := Unit) buf t) := by
  unfold decodeFl4UnsetBreakpoint; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeFl4UnsetBreakpoint _ _)

theorem ty_decodeFl4TcbExt (l : Fl4TcbExtLabel) (args : List Data) (t : ObjRef) (excaps : List (Cap × CslotPtr)) (buf : Option ObjRef) : TYKE OS (decodeFl4TcbExt (Z := Unit) l args t excaps buf) := by
  unfold decodeFl4TcbExt; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeFl4TcbExt _ _ _ _ _)

theorem ty_decodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : TYKE OS (decodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold decodeIrqControlInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeIrqControlInvocation _ _ _ _)

theorem ty_decodeIrqHandlerInvocation (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) : TYKE OS (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeIrqHandlerInvocation _ _ _)

theorem ty_getScReleased (scPtr : ObjRef) : TYK OS (getScReleased (Z := Unit) scPtr) := by
  unfold getScReleased; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getScReleased _)

theorem ty_decodeSchedContextBind (scPtr : ObjRef) (excaps : List Cap) : TYKE OS (decodeSchedContextBind (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextBind; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeSchedContextBind _ _)

theorem ty_decodeSchedContextUnbindObject (scPtr : ObjRef) (excaps : List Cap) : TYKE OS (decodeSchedContextUnbindObject (Z := Unit) scPtr excaps) := by
  unfold decodeSchedContextUnbindObject; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeSchedContextUnbindObject _ _)

theorem ty_decodeSchedContextYieldTo (scPtr : ObjRef) : TYKE OS (decodeSchedContextYieldTo (Z := Unit) scPtr) := by
  unfold decodeSchedContextYieldTo; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeSchedContextYieldTo _)

theorem ty_decodeSchedContextInvocation (label : Data) (scPtr : ObjRef) (excaps : List Cap) : TYKE OS (decodeSchedContextInvocation (Z := Unit) label scPtr excaps) := by
  unfold decodeSchedContextInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeSchedContextInvocation _ _ _)

theorem ty_decodeSchedControlInvocationFlags (label : Data) (args : List Data) (excaps : List Cap) : TYKE OS (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeSchedControlInvocationFlags _ _ _)

theorem ty_rangeCheck (v minV maxV : Word) : TYKE OS (rangeCheck (Z := Unit) v minV maxV) := by
  unfold rangeCheck; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_rangeCheck _ _ _)

theorem ty_decodeSetFlags (args : List Data) (cap : Cap) : TYKE OS (decodeSetFlags (Z := Unit) args cap) := by
  unfold decodeSetFlags; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeSetFlags _ _)

theorem ty_decodeSetIpcBuffer (args : List Data) (cap : Cap) (slot : CslotPtr) (excs : List (Cap × CslotPtr)) : TYKE OS (decodeSetIpcBuffer (Z := Unit) args cap slot excs) := by
  unfold decodeSetIpcBuffer; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeSetIpcBuffer _ _ _ _)

theorem ty_decodeSetMcpriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : TYKE OS (decodeSetMcpriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetMcpriority; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeSetMcpriority _ _ _ _)

theorem ty_decodeSetPriority (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : TYKE OS (decodeSetPriority (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetPriority; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeSetPriority _ _ _ _)

theorem ty_isBlocked (thread : ObjRef) : TYK OS (isBlocked (Z := Unit) thread) := by
  unfold isBlocked; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_isBlocked _)

theorem ty_decodeUpdateSc (cap : Cap) (_slot : CslotPtr) (scCap : Cap) : TYKE OS (decodeUpdateSc (Z := Unit) cap _slot scCap) := by
  unfold decodeUpdateSc; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeUpdateSc _ _ _)

theorem ty_decodeSetSchedParams (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : TYKE OS (decodeSetSchedParams (Z := Unit) args cap slot extraCaps) := by
  unfold decodeSetSchedParams; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeSetSchedParams _ _ _ _)

theorem ty_decodeSetSpace (args : List Data) (cap : Cap) (slot : CslotPtr) (excaps : List (Cap × CslotPtr)) : TYKE OS (decodeSetSpace (Z := Unit) args cap slot excaps) := by
  unfold decodeSetSpace; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeSetSpace _ _ _ _)

theorem ty_decodeSetTimeoutEp (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : TYKE OS (decodeSetTimeoutEp (Z := Unit) cap slot extraCaps) := by
  unfold decodeSetTimeoutEp; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeSetTimeoutEp _ _ _)

theorem ty_decodeSetTlsBase (args : List Data) (cap : Cap) : TYKE OS (decodeSetTlsBase (Z := Unit) args cap) := by
  unfold decodeSetTlsBase; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeSetTlsBase _ _)

theorem ty_decodeTcbConfigure (args : List Data) (cap : Cap) (slot : CslotPtr) (extraCaps : List (Cap × CslotPtr)) : TYKE OS (decodeTcbConfigure (Z := Unit) args cap slot extraCaps) := by
  unfold decodeTcbConfigure; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeTcbConfigure _ _ _ _)

theorem ty_decodeUnbindNotification (cap : Cap) : TYKE OS (decodeUnbindNotification (Z := Unit) cap) := by
  unfold decodeUnbindNotification; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeUnbindNotification _)

/-- On a thread cap (the only cap it is called with; elsewhere its register decodes are `undefined`). -/
theorem ty_decodeTcbInvocation (label : Data) (args : List Data) (p : ObjRef) (slot : CslotPtr)
    (excs : List (Cap × CslotPtr)) : TYKE OS (decodeTcbInvocation (Z := Unit) label args (.threadCap p) slot excs) := by
  unfold decodeTcbInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeTcbInvocation _ _ _ _ _)

theorem ty_decodeUntypedInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : TYKE OS (decodeUntypedInvocation (Z := Unit) label args slot cap excaps) := by
  unfold decodeUntypedInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeUntypedInvocation _ _ _ _ _)

theorem ty_decodeInvocation (firstPhase : Bool) (label : Data) (args : List Data) (capIndex : CapRef) (slot : CslotPtr) (cap : Cap) (excaps : List (Cap × CslotPtr)) (_buffer : Option ObjRef) : TYKE OS (decodeInvocation (Z := Unit) firstPhase label args capIndex slot cap excaps _buffer) := by
  unfold decodeInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeInvocation _ _ _ _ _ _ _ _)

theorem ty_decodePml4Flush (cap : ArchCap) : TYKE OS (decodePml4Flush (Z := Unit) cap) := by
  unfold decodePml4Flush; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodePml4Flush _)

theorem ty_frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : TYKE OS (frameMappingSlot (Z := Unit) p sz asid vaddr) := by
  unfold frameMappingSlot; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_frameMappingSlot _ _ _ _)

theorem ty_decodeTestAndClearAccessed (cap : ArchCap) : TYKE OS (decodeTestAndClearAccessed (Z := Unit) cap) := by
  unfold decodeTestAndClearAccessed; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeTestAndClearAccessed _)

theorem ty_decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap) (excaps : List Cap) : TYKE OS (decodeUntypedInvocationWith (Z := Unit) bitsApi label args slot cap excaps) := by
  unfold decodeUntypedInvocationWith; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeUntypedInvocationWith _ _ _ _ _ _)

theorem ty_doNbrecvFailedTransfer (thread : ObjRef) : TYK OS (doNbrecvFailedTransfer (Z := Unit) thread) := by
  unfold doNbrecvFailedTransfer; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_doNbrecvFailedTransfer _)

theorem ty_getMrs (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : TYK OS (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getMrs _ _ _)

theorem ty_handleArchFaultReply (_vmf : ArchFault) (_thread : ObjRef) (_x : Data) (_y : List Data) : TYK OS (handleArchFaultReply (Z := Unit) _vmf _thread _x _y) := by
  unfold handleArchFaultReply; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_handleArchFaultReply _ _ _ _)

theorem ty_handleFaultReply (a0 : Fault) (a1 : ObjRef) (a2 : Data) (a3 : List Data) : TYK OS (handleFaultReply (Z := Unit) a0 a1 a2 a3) := by
  unfold handleFaultReply; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_handleFaultReply _ _ _ _)

theorem ty_testPossibleSwitchTo (tcbPtr : ObjRef) : TYK OS (testPossibleSwitchTo (Z := Unit) tcbPtr) := by
  unfold testPossibleSwitchTo; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_testPossibleSwitchTo _)

theorem ty_restart (thread : ObjRef) : TYK OS (restart (Z := Unit) thread) := by
  unfold restart; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_restart _)

theorem ty_doReplyTransfer (sender reply : ObjRef) (grant : Bool) : TYK OS (doReplyTransfer (Z := Unit) sender reply grant) := by
  unfold doReplyTransfer; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_doReplyTransfer _ _ _)

theorem ty_domainScheduleConfigure (index : Nat) (domain : Domain) (duration : DomainDuration) : TYK OS (domainScheduleConfigure (Z := Unit) index domain duration) := by
  unfold domainScheduleConfigure; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_domainScheduleConfigure _ _ _)

theorem ty_setNextInterrupt  : TYK OS (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setNextInterrupt)

theorem ty_switchSchedContext  : TYK OS (switchSchedContext (Z := Unit)) := by
  unfold switchSchedContext; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_switchSchedContext)

theorem ty_scAndTimer  : TYK OS (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_scAndTimer)

theorem ty_scheduleChooseNewThread  : TYK OS (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_scheduleChooseNewThread)

theorem ty_scheduleSwitchThreadFastfail (ct it : ObjRef) (ctPrio targetPrio : Priority) : TYK OS (scheduleSwitchThreadFastfail (Z := Unit) ct it ctPrio targetPrio) := by
  unfold scheduleSwitchThreadFastfail; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_scheduleSwitchThreadFastfail _ _ _ _)

theorem ty_schedule  : TYK OS (schedule (Z := Unit)) := by
  unfold schedule; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_schedule)

theorem ty_domainSetStart (index : Nat) : TYK OS (domainSetStart (Z := Unit) index) := by
  unfold domainSetStart; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_domainSetStart _)

theorem ty_fl4ArchDecodeInvocation (label : Data) (args : List Data) (xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : TYKE OS (fl4ArchDecodeInvocation (Z := Unit) label args xSlot cte cap extraCaps) := by
  unfold fl4ArchDecodeInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_fl4ArchDecodeInvocation _ _ _ _ _ _)

theorem ty_performDeriveSubframe (iv : Fl4SubframeInvocation) : TYK OS (performDeriveSubframe (Z := Unit) iv) := by
  unfold performDeriveSubframe; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_performDeriveSubframe _)

theorem ty_performPml4Flush (a0 : Fl4Pml4Invocation) : TYK OS (performPml4Flush (Z := Unit) a0) := by
  unfold performPml4Flush; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_performPml4Flush _)

theorem ty_performTestAndClearAccessed (_slot : ObjRef) : TYK OS (performTestAndClearAccessed (Z := Unit) _slot) := by
  unfold performTestAndClearAccessed; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_performTestAndClearAccessed _)

end

end Fl4Proofs.P3.SInvTY
