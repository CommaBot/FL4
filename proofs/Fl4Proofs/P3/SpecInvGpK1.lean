/-
P3 (DESIGN.md §9), invariant line G1 (KENTRY-PLAN g7a-4 (3), s27): **no spec
step writes the global PML4 pointer** (`GpmIs g σ := σ.archState.x64GlobalPml4 =
g`), part 1, spec side only. C27 (`DevGpm`, l4v `valid_global_refs`) names the
state's global PML4, so the entry theorems need it constant. The family
`GpK g m := IK (GpmIs g) m` is sg1's idle-thread family (SpecInvSgI1..I6)
mechanically renamed (`IdleIs` → `GpmIs`, `idleThread` →
`archState.x64GlobalPml4`, `idk_` → `gpk_`): every leaf is a `get` / `modify` /
`select` of other fields (`gpk0_auto`; an `archState` update of another field
keeps it by definitional unfolding). Parts 2-6: SpecInvGpK2..K6.
-/
import Fl4Proofs.P3.SpecInvNativeScopeT
open Classical

namespace Fl4Proofs.P3.SInvGp
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- The global PML4 pointer is `N`. -/
def GpmIs (N : ObjRef) (σ : State Unit) : Prop := σ.archState.x64GlobalPml4 = N

abbrev GpK (N : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop := IK (GpmIs N) m
abbrev GpKE (N : ObjRef) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE (GpmIs N) m

variable {N : ObjRef}

macro "gpk_side" : tactic => `(tactic| first | (intro _ _ h; exact h) | (intro _ h; exact h) | trivial)

macro "gpk0_auto" : tactic => `(tactic| repeat' (first
  | ((with_reducible refine ik_doMachineOp ?_ _); gpk_side)
  | ((with_reducible refine ik_doExtendedOp ?_ _); gpk_side)
  | with_reducible exact ik_getObject _
  | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when)
  | (unfold NonDet.unless)))

theorem gpk_setObject (p : ObjRef) (o : KernelObject) : GpK N (setObject (Z := Unit) p o) := by
  unfold setObject; gpk0_auto

theorem gpk_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    GpK N (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo; repeat' (first | exact gpk_setObject _ _ | gpk0_auto)

theorem gpk_threadSet (f : Tcb → Tcb) (t : ObjRef) : GpK N (threadSet (Z := Unit) f t) := by
  unfold threadSet; repeat' (first | exact gpk_setObject _ _ | gpk0_auto)

theorem gpk_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : GpK N (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; repeat' (first | exact gpk_setObject _ _ | gpk0_auto)

theorem gpk_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : GpK N (asUser (Z := Unit) t u) := by
  unfold asUser; repeat' (first | exact gpk_setObject _ _ | gpk0_auto)

theorem gpk_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : GpK N (setMrs (Z := Unit) t b ms) := by
  unfold setMrs; repeat' (first | exact gpk_setObject _ _ | gpk0_auto)

theorem gpk_setCap (c : Cap) (sl : CslotPtr) : GpK N (setCap (Z := Unit) c sl) := by
  unfold setCap; repeat' (first | exact gpk_setObject _ _ | gpk0_auto)

theorem gpk_retypeRegionWith (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oBits : Nat) (ty : ApiObjectType)
    (dev : Bool) : GpK N (retypeRegionWith (Z := Unit) bA ptr n oBits ty dev) := by
  unfold retypeRegionWith; gpk0_auto

theorem gpk_retypeRegion (ptr : ObjRef) (n oBits : Nat) (ty : ApiObjectType) (dev : Bool) :
    GpK N (retypeRegion (Z := Unit) ptr n oBits ty dev) := by
  unfold retypeRegion; repeat' (first | exact gpk_retypeRegionWith _ _ _ _ _ _ | gpk0_auto)

theorem gpk_deleteObjects (ptr : Word) (bits : Nat) : GpK N (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects; gpk0_auto

theorem gpk_setThreadState (t : ObjRef) (ts : ThreadState) : GpK N (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (gpk_threadSet _ _) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; gpk0_auto

theorem gpk_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α) :
    GpK N (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact gpk_threadSet _ _

syntax "gpk_leaf" : tactic
macro_rules | `(tactic| gpk_leaf) => `(tactic| fail "no gpk_leaf")

macro "gpk_auto" : tactic => `(tactic| repeat' (first | gpk_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| gpk_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); gpk_side))
macro_rules | `(tactic| gpk_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); gpk_side))
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setObject _ _)
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setSimpleKo _ _ _)
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_threadSet _ _)
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archThreadSet _ _)
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_asUser _ _)
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setMrs _ _ _)
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setCap _ _)
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_retypeRegionWith _ _ _ _ _ _)
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_retypeRegion _ _ _ _ _)
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_deleteObjects _ _)
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setThreadState _ _)
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_optionUpdateThread _ _ _)

theorem gpk_archActivateIdleThread (_t : ObjRef) : GpK N (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archActivateIdleThread _)

theorem gpk_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : GpK N (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_threadGet _ _)

theorem gpk_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : GpK N (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getTcbObjRef _ _)

theorem gpk_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : GpK N (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_updateSchedContext _ _)

theorem gpk_schedContextCancelYieldTo (thread : ObjRef) : GpK N (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_schedContextCancelYieldTo _)

theorem gpk_getCap (a0 : CslotPtr) : GpK N (getCap (Z := Unit) a0) := by
  unfold getCap; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getCap _)

theorem gpk_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : GpK N (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_lookupIpcBuffer _ _)

theorem gpk_setMessageInfo (thread : ObjRef) (info : MessageInfo) : GpK N (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setMessageInfo _ _)

theorem gpk_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : GpK N (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_storeWordOffs _ _ _)

theorem gpk_replyFromKernel (thread : ObjRef) (x : Data × List Data) : GpK N (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_replyFromKernel _ _)

theorem gpk_getSchedContext (ptr : ObjRef) : GpK N (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getSchedContext _)

theorem gpk_schedContextUpdateConsumed (scPtr : ObjRef) : GpK N (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_schedContextUpdateConsumed _)

theorem gpk_setConsumed (scPtr tcbPtr : ObjRef) : GpK N (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setConsumed _ _)

theorem gpk_completeYieldTo (tcbPtr : ObjRef) : GpK N (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_completeYieldTo _)

theorem gpk_getThreadState (ref : ObjRef) : GpK N (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getThreadState _)

theorem gpk_setSchedulerAction (action : SchedulerAction) : GpK N (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setSchedulerAction _)

theorem gpk_setThreadStateAct (tcbPtr : ObjRef) : GpK N (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setThreadStateAct _)

theorem gpk_activateThread  : GpK N (activateThread (Z := Unit)) := by
  unfold activateThread; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_activateThread)

theorem gpk_archCheckIrq (_irq : Data) : GpKE N (archCheckIrq (Z := Unit) _irq) := by
  unfold archCheckIrq; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archCheckIrq _)

theorem gpk_ensureEmpty (slot : CslotPtr) : GpKE N (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_ensureEmpty _)

theorem gpk_isIoportRangeFree (f l : IoPort) : GpK N (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_isIoportRangeFree _ _)

theorem gpk_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : GpKE N m) : GpKE N (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; gpk_auto
  all_goals first | exact h_m
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible refine gpk_lookupErrorOnFailure _ _ ?_)

theorem gpk_resolveAddressBits' (p : Cap × CapRef) : GpKE N (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by gpk_auto)) fun nc => ?_
        split
        · exact gpk_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_resolveAddressBits' _)

theorem gpk_resolveAddressBits (a0 : Cap × CapRef) : GpKE N (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_resolveAddressBits _)

theorem gpk_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : GpKE N (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_lookupSlotForCnodeOp _ _ _ _)

theorem gpk_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : GpKE N (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_lookupTargetSlot _ _ _)

theorem gpk_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : GpKE N (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodeIoportControlInvocation _ _ _ _ _)

theorem gpk_getAsidPool (ptr : ObjRef) : GpK N (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getAsidPool _)

theorem gpk_findVspaceForAsid (asid : Asid) : GpKE N (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_findVspaceForAsid _)

theorem gpk_getPdpt (ptr : ObjRef) : GpK N (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getPdpt _)

theorem gpk_getPdpte (ptr : ObjRef) : GpK N (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getPdpte _)

theorem gpk_isFinalCap (cap : Cap) : GpK N (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_isFinalCap _)

theorem gpk_getPml4 (ptr : ObjRef) : GpK N (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getPml4 _)

theorem gpk_getPml4e (ptr : ObjRef) : GpK N (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getPml4e _)

theorem gpk_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : GpKE N (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_lookupPdptSlot _ _)

theorem gpk_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : GpKE N (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodePageDirectoryInvocation _ _ _ _ _)

theorem gpk_checkVpAlignment (sz : VMPageSize) (vptr : Word) : GpKE N (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_checkVpAlignment _ _)

theorem gpk_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : GpKE N (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_lookupPdSlot _ _)

theorem gpk_getPd (ptr : ObjRef) : GpK N (getPd (Z := Unit) ptr) := by
  unfold getPd; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getPd _)

theorem gpk_getPde (ptr : ObjRef) : GpK N (getPde (Z := Unit) ptr) := by
  unfold getPde; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getPde _)

theorem gpk_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : GpKE N (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_lookupPtSlot _ _)

theorem gpk_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : GpKE N (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_createMappingEntries _ _ _ _ _ _)

theorem gpk_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : GpKE N (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_ensureSafeMapping _)

theorem gpk_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : GpKE N (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodePageInvocation _ _ _ _ _)

theorem gpk_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : GpKE N (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodePageTableInvocation _ _ _ _ _)

theorem gpk_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : GpKE N (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodePdptInvocation _ _ _ _ _)

theorem gpk_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : GpKE N (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_ensurePortOperationAllowed _ _ _)

theorem gpk_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : GpKE N (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_decodePortInvocation _ _ _)

theorem gpk_ensureNoChildren (cslotPtr : CslotPtr) : GpKE N (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_ensureNoChildren _)

theorem gpk_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : GpK N (selectExt (Z := Unit) a S) := by
  unfold selectExt; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_selectExt _ _)

theorem gpk_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : GpKE N (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archDecodeInvocation _ _ _ _ _ _)

theorem gpk_getIrqState (irq : Irq) : GpK N (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getIrqState _)

theorem gpk_isIrqActive (irq : Irq) : GpK N (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_isIrqActive _)

theorem gpk_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : GpKE N (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archDecodeIrqControlInvocation _ _ _ _)

theorem gpk_archDeriveCap (c : ArchCap) : GpKE N (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_archDeriveCap _)

theorem gpk_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : GpK N (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_hwAsidInvalidate _ _)

theorem gpk_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : GpK N (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setAsidPool _ _)

theorem gpk_getCurrentCr3  : GpK N (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getCurrentCr3)

theorem gpk_setCurrentCr3 (c : Cr3) : GpK N (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setCurrentCr3 _)

theorem gpk_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : GpK N (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setCurrentVspaceRoot _ _)

theorem gpk_setVmRoot (tcb : ObjRef) : GpK N (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setVmRoot _)

theorem gpk_deleteAsid (asid : Asid) (pml4 : ObjRef) : GpK N (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_deleteAsid _ _)

theorem gpk_deleteAsidPool (base : Asid) (ptr : ObjRef) : GpK N (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_deleteAsidPool _ _)

theorem gpk_getPt (ptr : ObjRef) : GpK N (getPt (Z := Unit) ptr) := by
  unfold getPt; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getPt _)

theorem gpk_getPte (ptr : ObjRef) : GpK N (getPte (Z := Unit) ptr) := by
  unfold getPte; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_getPte _)

theorem gpk_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : GpK N (setPd (Z := Unit) ptr pd) := by
  unfold setPd; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setPd _ _)

theorem gpk_storePde (p : ObjRef) (pde : PDE) : GpK N (storePde (Z := Unit) p pde) := by
  unfold storePde; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_storePde _ _)

theorem gpk_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : GpK N (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_setPdpt _ _)

theorem gpk_storePdpte (p : ObjRef) (pte : PDPTE) : GpK N (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; gpk_auto
macro_rules | `(tactic| gpk_leaf) => `(tactic| with_reducible exact gpk_storePdpte _ _)
end

end Fl4Proofs.P3.SInvGp
