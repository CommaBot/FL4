/-
P3 (issue #16, s26): **the object half of l4v `valid_untyped` for device
untyped caps** (C26 of INV-PLAN §1.U3L; spec side only, outside the `JAtZ`
cone).

For a set `O` of (base, size bits) pairs, `OIn O σ`: every object of the
heap, with its `objBits`, is in `O`. The family `OBK O m := IK (OIn O) m`
is SpecInvUtZK1..ZK6's memory-half family `YK` (g5g, itself sg1's
SpecInvSgI1..I6) mechanically renamed (proofs/scratch/s26/mkob.py), with new
leaves: `ob_setObject` (`set_object` asserts the type of the old object, so
the size is kept: `dv_objBits_of_aType`), `ob_dmo` (machine operations do
not touch the heap), `ob_storeWordOffs`, `ob_portIn` / `ob_portOut`,
`ob_deleteObjects` (`detype` only removes objects). Left out, as in `YK`
(with their callers): `retype_region` (it creates objects), the performs,
the shells above them: SpecInvDvS..DvP.
-/
import Fl4Proofs.P3.SpecInvNativeScopeT
open Classical

namespace Fl4Proofs.P3.SInvDV
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- A set of objects (base, size bits). -/
abbrev ObSet := ObjRef → Nat → Prop

/-- **Every object of the heap, with its size, is in `O`.** -/
def OIn (O : ObSet) (σ : State Unit) : Prop := ∀ o ko, σ.kheap o = some ko → O o (objBits ko)

abbrev OBK (O : ObSet) {α : Type} (m : NonDet (State Unit) α) : Prop := IK (OIn O) m
abbrev OBKE (O : ObSet) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE (OIn O) m

/-- An object's type fixes its size (SpecKSz's `objBits_of_aType`, restated outside the `JAtZ` cone). -/
theorem dv_objBits_of_aType {ko ko' : KernelObject} (h : aType ko = aType ko') : objBits ko = objBits ko' := by
  cases ko <;> cases ko' <;> simp only [aType] at h <;> (try split_ifs at h) <;> simp_all [objBits] <;>
    (try (rename_i a b; cases a <;> cases b <;> simp_all [aaType, archKobjSize] <;> split_ifs at h <;> simp_all))

variable {O : ObSet}

theorem ob_dmo {α : Type} (mop : NonDet MachineState α) : OBK O (doMachineOp (Z := Unit) mop) :=
  ik_doMachineOp (fun _ _ h => h) mop

theorem ob_setObject (p : ObjRef) (o : KernelObject) : OBK O (setObject (Z := Unit) p o) := by
  unfold setObject
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := mem_getObject hy
  obtain ⟨old, y2⟩ := y
  simp only at hk hs; subst hs
  obtain ⟨z, ⟨hty, rfl⟩, hx⟩ := hx
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  intro o' ko ho'
  simp only [Function.update_apply] at ho'
  split_ifs at ho' with e
  · subst e
    cases ho'
    rw [← dv_objBits_of_aType hty]
    exact hσ _ _ hk
  · exact hσ _ _ ho'

theorem ob_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : OBK O (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  obtain ⟨z, ⟨hu, rfl⟩, hx⟩ := hx
  exact ob_dmo _ σ hσ x hx

macro "ob_side" : tactic => `(tactic| first | (intro _ _ h; exact h) | (intro _ h; exact h) | trivial)

macro "ob0_auto" : tactic => `(tactic| repeat' (first
  | with_reducible exact ob_dmo _
  | ((with_reducible refine ik_doExtendedOp ?_ _); ob_side)
  | with_reducible exact ik_getObject _
  | with_reducible exact ob_setObject _ _
  | with_reducible exact ob_storeWordOffs _ _ _
  | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when)
  | (unfold NonDet.unless)))

theorem ob_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    OBK O (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo; ob0_auto

theorem ob_threadSet (f : Tcb → Tcb) (t : ObjRef) : OBK O (threadSet (Z := Unit) f t) := by
  unfold threadSet; ob0_auto

theorem ob_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : OBK O (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; ob0_auto

theorem ob_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : OBK O (asUser (Z := Unit) t u) := by
  unfold asUser; ob0_auto

theorem ob_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : OBK O (setMrs (Z := Unit) t b ms) := by
  unfold setMrs; ob0_auto

theorem ob_setCap (c : Cap) (sl : CslotPtr) : OBK O (setCap (Z := Unit) c sl) := by
  unfold setCap; ob0_auto

theorem ob_deleteObjects (ptr : Word) (bits : Nat) : OBK O (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  refine ik_bind (ob_dmo _) fun _ => ik_modify fun σ h => ?_
  intro o ko ho
  by_cases hS : o ∈ {x | ptr ≤ x ∧ x ≤ ptr + 2 ^ bits - 1}
  · simp only [detype, if_pos hS] at ho; cases ho
  · simp only [detype, if_neg hS] at ho; exact h o ko ho

theorem ob_setThreadState (t : ObjRef) (ts : ThreadState) : OBK O (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (ob_threadSet _ _) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; ob0_auto

theorem ob_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α) :
    OBK O (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact ob_threadSet _ _

theorem ob_portIn (f : MachineMonad Data) : OBK O (portIn (Z := Unit) f) := by
  unfold portIn; exact ik_bind (ob_dmo _) fun _ => ik_pure _

theorem ob_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) :
    OBK O (portOut (Z := Unit) f w) := by
  unfold portOut; exact ik_bind (ob_dmo _) fun _ => ik_pure _

syntax "ob_leaf" : tactic
macro_rules | `(tactic| ob_leaf) => `(tactic| fail "no ob_leaf")

macro "ob_auto" : tactic => `(tactic| repeat' (first | ob_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_dmo _)
macro_rules | `(tactic| ob_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); ob_side))
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setObject _ _)
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_storeWordOffs _ _ _)
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setSimpleKo _ _ _)
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_threadSet _ _)
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archThreadSet _ _)
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_asUser _ _)
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setMrs _ _ _)
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setCap _ _)
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_deleteObjects _ _)
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setThreadState _ _)
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_optionUpdateThread _ _ _)
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_portIn _)
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_portOut _ _)

variable {OS : ObSet}

theorem ob_archActivateIdleThread (_t : ObjRef) : OBK OS (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archActivateIdleThread _)

theorem ob_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : OBK OS (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_threadGet _ _)

theorem ob_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : OBK OS (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getTcbObjRef _ _)

theorem ob_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : OBK OS (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_updateSchedContext _ _)

theorem ob_schedContextCancelYieldTo (thread : ObjRef) : OBK OS (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_schedContextCancelYieldTo _)

theorem ob_getCap (a0 : CslotPtr) : OBK OS (getCap (Z := Unit) a0) := by
  unfold getCap; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getCap _)

theorem ob_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : OBK OS (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_lookupIpcBuffer _ _)

theorem ob_setMessageInfo (thread : ObjRef) (info : MessageInfo) : OBK OS (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setMessageInfo _ _)

theorem ob_replyFromKernel (thread : ObjRef) (x : Data × List Data) : OBK OS (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_replyFromKernel _ _)

theorem ob_getSchedContext (ptr : ObjRef) : OBK OS (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getSchedContext _)

theorem ob_schedContextUpdateConsumed (scPtr : ObjRef) : OBK OS (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_schedContextUpdateConsumed _)

theorem ob_setConsumed (scPtr tcbPtr : ObjRef) : OBK OS (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setConsumed _ _)

theorem ob_completeYieldTo (tcbPtr : ObjRef) : OBK OS (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_completeYieldTo _)

theorem ob_getThreadState (ref : ObjRef) : OBK OS (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getThreadState _)

theorem ob_setSchedulerAction (action : SchedulerAction) : OBK OS (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setSchedulerAction _)

theorem ob_setThreadStateAct (tcbPtr : ObjRef) : OBK OS (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setThreadStateAct _)

theorem ob_activateThread  : OBK OS (activateThread (Z := Unit)) := by
  unfold activateThread; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_activateThread)

theorem ob_archCheckIrq (_irq : Data) : OBKE OS (archCheckIrq (Z := Unit) _irq) := by
  unfold archCheckIrq; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archCheckIrq _)

theorem ob_ensureEmpty (slot : CslotPtr) : OBKE OS (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_ensureEmpty _)

theorem ob_isIoportRangeFree (f l : IoPort) : OBK OS (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_isIoportRangeFree _ _)

theorem ob_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : OBKE OS m) : OBKE OS (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; ob_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible refine ob_lookupErrorOnFailure _ _ ?_)

theorem ob_resolveAddressBits' (p : Cap × CapRef) : OBKE OS (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by ob_auto)) fun nc => ?_
        split
        · exact ob_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_resolveAddressBits' _)

theorem ob_resolveAddressBits (a0 : Cap × CapRef) : OBKE OS (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_resolveAddressBits _)

theorem ob_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : OBKE OS (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_lookupSlotForCnodeOp _ _ _ _)

theorem ob_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : OBKE OS (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_lookupTargetSlot _ _ _)

theorem ob_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : OBKE OS (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodeIoportControlInvocation _ _ _ _ _)

theorem ob_getAsidPool (ptr : ObjRef) : OBK OS (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getAsidPool _)

theorem ob_findVspaceForAsid (asid : Asid) : OBKE OS (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_findVspaceForAsid _)

theorem ob_getPdpt (ptr : ObjRef) : OBK OS (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getPdpt _)

theorem ob_getPdpte (ptr : ObjRef) : OBK OS (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getPdpte _)

theorem ob_isFinalCap (cap : Cap) : OBK OS (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_isFinalCap _)

theorem ob_getPml4 (ptr : ObjRef) : OBK OS (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getPml4 _)

theorem ob_getPml4e (ptr : ObjRef) : OBK OS (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getPml4e _)

theorem ob_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : OBKE OS (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_lookupPdptSlot _ _)

theorem ob_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : OBKE OS (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodePageDirectoryInvocation _ _ _ _ _)

theorem ob_checkVpAlignment (sz : VMPageSize) (vptr : Word) : OBKE OS (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_checkVpAlignment _ _)

theorem ob_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : OBKE OS (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_lookupPdSlot _ _)

theorem ob_getPd (ptr : ObjRef) : OBK OS (getPd (Z := Unit) ptr) := by
  unfold getPd; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getPd _)

theorem ob_getPde (ptr : ObjRef) : OBK OS (getPde (Z := Unit) ptr) := by
  unfold getPde; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getPde _)

theorem ob_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : OBKE OS (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_lookupPtSlot _ _)

theorem ob_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : OBKE OS (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_createMappingEntries _ _ _ _ _ _)

theorem ob_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : OBKE OS (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_ensureSafeMapping _)

theorem ob_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : OBKE OS (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodePageInvocation _ _ _ _ _)

theorem ob_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : OBKE OS (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodePageTableInvocation _ _ _ _ _)

theorem ob_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : OBKE OS (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodePdptInvocation _ _ _ _ _)

theorem ob_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : OBKE OS (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_ensurePortOperationAllowed _ _ _)

theorem ob_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : OBKE OS (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_decodePortInvocation _ _ _)

theorem ob_ensureNoChildren (cslotPtr : CslotPtr) : OBKE OS (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_ensureNoChildren _)

theorem ob_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : OBK OS (selectExt (Z := Unit) a S) := by
  unfold selectExt; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_selectExt _ _)

theorem ob_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : OBKE OS (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archDecodeInvocation _ _ _ _ _ _)

theorem ob_getIrqState (irq : Irq) : OBK OS (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getIrqState _)

theorem ob_isIrqActive (irq : Irq) : OBK OS (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_isIrqActive _)

theorem ob_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : OBKE OS (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archDecodeIrqControlInvocation _ _ _ _)

theorem ob_archDeriveCap (c : ArchCap) : OBKE OS (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_archDeriveCap _)

theorem ob_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : OBK OS (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_hwAsidInvalidate _ _)

theorem ob_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : OBK OS (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setAsidPool _ _)

theorem ob_getCurrentCr3  : OBK OS (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getCurrentCr3)

theorem ob_setCurrentCr3 (c : Cr3) : OBK OS (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setCurrentCr3 _)

theorem ob_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : OBK OS (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setCurrentVspaceRoot _ _)

theorem ob_setVmRoot (tcb : ObjRef) : OBK OS (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setVmRoot _)

theorem ob_deleteAsid (asid : Asid) (pml4 : ObjRef) : OBK OS (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_deleteAsid _ _)

theorem ob_deleteAsidPool (base : Asid) (ptr : ObjRef) : OBK OS (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_deleteAsidPool _ _)

theorem ob_getPt (ptr : ObjRef) : OBK OS (getPt (Z := Unit) ptr) := by
  unfold getPt; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getPt _)

theorem ob_getPte (ptr : ObjRef) : OBK OS (getPte (Z := Unit) ptr) := by
  unfold getPte; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_getPte _)

theorem ob_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : OBK OS (setPd (Z := Unit) ptr pd) := by
  unfold setPd; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setPd _ _)

theorem ob_storePde (p : ObjRef) (pde : PDE) : OBK OS (storePde (Z := Unit) p pde) := by
  unfold storePde; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_storePde _ _)

theorem ob_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : OBK OS (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_setPdpt _ _)

theorem ob_storePdpte (p : ObjRef) (pte : PDPTE) : OBK OS (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; ob_auto
macro_rules | `(tactic| ob_leaf) => `(tactic| with_reducible exact ob_storePdpte _ _)
end

end Fl4Proofs.P3.SInvDV
