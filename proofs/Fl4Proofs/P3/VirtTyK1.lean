/-
P3x for virtualization (line virt, gen 3; proofs/VIRT-PLAN.md §10 R7 (b)): **the object-type family `TYK`**
(spec side only, outside the `JAtZ` cone).

For a predicate `T` on (address, object type) pairs, `TIn T σ`: every object of the heap, with its `aType`, is in
`T`; `TYK T m := IK (TIn T) m`. The family is SpecInvDvK1..K3's `OBK` (the object half of device
`valid_untyped`, itself SpecInvUtZK1..K3 renamed) with `objBits ko` replaced by `aType ko`, mechanically
(proofs/scratch/virt/mkty.py); only the leaf `ty_setObject` changes (`set_object` asserts the old object's type,
so the type is kept directly). Its use: `T := fun _ t => t ≠ .aArch .aVcpu` is "no VCPU object" (VirtR7b), kept
by `rec_del` and `cap_revoke` (`ty_recDel`, `ty_capRevoke`). No premises; new files only.
-/
import Fl4Proofs.P3.SpecInvNativeScopeT
open Classical

namespace Fl4Proofs.P3.SInvTY
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- A set of (address, object type) pairs. -/
abbrev TySet := ObjRef → AType → Prop

/-- **Every object of the heap, with its type, is in `O`.** -/
def TIn (O : TySet) (σ : State Unit) : Prop := ∀ o ko, σ.kheap o = some ko → O o (aType ko)

abbrev TYK (O : TySet) {α : Type} (m : NonDet (State Unit) α) : Prop := IK (TIn O) m
abbrev TYKE (O : TySet) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKE (TIn O) m

variable {O : TySet}

theorem ty_dmo {α : Type} (mop : NonDet MachineState α) : TYK O (doMachineOp (Z := Unit) mop) :=
  ik_doMachineOp (fun _ _ h => h) mop

theorem ty_setObject (p : ObjRef) (o : KernelObject) : TYK O (setObject (Z := Unit) p o) := by
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
    rw [← hty]
    exact hσ _ _ hk
  · exact hσ _ _ ho'

theorem ty_storeWordOffs (ptr : ObjRef) (offs : Nat) (v : Word) : TYK O (storeWordOffs (Z := Unit) ptr offs v) := by
  unfold storeWordOffs
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  obtain ⟨z, ⟨hu, rfl⟩, hx⟩ := hx
  exact ty_dmo _ σ hσ x hx

macro "ty_side" : tactic => `(tactic| first | (intro _ _ h; exact h) | (intro _ h; exact h) | trivial)

macro "ty0_auto" : tactic => `(tactic| repeat' (first
  | with_reducible exact ty_dmo _
  | ((with_reducible refine ik_doExtendedOp ?_ _); ty_side)
  | with_reducible exact ik_getObject _
  | with_reducible exact ty_setObject _ _
  | with_reducible exact ty_storeWordOffs _ _ _
  | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when)
  | (unfold NonDet.unless)))

theorem ty_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    TYK O (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo; ty0_auto

theorem ty_threadSet (f : Tcb → Tcb) (t : ObjRef) : TYK O (threadSet (Z := Unit) f t) := by
  unfold threadSet; ty0_auto

theorem ty_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : TYK O (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; ty0_auto

theorem ty_asUser {α : Type} (t : ObjRef) (u : UserMonad α) : TYK O (asUser (Z := Unit) t u) := by
  unfold asUser; ty0_auto

theorem ty_setMrs (t : ObjRef) (b : Option ObjRef) (ms : List Message) : TYK O (setMrs (Z := Unit) t b ms) := by
  unfold setMrs; ty0_auto

theorem ty_setCap (c : Cap) (sl : CslotPtr) : TYK O (setCap (Z := Unit) c sl) := by
  unfold setCap; ty0_auto

theorem ty_deleteObjects (ptr : Word) (bits : Nat) : TYK O (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  refine ik_bind (ty_dmo _) fun _ => ik_modify fun σ h => ?_
  intro o ko ho
  by_cases hS : o ∈ {x | ptr ≤ x ∧ x ≤ ptr + 2 ^ bits - 1}
  · simp only [detype, if_pos hS] at ho; cases ho
  · simp only [detype, if_neg hS] at ho; exact h o ko ho

theorem ty_setThreadState (t : ObjRef) (ts : ThreadState) : TYK O (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (ty_threadSet _ _) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; ty0_auto

theorem ty_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α) :
    TYK O (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact ty_threadSet _ _

theorem ty_portIn (f : MachineMonad Data) : TYK O (portIn (Z := Unit) f) := by
  unfold portIn; exact ik_bind (ty_dmo _) fun _ => ik_pure _

theorem ty_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) :
    TYK O (portOut (Z := Unit) f w) := by
  unfold portOut; exact ik_bind (ty_dmo _) fun _ => ik_pure _

syntax "ty_leaf" : tactic
macro_rules | `(tactic| ty_leaf) => `(tactic| fail "no ty_leaf")

macro "ty_auto" : tactic => `(tactic| repeat' (first | ty_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_dmo _)
macro_rules | `(tactic| ty_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); ty_side))
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setObject _ _)
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_storeWordOffs _ _ _)
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setSimpleKo _ _ _)
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_threadSet _ _)
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archThreadSet _ _)
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_asUser _ _)
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setMrs _ _ _)
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setCap _ _)
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_deleteObjects _ _)
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setThreadState _ _)
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_optionUpdateThread _ _ _)
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_portIn _)
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_portOut _ _)

variable {OS : TySet}

theorem ty_archActivateIdleThread (_t : ObjRef) : TYK OS (archActivateIdleThread (Z := Unit) _t) := by
  unfold archActivateIdleThread; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archActivateIdleThread _)

theorem ty_threadGet {α : Type} (f : Tcb → α) (tptr : ObjRef) : TYK OS (threadGet (Z := Unit) f tptr) := by
  unfold threadGet; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_threadGet _ _)

theorem ty_getTcbObjRef (f : Tcb → Option ObjRef) (ref : ObjRef) : TYK OS (getTcbObjRef (Z := Unit) f ref) := by
  unfold getTcbObjRef; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getTcbObjRef _ _)

theorem ty_updateSchedContext (ptr : ObjRef) (f : SchedContext → SchedContext) : TYK OS (updateSchedContext (Z := Unit) ptr f) := by
  unfold updateSchedContext; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_updateSchedContext _ _)

theorem ty_schedContextCancelYieldTo (thread : ObjRef) : TYK OS (schedContextCancelYieldTo (Z := Unit) thread) := by
  unfold schedContextCancelYieldTo; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_schedContextCancelYieldTo _)

theorem ty_getCap (a0 : CslotPtr) : TYK OS (getCap (Z := Unit) a0) := by
  unfold getCap; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getCap _)

theorem ty_lookupIpcBuffer (isReceiver : Bool) (thread : ObjRef) : TYK OS (lookupIpcBuffer (Z := Unit) isReceiver thread) := by
  unfold lookupIpcBuffer; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_lookupIpcBuffer _ _)

theorem ty_setMessageInfo (thread : ObjRef) (info : MessageInfo) : TYK OS (setMessageInfo (Z := Unit) thread info) := by
  unfold setMessageInfo; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setMessageInfo _ _)

theorem ty_replyFromKernel (thread : ObjRef) (x : Data × List Data) : TYK OS (replyFromKernel (Z := Unit) thread x) := by
  unfold replyFromKernel; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_replyFromKernel _ _)

theorem ty_getSchedContext (ptr : ObjRef) : TYK OS (getSchedContext (Z := Unit) ptr) := by
  unfold getSchedContext; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getSchedContext _)

theorem ty_schedContextUpdateConsumed (scPtr : ObjRef) : TYK OS (schedContextUpdateConsumed (Z := Unit) scPtr) := by
  unfold schedContextUpdateConsumed; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_schedContextUpdateConsumed _)

theorem ty_setConsumed (scPtr tcbPtr : ObjRef) : TYK OS (setConsumed (Z := Unit) scPtr tcbPtr) := by
  unfold setConsumed; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setConsumed _ _)

theorem ty_completeYieldTo (tcbPtr : ObjRef) : TYK OS (completeYieldTo (Z := Unit) tcbPtr) := by
  unfold completeYieldTo; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_completeYieldTo _)

theorem ty_getThreadState (ref : ObjRef) : TYK OS (getThreadState (Z := Unit) ref) := by
  unfold getThreadState; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getThreadState _)

theorem ty_setSchedulerAction (action : SchedulerAction) : TYK OS (setSchedulerAction (Z := Unit) action) := by
  unfold setSchedulerAction; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setSchedulerAction _)

theorem ty_setThreadStateAct (tcbPtr : ObjRef) : TYK OS (setThreadStateAct (Z := Unit) tcbPtr) := by
  unfold setThreadStateAct; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setThreadStateAct _)

theorem ty_activateThread  : TYK OS (activateThread (Z := Unit)) := by
  unfold activateThread; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_activateThread)

theorem ty_archCheckIrq (_irq : Data) : TYKE OS (archCheckIrq (Z := Unit) _irq) := by
  unfold archCheckIrq; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archCheckIrq _)

theorem ty_ensureEmpty (slot : CslotPtr) : TYKE OS (ensureEmpty (Z := Unit) slot) := by
  unfold ensureEmpty; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_ensureEmpty _)

theorem ty_isIoportRangeFree (f l : IoPort) : TYK OS (isIoportRangeFree (Z := Unit) f l) := by
  unfold isIoportRangeFree; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_isIoportRangeFree _ _)

theorem ty_lookupErrorOnFailure {α : Type} (s : Bool) (m : LFMonad Unit α) (h_m : TYKE OS m) : TYKE OS (lookupErrorOnFailure (Z := Unit) s m) := by
  unfold lookupErrorOnFailure; ty_auto
  all_goals first | exact h_m
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible refine ty_lookupErrorOnFailure _ _ ?_)

theorem ty_resolveAddressBits' (p : Cap × CapRef) : TYKE OS (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact ike_liftE ik_fail
    · refine ike_bind (ike_whenE _ (ike_throw _)) fun _ => ike_bind (ike_whenE _ (ike_throw _)) fun _ => ?_
      refine ike_returnOk_bind ?_
      dsimp only
      split
      · exact ike_returnOk _
      · refine ike_bind (ike_liftE (by ty_auto)) fun nc => ?_
        split
        · exact ty_resolveAddressBits' _
        · exact ike_returnOk _
  · exact ike_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_resolveAddressBits' _)

theorem ty_resolveAddressBits (a0 : Cap × CapRef) : TYKE OS (resolveAddressBits (Z := Unit) a0) := by
  unfold resolveAddressBits; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_resolveAddressBits _)

theorem ty_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : TYKE OS (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_lookupSlotForCnodeOp _ _ _ _)

theorem ty_lookupTargetSlot (a0 : Cap) (a1 : CapRef) (a2 : Nat) : TYKE OS (lookupTargetSlot (Z := Unit) a0 a1 a2) := by
  unfold lookupTargetSlot; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_lookupTargetSlot _ _ _)

theorem ty_decodeIoportControlInvocation (label : Data) (args : List Data) (slot : CslotPtr) (_cap : ArchCap) (extraCaps : List Cap) : TYKE OS (decodeIoportControlInvocation (Z := Unit) label args slot _cap extraCaps) := by
  unfold decodeIoportControlInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodeIoportControlInvocation _ _ _ _ _)

theorem ty_getAsidPool (ptr : ObjRef) : TYK OS (getAsidPool (Z := Unit) ptr) := by
  unfold getAsidPool; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getAsidPool _)

theorem ty_findVspaceForAsid (asid : Asid) : TYKE OS (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_findVspaceForAsid _)

theorem ty_getPdpt (ptr : ObjRef) : TYK OS (getPdpt (Z := Unit) ptr) := by
  unfold getPdpt; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getPdpt _)

theorem ty_getPdpte (ptr : ObjRef) : TYK OS (getPdpte (Z := Unit) ptr) := by
  unfold getPdpte; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getPdpte _)

theorem ty_isFinalCap (cap : Cap) : TYK OS (isFinalCap (Z := Unit) cap) := by
  unfold isFinalCap; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_isFinalCap _)

theorem ty_getPml4 (ptr : ObjRef) : TYK OS (getPml4 (Z := Unit) ptr) := by
  unfold getPml4; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getPml4 _)

theorem ty_getPml4e (ptr : ObjRef) : TYK OS (getPml4e (Z := Unit) ptr) := by
  unfold getPml4e; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getPml4e _)

theorem ty_lookupPdptSlot (pd : ObjRef) (vptr : VSpaceRef) : TYKE OS (lookupPdptSlot (Z := Unit) pd vptr) := by
  unfold lookupPdptSlot; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_lookupPdptSlot _ _)

theorem ty_decodePageDirectoryInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : TYKE OS (decodePageDirectoryInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageDirectoryInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodePageDirectoryInvocation _ _ _ _ _)

theorem ty_checkVpAlignment (sz : VMPageSize) (vptr : Word) : TYKE OS (checkVpAlignment (Z := Unit) sz vptr) := by
  unfold checkVpAlignment; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_checkVpAlignment _ _)

theorem ty_lookupPdSlot (pd : ObjRef) (vptr : VSpaceRef) : TYKE OS (lookupPdSlot (Z := Unit) pd vptr) := by
  unfold lookupPdSlot; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_lookupPdSlot _ _)

theorem ty_getPd (ptr : ObjRef) : TYK OS (getPd (Z := Unit) ptr) := by
  unfold getPd; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getPd _)

theorem ty_getPde (ptr : ObjRef) : TYK OS (getPde (Z := Unit) ptr) := by
  unfold getPde; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getPde _)

theorem ty_lookupPtSlot (vspace : ObjRef) (vptr : VSpaceRef) : TYKE OS (lookupPtSlot (Z := Unit) vspace vptr) := by
  unfold lookupPtSlot; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_lookupPtSlot _ _)

theorem ty_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (a0 : VMPageSize) (a1 : VMRights) (a2 : VMAttributes) (a3 : ObjRef) : TYKE OS (createMappingEntries (Z := Unit) base vptr a0 a1 a2 a3) := by
  unfold createMappingEntries; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_createMappingEntries _ _ _ _ _ _)

theorem ty_ensureSafeMapping (a0 : VMPageEntry × ObjRef) : TYKE OS (ensureSafeMapping (Z := Unit) a0) := by
  unfold ensureSafeMapping; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_ensureSafeMapping _)

theorem ty_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : TYKE OS (decodePageInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodePageInvocation _ _ _ _ _)

theorem ty_decodePageTableInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : TYKE OS (decodePageTableInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePageTableInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodePageTableInvocation _ _ _ _ _)

theorem ty_decodePdptInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : TYKE OS (decodePdptInvocation (Z := Unit) label args cte cap extraCaps) := by
  unfold decodePdptInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodePdptInvocation _ _ _ _ _)

theorem ty_ensurePortOperationAllowed (cap : ArchCap) (startPort : Word32) (sz : Nat) : TYKE OS (ensurePortOperationAllowed (Z := Unit) cap startPort sz) := by
  unfold ensurePortOperationAllowed; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_ensurePortOperationAllowed _ _ _)

theorem ty_decodePortInvocation (label : Data) (args : List Data) (cap : ArchCap) : TYKE OS (decodePortInvocation (Z := Unit) label args cap) := by
  unfold decodePortInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_decodePortInvocation _ _ _)

theorem ty_ensureNoChildren (cslotPtr : CslotPtr) : TYKE OS (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_ensureNoChildren _)

theorem ty_selectExt {D : Type} (a : State DetExt → D) (S : Set D) : TYK OS (selectExt (Z := Unit) a S) := by
  unfold selectExt; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_selectExt _ _)

theorem ty_archDecodeInvocation (label : Data) (args : List Data) (_xSlot : CapRef) (cte : CslotPtr) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) : TYKE OS (archDecodeInvocation (Z := Unit) label args _xSlot cte cap extraCaps) := by
  unfold archDecodeInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archDecodeInvocation _ _ _ _ _ _)

theorem ty_getIrqState (irq : Irq) : TYK OS (getIrqState (Z := Unit) irq) := by
  unfold getIrqState; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getIrqState _)

theorem ty_isIrqActive (irq : Irq) : TYK OS (isIrqActive (Z := Unit) irq) := by
  unfold isIrqActive; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_isIrqActive _)

theorem ty_archDecodeIrqControlInvocation (label : Data) (args : List Data) (srcSlot : CslotPtr) (cps : List Cap) : TYKE OS (archDecodeIrqControlInvocation (Z := Unit) label args srcSlot cps) := by
  unfold archDecodeIrqControlInvocation; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archDecodeIrqControlInvocation _ _ _ _)

theorem ty_archDeriveCap (c : ArchCap) : TYKE OS (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_archDeriveCap _)

theorem ty_hwAsidInvalidate (asid : Asid) (vspace : ObjRef) : TYK OS (hwAsidInvalidate (Z := Unit) asid vspace) := by
  unfold hwAsidInvalidate; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_hwAsidInvalidate _ _)

theorem ty_setAsidPool (ptr : ObjRef) (pool : AsidLowIndex → Option ObjRef) : TYK OS (setAsidPool (Z := Unit) ptr pool) := by
  unfold setAsidPool; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setAsidPool _ _)

theorem ty_getCurrentCr3  : TYK OS (getCurrentCr3 (Z := Unit)) := by
  unfold getCurrentCr3; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getCurrentCr3)

theorem ty_setCurrentCr3 (c : Cr3) : TYK OS (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setCurrentCr3 _)

theorem ty_setCurrentVspaceRoot (vspace : ObjRef) (asid : Asid) : TYK OS (setCurrentVspaceRoot (Z := Unit) vspace asid) := by
  unfold setCurrentVspaceRoot; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setCurrentVspaceRoot _ _)

theorem ty_setVmRoot (tcb : ObjRef) : TYK OS (setVmRoot (Z := Unit) tcb) := by
  unfold setVmRoot; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setVmRoot _)

theorem ty_deleteAsid (asid : Asid) (pml4 : ObjRef) : TYK OS (deleteAsid (Z := Unit) asid pml4) := by
  unfold deleteAsid; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_deleteAsid _ _)

theorem ty_deleteAsidPool (base : Asid) (ptr : ObjRef) : TYK OS (deleteAsidPool (Z := Unit) base ptr) := by
  unfold deleteAsidPool; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_deleteAsidPool _ _)

theorem ty_getPt (ptr : ObjRef) : TYK OS (getPt (Z := Unit) ptr) := by
  unfold getPt; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getPt _)

theorem ty_getPte (ptr : ObjRef) : TYK OS (getPte (Z := Unit) ptr) := by
  unfold getPte; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_getPte _)

theorem ty_setPd (ptr : ObjRef) (pd : BitVec 9 → PDE) : TYK OS (setPd (Z := Unit) ptr pd) := by
  unfold setPd; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setPd _ _)

theorem ty_storePde (p : ObjRef) (pde : PDE) : TYK OS (storePde (Z := Unit) p pde) := by
  unfold storePde; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_storePde _ _)

theorem ty_setPdpt (ptr : ObjRef) (pt : BitVec 9 → PDPTE) : TYK OS (setPdpt (Z := Unit) ptr pt) := by
  unfold setPdpt; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_setPdpt _ _)

theorem ty_storePdpte (p : ObjRef) (pte : PDPTE) : TYK OS (storePdpte (Z := Unit) p pte) := by
  unfold storePdpte; ty_auto
macro_rules | `(tactic| ty_leaf) => `(tactic| with_reducible exact ty_storePdpte _ _)
end

end Fl4Proofs.P3.SInvTY
