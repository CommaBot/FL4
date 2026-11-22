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
