/-
P3: **the spec's objects only keep their type or vanish** (`KSz`), the
frame of `SpecFree` (l4v `valid_untyped`, ScPlace).

* `KSz σ σ'`: every object of `σ'` is at an address where `σ` had an
  object of the same `aType` (so of the same size, `objBits_of_aType`).
  `set_object` asserts the type is unchanged, so whatever is built from
  `set_object`, `detype` and updates of other state fields keeps it
  (`NKZ`, the same combinators as `NKS`): the CSpace operations, thread
  state and scheduler updates, the preemption point, the reset.
* `SpecFree.frame`: `SpecFree` kept by a step with `KSz` whose untyped caps
  after each have one before over the same region with a free index no
  larger.

The spec writes its heap only through `set_object` (type kept),
`detype` (`delete_objects`) and `retype_region`; the last two occur only in
`invoke_untyped`. So the frame covers every operation but
`invoke_untyped`, given its FL4 side (untyped caps kept, copied with their
free index, or deleted). `invoke_untyped` (retype, and the reset, preempted
or not) adds objects, lowers or raises the source's free index and creates
untyped caps over new regions: `SpecFree.retype` (SpecFreeRetJ).
-/
import Fl4Proofs.P3.RetypeFresh
import Fl4Proofs.P3.ScPlace
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open Fl4Spec

noncomputable section

/-- An object's type fixes its size. -/
theorem objBits_of_aType {ko ko' : KernelObject} (h : aType ko = aType ko') : objBits ko = objBits ko' := by
  cases ko <;> cases ko' <;> simp only [aType] at h <;> (try split_ifs at h) <;> simp_all [objBits] <;>
    (try (rename_i a b; cases a <;> cases b <;> simp_all [aaType, archKobjSize] <;> split_ifs at h <;> simp_all))

/-- Every object of `σ'` was an object of the same type in `σ`. -/
def KSz (σ σ' : State Unit) : Prop :=
  ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ aType ko = aType ko'

theorem KSz.refl (σ : State Unit) : KSz σ σ := fun _ ko h => ⟨ko, h, rfl⟩

theorem KSz.trans {σ1 σ2 σ3 : State Unit} (h1 : KSz σ1 σ2) (h2 : KSz σ2 σ3) : KSz σ1 σ3 := by
  intro o ko h
  obtain ⟨k2, h2', e2⟩ := h2 o ko h
  obtain ⟨k1, h1', e1⟩ := h1 o k2 h2'
  exact ⟨k1, h1', e1.trans e2⟩

theorem KSz.of_kheap {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) : KSz σ σ' := by
  intro o ko hk; rw [h] at hk; exact ⟨ko, hk, rfl⟩

/-- Every outcome keeps `KSz`. -/
def NKZ {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → KSz σ x.2

theorem ksz_of_eq {α : Type} {m : NonDet (State Unit) α} (hm : NKZ m)
    {σ σ' : State Unit} {a : α} {X : Prop} (h : m σ = ({(a, σ')}, X)) : KSz σ σ' :=
  hm σ (a, σ') (by rw [h]; rfl)

theorem nkz_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : NKZ m)
    (hf : ∀ a, NKZ (f a)) : NKZ (m >>= f) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hf y.1 y.2 x hx)

theorem nkz_pure {α : Type} (a : α) : NKZ (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact KSz.refl σ

theorem nkz_pure' {α : Type} (a : α) : NKZ (NonDet.pure a : NonDet (State Unit) α) := nkz_pure a

theorem nkz_gets {α : Type} (f : State Unit → α) : NKZ (NonDet.gets f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact KSz.refl σ

theorem nkz_get : NKZ (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact KSz.refl σ

theorem nkz_modify {f : State Unit → State Unit} (hf : ∀ σ, (f σ).kheap = σ.kheap) : NKZ (NonDet.modify f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact KSz.of_kheap (hf σ)

/-- Objects vanish (`detype`). -/
theorem nkz_detype (R : Set ObjRef) : NKZ (NonDet.modify (detype (Z := Unit) R)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]
  intro o ko hk
  simp only [detype] at hk
  split_ifs at hk
  exact ⟨ko, hk, rfl⟩

theorem nkz_assert (P : Prop) : NKZ (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact KSz.refl σ

theorem nkz_fail {α : Type} : NKZ (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem nkz_assertOpt {α : Type} (o : Option α) : NKZ (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact nkz_fail
  · exact nkz_pure' _

theorem nkz_getsThe {α : Type} (f : State Unit → Option α) : NKZ (NonDet.getsThe f) := by
  intro σ x hx
  exact nkz_assertOpt (f σ) σ x hx

theorem nkz_selectF {α : Type} (S : Set α × Prop) : NKZ (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact KSz.refl σ

theorem nkz_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : NKZ m1) (h2 : NKZ m2) :
    NKZ (if P then m1 else m2) := by
  split <;> assumption

theorem nkz_getObject (p : ObjRef) : NKZ (getObject (Z := Unit) p) := nkz_getsThe _

theorem nkz_setObject (p : ObjRef) (o : KernelObject) : NKZ (setObject (Z := Unit) p o) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨k, hk⟩ : ∃ k, σ.kheap p = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap p with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  obtain ⟨hk, rfl⟩ := hk
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨hty, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  intro o' ko' h
  by_cases e : o' = p
  · subst e
    simp only [Function.update_self, Option.some.injEq] at h
    subst h
    exact ⟨k, hk, hty⟩
  · simp only [Function.update_of_ne e] at h; exact ⟨ko', h, rfl⟩

theorem nkz_get_put {f : State Unit → State Unit} (hf : ∀ σ, (f σ).kheap = σ.kheap) :
    NKZ (NonDet.get >>= fun s => NonDet.put (f s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact KSz.of_kheap (hf σ)

theorem nkz_when {P : Prop} {inst : Decidable P} {m : NonDet (State Unit) Unit} (h : NKZ m) :
    NKZ (@NonDet.when _ P inst m) := by
  unfold NonDet.when; split; exact h; exact nkz_pure' _

theorem nkz_unless {P : Prop} {inst : Decidable P} {m : NonDet (State Unit) Unit} (h : NKZ m) :
    NKZ (@NonDet.unless _ P inst m) := by
  unfold NonDet.unless; split; exact nkz_pure' _; exact h

theorem nkz_mapMx {α β : Type} {f : α → NonDet (State Unit) β} (hf : ∀ a, NKZ (f a)) :
    ∀ l, NKZ (NonDet.mapMx f l)
  | [] => nkz_pure' _
  | a :: l => nkz_bind (hf a) (fun _ => nkz_mapMx hf l)

macro "nkz_step" : tactic => `(tactic| first
  | exact nkz_pure _ | exact nkz_pure' _ | exact nkz_fail | exact nkz_gets _ | exact nkz_get
  | exact nkz_assert _ | exact nkz_assertOpt _ | exact nkz_getObject _ | exact nkz_setObject _ _
  | exact nkz_getsThe _
  | exact nkz_get_put (fun σ => rfl)
  | exact nkz_modify (fun σ => rfl)
  | (refine nkz_bind ?_ (fun _ => ?_))
  | (apply nkz_ite)
  | split)

theorem nkz_getCap (sl : CslotPtr) : NKZ (getCap (Z := Unit) sl) := by
  obtain ⟨o, c⟩ := sl
  unfold getCap
  refine nkz_bind (nkz_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> repeat nkz_step

theorem nkz_setCap (cap : Cap) (sl : CslotPtr) : NKZ (setCap (Z := Unit) cap sl) := by
  obtain ⟨o, c⟩ := sl
  unfold setCap
  refine nkz_bind (nkz_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> repeat nkz_step

theorem nkz_doExtendedOp (eop : DetExtMonad Unit) : NKZ (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine nkz_bind nkz_get (fun _ => nkz_bind (nkz_selectF _) (fun _ => ?_))
  split
  exact nkz_modify (fun σ => rfl)

theorem nkz_doMachineOp {α : Type} (mop : NonDet MachineState α) : NKZ (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine nkz_bind (nkz_gets _) (fun _ => nkz_bind (nkz_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact nkz_bind (nkz_modify (fun σ => rfl)) (fun _ => nkz_pure _)

macro "nkz_auto" : tactic => `(tactic| repeat (first | exact nkz_getCap _ | exact nkz_setCap _ _ | exact nkz_doExtendedOp _ | exact nkz_doMachineOp _ | nkz_step))

theorem nkz_threadSet (f : Tcb → Tcb) (t : ObjRef) : NKZ (threadSet (Z := Unit) f t) := by
  unfold threadSet; exact nkz_bind (nkz_getsThe _) (fun _ => nkz_setObject _ _)

theorem nkz_setThreadState (t : ObjRef) (ts : ThreadState) : NKZ (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState threadSet setThreadStateAct setSchedulerAction NonDet.when
  nkz_auto

theorem nkz_createCap (t : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (dev : Bool)
    (x : CslotPtr × ObjRef) : NKZ (createCap (Z := Unit) t bits untyped dev x) := by
  obtain ⟨d, o⟩ := x
  unfold createCap setCdt setOriginal
  nkz_auto

theorem nkz_initArchObjects (t : ApiObjectType) (dev : Bool) (ptr : ObjRef) (n sz : Nat)
    (refs : List ObjRef) : NKZ (initArchObjects (Z := Unit) t dev ptr n sz refs) := by
  unfold initArchObjects
  refine nkz_when (nkz_mapMx (fun pm => ?_) _)
  unfold copyGlobalMappings
  refine nkz_bind (nkz_gets _) (fun _ => nkz_bind (nkz_pure _) (fun _ => nkz_bind (nkz_pure _)
    (fun _ => nkz_bind (nkz_pure _) (fun _ => nkz_mapMx (fun i => ?_) _))))
  unfold getPml4e storePml4e getPml4 setPml4
  nkz_auto

theorem nkz_deleteObjects (ptr : Word) (bits : Nat) : NKZ (deleteObjects (Z := Unit) ptr bits) := by
  unfold deleteObjects
  exact nkz_bind (nkz_doMachineOp _) (fun _ => nkz_detype _)

/-! ## The exception monad -/

def NKZE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := NKZ (ExceptT.run m)

theorem nkze_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {f : α → NonDetE (State Unit) ε β}
    (hm : NKZE m) (hf : ∀ a, NKZE (f a)) : NKZE (m >>= f) := by
  unfold NKZE; rw [ExceptT.run_bind]
  refine nkz_bind hm (fun r => ?_)
  cases r with
  | ok a => exact hf a
  | error e => exact nkz_pure _

theorem nkze_liftE {ε α : Type} {m : NonDet (State Unit) α} (hm : NKZ m) : NKZE (NonDetE.liftE (ε := ε) m) := by
  unfold NKZE NonDetE.liftE; rw [ExceptT.run_lift]
  exact nkz_bind hm (fun _ => nkz_pure _)

theorem nkze_throw {ε α : Type} (e : ε) : NKZE (NonDetE.throwError e : NonDetE (State Unit) ε α) := nkz_pure _
theorem nkze_pure {ε α : Type} (a : α) : NKZE (pure a : NonDetE (State Unit) ε α) := nkz_pure _
theorem nkze_returnOk {ε α : Type} (a : α) : NKZE (NonDetE.returnOk a : NonDetE (State Unit) ε α) := nkz_pure _

theorem nkze_ite {ε α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : NKZE m1)
    (h2 : NKZE m2) : NKZE (if P then m1 else m2) := by split <;> assumption

theorem nkze_whenE {ε : Type} (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : NKZE m) :
    NKZE (NonDetE.whenE P m) := by unfold NonDetE.whenE; split; exact h; exact nkze_pure _

theorem nkze_orChoiceE {ε α : Type} (c : DetExtMonad Bool) {f g : NonDetE (State Unit) ε α} (hf : NKZE f)
    (hg : NKZE g) : NKZE (orChoiceE c f g) := by
  unfold orChoiceE
  refine nkze_bind (nkze_liftE nkz_get) (fun _ => nkze_bind (nkze_liftE (nkz_selectF _)) (fun x => ?_))
  obtain ⟨rv, _⟩ := x
  exact nkze_ite _ hf hg

theorem nkz_updateTimeStamp : NKZ (updateTimeStamp (Z := Unit)) := by
  unfold updateTimeStamp NonDet.when
  nkz_auto

theorem nkze_preemptionPoint : NKZE (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint
  refine nkze_bind (nkze_liftE (nkz_doExtendedOp _)) (fun _ => nkze_orChoiceE _ ?_ (nkze_returnOk _))
  refine nkze_bind (nkze_liftE (nkz_doExtendedOp _)) (fun _ => ?_)
  refine nkze_bind (nkze_liftE nkz_updateTimeStamp) (fun _ => ?_)
  refine nkze_bind (nkze_liftE (nkz_doMachineOp _)) (fun _ => ?_)
  refine nkze_bind (nkze_liftE (nkz_gets _)) (fun _ => ?_)
  refine nkze_bind (nkze_liftE (nkz_gets _)) (fun _ => ?_)
  refine nkze_bind (nkze_liftE (nkz_gets _)) (fun _ => ?_)
  refine nkze_bind (nkze_liftE (nkz_getsThe _)) (fun _ => ?_)
  refine nkze_bind (nkze_liftE (nkz_gets _)) (fun _ => ?_)
  exact nkze_whenE _ (nkze_throw _)

end

/-! ## `SpecFree`'s frame -/

section

/-- **`SpecFree` across a step that keeps the objects' types** (`KSz`) and
whose untyped caps each have one before over the same region with a free
index no larger. -/
theorem SpecFree.frame {m m' : U64 → U64} {G G' : MdbGhost} {σ σ' : State Unit}
    (h : Sched.SpecFree m G σ)
    (hu : ∀ x' ∈ G'.chains.flatten, ∀ p sb fi' d, capV m' x' = .Untyped p sb fi' d →
      ∃ x ∈ G.chains.flatten, ∃ fi d0, capV m x = .Untyped p sb fi d0 ∧ fi.val ≤ fi'.val)
    (hk : KSz σ σ') : Sched.SpecFree m' G' σ' := by
  intro x' hx' p sb fi' d hc o ko' ho
  obtain ⟨x, hx, fi, d0, hc0, hfi⟩ := hu x' hx' p sb fi' d hc
  obtain ⟨ko, hko, hty⟩ := hk o ko' ho
  rw [← objBits_of_aType hty]
  rcases h x hx p sb fi d0 hc0 o ko hko with e | e
  · exact Or.inl e
  · right; omega

end

end Fl4Proofs.P3
