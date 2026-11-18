/-
P3 (DESIGN.md §9), scheduling contexts: **the SC invocations keep the
current SC and the idle thread** (`FK`), for `JKern`'s current-SC fields
after an SC step.

* `FK σ σ'`: `curSc` and `idleThread` kept; `FKA m`: every outcome of `m`.
* The combinators and leaves (`setObject`, `modify` of the other fields),
  the `fk_step` tactic, and the operations: `fk_setThreadState`,
  `fk_invokeSchedControlConfigureFlags`, `fk_invokeSchedContext` (Bind,
  UnbindObject, a YieldTo from an SC yielded to by none).
-/
import Fl4Proofs.P3.ScXProd
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

/-- The current SC, the idle thread and the idle SC kept. -/
def FK (σ σ' : State Unit) : Prop :=
  σ'.curSc = σ.curSc ∧ σ'.idleThread = σ.idleThread ∧ σ'.idleSc = σ.idleSc

theorem FK.refl (σ : State Unit) : FK σ σ := ⟨rfl, rfl, rfl⟩

theorem FK.trans {σ1 σ2 σ3 : State Unit} (h1 : FK σ1 σ2) (h2 : FK σ2 σ3) : FK σ1 σ3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

/-- Every outcome keeps the current SC and the idle thread. -/
def FKA {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → FK σ x.2

theorem FKA.of_eq {α : Type} {m : NonDet (State Unit) α} (hP : FKA m) {σ σ' : State Unit} {a : α} {X : Prop}
    (h : m σ = ({(a, σ')}, X)) : FK σ σ' :=
  hP σ (a, σ') (by rw [h]; exact Set.mem_singleton _)

section Comb

theorem fk_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : FKA m)
    (hg : ∀ a, FKA (g a)) : FKA (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem fk_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : FKA m)
    (hg : ∀ a, FKA (g a)) : FKA (NonDet.bind m g) := fk_bind hm hg

theorem fk_same {α : Type} {m : NonDet (State Unit) α} (h : ∀ σ x, x ∈ (m σ).1 → x.2 = σ) : FKA m := by
  intro σ x hx; rw [h σ x hx]; exact FK.refl σ

theorem fk_pure {α : Type} (a : α) : FKA (pure a : NonDet (State Unit) α) :=
  fk_same fun _ x hx => by rw [Set.mem_singleton_iff.1 hx]

theorem fk_pure' {α : Type} (a : α) : FKA (NonDet.pure a : NonDet (State Unit) α) := fk_pure a

theorem fk_gets {α : Type} (g : State Unit → α) : FKA (NonDet.gets g) :=
  fk_same fun _ x hx => by rw [Set.mem_singleton_iff.1 hx]

theorem fk_get : FKA (NonDet.get : NonDet (State Unit) (State Unit)) :=
  fk_same fun _ x hx => by rw [Set.mem_singleton_iff.1 hx]

theorem fk_assert (P : Prop) : FKA (NonDet.assert P : NonDet (State Unit) Unit) :=
  fk_same fun _ x hx => by obtain ⟨-, rfl⟩ := hx; rfl

theorem fk_fail {α : Type} : FKA (NonDet.fail : NonDet (State Unit) α) := fun _ _ hx => hx.elim

theorem fk_assertOpt {α : Type} (o : Option α) : FKA (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact fk_fail
  · exact fk_pure' _

theorem fk_getsThe {α : Type} (g : State Unit → Option α) : FKA (NonDet.getsThe g) := by
  intro σ x hx; exact fk_assertOpt (g σ) σ x hx

theorem fk_selectF {α : Type} (S : Set α × Prop) : FKA (NonDet.selectF S : NonDet (State Unit) α) :=
  fk_same fun _ x hx => by obtain ⟨-, h⟩ := hx; exact h

theorem fk_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : FKA m1)
    (h2 : FKA m2) : FKA (if P then m1 else m2) := by
  split <;> assumption

theorem fk_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : FKA m) : FKA (NonDet.when P m) := by
  unfold NonDet.when; exact fk_ite P h (fk_pure' _)

theorem fk_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : FKA m) :
    FKA (NonDet.unless P m) := by
  unfold NonDet.unless; exact fk_ite P (fk_pure' _) h

theorem fk_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, FKA (g a)) (o : Option α) :
    FKA (NonDet.maybeM g o) := by
  cases o
  · exact fk_pure' _
  · exact h _

theorem fk_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : FKA m) : FKA (NonDet.liftM g m) :=
  fk_bind' h fun _ => fk_pure' _

theorem fk_modify {g : State Unit → State Unit} (hg : ∀ σ, FK σ (g σ)) : FKA (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hg σ

theorem fk_get_put {g : State Unit → State Unit} (hg : ∀ σ, FK σ (g σ)) :
    FKA (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hg σ

theorem fk_getObject (p : ObjRef) : FKA (getObject (Z := Unit) p) := fk_getsThe _

theorem fk_setObject (p : ObjRef) (o : KernelObject) : FKA (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨k, -, -, e⟩ := setObject_mem hx
  rw [e]; exact ⟨rfl, rfl, rfl⟩

theorem fk_doExtendedOp (eop : DetExtMonad Unit) : FKA (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine fk_bind fk_get (fun _ => fk_bind (fk_selectF _) (fun _ => ?_))
  split
  exact fk_modify (fun σ => ⟨rfl, rfl, rfl⟩)

theorem fk_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, FKA (B r)) (r : α) : FKA (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => exact FK.refl _
  | step _ hm _ ih => exact (hB _ _ _ hm).trans ih

theorem fk_mapMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, FKA (g a)) (xs : List α) :
    FKA (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact fk_pure' _
  | cons a xs' ih => exact fk_bind' (h a) fun _ => ih

theorem fk_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, FKA (g a)) (xs : List α) :
    FKA (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact fk_pure' _
  | cons a xs' ih => exact fk_bind' (h a) fun _ => fk_bind' ih fun _ => fk_pure' _

end Comb

macro "fk_step0" : tactic => `(tactic| first
  | with_reducible exact fk_pure _ | with_reducible exact fk_pure' _ | with_reducible exact fk_fail
  | with_reducible exact fk_gets _ | with_reducible exact fk_get
  | with_reducible exact fk_assert _ | with_reducible exact fk_assertOpt _
  | with_reducible exact fk_getObject _ | with_reducible exact fk_getsThe _
  | with_reducible exact fk_selectF _ | with_reducible exact fk_setObject _ _
  | ((with_reducible apply fk_modify); intro _; exact ⟨rfl, rfl, rfl⟩)
  | ((with_reducible apply fk_get_put); intro _; exact ⟨rfl, rfl, rfl⟩)
  | with_reducible exact fk_doExtendedOp _
  | (with_reducible refine fk_bind ?_ (fun _ => ?_))
  | (with_reducible refine fk_bind' ?_ (fun _ => ?_))
  | (with_reducible apply fk_ite) | (with_reducible apply fk_when) | (with_reducible apply fk_unless)
  | (with_reducible refine fk_maybeM (fun _ => ?_) _) | (with_reducible apply fk_liftM)
  | (with_reducible refine fk_whileLoop (fun _ => ?_) _)
  | (with_reducible refine fk_mapMx (fun _ => ?_) _)
  | (with_reducible refine fk_mapM (fun _ => ?_) _)
  | split
  | (dsimp only))

section Ops

theorem fk_threadSet (g : Tcb → Tcb) (p : ObjRef) : FKA (threadSet (Z := Unit) g p) := by
  unfold threadSet; repeat fk_step0

theorem fk_threadGet {α : Type} (g : Tcb → α) (p : ObjRef) : FKA (threadGet (Z := Unit) g p) := by
  unfold threadGet; repeat fk_step0

theorem fk_getSchedContext (p : ObjRef) : FKA (getSchedContext (Z := Unit) p) := by
  unfold getSchedContext; repeat fk_step0

theorem fk_updateSchedContext (p : ObjRef) (g : SchedContext → SchedContext) :
    FKA (updateSchedContext (Z := Unit) p g) := by
  unfold updateSchedContext; repeat fk_step0

theorem fk_getSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (p : ObjRef) :
    FKA (getSimpleKo (Z := Unit) C p) := by
  unfold getSimpleKo; repeat fk_step0

theorem fk_setSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (p : ObjRef) (e : α) :
    FKA (setSimpleKo (Z := Unit) C p e) := by
  unfold setSimpleKo; repeat fk_step0

theorem fk_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject)
    (g : (Option ObjRef → Option ObjRef) → α → α) (p : ObjRef) (new : Option ObjRef) :
    FKA (updateSkObjRef (Z := Unit) C g p new) := by
  unfold updateSkObjRef
  exact fk_bind (fk_getSimpleKo _ _) fun _ => fk_setSimpleKo _ _ _

end Ops

macro "fk_step" : tactic => `(tactic| first
  | with_reducible exact fk_threadGet _ _ | with_reducible exact fk_threadSet _ _
  | with_reducible exact fk_getSchedContext _ | with_reducible exact fk_updateSchedContext _ _
  | with_reducible exact fk_getSimpleKo _ _ | with_reducible exact fk_setSimpleKo _ _ _
  | with_reducible exact fk_updateSkObjRef _ _ _ _
  | fk_step0)

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

macro "fk_unf" : tactic => `(tactic| first
  | unfold getScObjRef | unfold tcbSchedAction | unfold getTcbQueue | unfold setTcbQueue
  | unfold rescheduleRequired | unfold setSchedulerAction | unfold getScRefillSufficient | unfold getScRefillReady
  | unfold tcbReleaseRemove | unfold setReleaseQueue | unfold tcbReleaseEnqueue | unfold readyTimesAppend
  | unfold orderedInsert | unfold postpone | unfold schedContextResume | unfold refillUnblockCheck
  | unfold isRoundRobin | unfold refillHeadOverlappingLoop | unfold mergeOverlappingRefills | unfold refillPopHead
  | unfold updateRefillHd | unfold getRefillHead | unfold ifCondRefillUnblockCheck | unfold schedContextBindTcb
  | unfold schedContextBindNtfn | unfold commitTime | unfold refillBudgetCheckRoundRobin | unfold refillBudgetCheck
  | unfold updateRefillTl | unfold refillAddTail | unfold getRefills | unfold getRefillTail | unfold refillFull
  | unfold refillSingle | unfold refillSize | unfold scheduleUsed | unfold chargeEntireHeadRefill
  | unfold handleOverrun | unfold headInsufficientLoop | unfold mergeNonoverlappingHeadRefill | unfold getScActive
  | unfold maybeAddEmptyTail | unfold refillNew | unfold refillUpdate | unfold possibleSwitchTo
  | unfold getTcbObjRef | unfold getThreadState | unfold schedContextUnbindTcb | unfold schedContextUnbindNtfn
  | unfold returnConsumed | unfold schedContextUpdateConsumed | unfold setThreadStateAct | unfold scheduleTcb
  | unfold getSkObjRef | unfold getScReleased | unfold getNtfnObjRef | unfold getReplyObjRef)

macro "fk_auto" : tactic => `(tactic| repeat (first | fk_step | fk_unf))

theorem fk_setThreadState (t : ObjRef) (ts : ThreadState) : FKA (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState; fk_auto

theorem fk_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) :
    FKA (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags; fk_auto


macro "fk_unf2" : tactic => `(tactic| first
  | unfold schedContextYieldTo | unfold ifSporadicActiveCurScTestRefillUnblockCheck
  | unfold ifSporadicCurScAssertRefillUnblockCheck | unfold completeYieldTo | unfold setConsumed
  | unfold schedContextCancelYieldTo | unfold setThreadState | unfold tcbSchedEnqueue | unfold tcbSchedAppend
  | unfold tcbSchedDequeue | unfold schedContextUnbindAllTcbs | unfold schedContextUnbindReply
  | unfold schedContextUnbindYieldFrom | unfold setTcbObjRef | unfold setScObjRef | unfold setReplyObjRef
  | unfold setNtfnObjRef)

theorem fk_schedContextYieldTo {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (hyf : x.scYieldFrom = none) :
    ∀ y ∈ (schedContextYieldTo (Z := Unit) p σ).1, FK σ y.2 := by
  intro y hy
  unfold schedContextYieldTo at hy
  rw [nd_bind_one (getScObjRef_eq hk _), hyf] at hy
  refine (show FKA _ from ?_) σ y hy
  refine fk_bind ?_ fun _ => ?_
  · unfold NonDet.when; simp only [ne_eq, not_true_eq_false, ↓reduceIte]; exact fk_pure' _
  repeat (any_goals (first | fk_step | fk_unf | fk_unf2))

/-- **Bind, UnbindObject and a YieldTo from an SC yielded to by none keep
the current SC and the idle thread** (the shapes of `tk_invokeSchedContext`). -/
theorem fk_invokeSchedContext {σ : State Unit} {inv : SchedContextInvocation}
    (h : (∃ sc cap, inv = .invokeSchedContextBind sc cap) ∨ (∃ sc cap, inv = .invokeSchedContextUnbindObject sc cap) ∨
      (∃ sc x n, inv = .invokeSchedContextYieldTo sc ∧ σ.kheap sc = some (.schedContext x n) ∧ x.scYieldFrom = none)) :
    ∀ y ∈ (invokeSchedContext (Z := Unit) inv σ).1, FK σ y.2 := by
  rcases h with ⟨sc, cap, rfl⟩ | ⟨sc, cap, rfl⟩ | ⟨sc, x, n, rfl, hk, hyf⟩
  · refine (show FKA (invokeSchedContext (Z := Unit) (.invokeSchedContextBind sc cap)) from ?_) σ
    simp only [invokeSchedContext]
    repeat (any_goals (first | fk_step | fk_unf | fk_unf2))
  · refine (show FKA (invokeSchedContext (Z := Unit) (.invokeSchedContextUnbindObject sc cap)) from ?_) σ
    simp only [invokeSchedContext]
    repeat (any_goals (first | fk_step | fk_unf | fk_unf2))
  · exact fk_schedContextYieldTo hk hyf

end

end Fl4Proofs.P3.Sched
