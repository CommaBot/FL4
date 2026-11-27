/-
P3 (line p3J, gen 25): **the SC-period frame** (spec side only; outside the `JAtZ` cone), a scripted copy of gen 21's
heap-type frame P3JKtF (`scratch/p3J/genRr.py`: `KQ` ↦ `RQ`, `ktV` ↦ `rpV`).

* `rpV σ o`: the period of the SC at `o` (`0` at every other object and at a free address). `RQ m := FK rpV m`.
* `set_object` checks only the `a_type`, so it does not keep `rpV` by itself. Leaves instead:
  `rq_setObject_nsc` (the new object's `a_type` is neither an SC's nor a garbage one: then neither is the old
  object's, both periods read `0`; every literal TCB / endpoint / notification / reply / arch-object write),
  `rq_setCap` (the CNode / TCB slot write), `rq_setSimpleKo'` (endpoint / notification / reply),
  `rq_updateSchedContext'` (an SC update `f` with `(f sc).scPeriod = sc.scPeriod`: every SC update of the spec but
  `refill_new` / `refill_update`'s `sc_period_update`, reached only from `SchedControl_Configure`).

Named premises: none. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.VsDom
import Fl4Spec.Ext.Entry
open Classical

namespace Fl4Proofs.P3.SInvRr
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

/-- The period of an SC object (`0` for every other object). -/
def pv1 (k : KernelObject) : Ticks :=
  match k with
  | .schedContext sc _ => sc.scPeriod
  | _ => 0

/-- The period of the SC at every address (`0` where there is no SC). -/
def rpV (σ : State Unit) : ObjRef → Ticks := fun o =>
  match σ.kheap o with
  | some k => pv1 k
  | none => 0

/-- Every outcome of `m` keeps the period of every SC. -/
abbrev RQ {α : Type} (m : NonDet (State Unit) α) : Prop := FK rpV m

/-- `RQ` for the exception monad. -/
abbrev RQE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := FKE rpV m

open Lean Meta Elab Tactic in
/-- Unfold the spec function at the head of an `FK`/`FKE` goal (sch12's
`fv_unfold`). -/
elab "zq_sf_unfold" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let args := t.getAppArgs
  if args.size == 0 then throwError "zq_sf_unfold: no arguments"
  let m := args.back!
  let m := if m.isAppOf ``ExceptT.run then m.getAppArgs.back! else m
  match m.getAppFn with
  | .const n _ =>
    if (`Fl4Spec).isPrefixOf n && !(`Fl4Spec.NonDet).isPrefixOf n && !(`Fl4Spec.NonDetE).isPrefixOf n then
      evalTactic (← `(tactic| unfold $(mkIdent n):ident))
    else throwError "zq_sf_unfold: {n} is not a spec function"
  | _ => throwError "zq_sf_unfold: no head constant"

/-- A `RQ` lemma of a spec function (extended below, one rule per lemma). -/
syntax "zq_leaf" : tactic
macro_rules | `(tactic| zq_leaf) => `(tactic| fail "no zq_leaf")

macro "zq_auto" : tactic => `(tactic| repeat' (first | zq_leaf | dk_step0 | zq_sf_unfold))

/-- `zq_auto` without unfolding (for the scripted copies of the `DK` lemmas). -/
macro "zq_auto0" : tactic => `(tactic| repeat' (first | zq_leaf | dk_step0))

/-! ## Leaves -/

theorem rq_doMachineOp {α : Type} (mop : NonDet MachineState α) : RQ (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_doMachineOp _)

theorem rq_doExtendedOp (eop : DetExtMonad Unit) : RQ (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_doExtendedOp _)

theorem rq_getCap (sl : CslotPtr) : RQ (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; dsimp only
  repeat' dk_step0
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getCap _)

theorem rqe_rab (p : Cap × CapRef) : RQE (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact dke_liftE (dk_fail)
    · refine dke_bind (dke_whenE _ (dke_throw _)) fun _ => dke_bind (dke_whenE _ (dke_throw _)) fun _ =>
        dke_bind (dke_returnOk _) fun _ => ?_
      dsimp only
      split
      · exact dke_returnOk _
      · refine dke_bind (dke_liftE (rq_getCap _)) fun nc => ?_
        split
        · exact rqe_rab _
        · exact dke_returnOk _
  · exact dke_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_rab _)

theorem rq_zipWithMx {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, RQ (g a b)) :
    ∀ l1 l2, RQ (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => dk_bind (h a b) (fun _ => rq_zipWithMx h l1 l2)
  | [], _ => dk_pure' _
  | _ :: _, [] => dk_pure' _
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible refine rq_zipWithMx (fun _ _ => ?_) _ _)

set_option maxRecDepth 20000

/-- An `a_type` that is neither an SC's nor a garbage one. -/
def NoScT (t : AType) : Prop := (∀ n, t ≠ .aSchedContext n) ∧ ∀ n, t ≠ .aGarbage n

theorem pv1_zero_of_noScT {k : KernelObject} (h : NoScT (aType k)) : pv1 k = 0 := by
  cases k with
  | schedContext sc n =>
    exfalso
    by_cases hv : validSchedContextSize n
    · exact h.1 n (by simp only [aType, if_pos hv])
    · exact h.2 (minSchedContextBits + n) (by simp only [aType, if_neg hv])
  | _ => rfl

theorem noScT_simple {k : KernelObject}
    (h : aType k ∈ ({.aEndpoint, .aNTFN, .aReply} : Set AType)) : NoScT (aType k) := by
  refine ⟨fun n e => ?_, fun n e => ?_⟩ <;> rw [e] at h <;> simp at h

theorem getObject_out {p : ObjRef} {σ : State Unit} {y : KernelObject × State Unit}
    (hy : y ∈ (getObject (Z := Unit) p σ).1) : ∃ k, σ.kheap p = some k ∧ y = (k, σ) := by
  unfold getObject NonDet.getsThe readObject at hy
  cases h : σ.kheap p with
  | none => rw [h] at hy; exact hy.elim
  | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩

theorem setObject_out {p : ObjRef} {o : KernelObject} {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (setObject (Z := Unit) p o σ).1) :
    ∃ k, σ.kheap p = some k ∧ aType k = aType o ∧
      x.2 = { σ with kheap := Function.update σ.kheap p (some o) } := by
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨k, hk, rfl⟩ := getObject_out hy
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨hty, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ⟨k, hk, hty, rfl⟩

theorem rpV_update {σ : State Unit} {p : ObjRef} {o k : KernelObject} (hk : σ.kheap p = some k)
    (h : pv1 o = pv1 k) : rpV { σ with kheap := Function.update σ.kheap p (some o) } = rpV σ := by
  funext q
  unfold rpV
  by_cases e : q = p
  · subst e; simp [Function.update_self, hk, h]
  · simp only [Function.update_of_ne e]

/-- `set_object` of an object whose `a_type` is neither an SC's nor garbage. -/
theorem rq_setObject_nsc (p : ObjRef) (o : KernelObject) (ho : NoScT (aType o)) :
    RQ (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨k, hk, hty, e⟩ := setObject_out hx
  rw [e]
  exact rpV_update hk (by rw [pv1_zero_of_noScT ho, pv1_zero_of_noScT (by rw [hty]; exact ho)])
/-- Discharge `NoScT (aType o)` for a literal non-SC, non-CNode object. -/
macro "noScT_lit" : tactic =>
  `(tactic| (refine ⟨fun _ h => ?_, fun _ h => ?_⟩ <;> first | cases h | (simp [aType] at h; done)))
macro_rules | `(tactic| zq_leaf) => `(tactic| ((with_reducible refine rq_setObject_nsc _ _ ?_) <;> noScT_lit))

/-- `update_sched_context` with an update that keeps the period. -/
theorem rq_updateSchedContext' (q : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ sc, (f sc).scPeriod = sc.scPeriod) : RQ (updateSchedContext (Z := Unit) q f) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨k, hk, rfl⟩ := getObject_out hy
  cases k with
  | schedContext sc n =>
    have hx' : x ∈ (setObject (Z := Unit) q (.schedContext (f sc) n) σ).1 := hx
    obtain ⟨-, -, -, e⟩ := setObject_out hx'
    rw [e]
    exact rpV_update hk (hf sc)
  | _ => exact False.elim hx
macro_rules | `(tactic| zq_leaf) => `(tactic| ((with_reducible refine rq_updateSchedContext' _ _ ?_) <;>
  (intro _; rfl)))

theorem rq_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    RQ (setSimpleKo (Z := Unit) C q e) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨k, hk, rfl⟩ := getObject_out hy
  obtain ⟨z1, ⟨hs, rfl⟩, hx⟩ := hx
  obtain ⟨z2, ⟨-, rfl⟩, hx⟩ := hx
  have hx' : x ∈ (setObject (Z := Unit) q (C e) σ).1 := hx
  obtain ⟨k2, hk2, hty, e2⟩ := setObject_out hx'
  have ek : k2 = k := Option.some.inj (hk2.symm.trans hk)
  rw [ek] at hty
  rw [e2]
  have hs' : NoScT (aType k) := noScT_simple hs
  exact rpV_update hk (by rw [pv1_zero_of_noScT hs', pv1_zero_of_noScT (by rw [← hty]; exact hs')])
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setSimpleKo' _ _ _)

theorem rq_setCap (c : Cap) (sl : CslotPtr) : RQ (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨k, hk, rfl⟩ := getObject_out hy
  have key : ∀ k' : KernelObject, pv1 k' = 0 → pv1 k = 0 → x ∈ (setObject (Z := Unit) o k' σ).1 →
      rpV x.2 = rpV σ := by
    intro k' h1 h2 hx'
    obtain ⟨-, -, -, e⟩ := setObject_out hx'
    rw [e]
    exact rpV_update hk (by rw [h1, h2])
  cases k <;> (try simp only at hx) <;> (repeat' split at hx) <;> first
    | exact False.elim hx
    | (obtain ⟨z, hz, -⟩ := hx; exact False.elim hz)
    | (obtain ⟨z, hz, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hz; exact key _ rfl rfl hx)
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setCap _ _)

/-- A bind on a returned value (so that the continuation sees the value). -/
theorem rqe_returnOk_bind {ε α β : Type} {v : α} {g : α → NonDetE (State Unit) ε β} (h : RQE (g v)) :
    RQE (NonDetE.returnOk v >>= g) := by
  show FK rpV (ExceptT.run (NonDetE.returnOk v >>= g))
  rw [ExceptT.run_bind]
  intro σ x ⟨y, hy, hx⟩
  obtain rfl := Set.mem_singleton_iff.1 hy
  exact h σ x hx
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible refine rqe_returnOk_bind ?_)

end

end Fl4Proofs.P3.SInvRr
