/-
P3 (DESIGN.md §9), IPC: **a backward release-queue frame for the spec's
reply path** (spec side only), as ScMaxKeep's `RQ`.

`RQK σ σ'`: every member of `σ'`'s release queue was one of `σ`'s. `RQ m`:
every outcome of `m` is `RQK`-related to its start (`rq_auto`); up to
`do_ipc_transfer`, `handle_fault_reply`, `set_thread_state` and the sporadic
unblock check (`rq_doIpcTransfer'`, `rq_unblock`).

Used by the reply tail: the receiver, not released after `reply_remove`
(it is inactive there, `not_released_of`), is not released at `postpone`.
-/
import Fl4Spec.Ext.Invocation
import Fl4Spec.Ext.VSpace
open Classical

namespace Fl4Proofs.P3.RelQ
open Fl4Spec

noncomputable section

/-- Every member of `σ'`'s release queue was one of `σ`'s. -/
def RQK (σ σ' : State Unit) : Prop := ∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue

theorem RQK.refl (σ : State Unit) : RQK σ σ := fun _ h => h

theorem RQK.trans {σ1 σ2 σ3 : State Unit} (h1 : RQK σ1 σ2) (h2 : RQK σ2 σ3) : RQK σ1 σ3 :=
  fun u h => h1 u (h2 u h)

theorem RQK.of_eq {σ σ' : State Unit} (h : σ'.releaseQueue = σ.releaseQueue) : RQK σ σ' := by
  intro u hu; rw [h] at hu; exact hu

/-- Every outcome of `m` keeps the release queue (backward). -/
def RQ {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → RQK σ x.2

section Comb

theorem rq_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : RQ m)
    (hg : ∀ a, RQ (g a)) : RQ (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem rq_bind_pure {α β : Type} {a : α} {g : α → NonDet (State Unit) β} (h : RQ (g a)) :
    RQ ((pure a : NonDet (State Unit) α) >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ x hx

theorem rq_fail_bind {α β : Type} {g : α → NonDet (State Unit) β} :
    RQ ((NonDet.fail : NonDet (State Unit) α) >>= g) := by
  intro σ x ⟨y, hy, _⟩
  exact hy.elim

theorem rq_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : RQ m)
    (hg : ∀ a, RQ (g a)) : RQ (NonDet.bind m g) := rq_bind hm hg

theorem rq_pure {α : Type} (a : α) : RQ (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact RQK.refl _

theorem rq_pure' {α : Type} (a : α) : RQ (NonDet.pure a : NonDet (State Unit) α) := rq_pure a

theorem rq_gets {α : Type} (g : State Unit → α) : RQ (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact RQK.refl _

theorem rq_get : RQ (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact RQK.refl _

theorem rq_assert (P : Prop) : RQ (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact RQK.refl _

theorem rq_fail {α : Type} : RQ (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem rq_assertOpt {α : Type} (o : Option α) : RQ (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact rq_fail
  · exact rq_pure' _

theorem rq_getsThe {α : Type} (g : State Unit → Option α) : RQ (NonDet.getsThe g) := by
  intro σ x hx; exact rq_assertOpt (g σ) σ x hx

theorem rq_selectF {α : Type} (S : Set α × Prop) : RQ (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact RQK.refl _

theorem rq_select {α : Type} (S : Set α) : RQ (NonDet.select S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact RQK.refl _

theorem rq_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : RQ m1)
    (h2 : RQ m2) : RQ (if P then m1 else m2) := by
  split <;> assumption

theorem rq_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : RQ m) :
    RQ (NonDet.when P m) := by
  unfold NonDet.when; exact rq_ite P h (rq_pure' _)

theorem rq_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : RQ m) :
    RQ (NonDet.unless P m) := by
  unfold NonDet.unless; exact rq_ite P (rq_pure' _) h

theorem rq_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, RQ (g a)) (o : Option α) :
    RQ (NonDet.maybeM g o) := by
  cases o
  · exact rq_pure' _
  · exact h _

theorem rq_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : RQ m) :
    RQ (NonDet.liftM g m) := rq_bind' h fun _ => rq_pure' _

theorem rq_modify {g : State Unit → State Unit} (hg : ∀ σ, (g σ).releaseQueue = σ.releaseQueue) :
    RQ (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact RQK.of_eq (hg σ)

theorem rq_get_put {g : State Unit → State Unit} (hg : ∀ σ, (g σ).releaseQueue = σ.releaseQueue) :
    RQ (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact RQK.of_eq (hg σ)

theorem rq_get_put' {g : State Unit → State Unit} (hg : ∀ σ, (g σ).releaseQueue = σ.releaseQueue) :
    RQ (do let s ← NonDet.get; NonDet.put (g s)) := rq_get_put hg

theorem rq_getObject (p : ObjRef) : RQ (getObject (Z := Unit) p) := rq_getsThe _

theorem rq_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, RQ (B r)) (r : α) : RQ (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => exact RQK.refl _
  | step _ hm _ ih => exact (hB _ _ _ hm).trans ih

theorem rq_mapMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, RQ (g a)) (xs : List α) :
    RQ (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact rq_pure' _
  | cons a xs' ih => exact rq_bind' (h a) fun _ => ih

theorem rq_forMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, RQ (g a)) (xs : List α) :
    RQ (NonDet.forMx xs g) := rq_mapMx h xs

theorem rq_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, RQ (g a)) (xs : List α) :
    RQ (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact rq_pure' _
  | cons a xs' ih => exact rq_bind' (h a) fun _ => rq_bind' ih fun _ => rq_pure' _

theorem rq_doMachineOp {α : Type} (mop : NonDet MachineState α) : RQ (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine rq_bind (rq_gets _) (fun _ => rq_bind (rq_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact rq_bind (rq_modify (fun σ => rfl)) (fun _ => rq_pure _)

theorem rq_doExtendedOp (eop : DetExtMonad Unit) : RQ (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine rq_bind rq_get (fun _ => rq_bind (rq_selectF _) (fun _ => ?_))
  split
  exact rq_modify (fun σ => rfl)

end Comb

/-- `RQ` for the exception monad. -/
def RQE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := RQ (ExceptT.run m)

section CombE
variable {ε : Type}

theorem rqe_bind {α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β} (hm : RQE m)
    (hg : ∀ a, RQE (g a)) : RQE (m >>= g) := by
  unfold RQE; rw [ExceptT.run_bind]
  refine rq_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact rq_pure _

theorem rqe_pure {α : Type} (a : α) : RQE (pure a : NonDetE (State Unit) ε α) := rq_pure _

theorem rqe_returnOk {α : Type} (a : α) : RQE (NonDetE.returnOk a : NonDetE (State Unit) ε α) := rq_pure _

theorem rqe_throw {α : Type} (e : ε) : RQE (NonDetE.throwError e : NonDetE (State Unit) ε α) := rq_pure _

theorem rqe_throw' {α : Type} (e : ε) : RQE (throw e : NonDetE (State Unit) ε α) := rq_pure _

theorem rqe_liftE {α : Type} {m : NonDet (State Unit) α} (h : RQ m) : RQE (NonDetE.liftE (ε := ε) m) := by
  unfold RQE NonDetE.liftE; rw [ExceptT.run_lift]
  exact rq_bind h fun _ => rq_pure _

theorem rqe_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : RQE m1)
    (h2 : RQE m2) : RQE (if P then m1 else m2) := by
  split <;> assumption

theorem rqe_whenE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : RQE m) :
    RQE (NonDetE.whenE P m) := by
  unfold NonDetE.whenE; exact rqe_ite P h (rqe_pure _)

theorem rqe_unlessE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : RQE m) :
    RQE (NonDetE.unlessE P m) := by
  unfold NonDetE.unlessE; exact rqe_ite P (rqe_pure _) h

theorem rqe_throwOpt {α : Type} (e : ε) (o : Option α) : RQE (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact rqe_throw' e
  · exact rqe_pure _

theorem rqe_assertE (P : Prop) : RQE (NonDetE.assertE P : NonDetE (State Unit) ε Unit) :=
  rqe_liftE (rq_assert P)

theorem rq_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : RQE m)
    (hh : ∀ e, RQ (h e)) : RQ (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine rq_bind' hm fun r => ?_
  cases r with
  | ok a => exact rq_pure' _
  | error e => exact hh e

theorem rqe_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : RQE m) (hh : ∀ e, RQE (h e)) : RQE (NonDetE.handleE m h) := by
  unfold NonDetE.handleE RQE
  rw [ExceptT.run_mk]
  refine rq_bind' hm fun r => ?_
  cases r with
  | ok a => exact rq_pure' _
  | error e => exact hh e

theorem rqe_liftME {α β : Type} (f : α → β) {m : NonDetE (State Unit) ε α} (h : RQE m) :
    RQE (NonDetE.liftME f m) := by
  unfold NonDetE.liftME; exact rqe_bind h fun _ => rqe_pure _

theorem rqe_mapMEx {α β : Type} {f : α → NonDetE (State Unit) ε β} (h : ∀ a, RQE (f a)) :
    ∀ xs : List α, RQE (NonDetE.mapMEx f xs)
  | [] => by unfold NonDetE.mapMEx; exact rqe_pure _
  | a :: as => by unfold NonDetE.mapMEx; exact rqe_bind (h a) fun _ => rqe_mapMEx h as

theorem rqe_mapME {α β : Type} {f : α → NonDetE (State Unit) ε β} (h : ∀ a, RQE (f a)) :
    ∀ xs : List α, RQE (NonDetE.mapME f xs)
  | [] => by unfold NonDetE.mapME; exact rqe_pure _
  | a :: as => by
    unfold NonDetE.mapME; exact rqe_bind (h a) fun _ => rqe_bind (rqe_mapME h as) fun _ => rqe_pure _

end CombE

theorem not_sc_tcb (x : Tcb) : ∀ y n, KernelObject.tcb x ≠ .schedContext y n := fun _ _ h => by cases h
theorem not_sc_cnode (r : Nat) (c : CnodeContents) : ∀ y n, KernelObject.cnode r c ≠ .schedContext y n :=
  fun _ _ h => by cases h
theorem not_sc_ep (x : Endpoint) : ∀ y n, KernelObject.endpoint x ≠ .schedContext y n := fun _ _ h => by cases h
theorem not_sc_ntfn (x : Notification) : ∀ y n, KernelObject.notification x ≠ .schedContext y n :=
  fun _ _ h => by cases h
theorem not_sc_reply (x : Reply) : ∀ y n, KernelObject.reply x ≠ .schedContext y n := fun _ _ h => by cases h
theorem not_sc_arch (x : ArchKernelObj) : ∀ y n, KernelObject.archObj x ≠ .schedContext y n :=
  fun _ _ h => by cases h

/-- One step of an `RQ` proof. -/
macro "rq_step0" : tactic => `(tactic| first
  | with_reducible exact rq_pure _ | with_reducible exact rq_pure' _ | with_reducible exact rq_fail
  | with_reducible exact rq_gets _ | with_reducible exact rq_get
  | with_reducible exact rq_assert _ | with_reducible exact rq_assertOpt _
  | with_reducible exact rq_getsThe _
  | with_reducible exact rq_selectF _ | with_reducible exact rq_select _
  | ((with_reducible apply rq_modify); intro _; rfl)
  | ((with_reducible apply rq_get_put); intro _; rfl)
  | (exact rq_get_put' (fun _ => rfl))
  | (exact rq_get_put (fun _ => rfl))
  | with_reducible exact rq_getObject _
  | with_reducible exact rq_doMachineOp _ | with_reducible exact rq_doExtendedOp _
  | (with_reducible refine rq_bind_pure ?_) | (with_reducible exact rq_fail_bind)
  | (with_reducible refine rq_bind ?_ (fun _ => ?_))
  | (with_reducible refine rq_bind' ?_ (fun _ => ?_))
  | (with_reducible apply rq_ite) | (with_reducible apply rq_when) | (with_reducible apply rq_unless)
  | (with_reducible refine rq_maybeM (fun _ => ?_) _) | (with_reducible apply rq_liftM)
  | (with_reducible refine rq_whileLoop (fun _ => ?_) _)
  | (with_reducible refine rq_mapMx (fun _ => ?_) _)
  | (with_reducible refine rq_mapM (fun _ => ?_) _)
  | (with_reducible refine rq_forMx (fun _ => ?_) _)
  | with_reducible exact rqe_pure _ | with_reducible exact rqe_returnOk _ | with_reducible exact rqe_throw _
  | with_reducible exact rqe_throw' _ | with_reducible exact rqe_throwOpt _ _ | with_reducible exact rqe_assertE _
  | (with_reducible refine rqe_bind ?_ (fun _ => ?_))
  | (with_reducible apply rqe_liftE) | (with_reducible apply rqe_ite) | (with_reducible apply rqe_whenE)
  | (with_reducible apply rqe_unlessE) | (with_reducible refine rq_catch ?_ (fun _ => ?_))
  | (with_reducible refine rqe_handleE ?_ (fun _ => ?_)) | (with_reducible apply rqe_liftME)
  | (with_reducible refine rqe_mapMEx (fun _ => ?_) _) | (with_reducible refine rqe_mapME (fun _ => ?_) _)
  | with_reducible exact not_sc_tcb _ | with_reducible exact not_sc_cnode _ _
  | with_reducible exact not_sc_ep _ | with_reducible exact not_sc_ntfn _ | with_reducible exact not_sc_reply _
  | with_reducible exact not_sc_arch _
  | with_reducible exact fun _ => not_sc_ep _ | with_reducible exact fun _ => not_sc_ntfn _
  | with_reducible exact fun _ => not_sc_reply _ | with_reducible exact fun _ => not_sc_tcb _
  | (with_reducible intro _; exact ⟨rfl, rfl⟩)
  | split
  | (dsimp only)
  | (simp only [letFun])
  | (dsimp only [letFun])
  | (with_reducible exact rq_pure _)
  | (exact rq_pure _))

macro "rq_auto0" : tactic => `(tactic| repeat' rq_step0)

/-- An `RQ` lemma of a spec function (extended below, one rule per lemma). -/
syntax "rq_leaf" : tactic
macro_rules | `(tactic| rq_leaf) => `(tactic| fail "no rq_leaf")

macro "rq_auto" : tactic => `(tactic| repeat' (first | rq_leaf | rq_step0))

/-! ## Object steps -/

/-- The outcome of `set_object`: the object there had the same type. -/
theorem rq_setObject_mem {σ : State Unit} {p : ObjRef} {o : KernelObject} {x : Unit × State Unit}
    (hx : x ∈ (setObject (Z := Unit) p o σ).1) :
    ∃ k, σ.kheap p = some k ∧ aType k = aType o ∧ x.2 = { σ with kheap := Function.update σ.kheap p (some o) } := by
  obtain ⟨y, hy, hx⟩ := hx
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
  exact ⟨k, hk, hty, rfl⟩

/-- `set_object` of an object other than an SC. -/
theorem rq_setObject (p : ObjRef) (o : KernelObject) :
    RQ (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨k, -, -, e⟩ := rq_setObject_mem hx
  rw [e]; exact RQK.refl _
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_setObject _ _)

/-- The outcome of `update_sched_context`. -/
theorem updSc_mem {σ : State Unit} {q : ObjRef} {f : SchedContext → SchedContext} {x : Unit × State Unit}
    (hx : x ∈ (updateSchedContext (Z := Unit) q f σ).1) :
    ∃ y0 n0, σ.kheap q = some (.schedContext y0 n0) ∧
      x.2 = { σ with kheap := Function.update σ.kheap q (some (.schedContext (f y0) n0)) } := by
  unfold updateSchedContext at hx
  obtain ⟨y, hy, hx⟩ := hx
  have hy' : y = (the (σ.kheap q), σ) ∧ σ.kheap q ≠ none := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap q with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨Set.mem_singleton_iff.1 hy, by simp⟩
  obtain ⟨rfl, hne⟩ := hy'
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hne
  rw [hk] at hx
  cases k with
  | schedContext sc n =>
    obtain ⟨k', -, -, e⟩ := rq_setObject_mem (o := .schedContext (f sc) n) hx
    exact ⟨sc, n, hk, e⟩
  | _ => exact hx.elim

/-- `update_sched_context`. -/
theorem rq_updateSchedContext (q : ObjRef) (f : SchedContext → SchedContext) :
    RQ (updateSchedContext (Z := Unit) q f) := by
  intro σ x hx
  obtain ⟨sc, n, hk, e⟩ := updSc_mem hx
  rw [e]; exact RQK.refl _
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_updateSchedContext _ _)

theorem rq_setCap (c : Cap) (sl : CslotPtr) : RQ (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl; unfold setCap
  refine rq_bind (rq_getObject o) (fun obj => ?_)
  cases obj <;> dsimp only <;> rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_setCap _ _)

theorem rq_getCap (sl : CslotPtr) : RQ (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap
  refine rq_bind (rq_getObject o) (fun obj => ?_)
  cases obj <;> simp only [letFun] <;> rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_getCap _)

theorem rq_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) :
    RQ (portOut (Z := Unit) f w) := by
  unfold portOut; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_portOut _ _)

theorem rq_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α)
    (hC : ∀ y n, C e ≠ .schedContext y n) : RQ (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo
  exact rq_bind (rq_getObject _) fun _ => rq_bind (rq_assert _) fun _ => rq_bind (rq_assert _) fun _ =>
    rq_setObject _ _
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible refine rq_setSimpleKo' _ _ _ ?_)

theorem rq_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef)
    (hC : ∀ e y n, C e ≠ .schedContext y n) : RQ (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef getSimpleKo
  refine rq_bind (rq_bind (rq_getObject _) fun _ => rq_bind (rq_assert _) fun _ => ?_) fun _ =>
    rq_setSimpleKo' _ _ _ (hC _)
  split
  · exact rq_pure _
  · exact rq_fail
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible refine rq_updateSkObjRef' _ _ _ _ ?_)

/-! ## The spec functions (VsDomOps, DomRecDel, AllDom's `DK` lemmas, for `RQ`) -/

theorem rq_setOriginal (slot : CslotPtr) (v : Bool) : RQ (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_setOriginal _ _)

theorem rq_updateCdt (f : Cdt → Cdt) : RQ (updateCdt (Z := Unit) f) := by
  unfold updateCdt; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_updateCdt _)

theorem rq_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : RQ (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_setUntypedCapAsFull _ _ _)

theorem rq_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : RQ (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_capInsert _ _ _)

theorem rq_threadSet' (f : Tcb → Tcb) (t : ObjRef) : RQ (threadSet (Z := Unit) f t) := by
  unfold threadSet; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_threadSet' _ _)

theorem rq_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : RQ (threadGet (Z := Unit) f t) := by
  unfold threadGet; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_threadGet' _ _)

theorem rq_setThreadState' (t : ObjRef) (ts : ThreadState) : RQ (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_setThreadState' _ _)

theorem rq_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    RQ (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_getSimpleKo' _ _)

theorem rq_getSchedContext' (q : ObjRef) : RQ (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_getSchedContext' _)

theorem rq_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : RQ (asUser (Z := Unit) t u) := by
  unfold asUser; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_asUser' _ _)

theorem rq_getThreadState' (t : ObjRef) : RQ (getThreadState (Z := Unit) t) := by
  unfold getThreadState; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_getThreadState' _)

theorem rq_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) : RQ (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_getSkObjRef' _ _ _)

theorem rq_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : RQ (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_getScObjRef' _ _)

theorem rq_lookupIpcBuffer' (b : Bool) (t : ObjRef) : RQ (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_lookupIpcBuffer' _ _)

theorem rq_zipWithMx' {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, RQ (g a b)) :
    ∀ l1 l2, RQ (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => rq_bind (h a b) (fun _ => rq_zipWithMx' h l1 l2)
  | [], _ => rq_pure' _
  | _ :: _, [] => rq_pure' _
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible refine rq_zipWithMx' (fun _ _ => ?_) _ _)

theorem rq_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : RQ (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_storeWordOffs' _ _ _)

theorem rq_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : RQ (setMrs (Z := Unit) t b m) := by
  unfold setMrs; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_setMrs' _ _ _)

theorem rq_setMessageInfo' (t : ObjRef) (i : MessageInfo) : RQ (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_setMessageInfo' _ _)

theorem rq_archThreadSet' (f : ArchTcb → ArchTcb) (t : ObjRef) : RQ (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_archThreadSet' _ _)

theorem rq_getTcbQueue' (d : Domain) (p : Priority) : RQ (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_getTcbQueue' _ _)

theorem rq_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : RQ (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_setTcbQueue' _ _ _)

theorem rq_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) : RQ (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_tcbSchedAction' _ _)

theorem rq_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : RQ (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_getTcbObjRef' _ _)

theorem rq_setSchedulerAction' (a : SchedulerAction) : RQ (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_setSchedulerAction' _)

theorem rq_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : RQ (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_getScRefillSufficient' _ _)

theorem rq_getScRefillReady' (sc : ObjRef) : RQ (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_getScRefillReady' _)

theorem rq_tcbReleaseRemove' (t : ObjRef) : RQ (tcbReleaseRemove (Z := Unit) t) := by
  intro σ x hx
  unfold tcbReleaseRemove at hx
  obtain ⟨y0, h0, hx⟩ := hx
  rw [show y0 = (σ.releaseQueue, σ) from Set.mem_singleton_iff.1 h0] at hx
  obtain ⟨y1, h1, hx⟩ := hx
  have hy1 : y1.2.releaseQueue = σ.releaseQueue := by
    unfold NonDet.when at h1
    split at h1
    · rw [Set.mem_singleton_iff.1 h1]
    · rw [Set.mem_singleton_iff.1 h1]
  obtain ⟨y2, h2, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 h2] at hx
  rw [Set.mem_singleton_iff.1 hx]
  intro u hu
  have hu' : u ∈ tcbSchedDequeue t σ.releaseQueue := hu
  exact (List.mem_filter.1 hu').1
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_tcbReleaseRemove' _)

theorem rq_rescheduleRequired' : RQ (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_rescheduleRequired' )

theorem rq_testReschedule' (t : ObjRef) : RQ (testReschedule (Z := Unit) t) := by
  unfold testReschedule; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_testReschedule' _)

theorem rq_possibleSwitchTo' (t : ObjRef) : RQ (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_possibleSwitchTo' _)

theorem rq_isRoundRobin' (sc : ObjRef) : RQ (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_isRoundRobin' _)

theorem rq_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : RQ (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_updateRefillHd' _ _)

theorem rq_getRefillHead' (sc : ObjRef) : RQ (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_getRefillHead' _)

theorem rq_refillPopHead' (sc : ObjRef) : RQ (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_refillPopHead' _)

theorem rq_mergeOverlappingRefills' (sc : ObjRef) : RQ (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_mergeOverlappingRefills' _)

theorem rq_refillHeadOverlappingLoop' (sc : ObjRef) : RQ (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_refillHeadOverlappingLoop' _)

theorem rq_refillUnblockCheck' (sc : ObjRef) : RQ (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_refillUnblockCheck' _)

theorem rq_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) : RQ (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_ifCondRefillUnblockCheck' _ _ _)

theorem rq_replyUnlinkSc' (sc r : ObjRef) : RQ (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_replyUnlinkSc' _ _)

theorem rq_schedContextUpdateConsumed' (sc : ObjRef) : RQ (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_schedContextUpdateConsumed' _)

theorem rqe_rab (p : Cap × CapRef) : RQE (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact rqe_liftE (rq_fail)
    · refine rqe_bind (rqe_whenE _ (rqe_throw _)) fun _ => rqe_bind (rqe_whenE _ (rqe_throw _)) fun _ =>
        rqe_bind (rqe_returnOk _) fun _ => ?_
      dsimp only
      split
      · exact rqe_returnOk _
      · refine rqe_bind (rqe_liftE (rq_getCap _)) fun nc => ?_
        split
        · exact rqe_rab _
        · exact rqe_returnOk _
  · exact rqe_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rqe_rab _)

theorem rqe_resolveAddressBits (p : Cap × CapRef) : RQE (resolveAddressBits (Z := Unit) p) := rqe_rab p
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rqe_resolveAddressBits _)

theorem rq_lookupSlotForThread' (thread : ObjRef) (cref : CapRef) : RQE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_lookupSlotForThread' _ _)

theorem rq_lookupCapAndSlot' (thread : ObjRef) (cptr : CapRef) : RQE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_lookupCapAndSlot' _ _)

theorem rq_lookupCap' (thread : ObjRef) (ref : CapRef) : RQE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_lookupCap' _ _)

theorem rq_captransferFromWords' (ptr : Word) : RQ (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_captransferFromWords' _)

theorem rq_loadCapTransfer' (buffer : ObjRef) : RQ (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_loadCapTransfer' _)

theorem rq_setExtraBadge' (buffer : ObjRef) (badge : Word) (n : Nat) : RQ (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_setExtraBadge' _ _ _)

theorem rqe_lookupErrorOnFailure' {α : Type} (b : Bool) {m : LFMonad Unit α} (h : RQE m) :
    RQE (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact rqe_handleE h fun _ => rqe_throw _
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible refine rqe_lookupErrorOnFailure' _ ?_)

theorem rq_lookupSlotForCnodeOp' (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : RQE (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_lookupSlotForCnodeOp' _ _ _ _)

theorem rq_lookupTargetSlot' (c : Cap) (r : CapRef) (n : Nat) : RQE (lookupTargetSlot (Z := Unit) c r n) := by
  unfold lookupTargetSlot; exact rq_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_lookupTargetSlot' _ _ _)

theorem rqe_bind_returnOk' {ε α β : Type} {a : α} {f : α → NonDetE (State Unit) ε β} (h : RQE (f a)) :
    RQE (NonDetE.returnOk a >>= f) := by
  intro σ x hx
  rw [ExceptT.run_bind] at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ x hx
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible refine rqe_bind_returnOk' ?_)

theorem rq_ensureNoChildren' (cslotPtr : CslotPtr) : RQE (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_ensureNoChildren' _)

theorem rqe_archDeriveCap' (c : ArchCap) : RQE (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rqe_archDeriveCap' _)

theorem rqe_deriveCap' (sl : CslotPtr) (c : Cap) : RQE (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rqe_deriveCap' _ _)

theorem rq_makeArchFaultMsg' (f : ArchFault) (t : ObjRef) : RQ (makeArchFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeArchFaultMsg <;> rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_makeArchFaultMsg' _ _)

theorem rqe_unifyFailure' {F α : Type} {m : NonDetE (State Unit) F α} (h : RQE m) :
    RQE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact rqe_handleE h fun _ => rqe_throw _
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible refine rqe_unifyFailure' ?_)

theorem rq_emptyOnFailure' {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : RQE m) :
    RQ (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact rq_catch h fun _ => rq_pure' _
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible refine rq_emptyOnFailure' ?_)

theorem rq_constOnFailure' {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : RQE m) :
    RQ (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact rq_catch h fun _ => rq_pure' _
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible refine rq_constOnFailure' _ ?_)

theorem rqe_capFaultOnFailure' {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : RQE m) :
    RQE (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact rqe_handleE h fun _ => rqe_throw _
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible refine rqe_capFaultOnFailure' _ _ ?_)

theorem rq_loadWordOffs' (ptr : ObjRef) (offs : Nat) : RQ (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; exact rq_doMachineOp _
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_loadWordOffs' _ _)

theorem rq_getExtraCptrs' (b : Option ObjRef) (mi : MessageInfo) : RQ (getExtraCptrs (Z := Unit) b mi) := by
  cases b
  · unfold getExtraCptrs; exact rq_pure _
  · unfold getExtraCptrs; exact rq_liftM _ (rq_mapM (fun _ => rq_loadWordOffs' _ _) _)
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_getExtraCptrs' _ _)

theorem rq_getReceiveSlots' (t : ObjRef) (b : Option ObjRef) : RQ (getReceiveSlots (Z := Unit) t b) := by
  cases b <;> unfold getReceiveSlots <;> rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_getReceiveSlots' _ _)

theorem rq_transferCapsLoop' (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (slots : List CslotPtr) (mi : MessageInfo),
      RQ (transferCapsLoop (Z := Unit) ep rb n caps slots mi)
  | n, [], slots, mi => by unfold transferCapsLoop; rq_auto
  | n, (c, sl) :: rest, slots, mi => by
    have ih := rq_transferCapsLoop' ep rb (n + 1) rest
    unfold transferCapsLoop
    rq_auto
    all_goals first | exact ih _ _ | skip
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_transferCapsLoop' _ _ _ _ _ _)

theorem rq_lookupExtraCaps' (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : RQE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_lookupExtraCaps' _ _ _)

theorem rq_copyMrs' (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : RQ (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_copyMrs' _ _ _ _ _)

theorem rq_transferCaps' (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : RQ (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_transferCaps' _ _ _ _ _)

theorem rq_makeFaultMsg' (f : Fault) (t : ObjRef) : RQ (makeFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeFaultMsg <;> rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_makeFaultMsg' _ _)

theorem rq_getMessageInfo' (thread : ObjRef) : RQ (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_getMessageInfo' _)

theorem rq_doNormalTransfer' (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : RQ (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_doNormalTransfer' _ _ _ _ _ _ _)

theorem rq_doFaultTransfer' (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : RQ (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_doFaultTransfer' _ _ _ _)

theorem rq_doIpcTransfer' (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : RQ (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_doIpcTransfer' _ _ _ _ _)

theorem rq_getMrs' (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : RQ (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_getMrs' _ _ _)

theorem rq_handleFaultReply' (f : Fault) (t : ObjRef) (x : Data) (y : List Data) :
    RQ (handleFaultReply (Z := Unit) f t x y) := by
  cases f <;> unfold handleFaultReply <;> rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_handleFaultReply' _ _ _ _)


/-- The sporadic unblock check of a thread's SC (`do_reply_transfer`'s, after
`reply_remove`). -/
theorem rq_unblock (t : ObjRef) :
    RQ (getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t >>= ifSporadicCurScTestRefillUnblockCheck (Z := Unit)) := by
  rq_auto

end

end Fl4Proofs.P3.RelQ
