/-
P3 (DESIGN.md §9), scheduling contexts: **a backward SC frame for the
spec's reply path** (spec side only).

`SCK σ σ'`: every SC of `σ'` was an SC of `σ` at the same reference and
size, with the same `REFILL_MAX` and bound thread (its refills may have
changed). `MK m`: every outcome of `m` is `SCK`-related to its start. Built
from the monad's combinators (`mk_auto`, as VsDom's `dk_auto`), with
`set_object` of a non-SC object and `update_sched_context` by a function
keeping `REFILL_MAX` and `sc_tcb` as the object steps, up to
`do_ipc_transfer`, `handle_fault_reply`, `set_thread_state` and the
sporadic unblock check (`mk_doIpcTransfer'`, `mk_specFaultReply`,
`mk_unblock`).

Used by the reply path (IpcReply's `reply_tail_top`): the receiver's SC,
active after `reply_remove`, is still active at the tail.
-/
import Fl4Spec.Ext.Invocation
import Fl4Spec.Ext.VSpace
open Classical

namespace Fl4Proofs.P3.MaxK
open Fl4Spec

noncomputable section

/-- Every SC of `σ'` was one of `σ`, with the same size, `REFILL_MAX` and
bound thread. -/
def SCK (σ σ' : State Unit) : Prop :=
  ∀ p y n, σ'.kheap p = some (.schedContext y n) →
    ∃ y0, σ.kheap p = some (.schedContext y0 n) ∧ y.scRefillMax = y0.scRefillMax ∧ y.scTcb = y0.scTcb

theorem SCK.refl (σ : State Unit) : SCK σ σ := fun _ y _ h => ⟨y, h, rfl, rfl⟩

theorem SCK.trans {σ1 σ2 σ3 : State Unit} (h1 : SCK σ1 σ2) (h2 : SCK σ2 σ3) : SCK σ1 σ3 := by
  intro p y n h
  obtain ⟨y2, h2', e1, e2⟩ := h2 p y n h
  obtain ⟨y1, h1', f1, f2⟩ := h1 p y2 n h2'
  exact ⟨y1, h1', e1.trans f1, e2.trans f2⟩

theorem SCK.of_kheap {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) : SCK σ σ' := by
  intro p y n hp; rw [h] at hp; exact ⟨y, hp, rfl, rfl⟩

/-- Every outcome of `m` keeps the SCs (backward). -/
def MK {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → SCK σ x.2

section Comb

theorem mk_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : MK m)
    (hg : ∀ a, MK (g a)) : MK (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem mk_bind_pure {α β : Type} {a : α} {g : α → NonDet (State Unit) β} (h : MK (g a)) :
    MK ((pure a : NonDet (State Unit) α) >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ x hx

theorem mk_fail_bind {α β : Type} {g : α → NonDet (State Unit) β} :
    MK ((NonDet.fail : NonDet (State Unit) α) >>= g) := by
  intro σ x ⟨y, hy, _⟩
  exact hy.elim

theorem mk_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : MK m)
    (hg : ∀ a, MK (g a)) : MK (NonDet.bind m g) := mk_bind hm hg

theorem mk_pure {α : Type} (a : α) : MK (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SCK.refl _

theorem mk_pure' {α : Type} (a : α) : MK (NonDet.pure a : NonDet (State Unit) α) := mk_pure a

theorem mk_gets {α : Type} (g : State Unit → α) : MK (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SCK.refl _

theorem mk_get : MK (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SCK.refl _

theorem mk_assert (P : Prop) : MK (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact SCK.refl _

theorem mk_fail {α : Type} : MK (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem mk_assertOpt {α : Type} (o : Option α) : MK (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact mk_fail
  · exact mk_pure' _

theorem mk_getsThe {α : Type} (g : State Unit → Option α) : MK (NonDet.getsThe g) := by
  intro σ x hx; exact mk_assertOpt (g σ) σ x hx

theorem mk_selectF {α : Type} (S : Set α × Prop) : MK (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact SCK.refl _

theorem mk_select {α : Type} (S : Set α) : MK (NonDet.select S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact SCK.refl _

theorem mk_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : MK m1)
    (h2 : MK m2) : MK (if P then m1 else m2) := by
  split <;> assumption

theorem mk_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : MK m) :
    MK (NonDet.when P m) := by
  unfold NonDet.when; exact mk_ite P h (mk_pure' _)

theorem mk_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : MK m) :
    MK (NonDet.unless P m) := by
  unfold NonDet.unless; exact mk_ite P (mk_pure' _) h

theorem mk_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, MK (g a)) (o : Option α) :
    MK (NonDet.maybeM g o) := by
  cases o
  · exact mk_pure' _
  · exact h _

theorem mk_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : MK m) :
    MK (NonDet.liftM g m) := mk_bind' h fun _ => mk_pure' _

theorem mk_modify {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap) :
    MK (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SCK.of_kheap (hg σ)

theorem mk_get_put {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap) :
    MK (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact SCK.of_kheap (hg σ)

theorem mk_get_put' {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap) :
    MK (do let s ← NonDet.get; NonDet.put (g s)) := mk_get_put hg

theorem mk_getObject (p : ObjRef) : MK (getObject (Z := Unit) p) := mk_getsThe _

theorem mk_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, MK (B r)) (r : α) : MK (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => exact SCK.refl _
  | step _ hm _ ih => exact (hB _ _ _ hm).trans ih

theorem mk_mapMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, MK (g a)) (xs : List α) :
    MK (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact mk_pure' _
  | cons a xs' ih => exact mk_bind' (h a) fun _ => ih

theorem mk_forMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, MK (g a)) (xs : List α) :
    MK (NonDet.forMx xs g) := mk_mapMx h xs

theorem mk_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, MK (g a)) (xs : List α) :
    MK (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact mk_pure' _
  | cons a xs' ih => exact mk_bind' (h a) fun _ => mk_bind' ih fun _ => mk_pure' _

theorem mk_doMachineOp {α : Type} (mop : NonDet MachineState α) : MK (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine mk_bind (mk_gets _) (fun _ => mk_bind (mk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact mk_bind (mk_modify (fun σ => rfl)) (fun _ => mk_pure _)

theorem mk_doExtendedOp (eop : DetExtMonad Unit) : MK (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine mk_bind mk_get (fun _ => mk_bind (mk_selectF _) (fun _ => ?_))
  split
  exact mk_modify (fun σ => rfl)

end Comb

/-- `MK` for the exception monad. -/
def MKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := MK (ExceptT.run m)

section CombE
variable {ε : Type}

theorem mke_bind {α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β} (hm : MKE m)
    (hg : ∀ a, MKE (g a)) : MKE (m >>= g) := by
  unfold MKE; rw [ExceptT.run_bind]
  refine mk_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact mk_pure _

theorem mke_pure {α : Type} (a : α) : MKE (pure a : NonDetE (State Unit) ε α) := mk_pure _

theorem mke_returnOk {α : Type} (a : α) : MKE (NonDetE.returnOk a : NonDetE (State Unit) ε α) := mk_pure _

theorem mke_throw {α : Type} (e : ε) : MKE (NonDetE.throwError e : NonDetE (State Unit) ε α) := mk_pure _

theorem mke_throw' {α : Type} (e : ε) : MKE (throw e : NonDetE (State Unit) ε α) := mk_pure _

theorem mke_liftE {α : Type} {m : NonDet (State Unit) α} (h : MK m) : MKE (NonDetE.liftE (ε := ε) m) := by
  unfold MKE NonDetE.liftE; rw [ExceptT.run_lift]
  exact mk_bind h fun _ => mk_pure _

theorem mke_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : MKE m1)
    (h2 : MKE m2) : MKE (if P then m1 else m2) := by
  split <;> assumption

theorem mke_whenE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : MKE m) :
    MKE (NonDetE.whenE P m) := by
  unfold NonDetE.whenE; exact mke_ite P h (mke_pure _)

theorem mke_unlessE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : MKE m) :
    MKE (NonDetE.unlessE P m) := by
  unfold NonDetE.unlessE; exact mke_ite P (mke_pure _) h

theorem mke_throwOpt {α : Type} (e : ε) (o : Option α) : MKE (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact mke_throw' e
  · exact mke_pure _

theorem mke_assertE (P : Prop) : MKE (NonDetE.assertE P : NonDetE (State Unit) ε Unit) :=
  mke_liftE (mk_assert P)

theorem mk_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : MKE m)
    (hh : ∀ e, MK (h e)) : MK (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine mk_bind' hm fun r => ?_
  cases r with
  | ok a => exact mk_pure' _
  | error e => exact hh e

theorem mke_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : MKE m) (hh : ∀ e, MKE (h e)) : MKE (NonDetE.handleE m h) := by
  unfold NonDetE.handleE MKE
  rw [ExceptT.run_mk]
  refine mk_bind' hm fun r => ?_
  cases r with
  | ok a => exact mk_pure' _
  | error e => exact hh e

theorem mke_liftME {α β : Type} (f : α → β) {m : NonDetE (State Unit) ε α} (h : MKE m) :
    MKE (NonDetE.liftME f m) := by
  unfold NonDetE.liftME; exact mke_bind h fun _ => mke_pure _

theorem mke_mapMEx {α β : Type} {f : α → NonDetE (State Unit) ε β} (h : ∀ a, MKE (f a)) :
    ∀ xs : List α, MKE (NonDetE.mapMEx f xs)
  | [] => by unfold NonDetE.mapMEx; exact mke_pure _
  | a :: as => by unfold NonDetE.mapMEx; exact mke_bind (h a) fun _ => mke_mapMEx h as

theorem mke_mapME {α β : Type} {f : α → NonDetE (State Unit) ε β} (h : ∀ a, MKE (f a)) :
    ∀ xs : List α, MKE (NonDetE.mapME f xs)
  | [] => by unfold NonDetE.mapME; exact mke_pure _
  | a :: as => by
    unfold NonDetE.mapME; exact mke_bind (h a) fun _ => mke_bind (mke_mapME h as) fun _ => mke_pure _

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

/-- One step of an `MK` proof. -/
macro "mk_step0" : tactic => `(tactic| first
  | with_reducible exact mk_pure _ | with_reducible exact mk_pure' _ | with_reducible exact mk_fail
  | with_reducible exact mk_gets _ | with_reducible exact mk_get
  | with_reducible exact mk_assert _ | with_reducible exact mk_assertOpt _
  | with_reducible exact mk_getsThe _
  | with_reducible exact mk_selectF _ | with_reducible exact mk_select _
  | ((with_reducible apply mk_modify); intro _; rfl)
  | ((with_reducible apply mk_get_put); intro _; rfl)
  | (exact mk_get_put' (fun _ => rfl))
  | (exact mk_get_put (fun _ => rfl))
  | with_reducible exact mk_getObject _
  | with_reducible exact mk_doMachineOp _ | with_reducible exact mk_doExtendedOp _
  | (with_reducible refine mk_bind_pure ?_) | (with_reducible exact mk_fail_bind)
  | (with_reducible refine mk_bind ?_ (fun _ => ?_))
  | (with_reducible refine mk_bind' ?_ (fun _ => ?_))
  | (with_reducible apply mk_ite) | (with_reducible apply mk_when) | (with_reducible apply mk_unless)
  | (with_reducible refine mk_maybeM (fun _ => ?_) _) | (with_reducible apply mk_liftM)
  | (with_reducible refine mk_whileLoop (fun _ => ?_) _)
  | (with_reducible refine mk_mapMx (fun _ => ?_) _)
  | (with_reducible refine mk_mapM (fun _ => ?_) _)
  | (with_reducible refine mk_forMx (fun _ => ?_) _)
  | with_reducible exact mke_pure _ | with_reducible exact mke_returnOk _ | with_reducible exact mke_throw _
  | with_reducible exact mke_throw' _ | with_reducible exact mke_throwOpt _ _ | with_reducible exact mke_assertE _
  | (with_reducible refine mke_bind ?_ (fun _ => ?_))
  | (with_reducible apply mke_liftE) | (with_reducible apply mke_ite) | (with_reducible apply mke_whenE)
  | (with_reducible apply mke_unlessE) | (with_reducible refine mk_catch ?_ (fun _ => ?_))
  | (with_reducible refine mke_handleE ?_ (fun _ => ?_)) | (with_reducible apply mke_liftME)
  | (with_reducible refine mke_mapMEx (fun _ => ?_) _) | (with_reducible refine mke_mapME (fun _ => ?_) _)
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
  | (with_reducible exact mk_pure _)
  | (exact mk_pure _))

macro "mk_auto0" : tactic => `(tactic| repeat' mk_step0)

/-- An `MK` lemma of a spec function (extended below, one rule per lemma). -/
syntax "mk_leaf" : tactic
macro_rules | `(tactic| mk_leaf) => `(tactic| fail "no mk_leaf")

macro "mk_auto" : tactic => `(tactic| repeat' (first | mk_leaf | mk_step0))

/-! ## Object steps -/

/-- The outcome of `set_object`: the object there had the same type. -/
theorem mk_setObject_mem {σ : State Unit} {p : ObjRef} {o : KernelObject} {x : Unit × State Unit}
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
theorem mk_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ y n, o ≠ .schedContext y n) :
    MK (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨k, -, -, e⟩ := mk_setObject_mem hx
  rw [e]
  intro q y n hq
  by_cases hqp : q = p
  · subst hqp; simp only [Function.update_self, Option.some.injEq] at hq; exact absurd hq (ho y n)
  · simp only [Function.update_of_ne hqp] at hq; exact ⟨y, hq, rfl, rfl⟩
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible refine mk_setObject _ _ ?_)

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
    obtain ⟨k', -, -, e⟩ := mk_setObject_mem (o := .schedContext (f sc) n) hx
    exact ⟨sc, n, hk, e⟩
  | _ => exact hx.elim

/-- `update_sched_context` by a function keeping `REFILL_MAX` and `sc_tcb`. -/
theorem mk_updateSchedContext (q : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, (f y).scRefillMax = y.scRefillMax ∧ (f y).scTcb = y.scTcb) :
    MK (updateSchedContext (Z := Unit) q f) := by
  intro σ x hx
  obtain ⟨sc, n, hk, e⟩ := updSc_mem hx
  rw [e]
  intro r z m hr
  by_cases hrq : r = q
  · subst hrq
    simp only [Function.update_self, Option.some.injEq, KernelObject.schedContext.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨sc, hk, (hf sc).1, (hf sc).2⟩
  · simp only [Function.update_of_ne hrq] at hr; exact ⟨z, hr, rfl, rfl⟩
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible refine mk_updateSchedContext _ _ ?_)

theorem mk_setCap (c : Cap) (sl : CslotPtr) : MK (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl; unfold setCap
  refine mk_bind (mk_getObject o) (fun obj => ?_)
  cases obj <;> dsimp only <;> mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_setCap _ _)

theorem mk_getCap (sl : CslotPtr) : MK (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap
  refine mk_bind (mk_getObject o) (fun obj => ?_)
  cases obj <;> simp only [letFun] <;> mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_getCap _)

theorem mk_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) :
    MK (portOut (Z := Unit) f w) := by
  unfold portOut; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_portOut _ _)

theorem mk_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α)
    (hC : ∀ y n, C e ≠ .schedContext y n) : MK (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo
  exact mk_bind (mk_getObject _) fun _ => mk_bind (mk_assert _) fun _ => mk_bind (mk_assert _) fun _ =>
    mk_setObject _ _ hC
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible refine mk_setSimpleKo' _ _ _ ?_)

theorem mk_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef)
    (hC : ∀ e y n, C e ≠ .schedContext y n) : MK (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef getSimpleKo
  refine mk_bind (mk_bind (mk_getObject _) fun _ => mk_bind (mk_assert _) fun _ => ?_) fun _ =>
    mk_setSimpleKo' _ _ _ (hC _)
  split
  · exact mk_pure _
  · exact mk_fail
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible refine mk_updateSkObjRef' _ _ _ _ ?_)

/-! ## The spec functions (VsDomOps, DomRecDel, AllDom's `DK` lemmas, for `MK`) -/

theorem mk_setOriginal (slot : CslotPtr) (v : Bool) : MK (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_setOriginal _ _)

theorem mk_updateCdt (f : Cdt → Cdt) : MK (updateCdt (Z := Unit) f) := by
  unfold updateCdt; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_updateCdt _)

theorem mk_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : MK (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_setUntypedCapAsFull _ _ _)

theorem mk_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : MK (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_capInsert _ _ _)

theorem mk_threadSet' (f : Tcb → Tcb) (t : ObjRef) : MK (threadSet (Z := Unit) f t) := by
  unfold threadSet; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_threadSet' _ _)

theorem mk_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : MK (threadGet (Z := Unit) f t) := by
  unfold threadGet; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_threadGet' _ _)

theorem mk_setThreadState' (t : ObjRef) (ts : ThreadState) : MK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_setThreadState' _ _)

theorem mk_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    MK (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_getSimpleKo' _ _)

theorem mk_getSchedContext' (q : ObjRef) : MK (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_getSchedContext' _)

theorem mk_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : MK (asUser (Z := Unit) t u) := by
  unfold asUser; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_asUser' _ _)

theorem mk_getThreadState' (t : ObjRef) : MK (getThreadState (Z := Unit) t) := by
  unfold getThreadState; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_getThreadState' _)

theorem mk_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) : MK (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_getSkObjRef' _ _ _)

theorem mk_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : MK (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_getScObjRef' _ _)

theorem mk_lookupIpcBuffer' (b : Bool) (t : ObjRef) : MK (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_lookupIpcBuffer' _ _)

theorem mk_zipWithMx' {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, MK (g a b)) :
    ∀ l1 l2, MK (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => mk_bind (h a b) (fun _ => mk_zipWithMx' h l1 l2)
  | [], _ => mk_pure' _
  | _ :: _, [] => mk_pure' _
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible refine mk_zipWithMx' (fun _ _ => ?_) _ _)

theorem mk_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : MK (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_storeWordOffs' _ _ _)

theorem mk_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : MK (setMrs (Z := Unit) t b m) := by
  unfold setMrs; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_setMrs' _ _ _)

theorem mk_setMessageInfo' (t : ObjRef) (i : MessageInfo) : MK (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_setMessageInfo' _ _)

theorem mk_archThreadSet' (f : ArchTcb → ArchTcb) (t : ObjRef) : MK (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_archThreadSet' _ _)

theorem mk_getTcbQueue' (d : Domain) (p : Priority) : MK (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_getTcbQueue' _ _)

theorem mk_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : MK (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_setTcbQueue' _ _ _)

theorem mk_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) : MK (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_tcbSchedAction' _ _)

theorem mk_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : MK (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_getTcbObjRef' _ _)

theorem mk_setSchedulerAction' (a : SchedulerAction) : MK (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_setSchedulerAction' _)

theorem mk_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : MK (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_getScRefillSufficient' _ _)

theorem mk_getScRefillReady' (sc : ObjRef) : MK (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_getScRefillReady' _)

theorem mk_tcbReleaseRemove' (t : ObjRef) : MK (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_tcbReleaseRemove' _)

theorem mk_rescheduleRequired' : MK (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_rescheduleRequired' )

theorem mk_testReschedule' (t : ObjRef) : MK (testReschedule (Z := Unit) t) := by
  unfold testReschedule; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_testReschedule' _)

theorem mk_possibleSwitchTo' (t : ObjRef) : MK (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_possibleSwitchTo' _)

theorem mk_isRoundRobin' (sc : ObjRef) : MK (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_isRoundRobin' _)

theorem mk_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : MK (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_updateRefillHd' _ _)

theorem mk_getRefillHead' (sc : ObjRef) : MK (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_getRefillHead' _)

theorem mk_refillPopHead' (sc : ObjRef) : MK (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_refillPopHead' _)

theorem mk_mergeOverlappingRefills' (sc : ObjRef) : MK (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_mergeOverlappingRefills' _)

theorem mk_refillHeadOverlappingLoop' (sc : ObjRef) : MK (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_refillHeadOverlappingLoop' _)

theorem mk_refillUnblockCheck' (sc : ObjRef) : MK (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_refillUnblockCheck' _)

theorem mk_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) : MK (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_ifCondRefillUnblockCheck' _ _ _)

theorem mk_replyUnlinkSc' (sc r : ObjRef) : MK (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_replyUnlinkSc' _ _)

theorem mk_schedContextUpdateConsumed' (sc : ObjRef) : MK (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_schedContextUpdateConsumed' _)

theorem mke_rab (p : Cap × CapRef) : MKE (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact mke_liftE (mk_fail)
    · refine mke_bind (mke_whenE _ (mke_throw _)) fun _ => mke_bind (mke_whenE _ (mke_throw _)) fun _ =>
        mke_bind (mke_returnOk _) fun _ => ?_
      dsimp only
      split
      · exact mke_returnOk _
      · refine mke_bind (mke_liftE (mk_getCap _)) fun nc => ?_
        split
        · exact mke_rab _
        · exact mke_returnOk _
  · exact mke_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mke_rab _)

theorem mke_resolveAddressBits (p : Cap × CapRef) : MKE (resolveAddressBits (Z := Unit) p) := mke_rab p
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mke_resolveAddressBits _)

theorem mk_lookupSlotForThread' (thread : ObjRef) (cref : CapRef) : MKE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_lookupSlotForThread' _ _)

theorem mk_lookupCapAndSlot' (thread : ObjRef) (cptr : CapRef) : MKE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_lookupCapAndSlot' _ _)

theorem mk_lookupCap' (thread : ObjRef) (ref : CapRef) : MKE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_lookupCap' _ _)

theorem mk_captransferFromWords' (ptr : Word) : MK (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_captransferFromWords' _)

theorem mk_loadCapTransfer' (buffer : ObjRef) : MK (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_loadCapTransfer' _)

theorem mk_setExtraBadge' (buffer : ObjRef) (badge : Word) (n : Nat) : MK (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_setExtraBadge' _ _ _)

theorem mke_lookupErrorOnFailure' {α : Type} (b : Bool) {m : LFMonad Unit α} (h : MKE m) :
    MKE (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact mke_handleE h fun _ => mke_throw _
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible refine mke_lookupErrorOnFailure' _ ?_)

theorem mk_lookupSlotForCnodeOp' (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : MKE (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_lookupSlotForCnodeOp' _ _ _ _)

theorem mk_lookupTargetSlot' (c : Cap) (r : CapRef) (n : Nat) : MKE (lookupTargetSlot (Z := Unit) c r n) := by
  unfold lookupTargetSlot; exact mk_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_lookupTargetSlot' _ _ _)

theorem mke_bind_returnOk' {ε α β : Type} {a : α} {f : α → NonDetE (State Unit) ε β} (h : MKE (f a)) :
    MKE (NonDetE.returnOk a >>= f) := by
  intro σ x hx
  rw [ExceptT.run_bind] at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ x hx
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible refine mke_bind_returnOk' ?_)

theorem mk_ensureNoChildren' (cslotPtr : CslotPtr) : MKE (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_ensureNoChildren' _)

theorem mke_archDeriveCap' (c : ArchCap) : MKE (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mke_archDeriveCap' _)

theorem mke_deriveCap' (sl : CslotPtr) (c : Cap) : MKE (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mke_deriveCap' _ _)

theorem mk_makeArchFaultMsg' (f : ArchFault) (t : ObjRef) : MK (makeArchFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeArchFaultMsg <;> mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_makeArchFaultMsg' _ _)

theorem mke_unifyFailure' {F α : Type} {m : NonDetE (State Unit) F α} (h : MKE m) :
    MKE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact mke_handleE h fun _ => mke_throw _
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible refine mke_unifyFailure' ?_)

theorem mk_emptyOnFailure' {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : MKE m) :
    MK (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact mk_catch h fun _ => mk_pure' _
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible refine mk_emptyOnFailure' ?_)

theorem mk_constOnFailure' {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : MKE m) :
    MK (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact mk_catch h fun _ => mk_pure' _
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible refine mk_constOnFailure' _ ?_)

theorem mke_capFaultOnFailure' {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : MKE m) :
    MKE (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact mke_handleE h fun _ => mke_throw _
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible refine mke_capFaultOnFailure' _ _ ?_)

theorem mk_loadWordOffs' (ptr : ObjRef) (offs : Nat) : MK (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; exact mk_doMachineOp _
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_loadWordOffs' _ _)

theorem mk_getExtraCptrs' (b : Option ObjRef) (mi : MessageInfo) : MK (getExtraCptrs (Z := Unit) b mi) := by
  cases b
  · unfold getExtraCptrs; exact mk_pure _
  · unfold getExtraCptrs; exact mk_liftM _ (mk_mapM (fun _ => mk_loadWordOffs' _ _) _)
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_getExtraCptrs' _ _)

theorem mk_getReceiveSlots' (t : ObjRef) (b : Option ObjRef) : MK (getReceiveSlots (Z := Unit) t b) := by
  cases b <;> unfold getReceiveSlots <;> mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_getReceiveSlots' _ _)

theorem mk_transferCapsLoop' (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (slots : List CslotPtr) (mi : MessageInfo),
      MK (transferCapsLoop (Z := Unit) ep rb n caps slots mi)
  | n, [], slots, mi => by unfold transferCapsLoop; mk_auto
  | n, (c, sl) :: rest, slots, mi => by
    have ih := mk_transferCapsLoop' ep rb (n + 1) rest
    unfold transferCapsLoop
    mk_auto
    all_goals first | exact ih _ _ | skip
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_transferCapsLoop' _ _ _ _ _ _)

theorem mk_lookupExtraCaps' (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : MKE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_lookupExtraCaps' _ _ _)

theorem mk_copyMrs' (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : MK (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_copyMrs' _ _ _ _ _)

theorem mk_transferCaps' (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : MK (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_transferCaps' _ _ _ _ _)

theorem mk_makeFaultMsg' (f : Fault) (t : ObjRef) : MK (makeFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeFaultMsg <;> mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_makeFaultMsg' _ _)

theorem mk_getMessageInfo' (thread : ObjRef) : MK (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_getMessageInfo' _)

theorem mk_doNormalTransfer' (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : MK (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_doNormalTransfer' _ _ _ _ _ _ _)

theorem mk_doFaultTransfer' (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : MK (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_doFaultTransfer' _ _ _ _)

theorem mk_doIpcTransfer' (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : MK (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_doIpcTransfer' _ _ _ _ _)

theorem mk_getMrs' (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : MK (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_getMrs' _ _ _)

theorem mk_handleFaultReply' (f : Fault) (t : ObjRef) (x : Data) (y : List Data) :
    MK (handleFaultReply (Z := Unit) f t x y) := by
  cases f <;> unfold handleFaultReply <;> mk_auto
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_handleFaultReply' _ _ _ _)


/-- The sporadic unblock check of a thread's SC (`do_reply_transfer`'s, after
`reply_remove`). -/
theorem mk_unblock (t : ObjRef) :
    MK (getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t >>= ifSporadicCurScTestRefillUnblockCheck (Z := Unit)) := by
  mk_auto

end

end Fl4Proofs.P3.MaxK
