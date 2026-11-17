/-
P3 (DESIGN.md §9), TCB invocations: **a backward frame of the other TCBs'
states** (spec side only), as IpcTscK's `OSK t0`.

`OSK t0 σ σ'`: every TCB of `σ'` other than `t0` was a TCB of `σ` with the
same `tcb_state`. `STK t0 m`: every outcome of `m` is `OSK t0`-related to its
start (`st_auto`), up to `suspend t0` (`st_suspend`).

Used by ReadRegisters (IpcReadRegs): the source's suspend keeps the caller
`Restart`.
-/
import Fl4Spec.Ext.Invocation
import Fl4Spec.Ext.VSpace
open Classical

namespace Fl4Proofs.P3.StK
open Fl4Spec

noncomputable section

/-- Every TCB of `σ'` other than `t0` was one of `σ`, with the same state. -/
def OSK (t0 : ObjRef) (σ σ' : State Unit) : Prop :=
  (∀ p y, p ≠ t0 → σ'.kheap p = some (.tcb y) → ∃ y0, σ.kheap p = some (.tcb y0) ∧ y.tcbState = y0.tcbState) ∧
  σ'.curThread = σ.curThread

variable {t0 : ObjRef}

theorem OSK.refl (σ : State Unit) : OSK t0 σ σ := ⟨fun _ y _ h => ⟨y, h, rfl⟩, rfl⟩

theorem OSK.trans {σ1 σ2 σ3 : State Unit} (h1 : OSK t0 σ1 σ2) (h2 : OSK t0 σ2 σ3) : OSK t0 σ1 σ3 := by
  refine ⟨fun p y hp h => ?_, h2.2.trans h1.2⟩
  obtain ⟨y2, h2', e1⟩ := h2.1 p y hp h
  obtain ⟨y1, h1', f1⟩ := h1.1 p y2 hp h2'
  exact ⟨y1, h1', e1.trans f1⟩

theorem OSK.of_kheap {σ σ' : State Unit} (h : σ'.kheap = σ.kheap ∧ σ'.curThread = σ.curThread) :
    OSK t0 σ σ' := by
  refine ⟨fun p y _ hp => ?_, h.2⟩; rw [h.1] at hp; exact ⟨y, hp, rfl⟩

/-- Every outcome of `m` keeps the TCBs' bound SCs (backward). -/
def STK (t0 : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → OSK t0 σ x.2

section Comb

theorem st_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : STK t0 m)
    (hg : ∀ a, STK t0 (g a)) : STK t0 (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem st_bind_pure {α β : Type} {a : α} {g : α → NonDet (State Unit) β} (h : STK t0 (g a)) :
    STK t0 ((pure a : NonDet (State Unit) α) >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ x hx

theorem st_fail_bind {α β : Type} {g : α → NonDet (State Unit) β} :
    STK t0 ((NonDet.fail : NonDet (State Unit) α) >>= g) := by
  intro σ x ⟨y, hy, _⟩
  exact hy.elim

theorem st_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : STK t0 m)
    (hg : ∀ a, STK t0 (g a)) : STK t0 (NonDet.bind m g) := st_bind hm hg

theorem st_pure {α : Type} (a : α) : STK t0 (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact OSK.refl _

theorem st_pure' {α : Type} (a : α) : STK t0 (NonDet.pure a : NonDet (State Unit) α) := st_pure a

theorem st_gets {α : Type} (g : State Unit → α) : STK t0 (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact OSK.refl _

theorem st_get : STK t0 (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact OSK.refl _

theorem st_assert (P : Prop) : STK t0 (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact OSK.refl _

theorem st_fail {α : Type} : STK t0 (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem st_assertOpt {α : Type} (o : Option α) : STK t0 (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact st_fail
  · exact st_pure' _

theorem st_getsThe {α : Type} (g : State Unit → Option α) : STK t0 (NonDet.getsThe g) := by
  intro σ x hx; exact st_assertOpt (g σ) σ x hx

theorem st_selectF {α : Type} (S : Set α × Prop) : STK t0 (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact OSK.refl _

theorem st_select {α : Type} (S : Set α) : STK t0 (NonDet.select S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact OSK.refl _

theorem st_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : STK t0 m1)
    (h2 : STK t0 m2) : STK t0 (if P then m1 else m2) := by
  split <;> assumption

theorem st_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : STK t0 m) :
    STK t0 (NonDet.when P m) := by
  unfold NonDet.when; exact st_ite P h (st_pure' _)

theorem st_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : STK t0 m) :
    STK t0 (NonDet.unless P m) := by
  unfold NonDet.unless; exact st_ite P (st_pure' _) h

theorem st_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, STK t0 (g a)) (o : Option α) :
    STK t0 (NonDet.maybeM g o) := by
  cases o
  · exact st_pure' _
  · exact h _

theorem st_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : STK t0 m) :
    STK t0 (NonDet.liftM g m) := st_bind' h fun _ => st_pure' _

theorem st_modify {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap ∧ (g σ).curThread = σ.curThread) :
    STK t0 (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact OSK.of_kheap (hg σ)

theorem st_get_put {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap ∧ (g σ).curThread = σ.curThread) :
    STK t0 (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact OSK.of_kheap (hg σ)

theorem st_get_put' {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap ∧ (g σ).curThread = σ.curThread) :
    STK t0 (do let s ← NonDet.get; NonDet.put (g s)) := st_get_put hg

theorem st_getObject (p : ObjRef) : STK t0 (getObject (Z := Unit) p) := st_getsThe _

theorem st_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, STK t0 (B r)) (r : α) : STK t0 (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => exact OSK.refl _
  | step _ hm _ ih => exact (hB _ _ _ hm).trans ih

theorem st_mapMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, STK t0 (g a)) (xs : List α) :
    STK t0 (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact st_pure' _
  | cons a xs' ih => exact st_bind' (h a) fun _ => ih

theorem st_forMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, STK t0 (g a)) (xs : List α) :
    STK t0 (NonDet.forMx xs g) := st_mapMx h xs

theorem st_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, STK t0 (g a)) (xs : List α) :
    STK t0 (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact st_pure' _
  | cons a xs' ih => exact st_bind' (h a) fun _ => st_bind' ih fun _ => st_pure' _

theorem st_doMachineOp {α : Type} (mop : NonDet MachineState α) : STK t0 (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine st_bind (st_gets _) (fun _ => st_bind (st_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact st_bind (st_modify (fun σ => ⟨rfl, rfl⟩)) (fun _ => st_pure _)

theorem st_doExtendedOp (eop : DetExtMonad Unit) : STK t0 (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine st_bind st_get (fun _ => st_bind (st_selectF _) (fun _ => ?_))
  split
  exact st_modify (fun σ => ⟨rfl, rfl⟩)

end Comb

/-- `STK t0` for the exception monad. -/
def STKE (t0 : ObjRef) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := STK t0 (ExceptT.run m)

section CombE
variable {ε : Type}

theorem ste_bind {α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β} (hm : STKE t0 m)
    (hg : ∀ a, STKE t0 (g a)) : STKE t0 (m >>= g) := by
  unfold STKE; rw [ExceptT.run_bind]
  refine st_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact st_pure _

theorem ste_pure {α : Type} (a : α) : STKE t0 (pure a : NonDetE (State Unit) ε α) := st_pure _

theorem ste_returnOk {α : Type} (a : α) : STKE t0 (NonDetE.returnOk a : NonDetE (State Unit) ε α) := st_pure _

theorem ste_throw {α : Type} (e : ε) : STKE t0 (NonDetE.throwError e : NonDetE (State Unit) ε α) := st_pure _

theorem ste_throw' {α : Type} (e : ε) : STKE t0 (throw e : NonDetE (State Unit) ε α) := st_pure _

theorem ste_liftE {α : Type} {m : NonDet (State Unit) α} (h : STK t0 m) : STKE t0 (NonDetE.liftE (ε := ε) m) := by
  unfold STKE NonDetE.liftE; rw [ExceptT.run_lift]
  exact st_bind h fun _ => st_pure _

theorem ste_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : STKE t0 m1)
    (h2 : STKE t0 m2) : STKE t0 (if P then m1 else m2) := by
  split <;> assumption

theorem ste_whenE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : STKE t0 m) :
    STKE t0 (NonDetE.whenE P m) := by
  unfold NonDetE.whenE; exact ste_ite P h (ste_pure _)

theorem ste_unlessE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : STKE t0 m) :
    STKE t0 (NonDetE.unlessE P m) := by
  unfold NonDetE.unlessE; exact ste_ite P (ste_pure _) h

theorem ste_throwOpt {α : Type} (e : ε) (o : Option α) : STKE t0 (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact ste_throw' e
  · exact ste_pure _

theorem ste_assertE (P : Prop) : STKE t0 (NonDetE.assertE P : NonDetE (State Unit) ε Unit) :=
  ste_liftE (st_assert P)

theorem st_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : STKE t0 m)
    (hh : ∀ e, STK t0 (h e)) : STK t0 (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine st_bind' hm fun r => ?_
  cases r with
  | ok a => exact st_pure' _
  | error e => exact hh e

theorem ste_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : STKE t0 m) (hh : ∀ e, STKE t0 (h e)) : STKE t0 (NonDetE.handleE m h) := by
  unfold NonDetE.handleE STKE
  rw [ExceptT.run_mk]
  refine st_bind' hm fun r => ?_
  cases r with
  | ok a => exact st_pure' _
  | error e => exact hh e

theorem ste_liftME {α β : Type} (f : α → β) {m : NonDetE (State Unit) ε α} (h : STKE t0 m) :
    STKE t0 (NonDetE.liftME f m) := by
  unfold NonDetE.liftME; exact ste_bind h fun _ => ste_pure _

theorem ste_mapMEx {α β : Type} {f : α → NonDetE (State Unit) ε β} (h : ∀ a, STKE t0 (f a)) :
    ∀ xs : List α, STKE t0 (NonDetE.mapMEx f xs)
  | [] => by unfold NonDetE.mapMEx; exact ste_pure _
  | a :: as => by unfold NonDetE.mapMEx; exact ste_bind (h a) fun _ => ste_mapMEx h as

theorem ste_mapME {α β : Type} {f : α → NonDetE (State Unit) ε β} (h : ∀ a, STKE t0 (f a)) :
    ∀ xs : List α, STKE t0 (NonDetE.mapME f xs)
  | [] => by unfold NonDetE.mapME; exact ste_pure _
  | a :: as => by
    unfold NonDetE.mapME; exact ste_bind (h a) fun _ => ste_bind (ste_mapME h as) fun _ => ste_pure _

end CombE

theorem not_tcb_sc (y : SchedContext) (n : Nat) : ∀ x, KernelObject.schedContext y n ≠ .tcb x := fun _ h => by cases h
theorem not_tcb_cnode (r : Nat) (c : CnodeContents) : ∀ x, KernelObject.cnode r c ≠ .tcb x := fun _ h => by cases h
theorem not_tcb_ep (x : Endpoint) : ∀ y, KernelObject.endpoint x ≠ .tcb y := fun _ h => by cases h
theorem not_tcb_ntfn (x : Notification) : ∀ y, KernelObject.notification x ≠ .tcb y := fun _ h => by cases h
theorem not_tcb_reply (x : Reply) : ∀ y, KernelObject.reply x ≠ .tcb y := fun _ h => by cases h
theorem not_tcb_arch (x : ArchKernelObj) : ∀ y, KernelObject.archObj x ≠ .tcb y := fun _ h => by cases h

/-- One step of an `STK t0` proof. -/
macro "st_step0" : tactic => `(tactic| first
  | with_reducible exact st_pure _ | with_reducible exact st_pure' _ | with_reducible exact st_fail
  | with_reducible exact st_gets _ | with_reducible exact st_get
  | with_reducible exact st_assert _ | with_reducible exact st_assertOpt _
  | with_reducible exact st_getsThe _
  | with_reducible exact st_selectF _ | with_reducible exact st_select _
  | ((with_reducible apply st_modify); intro _; exact ⟨rfl, rfl⟩)
  | ((with_reducible apply st_get_put); intro _; exact ⟨rfl, rfl⟩)
  | (exact st_get_put' (fun _ => ⟨rfl, rfl⟩))
  | (exact st_get_put (fun _ => ⟨rfl, rfl⟩))
  | with_reducible exact st_getObject _
  | with_reducible exact st_doMachineOp _ | with_reducible exact st_doExtendedOp _
  | (with_reducible refine st_bind_pure ?_) | (with_reducible exact st_fail_bind)
  | (with_reducible refine st_bind ?_ (fun _ => ?_))
  | (with_reducible refine st_bind' ?_ (fun _ => ?_))
  | (with_reducible apply st_ite) | (with_reducible apply st_when) | (with_reducible apply st_unless)
  | (with_reducible refine st_maybeM (fun _ => ?_) _) | (with_reducible apply st_liftM)
  | (with_reducible refine st_whileLoop (fun _ => ?_) _)
  | (with_reducible refine st_mapMx (fun _ => ?_) _)
  | (with_reducible refine st_mapM (fun _ => ?_) _)
  | (with_reducible refine st_forMx (fun _ => ?_) _)
  | with_reducible exact ste_pure _ | with_reducible exact ste_returnOk _ | with_reducible exact ste_throw _
  | with_reducible exact ste_throw' _ | with_reducible exact ste_throwOpt _ _ | with_reducible exact ste_assertE _
  | (with_reducible refine ste_bind ?_ (fun _ => ?_))
  | (with_reducible apply ste_liftE) | (with_reducible apply ste_ite) | (with_reducible apply ste_whenE)
  | (with_reducible apply ste_unlessE) | (with_reducible refine st_catch ?_ (fun _ => ?_))
  | (with_reducible refine ste_handleE ?_ (fun _ => ?_)) | (with_reducible apply ste_liftME)
  | (with_reducible refine ste_mapMEx (fun _ => ?_) _) | (with_reducible refine ste_mapME (fun _ => ?_) _)
  | with_reducible exact not_tcb_sc _ _ | with_reducible exact not_tcb_cnode _ _
  | with_reducible exact not_tcb_ep _ | with_reducible exact not_tcb_ntfn _ | with_reducible exact not_tcb_reply _
  | with_reducible exact not_tcb_arch _
  | with_reducible exact fun _ => not_tcb_ep _ | with_reducible exact fun _ => not_tcb_ntfn _
  | with_reducible exact fun _ => not_tcb_reply _
  | (with_reducible intro _; exact rfl)
  | split
  | (dsimp only)
  | (simp only [letFun])
  | (dsimp only [letFun])
  | (with_reducible exact st_pure _)
  | (exact st_pure _))

macro "st_auto0" : tactic => `(tactic| repeat' st_step0)

/-- An `STK t0` lemma of a spec function (extended below, one rule per lemma). -/
syntax "st_leaf" : tactic
macro_rules | `(tactic| st_leaf) => `(tactic| fail "no st_leaf")

macro "st_auto" : tactic => `(tactic| repeat' (first | st_leaf | st_step0))

/-! ## Object steps -/

/-- The outcome of `set_object`: the object there had the same type. -/
theorem st_setObject_mem {σ : State Unit} {p : ObjRef} {o : KernelObject} {x : Unit × State Unit}
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

/-- `set_object` of an object other than a TCB. -/
theorem st_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ y, o ≠ .tcb y) :
    STK t0 (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨k, -, -, e⟩ := st_setObject_mem hx
  rw [e]
  refine ⟨fun q y _ hq => ?_, rfl⟩
  by_cases hqp : q = p
  · subst hqp; simp only [Function.update_self, Option.some.injEq] at hq; exact absurd hq (ho y)
  · simp only [Function.update_of_ne hqp] at hq; exact ⟨y, hq, rfl⟩
macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible refine st_setObject _ _ ?_)

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
    obtain ⟨k', -, -, e⟩ := st_setObject_mem (o := .schedContext (f sc) n) hx
    exact ⟨sc, n, hk, e⟩
  | _ => exact hx.elim

/-- `update_sched_context`. -/
theorem st_updateSchedContext (q : ObjRef) (f : SchedContext → SchedContext) :
    STK t0 (updateSchedContext (Z := Unit) q f) := by
  intro σ x hx
  obtain ⟨sc, n, hk, e⟩ := updSc_mem hx
  rw [e]
  refine ⟨fun r z _ hr => ?_, rfl⟩
  by_cases hrq : r = q
  · subst hrq; simp at hr
  · simp only [Function.update_of_ne hrq] at hr; exact ⟨z, hr, rfl⟩
macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_updateSchedContext _ _)


theorem st_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α)
    (hC : ∀ y, C e ≠ .tcb y) : STK t0 (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo
  exact st_bind (st_getObject _) fun _ => st_bind (st_assert _) fun _ => st_bind (st_assert _) fun _ =>
    st_setObject _ _ hC
macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible refine st_setSimpleKo' _ _ _ ?_)

theorem st_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef)
    (hC : ∀ e y, C e ≠ .tcb y) : STK t0 (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef getSimpleKo
  refine st_bind (st_bind (st_getObject _) fun _ => st_bind (st_assert _) fun _ => ?_) fun _ =>
    st_setSimpleKo' _ _ _ (hC _)
  split
  · exact st_pure _
  · exact st_fail
macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible refine st_updateSkObjRef' _ _ _ _ ?_)

/-! ## The thread steps -/

/-- `set_object` at `t0`. -/
theorem st_setObject_t0 (o : KernelObject) : STK t0 (setObject (Z := Unit) t0 o) := by
  intro σ x hx
  obtain ⟨k, -, -, e⟩ := st_setObject_mem hx
  rw [e]
  refine ⟨fun q y hq h => ?_, rfl⟩
  simp only [Function.update_of_ne hq] at h; exact ⟨y, h, rfl⟩

theorem st_threadSet_t0 (f : Tcb → Tcb) : STK t0 (threadSet (Z := Unit) f t0) := by
  unfold threadSet
  exact st_bind (st_getsThe _) fun _ => st_setObject_t0 _

theorem st_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : STK t0 (threadGet (Z := Unit) f t) := by
  unfold threadGet; st_auto
macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_threadGet' _ _)

theorem st_getThreadState' (t : ObjRef) : STK t0 (getThreadState (Z := Unit) t) := by
  unfold getThreadState; st_auto
macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_getThreadState' _)

theorem st_setThreadState_t0 (ts : ThreadState) : STK t0 (setThreadState (Z := Unit) t0 ts) := by
  unfold setThreadState
  refine st_bind (st_threadSet_t0 _) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; st_auto
macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_setThreadState_t0 _)

theorem st_asUser_t0 {α : Type} (u : UserMonad α) : STK t0 (asUser (Z := Unit) t0 u) := by
  unfold asUser
  refine st_bind (st_getsThe _) fun _ => st_bind (st_pure _) fun _ => st_bind (st_selectF _) fun _ =>
    st_bind (st_pure _) fun _ => st_bind (st_setObject_t0 _) fun _ => st_pure _

theorem st_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    STK t0 (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; st_auto
macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_getSimpleKo' _ _)

theorem st_getSchedContext' (q : ObjRef) : STK t0 (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; st_auto
macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_getSchedContext' _)

theorem st_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) :
    STK t0 (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; st_auto
macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_getSkObjRef' _ _ _)

theorem st_tcbEpDequeue (e : ObjRef) : STK t0 (tcbEpDequeue (Z := Unit) t0 e) := by
  unfold tcbEpDequeue setEndpoint; st_auto
macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_tcbEpDequeue _)

theorem st_tcbNtfnDequeue (n : ObjRef) : STK t0 (tcbNtfnDequeue (Z := Unit) t0 n) := by
  unfold tcbNtfnDequeue setNotification; st_auto
macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_tcbNtfnDequeue _)

theorem st_replyUnlinkTcb (r : ObjRef) : STK t0 (replyUnlinkTcb (Z := Unit) t0 r) := by
  unfold replyUnlinkTcb setReplyObjRef; st_auto
macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_replyUnlinkTcb _)

theorem st_replyRemoveTcb (r : ObjRef) : STK t0 (replyRemoveTcb (Z := Unit) t0 r) := by
  unfold replyRemoveTcb setReplyObjRef; st_auto
macro_rules | `(tactic| st_leaf) => `(tactic| with_reducible exact st_replyRemoveTcb _)

theorem st_cancelIpc : STK t0 (cancelIpc (Z := Unit) t0) := by
  unfold cancelIpc
  refine st_bind (st_getThreadState' _) fun _ => st_bind (st_threadSet_t0 _) fun _ => ?_
  unfold cancelSignal blockedCancelIpc getBlockingObject
  st_auto

theorem st_tcbSchedAction (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    STK t0 (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction getTcbQueue setTcbQueue; st_auto

theorem st_tcbReleaseRemove (t : ObjRef) : STK t0 (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; st_auto

theorem st_cancelYieldTo : STK t0 (schedContextCancelYieldTo (Z := Unit) t0) := by
  unfold schedContextCancelYieldTo getTcbObjRef
  refine st_bind (st_threadGet' _ _) fun o => ?_
  cases o
  · exact st_pure' _
  · exact st_bind (st_updateSchedContext _ _) fun _ => st_threadSet_t0 _

theorem st_suspend : STK t0 (suspend (Z := Unit) t0) := by
  unfold suspend updateRestartPc
  refine st_bind st_cancelIpc fun _ => st_bind (st_getThreadState' _) fun _ => ?_
  refine st_bind (st_when _ (st_asUser_t0 _)) fun _ => ?_
  exact st_bind (st_tcbSchedAction _ _) fun _ => st_bind (st_tcbReleaseRemove _) fun _ =>
    st_bind st_cancelYieldTo fun _ => st_setThreadState_t0 _

end

end Fl4Proofs.P3.StK
