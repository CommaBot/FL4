/-
P3 (DESIGN.md §9), TCB invocations: **a backward frame of the TCBs' bound
SC** (spec side only), as ScMaxKeep's `SK`.

`TSK σ σ'`: every TCB of `σ'` was a TCB of `σ` at the same reference with
the same `tcb_sched_context`. `SK m`: every outcome of `m` is `TSK`-related
to its start (`sk_auto`), up to `cancel_ipc` and `set_thread_state`
(`sk_cancelIpc`, `sk_setThreadState'`).

Used by Resume (IpcResume): the spec's `restart` reads the thread's SC before
`cancel_ipc` and `set_thread_state`, FL4 after.
-/
import Fl4Spec.Ext.Invocation
import Fl4Spec.Ext.VSpace
open Classical

namespace Fl4Proofs.P3.TscK
open Fl4Spec

noncomputable section

/-- Every TCB of `σ'` was one of `σ`, with the same bound SC; the ready
queues and the current thread are kept. -/
def TSK (σ σ' : State Unit) : Prop :=
  (∀ p y, σ'.kheap p = some (.tcb y) → ∃ y0, σ.kheap p = some (.tcb y0) ∧ y.tcbSchedContext = y0.tcbSchedContext) ∧
  σ'.readyQueues = σ.readyQueues ∧ σ'.curThread = σ.curThread

theorem TSK.refl (σ : State Unit) : TSK σ σ := ⟨fun _ y h => ⟨y, h, rfl⟩, rfl, rfl⟩

theorem TSK.trans {σ1 σ2 σ3 : State Unit} (h1 : TSK σ1 σ2) (h2 : TSK σ2 σ3) : TSK σ1 σ3 := by
  refine ⟨fun p y h => ?_, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩
  obtain ⟨y2, h2', e1⟩ := h2.1 p y h
  obtain ⟨y1, h1', f1⟩ := h1.1 p y2 h2'
  exact ⟨y1, h1', e1.trans f1⟩

theorem TSK.of_kheap {σ σ' : State Unit}
    (h : σ'.kheap = σ.kheap ∧ σ'.readyQueues = σ.readyQueues ∧ σ'.curThread = σ.curThread) : TSK σ σ' := by
  refine ⟨fun p y hp => ?_, h.2⟩; rw [h.1] at hp; exact ⟨y, hp, rfl⟩

/-- Every outcome of `m` keeps the TCBs' bound SCs (backward). -/
def SK {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → TSK σ x.2

section Comb

theorem sk_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : SK m)
    (hg : ∀ a, SK (g a)) : SK (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem sk_bind_pure {α β : Type} {a : α} {g : α → NonDet (State Unit) β} (h : SK (g a)) :
    SK ((pure a : NonDet (State Unit) α) >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ x hx

theorem sk_fail_bind {α β : Type} {g : α → NonDet (State Unit) β} :
    SK ((NonDet.fail : NonDet (State Unit) α) >>= g) := by
  intro σ x ⟨y, hy, _⟩
  exact hy.elim

theorem sk_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : SK m)
    (hg : ∀ a, SK (g a)) : SK (NonDet.bind m g) := sk_bind hm hg

theorem sk_pure {α : Type} (a : α) : SK (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact TSK.refl _

theorem sk_pure' {α : Type} (a : α) : SK (NonDet.pure a : NonDet (State Unit) α) := sk_pure a

theorem sk_gets {α : Type} (g : State Unit → α) : SK (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact TSK.refl _

theorem sk_get : SK (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact TSK.refl _

theorem sk_assert (P : Prop) : SK (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact TSK.refl _

theorem sk_fail {α : Type} : SK (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem sk_assertOpt {α : Type} (o : Option α) : SK (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact sk_fail
  · exact sk_pure' _

theorem sk_getsThe {α : Type} (g : State Unit → Option α) : SK (NonDet.getsThe g) := by
  intro σ x hx; exact sk_assertOpt (g σ) σ x hx

theorem sk_selectF {α : Type} (S : Set α × Prop) : SK (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact TSK.refl _

theorem sk_select {α : Type} (S : Set α) : SK (NonDet.select S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact TSK.refl _

theorem sk_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : SK m1)
    (h2 : SK m2) : SK (if P then m1 else m2) := by
  split <;> assumption

theorem sk_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : SK m) :
    SK (NonDet.when P m) := by
  unfold NonDet.when; exact sk_ite P h (sk_pure' _)

theorem sk_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : SK m) :
    SK (NonDet.unless P m) := by
  unfold NonDet.unless; exact sk_ite P (sk_pure' _) h

theorem sk_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, SK (g a)) (o : Option α) :
    SK (NonDet.maybeM g o) := by
  cases o
  · exact sk_pure' _
  · exact h _

theorem sk_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : SK m) :
    SK (NonDet.liftM g m) := sk_bind' h fun _ => sk_pure' _

theorem sk_modify {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap ∧ (g σ).readyQueues = σ.readyQueues ∧ (g σ).curThread = σ.curThread) :
    SK (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact TSK.of_kheap (hg σ)

theorem sk_get_put {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap ∧ (g σ).readyQueues = σ.readyQueues ∧ (g σ).curThread = σ.curThread) :
    SK (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact TSK.of_kheap (hg σ)

theorem sk_get_put' {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap ∧ (g σ).readyQueues = σ.readyQueues ∧ (g σ).curThread = σ.curThread) :
    SK (do let s ← NonDet.get; NonDet.put (g s)) := sk_get_put hg

theorem sk_getObject (p : ObjRef) : SK (getObject (Z := Unit) p) := sk_getsThe _

theorem sk_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, SK (B r)) (r : α) : SK (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => exact TSK.refl _
  | step _ hm _ ih => exact (hB _ _ _ hm).trans ih

theorem sk_mapMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, SK (g a)) (xs : List α) :
    SK (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact sk_pure' _
  | cons a xs' ih => exact sk_bind' (h a) fun _ => ih

theorem sk_forMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, SK (g a)) (xs : List α) :
    SK (NonDet.forMx xs g) := sk_mapMx h xs

theorem sk_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, SK (g a)) (xs : List α) :
    SK (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact sk_pure' _
  | cons a xs' ih => exact sk_bind' (h a) fun _ => sk_bind' ih fun _ => sk_pure' _

theorem sk_doMachineOp {α : Type} (mop : NonDet MachineState α) : SK (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine sk_bind (sk_gets _) (fun _ => sk_bind (sk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact sk_bind (sk_modify (fun σ => ⟨rfl, rfl, rfl⟩)) (fun _ => sk_pure _)

theorem sk_doExtendedOp (eop : DetExtMonad Unit) : SK (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine sk_bind sk_get (fun _ => sk_bind (sk_selectF _) (fun _ => ?_))
  split
  exact sk_modify (fun σ => ⟨rfl, rfl, rfl⟩)

end Comb

/-- `SK` for the exception monad. -/
def SKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := SK (ExceptT.run m)

section CombE
variable {ε : Type}

theorem ske_bind {α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β} (hm : SKE m)
    (hg : ∀ a, SKE (g a)) : SKE (m >>= g) := by
  unfold SKE; rw [ExceptT.run_bind]
  refine sk_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact sk_pure _

theorem ske_pure {α : Type} (a : α) : SKE (pure a : NonDetE (State Unit) ε α) := sk_pure _

theorem ske_returnOk {α : Type} (a : α) : SKE (NonDetE.returnOk a : NonDetE (State Unit) ε α) := sk_pure _

theorem ske_throw {α : Type} (e : ε) : SKE (NonDetE.throwError e : NonDetE (State Unit) ε α) := sk_pure _

theorem ske_throw' {α : Type} (e : ε) : SKE (throw e : NonDetE (State Unit) ε α) := sk_pure _

theorem ske_liftE {α : Type} {m : NonDet (State Unit) α} (h : SK m) : SKE (NonDetE.liftE (ε := ε) m) := by
  unfold SKE NonDetE.liftE; rw [ExceptT.run_lift]
  exact sk_bind h fun _ => sk_pure _

theorem ske_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : SKE m1)
    (h2 : SKE m2) : SKE (if P then m1 else m2) := by
  split <;> assumption

theorem ske_whenE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : SKE m) :
    SKE (NonDetE.whenE P m) := by
  unfold NonDetE.whenE; exact ske_ite P h (ske_pure _)

theorem ske_unlessE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : SKE m) :
    SKE (NonDetE.unlessE P m) := by
  unfold NonDetE.unlessE; exact ske_ite P (ske_pure _) h

theorem ske_throwOpt {α : Type} (e : ε) (o : Option α) : SKE (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact ske_throw' e
  · exact ske_pure _

theorem ske_assertE (P : Prop) : SKE (NonDetE.assertE P : NonDetE (State Unit) ε Unit) :=
  ske_liftE (sk_assert P)

theorem sk_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : SKE m)
    (hh : ∀ e, SK (h e)) : SK (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine sk_bind' hm fun r => ?_
  cases r with
  | ok a => exact sk_pure' _
  | error e => exact hh e

theorem ske_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : SKE m) (hh : ∀ e, SKE (h e)) : SKE (NonDetE.handleE m h) := by
  unfold NonDetE.handleE SKE
  rw [ExceptT.run_mk]
  refine sk_bind' hm fun r => ?_
  cases r with
  | ok a => exact sk_pure' _
  | error e => exact hh e

theorem ske_liftME {α β : Type} (f : α → β) {m : NonDetE (State Unit) ε α} (h : SKE m) :
    SKE (NonDetE.liftME f m) := by
  unfold NonDetE.liftME; exact ske_bind h fun _ => ske_pure _

theorem ske_mapMEx {α β : Type} {f : α → NonDetE (State Unit) ε β} (h : ∀ a, SKE (f a)) :
    ∀ xs : List α, SKE (NonDetE.mapMEx f xs)
  | [] => by unfold NonDetE.mapMEx; exact ske_pure _
  | a :: as => by unfold NonDetE.mapMEx; exact ske_bind (h a) fun _ => ske_mapMEx h as

theorem ske_mapME {α β : Type} {f : α → NonDetE (State Unit) ε β} (h : ∀ a, SKE (f a)) :
    ∀ xs : List α, SKE (NonDetE.mapME f xs)
  | [] => by unfold NonDetE.mapME; exact ske_pure _
  | a :: as => by
    unfold NonDetE.mapME; exact ske_bind (h a) fun _ => ske_bind (ske_mapME h as) fun _ => ske_pure _

end CombE

theorem not_tcb_sc (y : SchedContext) (n : Nat) : ∀ x, KernelObject.schedContext y n ≠ .tcb x := fun _ h => by cases h
theorem not_tcb_cnode (r : Nat) (c : CnodeContents) : ∀ x, KernelObject.cnode r c ≠ .tcb x := fun _ h => by cases h
theorem not_tcb_ep (x : Endpoint) : ∀ y, KernelObject.endpoint x ≠ .tcb y := fun _ h => by cases h
theorem not_tcb_ntfn (x : Notification) : ∀ y, KernelObject.notification x ≠ .tcb y := fun _ h => by cases h
theorem not_tcb_reply (x : Reply) : ∀ y, KernelObject.reply x ≠ .tcb y := fun _ h => by cases h
theorem not_tcb_arch (x : ArchKernelObj) : ∀ y, KernelObject.archObj x ≠ .tcb y := fun _ h => by cases h

/-- One step of an `SK` proof. -/
macro "sk_step0" : tactic => `(tactic| first
  | with_reducible exact sk_pure _ | with_reducible exact sk_pure' _ | with_reducible exact sk_fail
  | with_reducible exact sk_gets _ | with_reducible exact sk_get
  | with_reducible exact sk_assert _ | with_reducible exact sk_assertOpt _
  | with_reducible exact sk_getsThe _
  | with_reducible exact sk_selectF _ | with_reducible exact sk_select _
  | ((with_reducible apply sk_modify); intro _; exact ⟨rfl, rfl, rfl⟩)
  | ((with_reducible apply sk_get_put); intro _; exact ⟨rfl, rfl, rfl⟩)
  | (exact sk_get_put' (fun _ => ⟨rfl, rfl, rfl⟩))
  | (exact sk_get_put (fun _ => ⟨rfl, rfl, rfl⟩))
  | with_reducible exact sk_getObject _
  | with_reducible exact sk_doMachineOp _ | with_reducible exact sk_doExtendedOp _
  | (with_reducible refine sk_bind_pure ?_) | (with_reducible exact sk_fail_bind)
  | (with_reducible refine sk_bind ?_ (fun _ => ?_))
  | (with_reducible refine sk_bind' ?_ (fun _ => ?_))
  | (with_reducible apply sk_ite) | (with_reducible apply sk_when) | (with_reducible apply sk_unless)
  | (with_reducible refine sk_maybeM (fun _ => ?_) _) | (with_reducible apply sk_liftM)
  | (with_reducible refine sk_whileLoop (fun _ => ?_) _)
  | (with_reducible refine sk_mapMx (fun _ => ?_) _)
  | (with_reducible refine sk_mapM (fun _ => ?_) _)
  | (with_reducible refine sk_forMx (fun _ => ?_) _)
  | with_reducible exact ske_pure _ | with_reducible exact ske_returnOk _ | with_reducible exact ske_throw _
  | with_reducible exact ske_throw' _ | with_reducible exact ske_throwOpt _ _ | with_reducible exact ske_assertE _
  | (with_reducible refine ske_bind ?_ (fun _ => ?_))
  | (with_reducible apply ske_liftE) | (with_reducible apply ske_ite) | (with_reducible apply ske_whenE)
  | (with_reducible apply ske_unlessE) | (with_reducible refine sk_catch ?_ (fun _ => ?_))
  | (with_reducible refine ske_handleE ?_ (fun _ => ?_)) | (with_reducible apply ske_liftME)
  | (with_reducible refine ske_mapMEx (fun _ => ?_) _) | (with_reducible refine ske_mapME (fun _ => ?_) _)
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
  | (with_reducible exact sk_pure _)
  | (exact sk_pure _))

macro "sk_auto0" : tactic => `(tactic| repeat' sk_step0)

/-- An `SK` lemma of a spec function (extended below, one rule per lemma). -/
syntax "sk_leaf" : tactic
macro_rules | `(tactic| sk_leaf) => `(tactic| fail "no sk_leaf")

macro "sk_auto" : tactic => `(tactic| repeat' (first | sk_leaf | sk_step0))

/-! ## Object steps -/

/-- The outcome of `set_object`: the object there had the same type. -/
theorem sk_setObject_mem {σ : State Unit} {p : ObjRef} {o : KernelObject} {x : Unit × State Unit}
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
theorem sk_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ y, o ≠ .tcb y) :
    SK (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨k, -, -, e⟩ := sk_setObject_mem hx
  rw [e]
  refine ⟨fun q y hq => ?_, rfl, rfl⟩
  by_cases hqp : q = p
  · subst hqp; simp only [Function.update_self, Option.some.injEq] at hq; exact absurd hq (ho y)
  · simp only [Function.update_of_ne hqp] at hq; exact ⟨y, hq, rfl⟩
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible refine sk_setObject _ _ ?_)

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
    obtain ⟨k', -, -, e⟩ := sk_setObject_mem (o := .schedContext (f sc) n) hx
    exact ⟨sc, n, hk, e⟩
  | _ => exact hx.elim

/-- `update_sched_context`. -/
theorem sk_updateSchedContext (q : ObjRef) (f : SchedContext → SchedContext) :
    SK (updateSchedContext (Z := Unit) q f) := by
  intro σ x hx
  obtain ⟨sc, n, hk, e⟩ := updSc_mem hx
  rw [e]
  refine ⟨fun r z hr => ?_, rfl, rfl⟩
  by_cases hrq : r = q
  · subst hrq; simp at hr
  · simp only [Function.update_of_ne hrq] at hr; exact ⟨z, hr, rfl⟩
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_updateSchedContext _ _)


theorem sk_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α)
    (hC : ∀ y, C e ≠ .tcb y) : SK (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo
  exact sk_bind (sk_getObject _) fun _ => sk_bind (sk_assert _) fun _ => sk_bind (sk_assert _) fun _ =>
    sk_setObject _ _ hC
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible refine sk_setSimpleKo' _ _ _ ?_)

theorem sk_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef)
    (hC : ∀ e y, C e ≠ .tcb y) : SK (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef getSimpleKo
  refine sk_bind (sk_bind (sk_getObject _) fun _ => sk_bind (sk_assert _) fun _ => ?_) fun _ =>
    sk_setSimpleKo' _ _ _ (hC _)
  split
  · exact sk_pure _
  · exact sk_fail
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible refine sk_updateSkObjRef' _ _ _ _ ?_)

/-! ## The TCB steps -/

/-- `thread_set` by a function keeping `tcb_sched_context`. -/
theorem sk_threadSet (f : Tcb → Tcb) (hf : ∀ x, (f x).tcbSchedContext = x.tcbSchedContext) (t : ObjRef) :
    SK (threadSet (Z := Unit) f t) := by
  intro σ x hx
  unfold threadSet at hx
  obtain ⟨y, hy, hx⟩ := hx
  have hy' : ∃ x0, σ.kheap t = some (.tcb x0) ∧ y = (x0, σ) := by
    unfold NonDet.getsThe getTcb readObject at hy
    cases h : σ.kheap t with
    | none => rw [h] at hy; exact hy.elim
    | some k =>
      rw [h] at hy
      cases k with
      | tcb x0 => exact ⟨x0, rfl, Set.mem_singleton_iff.1 hy⟩
      | _ => exact hy.elim
  obtain ⟨x0, hk0, rfl⟩ := hy'
  obtain ⟨k, -, -, e⟩ := sk_setObject_mem hx
  rw [e]
  refine ⟨fun q z hq => ?_, rfl, rfl⟩
  by_cases hqp : q = t
  · subst hqp
    simp only [Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hq
    subst hq
    exact ⟨x0, hk0, hf x0⟩
  · simp only [Function.update_of_ne hqp] at hq; exact ⟨z, hq, rfl⟩

theorem sk_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : SK (threadGet (Z := Unit) f t) := by
  unfold threadGet; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_threadGet' _ _)

theorem sk_setThreadState' (t : ObjRef) (ts : ThreadState) : SK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine sk_bind (sk_threadSet (fun tcb => { tcb with tcbState := ts }) (fun _ => rfl) t) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_setThreadState' _ _)

theorem sk_getThreadState' (t : ObjRef) : SK (getThreadState (Z := Unit) t) := by
  unfold getThreadState; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_getThreadState' _)

theorem sk_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    SK (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_getSimpleKo' _ _)

theorem sk_getSchedContext' (q : ObjRef) : SK (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_getSchedContext' _)

theorem sk_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) :
    SK (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_getSkObjRef' _ _ _)

theorem sk_tcbEpDequeue (t e : ObjRef) : SK (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue setEndpoint; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_tcbEpDequeue _ _)

theorem sk_tcbNtfnDequeue (t n : ObjRef) : SK (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue setNotification; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_tcbNtfnDequeue _ _)

theorem sk_replyUnlinkTcb (t r : ObjRef) : SK (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb setReplyObjRef; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_replyUnlinkTcb _ _)

theorem sk_replyRemoveTcb (t r : ObjRef) : SK (replyRemoveTcb (Z := Unit) t r) := by
  unfold replyRemoveTcb setReplyObjRef; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_replyRemoveTcb _ _)

theorem sk_cancelIpc (t : ObjRef) : SK (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc
  refine sk_bind (sk_getThreadState' _) fun st =>
    sk_bind (sk_threadSet (fun tcb => { tcb with tcbFault := none }) (fun _ => rfl) t) fun _ => ?_
  unfold cancelSignal blockedCancelIpc getBlockingObject
  sk_auto

/-! ## The refill steps -/

theorem sk_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : SK (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_getScRefillSufficient' _ _)


theorem sk_getScRefillReady' (sc : ObjRef) : SK (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_getScRefillReady' _)


theorem sk_isRoundRobin' (sc : ObjRef) : SK (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_isRoundRobin' _)


theorem sk_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : SK (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_updateRefillHd' _ _)


theorem sk_getRefillHead' (sc : ObjRef) : SK (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_getRefillHead' _)


theorem sk_refillPopHead' (sc : ObjRef) : SK (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_refillPopHead' _)


theorem sk_mergeOverlappingRefills' (sc : ObjRef) : SK (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_mergeOverlappingRefills' _)


theorem sk_refillHeadOverlappingLoop' (sc : ObjRef) : SK (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_refillHeadOverlappingLoop' _)


theorem sk_refillUnblockCheck' (sc : ObjRef) : SK (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_refillUnblockCheck' _)


theorem sk_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) : SK (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; sk_auto
macro_rules | `(tactic| sk_leaf) => `(tactic| with_reducible exact sk_ifCondRefillUnblockCheck' _ _ _)



/-- The sporadic unblock check of an SC (`restart`'s, after `set_thread_state`). -/
theorem sk_unblock (o : Option ObjRef) : SK (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) o) := by
  sk_auto

end

end Fl4Proofs.P3.TscK
