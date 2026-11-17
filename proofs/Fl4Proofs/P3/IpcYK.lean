/-
P3 (DESIGN.md §9), TCB invocations: **a frame of the yield-to links** (spec
side only), in the shape of IpcTscK's `TSK`.

`YKS σ σ'`: every object keeps its yield view (`yv`: a TCB's
`tcb_yield_to`, an SC's `sc_yield_from` and size). `YKM m`: every outcome
of `m` is `YKS`-related to its start (`yk_auto`), up to `cancel_ipc`
(`yk_cancelIpc`). `YKS.ykeep`: ScYield's `YKeep`, for `YieldRel.frame`.

Used by Suspend (IpcSuspend's `suspend_irelY`): `YieldRel` across
`cancel_ipc`, the restart PC, the dequeue and the release-queue removal.
-/
import Fl4Proofs.P3.ScYield
open Classical

namespace Fl4Proofs.P3.YK
open Fl4Spec

noncomputable section

/-- The yield view of an object: a TCB's `tcb_yield_to`, an SC's
`sc_yield_from` and size, nothing else. -/
def yv : Option KernelObject → Nat × Option ObjRef × Nat
  | some (.tcb x) => (1, x.tcbYieldTo, 0)
  | some (.schedContext y n) => (2, y.scYieldFrom, n)
  | _ => (0, none, 0)

/-- Every object keeps its yield view. -/
def YKS (σ σ' : State Unit) : Prop := ∀ p, yv (σ'.kheap p) = yv (σ.kheap p)

theorem YKS.refl (σ : State Unit) : YKS σ σ := fun _ => rfl

theorem YKS.trans {σ1 σ2 σ3 : State Unit} (h1 : YKS σ1 σ2) (h2 : YKS σ2 σ3) : YKS σ1 σ3 :=
  fun p => (h2 p).trans (h1 p)

theorem YKS.of_kheap {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) : YKS σ σ' := by
  intro p; rw [h]

theorem yv_tcb {o : Option KernelObject} {a : Option ObjRef} {b : Nat} (h : yv o = (1, a, b)) :
    ∃ y, o = some (.tcb y) ∧ y.tcbYieldTo = a := by
  rcases o with _ | o
  · simp [yv] at h
  · cases o <;> simp [yv] at h
    exact ⟨_, rfl, h.1⟩

theorem yv_sc {o : Option KernelObject} {a : Option ObjRef} {b : Nat} (h : yv o = (2, a, b)) :
    ∃ y, o = some (.schedContext y b) ∧ y.scYieldFrom = a := by
  rcases o with _ | o
  · simp [yv] at h
  · cases o <;> simp [yv] at h
    obtain ⟨h1, rfl⟩ := h
    exact ⟨_, rfl, h1⟩

/-- **`YKS` gives ScYield's `YKeep`.** -/
theorem YKS.ykeep {σ σ' : State Unit} (h : YKS σ σ') : Sched.YKeep σ σ' := by
  refine ⟨fun p x hp => ?_, fun p x n hp => ?_, fun p y n hp => ?_⟩
  · have e := h p; rw [hp] at e
    obtain ⟨y, hy, ey⟩ := yv_tcb e
    exact ⟨y, hy, ey⟩
  · have e := h p; rw [hp] at e
    obtain ⟨y, hy, ey⟩ := yv_sc e
    exact ⟨y, hy, ey⟩
  · have e := (h p).symm; rw [hp] at e
    obtain ⟨x, hx, ex⟩ := yv_sc e
    exact ⟨x, hx, ex.symm⟩

/-- Every outcome of `m` keeps the TCBs' bound SCs (backward). -/
def YKM {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → YKS σ x.2

section Comb

theorem yk_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : YKM m)
    (hg : ∀ a, YKM (g a)) : YKM (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem yk_bind_pure {α β : Type} {a : α} {g : α → NonDet (State Unit) β} (h : YKM (g a)) :
    YKM ((pure a : NonDet (State Unit) α) >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ x hx

theorem yk_fail_bind {α β : Type} {g : α → NonDet (State Unit) β} :
    YKM ((NonDet.fail : NonDet (State Unit) α) >>= g) := by
  intro σ x ⟨y, hy, _⟩
  exact hy.elim

theorem yk_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : YKM m)
    (hg : ∀ a, YKM (g a)) : YKM (NonDet.bind m g) := yk_bind hm hg

theorem yk_pure {α : Type} (a : α) : YKM (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact YKS.refl _

theorem yk_pure' {α : Type} (a : α) : YKM (NonDet.pure a : NonDet (State Unit) α) := yk_pure a

theorem yk_gets {α : Type} (g : State Unit → α) : YKM (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact YKS.refl _

theorem yk_get : YKM (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact YKS.refl _

theorem yk_assert (P : Prop) : YKM (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact YKS.refl _

theorem yk_fail {α : Type} : YKM (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem yk_assertOpt {α : Type} (o : Option α) : YKM (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact yk_fail
  · exact yk_pure' _

theorem yk_getsThe {α : Type} (g : State Unit → Option α) : YKM (NonDet.getsThe g) := by
  intro σ x hx; exact yk_assertOpt (g σ) σ x hx

theorem yk_selectF {α : Type} (S : Set α × Prop) : YKM (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact YKS.refl _

theorem yk_select {α : Type} (S : Set α) : YKM (NonDet.select S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact YKS.refl _

theorem yk_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : YKM m1)
    (h2 : YKM m2) : YKM (if P then m1 else m2) := by
  split <;> assumption

theorem yk_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : YKM m) :
    YKM (NonDet.when P m) := by
  unfold NonDet.when; exact yk_ite P h (yk_pure' _)

theorem yk_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : YKM m) :
    YKM (NonDet.unless P m) := by
  unfold NonDet.unless; exact yk_ite P (yk_pure' _) h

theorem yk_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, YKM (g a)) (o : Option α) :
    YKM (NonDet.maybeM g o) := by
  cases o
  · exact yk_pure' _
  · exact h _

theorem yk_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : YKM m) :
    YKM (NonDet.liftM g m) := yk_bind' h fun _ => yk_pure' _

theorem yk_modify {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap) :
    YKM (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact YKS.of_kheap (hg σ)

theorem yk_get_put {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap) :
    YKM (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact YKS.of_kheap (hg σ)

theorem yk_get_put' {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap) :
    YKM (do let s ← NonDet.get; NonDet.put (g s)) := yk_get_put hg

theorem yk_getObject (p : ObjRef) : YKM (getObject (Z := Unit) p) := yk_getsThe _

theorem yk_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, YKM (B r)) (r : α) : YKM (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => exact YKS.refl _
  | step _ hm _ ih => exact (hB _ _ _ hm).trans ih

theorem yk_mapMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, YKM (g a)) (xs : List α) :
    YKM (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact yk_pure' _
  | cons a xs' ih => exact yk_bind' (h a) fun _ => ih

theorem yk_forMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, YKM (g a)) (xs : List α) :
    YKM (NonDet.forMx xs g) := yk_mapMx h xs

theorem yk_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, YKM (g a)) (xs : List α) :
    YKM (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact yk_pure' _
  | cons a xs' ih => exact yk_bind' (h a) fun _ => yk_bind' ih fun _ => yk_pure' _

theorem yk_doMachineOp {α : Type} (mop : NonDet MachineState α) : YKM (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine yk_bind (yk_gets _) (fun _ => yk_bind (yk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact yk_bind (yk_modify (fun σ => rfl)) (fun _ => yk_pure _)

theorem yk_doExtendedOp (eop : DetExtMonad Unit) : YKM (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine yk_bind yk_get (fun _ => yk_bind (yk_selectF _) (fun _ => ?_))
  split
  exact yk_modify (fun σ => rfl)

end Comb

/-- `YKM` for the exception monad. -/
def YKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := YKM (ExceptT.run m)

section CombE
variable {ε : Type}

theorem yke_bind {α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β} (hm : YKE m)
    (hg : ∀ a, YKE (g a)) : YKE (m >>= g) := by
  unfold YKE; rw [ExceptT.run_bind]
  refine yk_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact yk_pure _

theorem yke_pure {α : Type} (a : α) : YKE (pure a : NonDetE (State Unit) ε α) := yk_pure _

theorem yke_returnOk {α : Type} (a : α) : YKE (NonDetE.returnOk a : NonDetE (State Unit) ε α) := yk_pure _

theorem yke_throw {α : Type} (e : ε) : YKE (NonDetE.throwError e : NonDetE (State Unit) ε α) := yk_pure _

theorem yke_throw' {α : Type} (e : ε) : YKE (throw e : NonDetE (State Unit) ε α) := yk_pure _

theorem yke_liftE {α : Type} {m : NonDet (State Unit) α} (h : YKM m) : YKE (NonDetE.liftE (ε := ε) m) := by
  unfold YKE NonDetE.liftE; rw [ExceptT.run_lift]
  exact yk_bind h fun _ => yk_pure _

theorem yke_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : YKE m1)
    (h2 : YKE m2) : YKE (if P then m1 else m2) := by
  split <;> assumption

theorem yke_whenE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : YKE m) :
    YKE (NonDetE.whenE P m) := by
  unfold NonDetE.whenE; exact yke_ite P h (yke_pure _)

theorem yke_unlessE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : YKE m) :
    YKE (NonDetE.unlessE P m) := by
  unfold NonDetE.unlessE; exact yke_ite P (yke_pure _) h

theorem yke_throwOpt {α : Type} (e : ε) (o : Option α) : YKE (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact yke_throw' e
  · exact yke_pure _

theorem yke_assertE (P : Prop) : YKE (NonDetE.assertE P : NonDetE (State Unit) ε Unit) :=
  yke_liftE (yk_assert P)

theorem yk_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : YKE m)
    (hh : ∀ e, YKM (h e)) : YKM (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine yk_bind' hm fun r => ?_
  cases r with
  | ok a => exact yk_pure' _
  | error e => exact hh e

theorem yke_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : YKE m) (hh : ∀ e, YKE (h e)) : YKE (NonDetE.handleE m h) := by
  unfold NonDetE.handleE YKE
  rw [ExceptT.run_mk]
  refine yk_bind' hm fun r => ?_
  cases r with
  | ok a => exact yk_pure' _
  | error e => exact hh e

theorem yke_liftME {α β : Type} (f : α → β) {m : NonDetE (State Unit) ε α} (h : YKE m) :
    YKE (NonDetE.liftME f m) := by
  unfold NonDetE.liftME; exact yke_bind h fun _ => yke_pure _

theorem yke_mapMEx {α β : Type} {f : α → NonDetE (State Unit) ε β} (h : ∀ a, YKE (f a)) :
    ∀ xs : List α, YKE (NonDetE.mapMEx f xs)
  | [] => by unfold NonDetE.mapMEx; exact yke_pure _
  | a :: rest => by unfold NonDetE.mapMEx; exact yke_bind (h a) fun _ => yke_mapMEx h rest

theorem yke_mapME {α β : Type} {f : α → NonDetE (State Unit) ε β} (h : ∀ a, YKE (f a)) :
    ∀ xs : List α, YKE (NonDetE.mapME f xs)
  | [] => by unfold NonDetE.mapME; exact yke_pure _
  | a :: rest => by
    unfold NonDetE.mapME; exact yke_bind (h a) fun _ => yke_bind (yke_mapME h rest) fun _ => yke_pure _

end CombE

theorem yo_ep (x : Endpoint) : ∀ k, aType k = aType (.endpoint x) → yv (some k) = yv (some (.endpoint x)) := by
  intro k hk; cases k <;> simp only [aType] at hk <;> (try split at hk) <;> first | rfl | exact nomatch hk
theorem yo_ntfn (x : Notification) : ∀ k, aType k = aType (.notification x) →
    yv (some k) = yv (some (.notification x)) := by
  intro k hk; cases k <;> simp only [aType] at hk <;> (try split at hk) <;> first | rfl | exact nomatch hk
theorem yo_reply (x : Reply) : ∀ k, aType k = aType (.reply x) → yv (some k) = yv (some (.reply x)) := by
  intro k hk; cases k <;> simp only [aType] at hk <;> (try split at hk) <;> first | rfl | exact nomatch hk

/-- One step of an `YKM` proof. -/
macro "yk_step0" : tactic => `(tactic| first
  | with_reducible exact yk_pure _ | with_reducible exact yk_pure' _ | with_reducible exact yk_fail
  | with_reducible exact yk_gets _ | with_reducible exact yk_get
  | with_reducible exact yk_assert _ | with_reducible exact yk_assertOpt _
  | with_reducible exact yk_getsThe _
  | with_reducible exact yk_selectF _ | with_reducible exact yk_select _
  | ((with_reducible apply yk_modify); intro _; exact rfl)
  | ((with_reducible apply yk_get_put); intro _; exact rfl)
  | (exact yk_get_put' (fun _ => rfl))
  | (exact yk_get_put (fun _ => rfl))
  | with_reducible exact yk_getObject _
  | with_reducible exact yk_doMachineOp _ | with_reducible exact yk_doExtendedOp _
  | (with_reducible refine yk_bind_pure ?_) | (with_reducible exact yk_fail_bind)
  | (with_reducible refine yk_bind ?_ (fun _ => ?_))
  | (with_reducible refine yk_bind' ?_ (fun _ => ?_))
  | (with_reducible apply yk_ite) | (with_reducible apply yk_when) | (with_reducible apply yk_unless)
  | (with_reducible refine yk_maybeM (fun _ => ?_) _) | (with_reducible apply yk_liftM)
  | (with_reducible refine yk_whileLoop (fun _ => ?_) _)
  | (with_reducible refine yk_mapMx (fun _ => ?_) _)
  | (with_reducible refine yk_mapM (fun _ => ?_) _)
  | (with_reducible refine yk_forMx (fun _ => ?_) _)
  | with_reducible exact yke_pure _ | with_reducible exact yke_returnOk _ | with_reducible exact yke_throw _
  | with_reducible exact yke_throw' _ | with_reducible exact yke_throwOpt _ _ | with_reducible exact yke_assertE _
  | (with_reducible refine yke_bind ?_ (fun _ => ?_))
  | (with_reducible apply yke_liftE) | (with_reducible apply yke_ite) | (with_reducible apply yke_whenE)
  | (with_reducible apply yke_unlessE) | (with_reducible refine yk_catch ?_ (fun _ => ?_))
  | (with_reducible refine yke_handleE ?_ (fun _ => ?_)) | (with_reducible apply yke_liftME)
  | (with_reducible refine yke_mapMEx (fun _ => ?_) _) | (with_reducible refine yke_mapME (fun _ => ?_) _)
  | with_reducible exact yo_ep _ | with_reducible exact yo_ntfn _ | with_reducible exact yo_reply _
  | with_reducible exact fun _ => yo_ep _ | with_reducible exact fun _ => yo_ntfn _
  | with_reducible exact fun _ => yo_reply _
  | (with_reducible intro _; exact rfl)
  | (intro _; rfl)
  | split
  | (dsimp only)
  | (simp only [letFun])
  | (dsimp only [letFun])
  | (with_reducible exact yk_pure _)
  | (exact yk_pure _))

macro "yk_auto0" : tactic => `(tactic| repeat' yk_step0)

/-- An `YKM` lemma of a spec function (extended below, one rule per lemma). -/
syntax "yk_leaf" : tactic
macro_rules | `(tactic| yk_leaf) => `(tactic| fail "no yk_leaf")

macro "yk_auto" : tactic => `(tactic| repeat' (first | yk_leaf | yk_step0))

/-! ## Object steps -/

/-- The outcome of `set_object`: the object there had the same type. -/
theorem yk_setObject_mem {σ : State Unit} {p : ObjRef} {o : KernelObject} {x : Unit × State Unit}
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

/-- `set_object` of an object keeping the yield view of what it replaces. -/
theorem yk_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ k, aType k = aType o → yv (some k) = yv (some o)) :
    YKM (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨k, hk, hty, e⟩ := yk_setObject_mem hx
  rw [e]
  intro q
  by_cases hqp : q = p
  · subst hqp; simp only [Function.update_self, hk]; exact (ho k hty).symm
  · simp only [Function.update_of_ne hqp]
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible refine yk_setObject _ _ ?_)

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
    obtain ⟨k', -, -, e⟩ := yk_setObject_mem (o := .schedContext (f sc) n) hx
    exact ⟨sc, n, hk, e⟩
  | _ => exact hx.elim

/-- `update_sched_context` by a function keeping `sc_yield_from`. -/
theorem yk_updateSchedContext (q : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, (f y).scYieldFrom = y.scYieldFrom) : YKM (updateSchedContext (Z := Unit) q f) := by
  intro σ x hx
  obtain ⟨sc, n, hk, e⟩ := updSc_mem hx
  rw [e]
  intro r
  by_cases hrq : r = q
  · subst hrq; simp only [Function.update_self, hk, yv, hf]
  · simp only [Function.update_of_ne hrq]
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible refine yk_updateSchedContext _ _ ?_)


theorem yk_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α)
    (hC : ∀ k, aType k = aType (C e) → yv (some k) = yv (some (C e))) : YKM (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo
  exact yk_bind (yk_getObject _) fun _ => yk_bind (yk_assert _) fun _ => yk_bind (yk_assert _) fun _ =>
    yk_setObject _ _ hC
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible refine yk_setSimpleKo' _ _ _ ?_)

theorem yk_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef)
    (hC : ∀ e k, aType k = aType (C e) → yv (some k) = yv (some (C e))) :
    YKM (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef getSimpleKo
  refine yk_bind (yk_bind (yk_getObject _) fun _ => yk_bind (yk_assert _) fun _ => ?_) fun _ =>
    yk_setSimpleKo' _ _ _ (hC _)
  split
  · exact yk_pure _
  · exact yk_fail
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible refine yk_updateSkObjRef' _ _ _ _ ?_)

/-! ## The TCB steps -/

/-- `thread_set` by a function keeping `tcb_yield_to`. -/
theorem yk_threadSet (f : Tcb → Tcb) (hf : ∀ x, (f x).tcbYieldTo = x.tcbYieldTo) (t : ObjRef) :
    YKM (threadSet (Z := Unit) f t) := by
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
  obtain ⟨k, -, -, e⟩ := yk_setObject_mem hx
  rw [e]
  intro q
  by_cases hqp : q = t
  · subst hqp; simp only [Function.update_self, hk0, yv, hf]
  · simp only [Function.update_of_ne hqp]

theorem yk_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : YKM (threadGet (Z := Unit) f t) := by
  unfold threadGet; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_threadGet' _ _)

theorem yk_setThreadState' (t : ObjRef) (ts : ThreadState) : YKM (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine yk_bind (yk_threadSet (fun tcb => { tcb with tcbState := ts }) (fun _ => rfl) t) fun _ => ?_
  unfold setThreadStateAct setSchedulerAction; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_setThreadState' _ _)

theorem yk_getThreadState' (t : ObjRef) : YKM (getThreadState (Z := Unit) t) := by
  unfold getThreadState; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getThreadState' _)

theorem yk_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    YKM (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getSimpleKo' _ _)

theorem yk_getSchedContext' (q : ObjRef) : YKM (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getSchedContext' _)

theorem yk_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) :
    YKM (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getSkObjRef' _ _ _)

theorem yk_tcbEpDequeue (t e : ObjRef) : YKM (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue setEndpoint; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_tcbEpDequeue _ _)

theorem yk_tcbNtfnDequeue (t n : ObjRef) : YKM (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue setNotification; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_tcbNtfnDequeue _ _)

theorem yk_replyUnlinkTcb (t r : ObjRef) : YKM (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb setReplyObjRef; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_replyUnlinkTcb _ _)

theorem yk_replyRemoveTcb (t r : ObjRef) : YKM (replyRemoveTcb (Z := Unit) t r) := by
  unfold replyRemoveTcb setReplyObjRef; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_replyRemoveTcb _ _)

theorem yk_cancelIpc (t : ObjRef) : YKM (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc
  refine yk_bind (yk_getThreadState' _) fun st =>
    yk_bind (yk_threadSet (fun tcb => { tcb with tcbFault := none }) (fun _ => rfl) t) fun _ => ?_
  unfold cancelSignal blockedCancelIpc getBlockingObject
  yk_auto

macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible refine yk_threadSet _ ?_ _)

theorem yk_tcbSchedAction (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    YKM (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction getTcbQueue setTcbQueue; yk_auto

theorem yk_tcbReleaseRemove (t : ObjRef) : YKM (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove setReleaseQueue; yk_auto

/-- A TCB update keeping `tcb_yield_to`. -/
theorem YKS.updTcb {σ : State Unit} {p : ObjRef} {x y : Tcb} (hk : σ.kheap p = some (.tcb x))
    (hy : y.tcbYieldTo = x.tcbYieldTo) : YKS σ (Notif.updK σ p (.tcb y)) := by
  intro q
  by_cases e : q = p
  · subst e; simp [Notif.updK, hk, yv, hy]
  · simp [Notif.updK, Function.update_of_ne e]

end

end Fl4Proofs.P3.YK
