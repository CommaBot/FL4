/-
P3 (DESIGN.md §9), IPC: **a frame of the scheduler's view for the IPC wake
tails** (spec side only), in the shape of IpcQP's `SVS`.

`SVS σ σ'`: every object keeps its scheduler view (`sv`: a TCB's SC, an
SC's refills, `REFILL_MAX`, bound TCB and size), the time is kept, and the
scheduler action is kept or becomes `ChooseNewThread`. `SVM m`: every outcome
of `m` is `SVS`-related to its start (`sv_auto`).

`ActReadyW` (the switch target's SC, when bound and active, ready and
sufficient, with no `schedulable` precondition) and `SCBack` (a TCB's SC is
bound back to it) are `SVS`-stable, and so are the endpoint and notification
step classes (`EpStep`, `NtfnStep`). `ActReadyW` gives `ActReady`.
-/
import Fl4Proofs.P3.EpRel
import Fl4Spec.Ext.Invocation
import Fl4Spec.Ext.VSpace
open Classical

namespace Fl4Proofs.P3.SVK
open Fl4Spec

noncomputable section

/-- The scheduler view of an object: a TCB's SC; an SC's refills,
`REFILL_MAX`, bound TCB and size; nothing else. -/
def sv : Option KernelObject → Nat × Option ObjRef × List Refill × Nat × Option ObjRef × Nat
  | some (.tcb x) => (1, x.tcbSchedContext, [], 0, none, 0)
  | some (.schedContext y n) => (2, none, y.scRefills, y.scRefillMax, y.scTcb, n)
  | _ => (0, none, [], 0, none, 0)

/-- Every object keeps its scheduler view; the time kept; the action kept or
`ChooseNewThread`. -/
def SVS (σ σ' : State Unit) : Prop :=
  (∀ p, sv (σ'.kheap p) = sv (σ.kheap p)) ∧ σ'.curTime = σ.curTime ∧
    (σ'.schedulerAction = σ.schedulerAction ∨ σ'.schedulerAction = .chooseNewThread)

theorem SVS.refl (σ : State Unit) : SVS σ σ := ⟨fun _ => rfl, rfl, Or.inl rfl⟩

theorem SVS.trans {σ1 σ2 σ3 : State Unit} (h1 : SVS σ1 σ2) (h2 : SVS σ2 σ3) : SVS σ1 σ3 := by
  refine ⟨fun p => (h2.1 p).trans (h1.1 p), h2.2.1.trans h1.2.1, ?_⟩
  rcases h2.2.2 with e | e
  · rw [e]; exact h1.2.2
  · exact Or.inr e

theorem SVS.of_eq {σ σ' : State Unit}
    (h : σ'.kheap = σ.kheap ∧ σ'.curTime = σ.curTime ∧ σ'.schedulerAction = σ.schedulerAction) : SVS σ σ' :=
  ⟨fun p => by rw [h.1], h.2.1, Or.inl h.2.2⟩

theorem sv_tcb {o : Option KernelObject} {a : Option ObjRef} (h : sv o = (1, a, [], 0, none, 0)) :
    ∃ y, o = some (.tcb y) ∧ y.tcbSchedContext = a := by
  rcases o with _ | o
  · simp [sv] at h
  · cases o <;> simp [sv] at h
    exact ⟨_, rfl, h⟩

theorem sv_sc {o : Option KernelObject} {rf : List Refill} {m : Nat} {t : Option ObjRef} {n : Nat}
    (h : sv o = (2, none, rf, m, t, n)) :
    ∃ y, o = some (.schedContext y n) ∧ y.scRefills = rf ∧ y.scRefillMax = m ∧ y.scTcb = t := by
  rcases o with _ | o
  · simp [sv] at h
  · cases o <;> simp [sv] at h
    obtain ⟨h1, h2, h3, rfl⟩ := h
    exact ⟨_, rfl, h1, h2, h3⟩

/-- Every outcome of `m` keeps the release queue (backward). -/
def SVM {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → SVS σ x.2

section Comb

theorem sv_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : SVM m)
    (hg : ∀ a, SVM (g a)) : SVM (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem sv_bind_pure {α β : Type} {a : α} {g : α → NonDet (State Unit) β} (h : SVM (g a)) :
    SVM ((pure a : NonDet (State Unit) α) >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ x hx

theorem sv_fail_bind {α β : Type} {g : α → NonDet (State Unit) β} :
    SVM ((NonDet.fail : NonDet (State Unit) α) >>= g) := by
  intro σ x ⟨y, hy, _⟩
  exact hy.elim

theorem sv_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : SVM m)
    (hg : ∀ a, SVM (g a)) : SVM (NonDet.bind m g) := sv_bind hm hg

theorem sv_pure {α : Type} (a : α) : SVM (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SVS.refl _

theorem sv_pure' {α : Type} (a : α) : SVM (NonDet.pure a : NonDet (State Unit) α) := sv_pure a

theorem sv_gets {α : Type} (g : State Unit → α) : SVM (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SVS.refl _

theorem sv_get : SVM (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SVS.refl _

theorem sv_assert (P : Prop) : SVM (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact SVS.refl _

theorem sv_fail {α : Type} : SVM (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem sv_assertOpt {α : Type} (o : Option α) : SVM (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact sv_fail
  · exact sv_pure' _

theorem sv_getsThe {α : Type} (g : State Unit → Option α) : SVM (NonDet.getsThe g) := by
  intro σ x hx; exact sv_assertOpt (g σ) σ x hx

theorem sv_selectF {α : Type} (S : Set α × Prop) : SVM (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact SVS.refl _

theorem sv_select {α : Type} (S : Set α) : SVM (NonDet.select S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact SVS.refl _

theorem sv_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : SVM m1)
    (h2 : SVM m2) : SVM (if P then m1 else m2) := by
  split <;> assumption

theorem sv_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : SVM m) :
    SVM (NonDet.when P m) := by
  unfold NonDet.when; exact sv_ite P h (sv_pure' _)

theorem sv_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : SVM m) :
    SVM (NonDet.unless P m) := by
  unfold NonDet.unless; exact sv_ite P (sv_pure' _) h

theorem sv_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, SVM (g a)) (o : Option α) :
    SVM (NonDet.maybeM g o) := by
  cases o
  · exact sv_pure' _
  · exact h _

theorem sv_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : SVM m) :
    SVM (NonDet.liftM g m) := sv_bind' h fun _ => sv_pure' _

theorem sv_modify {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap ∧ (g σ).curTime = σ.curTime ∧ (g σ).schedulerAction = σ.schedulerAction) :
    SVM (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SVS.of_eq (hg σ)

theorem sv_get_put {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap ∧ (g σ).curTime = σ.curTime ∧ (g σ).schedulerAction = σ.schedulerAction) :
    SVM (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact SVS.of_eq (hg σ)

theorem sv_get_put' {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap ∧ (g σ).curTime = σ.curTime ∧ (g σ).schedulerAction = σ.schedulerAction) :
    SVM (do let s ← NonDet.get; NonDet.put (g s)) := sv_get_put hg

theorem sv_getObject (p : ObjRef) : SVM (getObject (Z := Unit) p) := sv_getsThe _

theorem sv_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, SVM (B r)) (r : α) : SVM (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => exact SVS.refl _
  | step _ hm _ ih => exact (hB _ _ _ hm).trans ih

theorem sv_mapMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, SVM (g a)) (xs : List α) :
    SVM (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact sv_pure' _
  | cons a xs' ih => exact sv_bind' (h a) fun _ => ih

theorem sv_forMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, SVM (g a)) (xs : List α) :
    SVM (NonDet.forMx xs g) := sv_mapMx h xs

theorem sv_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, SVM (g a)) (xs : List α) :
    SVM (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact sv_pure' _
  | cons a xs' ih => exact sv_bind' (h a) fun _ => sv_bind' ih fun _ => sv_pure' _

theorem sv_doMachineOp {α : Type} (mop : NonDet MachineState α) : SVM (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine sv_bind (sv_gets _) (fun _ => sv_bind (sv_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact sv_bind (sv_modify (fun σ => ⟨rfl, rfl, rfl⟩)) (fun _ => sv_pure _)

theorem sv_doExtendedOp (eop : DetExtMonad Unit) : SVM (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine sv_bind sv_get (fun _ => sv_bind (sv_selectF _) (fun _ => ?_))
  split
  exact sv_modify (fun σ => ⟨rfl, rfl, rfl⟩)

end Comb

/-- `SVM` for the exception monad. -/
def SVE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := SVM (ExceptT.run m)

section CombE
variable {ε : Type}

theorem sve_bind {α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β} (hm : SVE m)
    (hg : ∀ a, SVE (g a)) : SVE (m >>= g) := by
  unfold SVE; rw [ExceptT.run_bind]
  refine sv_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact sv_pure _

theorem sve_pure {α : Type} (a : α) : SVE (pure a : NonDetE (State Unit) ε α) := sv_pure _

theorem sve_returnOk {α : Type} (a : α) : SVE (NonDetE.returnOk a : NonDetE (State Unit) ε α) := sv_pure _

theorem sve_throw {α : Type} (e : ε) : SVE (NonDetE.throwError e : NonDetE (State Unit) ε α) := sv_pure _

theorem sve_throw' {α : Type} (e : ε) : SVE (throw e : NonDetE (State Unit) ε α) := sv_pure _

theorem sve_liftE {α : Type} {m : NonDet (State Unit) α} (h : SVM m) : SVE (NonDetE.liftE (ε := ε) m) := by
  unfold SVE NonDetE.liftE; rw [ExceptT.run_lift]
  exact sv_bind h fun _ => sv_pure _

theorem sve_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : SVE m1)
    (h2 : SVE m2) : SVE (if P then m1 else m2) := by
  split <;> assumption

theorem sve_whenE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : SVE m) :
    SVE (NonDetE.whenE P m) := by
  unfold NonDetE.whenE; exact sve_ite P h (sve_pure _)

theorem sve_unlessE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : SVE m) :
    SVE (NonDetE.unlessE P m) := by
  unfold NonDetE.unlessE; exact sve_ite P (sve_pure _) h

theorem sve_throwOpt {α : Type} (e : ε) (o : Option α) : SVE (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact sve_throw' e
  · exact sve_pure _

theorem sve_assertE (P : Prop) : SVE (NonDetE.assertE P : NonDetE (State Unit) ε Unit) :=
  sve_liftE (sv_assert P)

theorem sv_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : SVE m)
    (hh : ∀ e, SVM (h e)) : SVM (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine sv_bind' hm fun r => ?_
  cases r with
  | ok a => exact sv_pure' _
  | error e => exact hh e

theorem sve_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : SVE m) (hh : ∀ e, SVE (h e)) : SVE (NonDetE.handleE m h) := by
  unfold NonDetE.handleE SVE
  rw [ExceptT.run_mk]
  refine sv_bind' hm fun r => ?_
  cases r with
  | ok a => exact sv_pure' _
  | error e => exact hh e

theorem sve_liftME {α β : Type} (f : α → β) {m : NonDetE (State Unit) ε α} (h : SVE m) :
    SVE (NonDetE.liftME f m) := by
  unfold NonDetE.liftME; exact sve_bind h fun _ => sve_pure _

theorem sve_mapMEx {α β : Type} {f : α → NonDetE (State Unit) ε β} (h : ∀ a, SVE (f a)) :
    ∀ xs : List α, SVE (NonDetE.mapMEx f xs)
  | [] => by unfold NonDetE.mapMEx; exact sve_pure _
  | a :: rest => by unfold NonDetE.mapMEx; exact sve_bind (h a) fun _ => sve_mapMEx h rest

theorem sve_mapME {α β : Type} {f : α → NonDetE (State Unit) ε β} (h : ∀ a, SVE (f a)) :
    ∀ xs : List α, SVE (NonDetE.mapME f xs)
  | [] => by unfold NonDetE.mapME; exact sve_pure _
  | a :: rest => by
    unfold NonDetE.mapME; exact sve_bind (h a) fun _ => sve_bind (sve_mapME h rest) fun _ => sve_pure _

end CombE

theorem so_reply (x : Reply) : ∀ k, aType k = aType (.reply x) → sv (some k) = sv (some (.reply x)) := by
  intro k hk; cases k <;> simp only [aType] at hk <;> (try split_ifs at hk) <;> first | rfl | (cases hk) | (simp at hk)
theorem so_ep (x : Endpoint) : ∀ k, aType k = aType (.endpoint x) → sv (some k) = sv (some (.endpoint x)) := by
  intro k hk; cases k <;> simp only [aType] at hk <;> (try split_ifs at hk) <;> first | rfl | (cases hk) | (simp at hk)
theorem so_ntfn (x : Notification) : ∀ k, aType k = aType (.notification x) →
    sv (some k) = sv (some (.notification x)) := by
  intro k hk; cases k <;> simp only [aType] at hk <;> (try split_ifs at hk) <;> first | rfl | (cases hk) | (simp at hk)
theorem so_arch (x : ArchKernelObj) : ∀ k, aType k = aType (.archObj x) → sv (some k) = sv (some (.archObj x)) := by
  intro k hk; cases k <;> simp only [aType] at hk <;> (try split_ifs at hk) <;> first | rfl | (cases hk) | (simp at hk)

/-- One step of an `SVM` proof. -/
macro "sv_step0" : tactic => `(tactic| first
  | with_reducible exact sv_pure _ | with_reducible exact sv_pure' _ | with_reducible exact sv_fail
  | with_reducible exact sv_gets _ | with_reducible exact sv_get
  | with_reducible exact sv_assert _ | with_reducible exact sv_assertOpt _
  | with_reducible exact sv_getsThe _
  | with_reducible exact sv_selectF _ | with_reducible exact sv_select _
  | ((with_reducible apply sv_modify); intro _; exact ⟨rfl, rfl, rfl⟩)
  | ((with_reducible apply sv_get_put); intro _; exact ⟨rfl, rfl, rfl⟩)
  | (exact sv_get_put' (fun _ => ⟨rfl, rfl, rfl⟩))
  | (exact sv_get_put (fun _ => ⟨rfl, rfl, rfl⟩))
  | with_reducible exact sv_getObject _
  | with_reducible exact sv_doMachineOp _ | with_reducible exact sv_doExtendedOp _
  | (with_reducible refine sv_bind_pure ?_) | (with_reducible exact sv_fail_bind)
  | (with_reducible refine sv_bind ?_ (fun _ => ?_))
  | (with_reducible refine sv_bind' ?_ (fun _ => ?_))
  | (with_reducible apply sv_ite) | (with_reducible apply sv_when) | (with_reducible apply sv_unless)
  | (with_reducible refine sv_maybeM (fun _ => ?_) _) | (with_reducible apply sv_liftM)
  | (with_reducible refine sv_whileLoop (fun _ => ?_) _)
  | (with_reducible refine sv_mapMx (fun _ => ?_) _)
  | (with_reducible refine sv_mapM (fun _ => ?_) _)
  | (with_reducible refine sv_forMx (fun _ => ?_) _)
  | with_reducible exact sve_pure _ | with_reducible exact sve_returnOk _ | with_reducible exact sve_throw _
  | with_reducible exact sve_throw' _ | with_reducible exact sve_throwOpt _ _ | with_reducible exact sve_assertE _
  | (with_reducible refine sve_bind ?_ (fun _ => ?_))
  | (with_reducible apply sve_liftE) | (with_reducible apply sve_ite) | (with_reducible apply sve_whenE)
  | (with_reducible apply sve_unlessE) | (with_reducible refine sv_catch ?_ (fun _ => ?_))
  | (with_reducible refine sve_handleE ?_ (fun _ => ?_)) | (with_reducible apply sve_liftME)
  | (with_reducible refine sve_mapMEx (fun _ => ?_) _) | (with_reducible refine sve_mapME (fun _ => ?_) _)
  | with_reducible exact so_reply _ | with_reducible exact so_ep _
  | with_reducible exact so_ntfn _ | with_reducible exact fun _ => so_ep _ | with_reducible exact fun _ => so_ntfn _
  | with_reducible exact so_arch _ | with_reducible exact fun _ => so_reply _
  | (with_reducible intro _; exact ⟨rfl, rfl⟩)
  | (intro _; rfl)
  | (intro _; trivial)
  | split
  | (dsimp only)
  | (simp only [letFun])
  | (dsimp only [letFun])
  | (with_reducible exact sv_pure _)
  | (exact sv_pure _))

macro "sv_auto0" : tactic => `(tactic| repeat' sv_step0)

/-- An `SVM` lemma of a spec function (extended below, one rule per lemma). -/
syntax "sv_leaf" : tactic
macro_rules | `(tactic| sv_leaf) => `(tactic| fail "no sv_leaf")

macro "sv_auto" : tactic => `(tactic| repeat' (first | sv_leaf | sv_step0))

/-! ## Object steps -/

/-- The outcome of `set_object`: the object there had the same type. -/
theorem sv_setObject_mem {σ : State Unit} {p : ObjRef} {o : KernelObject} {x : Unit × State Unit}
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

/-- The state after writing `ko` at `o` over `k`, with the same view. -/
theorem svs_upd {σ : State Unit} {o : ObjRef} {k ko : KernelObject} (hk : σ.kheap o = some k)
    (hq : sv (some ko) = sv (some k)) : SVS σ { σ with kheap := Function.update σ.kheap o (some ko) } := by
  refine ⟨fun q => ?_, rfl, Or.inl rfl⟩
  by_cases h : q = o
  · subst h; simp only [Function.update_self]; rw [hk]; exact hq
  · simp only [Function.update_of_ne h]

theorem sv_setSchedulerAction' : SVM (setSchedulerAction (Z := Unit) .chooseNewThread) := by
  intro σ x hx
  unfold setSchedulerAction at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ⟨fun _ => rfl, rfl, Or.inr rfl⟩
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_setSchedulerAction')

/-- `set_object` of an object keeping the view of what it replaces. -/
theorem sv_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ k, aType k = aType o → sv (some k) = sv (some o)) :
    SVM (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨k, hk, hty, e⟩ := sv_setObject_mem hx
  rw [e]; exact svs_upd hk (ho k hty).symm
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible refine sv_setObject _ _ ?_)

theorem set_fin {σ : State Unit} {o : ObjRef} {k ko : KernelObject} (hk : σ.kheap o = some k)
    {x : Unit × State Unit} (hx : x ∈ (setObject (Z := Unit) o ko σ).1) (hq : sv (some ko) = sv (some k)) :
    SVS σ x.2 := by
  obtain ⟨k', hk', -, e⟩ := sv_setObject_mem hx
  rw [e]; exact svs_upd hk hq

theorem pure_set {σ : State Unit} {o : ObjRef} {ko : KernelObject} {x : Unit × State Unit}
    (hx : x ∈ (((pure ko : NonDet (State Unit) KernelObject) >>= fun obj' => setObject (Z := Unit) o obj') σ).1) :
    x ∈ (setObject (Z := Unit) o ko σ).1 := by
  obtain ⟨y2, hy2, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy2] at hx; exact hx

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
    obtain ⟨k', -, -, e⟩ := sv_setObject_mem (o := .schedContext (f sc) n) hx
    exact ⟨sc, n, hk, e⟩
  | _ => exact hx.elim

/-- `update_sched_context` by a function keeping the view. -/
theorem sv_updateSchedContext (q : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, (f y).scRefills = y.scRefills ∧ (f y).scRefillMax = y.scRefillMax ∧ (f y).scTcb = y.scTcb) :
    SVM (updateSchedContext (Z := Unit) q f) := by
  intro σ x hx
  obtain ⟨sc, n, hk, e⟩ := updSc_mem hx
  rw [e]; exact svs_upd hk (by obtain ⟨h1, h2, h3⟩ := hf sc; simp [sv, h1, h2, h3])
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible refine sv_updateSchedContext _ _ ?_)

theorem sv_setCap (c : Cap) (sl : CslotPtr) : SVM (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  intro σ x hx
  unfold setCap at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨k, hk, rfl⟩ : ∃ k, σ.kheap o = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap o with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  dsimp only at hx
  cases k with
  | cnode sz cn =>
    dsimp only at hx; split_ifs at hx
    · exact set_fin hk (pure_set hx) rfl
    · obtain ⟨_, h, _⟩ := hx; exact h.elim
  | tcb t =>
    dsimp only at hx
    split_ifs at hx <;> first | exact set_fin hk (pure_set hx) rfl | (obtain ⟨_, h, _⟩ := hx; exact h.elim)
  | _ => obtain ⟨_, h, _⟩ := hx; exact h.elim
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_setCap _ _)

theorem sv_getCap (sl : CslotPtr) : SVM (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap
  refine sv_bind (sv_getObject o) (fun obj => ?_)
  cases obj <;> simp only [letFun] <;> sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_getCap _)

theorem sv_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) :
    SVM (portOut (Z := Unit) f w) := by
  unfold portOut; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_portOut _ _)

theorem sv_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α)
    (hC : ∀ k, aType k = aType (C e) → sv (some k) = sv (some (C e))) : SVM (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo
  exact sv_bind (sv_getObject _) fun _ => sv_bind (sv_assert _) fun _ => sv_bind (sv_assert _) fun _ =>
    sv_setObject _ _ hC
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible refine sv_setSimpleKo' _ _ _ ?_)

theorem sv_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef)
    (hC : ∀ e k, aType k = aType (C e) → sv (some k) = sv (some (C e))) :
    SVM (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef getSimpleKo
  refine sv_bind (sv_bind (sv_getObject _) fun _ => sv_bind (sv_assert _) fun _ => ?_) fun _ =>
    sv_setSimpleKo' _ _ _ (hC _)
  split
  · exact sv_pure _
  · exact sv_fail
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible refine sv_updateSkObjRef' _ _ _ _ ?_)

/-! ## The spec functions (VsDomOps, DomRecDel, AllDom's `DK` lemmas, for `SVM`) -/

theorem sv_setOriginal (slot : CslotPtr) (v : Bool) : SVM (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_setOriginal _ _)

theorem sv_updateCdt (f : Cdt → Cdt) : SVM (updateCdt (Z := Unit) f) := by
  unfold updateCdt; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_updateCdt _)

theorem sv_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : SVM (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_setUntypedCapAsFull _ _ _)

theorem sv_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : SVM (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_capInsert _ _ _)

theorem sv_threadSet' (f : Tcb → Tcb) (hf : ∀ x, (f x).tcbSchedContext = x.tcbSchedContext) (t : ObjRef) :
    SVM (threadSet (Z := Unit) f t) := by
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
  exact set_fin hk0 hx (by simp [sv, hf])
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible refine sv_threadSet' _ ?_ _)

theorem sv_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : SVM (threadGet (Z := Unit) f t) := by
  unfold threadGet; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_threadGet' _ _)

theorem sv_setThreadState' (t : ObjRef) (ts : ThreadState) : SVM (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_setThreadState' _ _)

theorem sv_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    SVM (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_getSimpleKo' _ _)

theorem sv_getSchedContext' (q : ObjRef) : SVM (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_getSchedContext' _)

theorem sv_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : SVM (asUser (Z := Unit) t u) := by
  intro σ x hx
  unfold asUser at hx
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
  obtain ⟨y1, hy1, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy1] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  obtain ⟨-, e2⟩ := hy2
  obtain ⟨⟨a, uc'⟩, σ2⟩ := y2
  simp only at e2
  subst e2
  obtain ⟨y3, hy3, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy3] at hx
  obtain ⟨y4, hy4, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hx]
  exact set_fin hk0 hy4 rfl
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_asUser' _ _)

theorem sv_getThreadState' (t : ObjRef) : SVM (getThreadState (Z := Unit) t) := by
  unfold getThreadState; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_getThreadState' _)

theorem sv_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) : SVM (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_getSkObjRef' _ _ _)

theorem sv_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : SVM (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_getScObjRef' _ _)

theorem sv_lookupIpcBuffer' (b : Bool) (t : ObjRef) : SVM (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_lookupIpcBuffer' _ _)

theorem sv_zipWithMx' {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, SVM (g a b)) :
    ∀ l1 l2, SVM (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => sv_bind (h a b) (fun _ => sv_zipWithMx' h l1 l2)
  | [], _ => sv_pure' _
  | _ :: _, [] => sv_pure' _
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible refine sv_zipWithMx' (fun _ _ => ?_) _ _)

theorem sv_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : SVM (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_storeWordOffs' _ _ _)

theorem sv_set_bind {β : Type} {σ : State Unit} {t : ObjRef} {x0 : Tcb} {y : Tcb} {K : Unit → NonDet (State Unit) β}
    (hk : σ.kheap t = some (.tcb x0)) (hq : y.tcbSchedContext = x0.tcbSchedContext) (hK : ∀ u, SVM (K u)) :
    ∀ x ∈ ((setObject (Z := Unit) t (.tcb y) >>= K) σ).1, SVS σ x.2 := by
  intro x ⟨y3, hy3, hx⟩
  exact (set_fin hk hy3 (by simp [sv, hq])).trans (hK _ _ _ hx)

theorem sv_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : SVM (setMrs (Z := Unit) t b m) := by
  intro σ x hx
  unfold setMrs at hx
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
  obtain ⟨y1, hy1, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy1] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy2] at hx
  beta_reduce at hx
  refine sv_set_bind hk0 ?_ ?_ x hx
  · rfl
  · intro _; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_setMrs' _ _ _)

theorem sv_setMessageInfo' (t : ObjRef) (i : MessageInfo) : SVM (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_setMessageInfo' _ _)

theorem sv_archThreadSet' (f : ArchTcb → ArchTcb) (t : ObjRef) : SVM (archThreadSet (Z := Unit) f t) := by
  intro σ x hx
  unfold archThreadSet at hx
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
  exact set_fin hk0 hx rfl
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_archThreadSet' _ _)

theorem sv_getTcbQueue' (d : Domain) (p : Priority) : SVM (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_getTcbQueue' _ _)

theorem sv_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : SVM (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_setTcbQueue' _ _ _)

theorem sv_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) : SVM (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_tcbSchedAction' _ _)

theorem sv_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : SVM (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_getTcbObjRef' _ _)


theorem sv_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : SVM (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_getScRefillSufficient' _ _)

theorem sv_getScRefillReady' (sc : ObjRef) : SVM (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_getScRefillReady' _)

theorem sv_tcbReleaseRemove' (t : ObjRef) : SVM (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove setReleaseQueue; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_tcbReleaseRemove' _)

theorem sv_replyUnlinkSc' (sc r : ObjRef) : SVM (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_replyUnlinkSc' _ _)

theorem sv_schedContextUpdateConsumed' (sc : ObjRef) : SVM (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_schedContextUpdateConsumed' _)

theorem sve_rab (p : Cap × CapRef) : SVE (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact sve_liftE (sv_fail)
    · refine sve_bind (sve_whenE _ (sve_throw _)) fun _ => sve_bind (sve_whenE _ (sve_throw _)) fun _ =>
        sve_bind (sve_returnOk _) fun _ => ?_
      dsimp only
      split
      · exact sve_returnOk _
      · refine sve_bind (sve_liftE (sv_getCap _)) fun nc => ?_
        split
        · exact sve_rab _
        · exact sve_returnOk _
  · exact sve_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sve_rab _)

theorem sve_resolveAddressBits (p : Cap × CapRef) : SVE (resolveAddressBits (Z := Unit) p) := sve_rab p
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sve_resolveAddressBits _)

theorem sv_lookupSlotForThread' (thread : ObjRef) (cref : CapRef) : SVE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_lookupSlotForThread' _ _)

theorem sv_lookupCapAndSlot' (thread : ObjRef) (cptr : CapRef) : SVE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_lookupCapAndSlot' _ _)

theorem sv_lookupCap' (thread : ObjRef) (ref : CapRef) : SVE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_lookupCap' _ _)

theorem sv_captransferFromWords' (ptr : Word) : SVM (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_captransferFromWords' _)

theorem sv_loadCapTransfer' (buffer : ObjRef) : SVM (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_loadCapTransfer' _)

theorem sv_setExtraBadge' (buffer : ObjRef) (badge : Word) (n : Nat) : SVM (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_setExtraBadge' _ _ _)

theorem sve_lookupErrorOnFailure' {α : Type} (b : Bool) {m : LFMonad Unit α} (h : SVE m) :
    SVE (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact sve_handleE h fun _ => sve_throw _
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible refine sve_lookupErrorOnFailure' _ ?_)

theorem sv_lookupSlotForCnodeOp' (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : SVE (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_lookupSlotForCnodeOp' _ _ _ _)

theorem sv_lookupTargetSlot' (c : Cap) (r : CapRef) (n : Nat) : SVE (lookupTargetSlot (Z := Unit) c r n) := by
  unfold lookupTargetSlot; exact sv_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_lookupTargetSlot' _ _ _)

theorem sve_bind_returnOk' {ε α β : Type} {a : α} {f : α → NonDetE (State Unit) ε β} (h : SVE (f a)) :
    SVE (NonDetE.returnOk a >>= f) := by
  intro σ x hx
  rw [ExceptT.run_bind] at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ x hx
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible refine sve_bind_returnOk' ?_)

theorem sv_ensureNoChildren' (cslotPtr : CslotPtr) : SVE (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_ensureNoChildren' _)

theorem sve_archDeriveCap' (c : ArchCap) : SVE (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sve_archDeriveCap' _)

theorem sve_deriveCap' (sl : CslotPtr) (c : Cap) : SVE (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sve_deriveCap' _ _)

theorem sv_makeArchFaultMsg' (f : ArchFault) (t : ObjRef) : SVM (makeArchFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeArchFaultMsg <;> sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_makeArchFaultMsg' _ _)

theorem sve_unifyFailure' {F α : Type} {m : NonDetE (State Unit) F α} (h : SVE m) :
    SVE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact sve_handleE h fun _ => sve_throw _
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible refine sve_unifyFailure' ?_)

theorem sv_emptyOnFailure' {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : SVE m) :
    SVM (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact sv_catch h fun _ => sv_pure' _
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible refine sv_emptyOnFailure' ?_)

theorem sv_constOnFailure' {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : SVE m) :
    SVM (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact sv_catch h fun _ => sv_pure' _
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible refine sv_constOnFailure' _ ?_)

theorem sve_capFaultOnFailure' {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : SVE m) :
    SVE (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact sve_handleE h fun _ => sve_throw _
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible refine sve_capFaultOnFailure' _ _ ?_)

theorem sv_loadWordOffs' (ptr : ObjRef) (offs : Nat) : SVM (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; exact sv_doMachineOp _
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_loadWordOffs' _ _)

theorem sv_getExtraCptrs' (b : Option ObjRef) (mi : MessageInfo) : SVM (getExtraCptrs (Z := Unit) b mi) := by
  cases b
  · unfold getExtraCptrs; exact sv_pure _
  · unfold getExtraCptrs; exact sv_liftM _ (sv_mapM (fun _ => sv_loadWordOffs' _ _) _)
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_getExtraCptrs' _ _)

theorem sv_getReceiveSlots' (t : ObjRef) (b : Option ObjRef) : SVM (getReceiveSlots (Z := Unit) t b) := by
  cases b <;> unfold getReceiveSlots <;> sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_getReceiveSlots' _ _)

theorem sv_transferCapsLoop' (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (slots : List CslotPtr) (mi : MessageInfo),
      SVM (transferCapsLoop (Z := Unit) ep rb n caps slots mi)
  | n, [], slots, mi => by unfold transferCapsLoop; sv_auto
  | n, (c, sl) :: rest, slots, mi => by
    have ih := sv_transferCapsLoop' ep rb (n + 1) rest
    unfold transferCapsLoop
    sv_auto
    all_goals first | exact ih _ _ | skip
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_transferCapsLoop' _ _ _ _ _ _)

theorem sv_lookupExtraCaps' (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : SVE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_lookupExtraCaps' _ _ _)

theorem sv_copyMrs' (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : SVM (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_copyMrs' _ _ _ _ _)

theorem sv_transferCaps' (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : SVM (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_transferCaps' _ _ _ _ _)

theorem sv_makeFaultMsg' (f : Fault) (t : ObjRef) : SVM (makeFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeFaultMsg <;> sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_makeFaultMsg' _ _)

theorem sv_getMessageInfo' (thread : ObjRef) : SVM (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_getMessageInfo' _)

theorem sv_doNormalTransfer' (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : SVM (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_doNormalTransfer' _ _ _ _ _ _ _)

theorem sv_doFaultTransfer' (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : SVM (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_doFaultTransfer' _ _ _ _)

theorem sv_doIpcTransfer' (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : SVM (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_doIpcTransfer' _ _ _ _ _)

theorem sv_getMrs' (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : SVM (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_getMrs' _ _ _)

theorem sv_handleFaultReply' (f : Fault) (t : ObjRef) (x : Data) (y : List Data) :
    SVM (handleFaultReply (Z := Unit) f t x y) := by
  cases f <;> unfold handleFaultReply <;> sv_auto
macro_rules | `(tactic| sv_leaf) => `(tactic| with_reducible exact sv_handleFaultReply' _ _ _ _)


theorem svs_updK {σ : State Unit} {p : ObjRef} {k ko : KernelObject} (hk : σ.kheap p = some k)
    (hq : sv (some ko) = sv (some k)) : SVS σ (Notif.updK σ p ko) := svs_upd hk hq

theorem svs_stsAct (σ : State Unit) (t : ObjRef) : SVS σ (Notif.stsAct σ t) := by
  unfold Notif.stsAct; split_ifs
  · exact ⟨fun _ => rfl, rfl, Or.inr rfl⟩
  · exact SVS.refl _

theorem SVM.of_eq {α : Type} {m : NonDet (State Unit) α} (h : SVM m) {σ σ' : State Unit} {a : α}
    (he : m σ = ({(a, σ')}, False)) : SVS σ σ' :=
  h σ (a, σ') (by rw [he]; exact Set.mem_singleton _)

/-! ## The switch target's readiness, and the SCs' back-pointers -/

/-- **The switch target's SC, when bound and active, is ready and
sufficient** (the weak `ActReady`: no `schedulable` precondition). -/
def ActReadyW (σ : State Unit) : Prop :=
  ∀ u, σ.schedulerAction = .switchThread u → ∀ x scp y n, σ.kheap u = some (.tcb x) →
    x.tcbSchedContext = some scp → σ.kheap scp = some (.schedContext y n) → scActive y = true →
    y.scRefills ≠ [] ∧ refillSufficient 0 (refillHd y) = true ∧ refillReady σ.curTime (refillHd y) = true

/-- **A TCB's SC is bound back to it** (l4v `sym_refs`; `Inv.back`). -/
def SCBack (σ : State Unit) : Prop :=
  ∀ u x p, σ.kheap u = some (.tcb x) → x.tcbSchedContext = some p →
    ∃ y n, σ.kheap p = some (.schedContext y n) ∧ y.scTcb = some u

/-- **What a wake tail needs of its state**: `ActReadyW`, `SCBack`, the
woken thread not the switch target. -/
def WakeOK (σ : State Unit) (t : ObjRef) : Prop :=
  ActReadyW σ ∧ SCBack σ ∧ ∀ u, σ.schedulerAction = .switchThread u → u ≠ t

/-- **What a transfer path carries from its start**: `ActReadyW`, `SCBack`,
and the switch target a runnable TCB (l4v `valid_sched_action`). -/
def TailOK (σ : State Unit) : Prop :=
  ActReadyW σ ∧ SCBack σ ∧ ∀ u, σ.schedulerAction = .switchThread u → ∃ x, σ.kheap u = some (.tcb x) ∧
    runnable x.tcbState = true

theorem SVS.actReadyW {σ σ' : State Unit} (h : SVS σ σ') (hW : ActReadyW σ) : ActReadyW σ' := by
  intro u hu x' scp y' n hk' hsc' hky' hact'
  have hu0 : σ.schedulerAction = .switchThread u := by
    rcases h.2.2 with e | e
    · rw [← e]; exact hu
    · rw [e] at hu; cases hu
  have e1 := (h.1 u).symm; rw [hk'] at e1
  obtain ⟨x, hx, hxs⟩ := sv_tcb (o := σ.kheap u) e1
  have e2 := (h.1 scp).symm; rw [hky'] at e2
  obtain ⟨y, hy, hr, hm, -⟩ := sv_sc (o := σ.kheap scp) e2
  have hact : scActive y = true := by simpa [scActive, hm] using hact'
  obtain ⟨hne, hsf, hrd⟩ := hW u hu0 x scp y n hx (hxs.trans hsc') hy hact
  refine ⟨by rw [← hr]; exact hne, by unfold refillHd at hsf ⊢; rw [← hr]; exact hsf, ?_⟩
  rw [h.2.1]; unfold refillHd at hrd ⊢; rw [← hr]; exact hrd

theorem SVS.scBack {σ σ' : State Unit} (h : SVS σ σ') (hB : SCBack σ) : SCBack σ' := by
  intro u x' p hk' hp'
  have e1 := (h.1 u).symm; rw [hk'] at e1
  obtain ⟨x, hx, hxs⟩ := sv_tcb (o := σ.kheap u) e1
  obtain ⟨y, n, hy, hyt⟩ := hB u x p hx (hxs.trans hp')
  have e2 := h.1 p; rw [hy] at e2
  obtain ⟨y', hy', -, -, ht⟩ := sv_sc e2
  exact ⟨y', n, hy', ht.trans hyt⟩


/-! ## The step classes -/

theorem svs_epStep {σ σ' : State Unit} (h : Fl4Proofs.P3.Endp.EpStep σ σ') : SVS σ σ' := by
  have e := h.2.1
  refine ⟨fun p => ?_, by have := congrArg AbstractState.curTime e; exact this,
    Or.inl (by have := congrArg AbstractState.schedulerAction e; exact this)⟩
  rcases h.2.2 p with e1 | ⟨a, b, ha, hb⟩ | ⟨a, b, ha, hb, -⟩ | ⟨a, b, ha, hb, e2⟩
  · rw [e1]
  · rw [ha, hb]; rfl
  · rw [ha, hb]; rfl
  · rw [ha, hb, e2]; rfl

theorem svs_ntfnStep {σ σ' : State Unit} (h : Fl4Proofs.P3.Notif.NtfnStep σ σ') : SVS σ σ' := by
  have e := h.2.1
  refine ⟨fun p => ?_, by have := congrArg AbstractState.curTime e; exact this,
    Or.inl (by have := congrArg AbstractState.schedulerAction e; exact this)⟩
  rcases h.2.2 p with e1 | ⟨a, b, ha, hb, -⟩ | ⟨a, b, ha, hb, e2⟩
  · rw [e1]
  · rw [ha, hb]; rfl
  · rw [ha, hb, e2]; rfl

theorem sv_replyUnlinkTcb (t r : ObjRef) : SVM (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb setReplyObjRef; sv_auto

/-! ## The sporadic unblock check: only the thread's SC changes -/

/-- Only the object at `p` changes, an SC to an SC of the same size and bound
thread; the time and the action kept. -/
def OSS (p : ObjRef) (σ σ' : State Unit) : Prop :=
  (∀ q, q ≠ p → σ'.kheap q = σ.kheap q) ∧
  (σ'.kheap p = σ.kheap p ∨ ∃ y n y', σ.kheap p = some (.schedContext y n) ∧
    σ'.kheap p = some (.schedContext y' n) ∧ y'.scTcb = y.scTcb) ∧
  σ'.curTime = σ.curTime ∧ σ'.schedulerAction = σ.schedulerAction

theorem OSS.refl (p : ObjRef) (σ : State Unit) : OSS p σ σ := ⟨fun _ _ => rfl, Or.inl rfl, rfl, rfl⟩

theorem OSS.trans {p : ObjRef} {σ1 σ2 σ3 : State Unit} (h1 : OSS p σ1 σ2) (h2 : OSS p σ2 σ3) : OSS p σ1 σ3 := by
  refine ⟨fun q hq => (h2.1 q hq).trans (h1.1 q hq), ?_, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩
  rcases h1.2.1 with e1 | ⟨y, n, y', h1a, h1b, h1c⟩ <;> rcases h2.2.1 with e2 | ⟨z, m, z', h2a, h2b, h2c⟩
  · exact Or.inl (e2.trans e1)
  · rw [e1] at h2a; exact Or.inr ⟨z, m, z', h2a, h2b, h2c⟩
  · rw [← e2] at h1b; exact Or.inr ⟨y, n, y', h1a, h1b, h1c⟩
  · rw [h1b] at h2a; cases h2a; exact Or.inr ⟨y, n, z', h1a, h2b, h2c.trans h1c⟩

def OSM (p : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → OSS p σ x.2

theorem os_bind {p : ObjRef} {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : OSM p m) (hg : ∀ a, OSM p (g a)) : OSM p (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem os_pure {p : ObjRef} {α : Type} (a : α) : OSM p (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact OSS.refl _ _

theorem os_gets {p : ObjRef} {α : Type} (g : State Unit → α) : OSM p (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact OSS.refl _ _

theorem os_pure' {p : ObjRef} {α : Type} (a : α) : OSM p (NonDet.pure a : NonDet (State Unit) α) := os_pure a

theorem os_assertOpt {p : ObjRef} {α : Type} (o : Option α) : OSM p (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · intro σ x hx; exact hx.elim
  · exact os_pure' _

theorem os_getsThe {p : ObjRef} {α : Type} (g : State Unit → Option α) : OSM p (NonDet.getsThe g) := by
  intro σ x hx; exact os_assertOpt (g σ) σ x hx

theorem os_when {p : ObjRef} (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : OSM p m) :
    OSM p (NonDet.when P m) := by
  unfold NonDet.when; split
  · exact h
  · exact os_pure _

theorem os_reprogram (p : ObjRef) : OSM p (NonDet.modify fun s : State Unit => { s with reprogramTimer := true }) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ⟨fun _ _ => rfl, Or.inl rfl, rfl, rfl⟩

theorem os_updSc (p : ObjRef) (f : SchedContext → SchedContext) (hf : ∀ y, (f y).scTcb = y.scTcb) :
    OSM p (updateSchedContext (Z := Unit) p f) := by
  intro σ x hx
  obtain ⟨sc, n, hk, e⟩ := updSc_mem hx
  rw [e]
  refine ⟨fun q hq => by simp [Function.update_of_ne hq], Or.inr ⟨sc, n, f sc, hk, by simp, hf sc⟩, rfl, rfl⟩

theorem os_whileLoop {p : ObjRef} {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, OSM p (B r)) (r : α) : OSM p (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => exact OSS.refl _ _
  | step _ hm _ ih => exact (hB _ _ _ hm).trans ih

theorem os_fail {p : ObjRef} {α : Type} : OSM p (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem os_getSchedContext (p q : ObjRef) : OSM p (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext getObject
  refine os_bind (os_getsThe _) fun k => ?_
  cases k <;> first | exact os_pure _ | exact os_fail

theorem os_updRefillHd (p : ObjRef) (f : Refill → Refill) : OSM p (updateRefillHd (Z := Unit) p f) := by
  unfold updateRefillHd; exact os_updSc _ _ fun _ => rfl

theorem os_refillUnblockCheck (p : ObjRef) : OSM p (refillUnblockCheck (Z := Unit) p) := by
  unfold refillUnblockCheck isRoundRobin getScRefillReady
  refine os_bind (os_bind (os_getSchedContext p p) fun _ => os_pure _) fun _ => os_bind (os_getsThe _) fun _ => ?_
  refine os_when _ (os_bind (os_gets _) fun _ => os_bind (os_updRefillHd _ _) fun _ =>
    os_bind (os_reprogram p) fun _ => ?_)
  unfold refillHeadOverlappingLoop
  refine os_whileLoop (fun _ => ?_) _
  unfold mergeOverlappingRefills refillPopHead getRefillHead
  exact os_bind (os_bind (os_getsThe _) fun _ => os_bind (os_updSc _ _ fun _ => rfl) fun _ => os_pure _) fun _ =>
    os_updRefillHd _ _

/-- **`WakeOK` at a later state**: `SVS` from a `TailOK` start, the woken
thread not runnable at the start. -/
theorem SVS.wakeOK {σ σ' : State Unit} (h : SVS σ σ') (hT : TailOK σ) {t : ObjRef}
    (ht : ∀ x, σ.kheap t = some (.tcb x) → runnable x.tcbState = false) : WakeOK σ' t := by
  refine ⟨h.actReadyW hT.1, h.scBack hT.2.1, fun u hu e => ?_⟩
  have hu0 : σ.schedulerAction = .switchThread u := by
    rcases h.2.2 with e | e
    · rw [← e]; exact hu
    · rw [e] at hu; cases hu
  obtain ⟨x, hx, hr⟩ := hT.2.2 u hu0
  subst e; rw [ht x hx] at hr; cases hr

/-- The unblock check of an SC (any guard): only that SC changes. -/
theorem os_ifCond (p : ObjRef) (a b : Option Bool) : OSM p (ifCondRefillUnblockCheck (Z := Unit) (some p) a b) := by
  unfold ifCondRefillUnblockCheck
  simp only [NonDet.maybeM]
  exact os_bind (os_getSchedContext p p) fun _ => os_bind (os_gets _) fun _ => os_bind (os_pure _) fun _ =>
    os_when _ (os_when _ (os_refillUnblockCheck p))

/-- **`ActReadyW` across `OSS p`** for `p` the woken thread's SC. -/
theorem OSS.actReadyW {p t : ObjRef} {σ σ1 : State Unit} {y : SchedContext} {n : Nat} (hO : OSS p σ σ1)
    (hky : σ.kheap p = some (.schedContext y n)) (hyt : y.scTcb = some t) (hW : WakeOK σ t) :
    ActReadyW σ1 ∧ SCBack σ1 := by
  obtain ⟨hA, hB, hT⟩ := hW
  have hp : ∀ u x', σ1.kheap u = some (.tcb x') → u ≠ p := by
    intro u x' hk' e; subst e
    rcases hO.2.1 with e1 | ⟨_, _, _, _, h2, _⟩
    · rw [e1, hky] at hk'; cases hk'
    · rw [h2] at hk'; cases hk'
  refine ⟨fun u hu x' scp y' n' hk' hsc' hky' hact' => ?_, fun u x' q hk' hq' => ?_⟩
  · have hu0 : σ.schedulerAction = .switchThread u := by rw [← hO.2.2.2]; exact hu
    have hne : u ≠ t := hT u hu0
    have hk0 : σ.kheap u = some (.tcb x') := by rw [← hO.1 u (hp u x' hk')]; exact hk'
    have hsp : scp ≠ p := by
      intro e; subst e
      obtain ⟨y0, n0, hy0, hy0t⟩ := hB u x' scp hk0 hsc'
      rw [hky] at hy0; cases hy0
      rw [hyt] at hy0t; exact hne (Option.some.inj hy0t).symm
    have hky0 : σ.kheap scp = some (.schedContext y' n') := by rw [← hO.1 scp hsp]; exact hky'
    obtain ⟨h1, h2, h3⟩ := hA u hu0 x' scp y' n' hk0 hsc' hky0 hact'
    exact ⟨h1, h2, by rw [hO.2.2.1]; exact h3⟩
  · have hk0 : σ.kheap u = some (.tcb x') := by rw [← hO.1 u (hp u x' hk')]; exact hk'
    obtain ⟨y0, n0, hy0, hy0t⟩ := hB u x' q hk0 hq'
    by_cases e : q = p
    · subst e
      rcases hO.2.1 with e1 | ⟨y1, n1, y1', h1a, h1b, h1c⟩
      · exact ⟨y0, n0, by rw [e1]; exact hy0, hy0t⟩
      · rw [hy0] at h1a; cases h1a; exact ⟨y1', _, h1b, h1c.trans hy0t⟩
    · exact ⟨y0, n0, by rw [hO.1 q e]; exact hy0, hy0t⟩

/-- **The woken thread's unblock check keeps `ActReadyW` and `SCBack`**
(any guard). -/
theorem unblock_wake {σ σ1 : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (a b : Option Bool) (hW : WakeOK σ t)
    (hu : ((), σ1) ∈ ((getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t >>= fun o =>
      ifCondRefillUnblockCheck (Z := Unit) o a b) σ).1) : ActReadyW σ1 ∧ SCBack σ1 := by
  obtain ⟨y0, hy0, hx⟩ := hu
  have hy : y0 = (x.tcbSchedContext, σ) := by
    unfold getTcbObjRef threadGet at hy0
    obtain ⟨z, hz, hz2⟩ := hy0
    unfold NonDet.getsThe getTcb readObject at hz
    rw [hk] at hz
    rw [Set.mem_singleton_iff.1 hz] at hz2
    exact Set.mem_singleton_iff.1 hz2
  subst hy
  cases hsc : x.tcbSchedContext with
  | none =>
    rw [hsc] at hx
    have : σ1 = σ := by
      unfold ifCondRefillUnblockCheck at hx; simp only [NonDet.maybeM] at hx
      exact (Prod.mk.inj (Set.mem_singleton_iff.1 hx)).2
    subst this; exact ⟨hW.1, hW.2.1⟩
  | some p =>
    rw [hsc] at hx
    obtain ⟨y, n, hky, hyt⟩ := hW.2.1 t x p hk hsc
    exact (os_ifCond p a b σ ((), σ1) hx).actReadyW hky hyt hW

end

end Fl4Proofs.P3.SVK
