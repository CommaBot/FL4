/-
P3 (DESIGN.md §9), CSpace: **the spec's `finalise_cap` keeps `PPR0`**
(ScPPR; spec side only), discharging XTopJointDelR's `JFinPPHyp`.

* `TR E σ σ'`: the time, the consumed time and the current SC kept, the
  release queue shrunk, the current SC active after only if active before
  with the same head refill, and a thread bound to the current SC and in the
  release queue after either bound to it before or in `E` (reflexive,
  transitive). `TK E c m`: from a state whose current SC is `c`, every
  outcome of `m` is `TR E`-related to its start (the combinators and
  `tk_auto`, as ScMaxKeep's `MK`/`mk_auto`; the leaves as DomRecDel's).
* Object steps: `set_object` of an object neither an SC nor a TCB;
  `thread_set` keeping a TCB's SC link or clearing it (`tk_threadSet`), any
  `thread_set` of a thread in `E`; `update_sched_context` keeping an active
  SC's activity and head (`tk_updateSchedContext`), any update of an SC
  other than `c` (`tk_updateSchedContext_ne`); the CNode steps (`NKN`), the
  arch finalisation (`archF`).
* The other leaves: `tcb_release_remove` (the queue filtered),
  `sched_context_set_inactive` (the SC inactive after), the sporadic unblock
  check of `cancel_all_ipc`/`cancel_all_signals` (an SC other than the
  current one: `if_sporadic_cur_sc_assert_refill_unblock_check`),
  `sched_context_donate` and `reply_remove` to a thread in `E`.
* `tr_finaliseCap`: from an `Inv` state, every outcome of `finalise_cap` is
  `TR`-related with `E` empty: `reply_remove`'s donee is blocked on the
  reply, hence (`Inv.rel`) outside the release queue, which only shrinks.
  `PPR0` is kept by `TR` (`PPR0.of_tr`): `ppr0_finaliseCap`.
-/
import Fl4Proofs.P3.DomRecDel
import Fl4Proofs.P3.XTopJointFinVsSpec
import Fl4Proofs.P3.XTopFinSc
import Fl4Proofs.P3.DelW
import Fl4Proofs.P3.ScPPR
open Classical

namespace Fl4Proofs.P3.PPS
open Fl4Spec

noncomputable section

/-! ## The relation -/

/-- **What the deletion keeps for `PPR0`** (module docstring). -/
structure TR (E : ObjRef → Prop) (σ σ' : State Unit) : Prop where
  cons : σ'.consumedTime = σ.consumedTime
  time : σ'.curTime = σ.curTime
  csc : σ'.curSc = σ.curSc
  rel : ∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue
  sc : ∀ y n, σ'.kheap σ.curSc = some (.schedContext y n) → scActive y = true →
    ∃ y0 n0, σ.kheap σ.curSc = some (.schedContext y0 n0) ∧ scActive y0 = true ∧ refillHd y = refillHd y0
  own : ∀ u xt, σ'.kheap u = some (.tcb xt) → xt.tcbSchedContext = some σ.curSc → u ∈ σ'.releaseQueue →
    E u ∨ ∃ x0, σ.kheap u = some (.tcb x0) ∧ x0.tcbSchedContext = some σ.curSc

variable {E : ObjRef → Prop}

theorem TR.of_eq {σ σ' : State Unit} (hk : σ'.kheap = σ.kheap) (h1 : σ'.consumedTime = σ.consumedTime)
    (h2 : σ'.curTime = σ.curTime) (h3 : σ'.curSc = σ.curSc) (h4 : σ'.releaseQueue = σ.releaseQueue) :
    TR E σ σ' :=
  ⟨h1, h2, h3, fun u hu => by rw [h4] at hu; exact hu,
    fun y n hy ha => ⟨y, n, by rw [← hk]; exact hy, ha, rfl⟩,
    fun u xt hu hs _ => Or.inr ⟨xt, by rw [← hk]; exact hu, hs⟩⟩

theorem TR.refl (σ : State Unit) : TR E σ σ := TR.of_eq rfl rfl rfl rfl rfl

theorem TR.trans {σ1 σ2 σ3 : State Unit} (h1 : TR E σ1 σ2) (h2 : TR E σ2 σ3) : TR E σ1 σ3 := by
  refine ⟨h2.cons.trans h1.cons, h2.time.trans h1.time, h2.csc.trans h1.csc,
    fun u hu => h1.rel u (h2.rel u hu), fun y n hy ha => ?_, fun u xt hu hs hr => ?_⟩
  · rw [← h1.csc] at hy
    obtain ⟨y2, n2, hy2, ha2, e2⟩ := h2.sc y n hy ha
    rw [h1.csc] at hy2
    obtain ⟨y1, n1, hy1, ha1, e1⟩ := h1.sc y2 n2 hy2 ha2
    exact ⟨y1, n1, hy1, ha1, e2.trans e1⟩
  · rw [← h1.csc] at hs
    rcases h2.own u xt hu hs hr with h | ⟨x2, hx2, hs2⟩
    · exact Or.inl h
    · rw [h1.csc] at hs2
      exact h1.own u x2 hx2 hs2 (h2.rel u hr)

/-- From a state whose current SC is `c`, every outcome of `m` is
`TR E`-related to its start. -/
def TK (E : ObjRef → Prop) (c : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, σ.curSc = c → ∀ x, x ∈ (m σ).1 → TR E σ x.2

/-- `TK` for the exception monad. -/
def TKE (E : ObjRef → Prop) (c : ObjRef) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  TK E c (ExceptT.run m)

section Comb
variable {c : ObjRef}

theorem tk_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : TK E c m)
    (hg : ∀ a, TK E c (g a)) : TK E c (m >>= g) := by
  intro σ hc x ⟨y, hy, hx⟩
  have h1 := hm σ hc y hy
  exact h1.trans (hg y.1 y.2 (h1.csc.trans hc) x hx)

theorem tk_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : TK E c m)
    (hg : ∀ a, TK E c (g a)) : TK E c (NonDet.bind m g) := tk_bind hm hg

theorem tk_pure {α : Type} (a : α) : TK E c (pure a : NonDet (State Unit) α) := by
  intro σ _ x hx; rw [Set.mem_singleton_iff.1 hx]; exact TR.refl _

theorem tk_pure' {α : Type} (a : α) : TK E c (NonDet.pure a : NonDet (State Unit) α) := tk_pure a

theorem tk_gets {α : Type} (g : State Unit → α) : TK E c (NonDet.gets g) := by
  intro σ _ x hx; rw [Set.mem_singleton_iff.1 hx]; exact TR.refl _

theorem tk_get : TK E c (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ _ x hx; rw [Set.mem_singleton_iff.1 hx]; exact TR.refl _

theorem tk_assert (P : Prop) : TK E c (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ _ x hx; obtain ⟨-, rfl⟩ := hx; exact TR.refl _

theorem tk_fail {α : Type} : TK E c (NonDet.fail : NonDet (State Unit) α) := by
  intro σ _ x hx; exact hx.elim

theorem tk_assertOpt {α : Type} (o : Option α) : TK E c (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact tk_fail
  · exact tk_pure' _

theorem tk_getsThe {α : Type} (g : State Unit → Option α) : TK E c (NonDet.getsThe g) := by
  intro σ hc x hx; exact tk_assertOpt (g σ) σ hc x hx

theorem tk_selectF {α : Type} (S : Set α × Prop) : TK E c (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ _ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact TR.refl _

theorem tk_select {α : Type} (S : Set α) : TK E c (NonDet.select S : NonDet (State Unit) α) := by
  intro σ _ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact TR.refl _

theorem tk_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : TK E c m1)
    (h2 : TK E c m2) : TK E c (if P then m1 else m2) := by
  split <;> assumption

theorem tk_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : TK E c m) :
    TK E c (NonDet.when P m) := by
  unfold NonDet.when; exact tk_ite P h (tk_pure' _)

theorem tk_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : TK E c m) :
    TK E c (NonDet.unless P m) := by
  unfold NonDet.unless; exact tk_ite P (tk_pure' _) h

theorem tk_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, TK E c (g a)) (o : Option α) :
    TK E c (NonDet.maybeM g o) := by
  cases o
  · exact tk_pure' _
  · exact h _

theorem tk_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : TK E c m) :
    TK E c (NonDet.liftM g m) := tk_bind' h fun _ => tk_pure' _

theorem tk_modify {g : State Unit → State Unit} (hg : ∀ σ, TR E σ (g σ)) : TK E c (NonDet.modify g) := by
  intro σ _ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hg σ

theorem tk_get_put {g : State Unit → State Unit} (hg : ∀ σ, TR E σ (g σ)) :
    TK E c (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ _ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hg σ

theorem tk_get_put' {g : State Unit → State Unit} (hg : ∀ σ, TR E σ (g σ)) :
    TK E c (do let s ← NonDet.get; NonDet.put (g s)) := tk_get_put hg

theorem tk_getObject (p : ObjRef) : TK E c (getObject (Z := Unit) p) := tk_getsThe _

theorem tk_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, TK E c (B r)) (r : α) : TK E c (NonDet.whileLoop C B r) := by
  intro σ hc x hx
  induction hx with
  | done _ => exact TR.refl _
  | step _ hm _ ih =>
    have h1 := hB _ _ hc _ hm
    exact h1.trans (ih (h1.csc.trans hc))

theorem tk_mapMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, TK E c (g a)) (xs : List α) :
    TK E c (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact tk_pure' _
  | cons a xs' ih => exact tk_bind' (h a) fun _ => ih

theorem tk_forMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, TK E c (g a)) (xs : List α) :
    TK E c (NonDet.forMx xs g) := tk_mapMx h xs

theorem tk_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, TK E c (g a)) (xs : List α) :
    TK E c (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact tk_pure' _
  | cons a xs' ih => exact tk_bind' (h a) fun _ => tk_bind' ih fun _ => tk_pure' _

theorem tk_doMachineOp {α : Type} (mop : NonDet MachineState α) : TK E c (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine tk_bind (tk_gets _) (fun _ => tk_bind (tk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact tk_bind (tk_modify (fun σ => TR.of_eq rfl rfl rfl rfl rfl)) (fun _ => tk_pure _)

theorem tk_doExtendedOp (eop : DetExtMonad Unit) : TK E c (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine tk_bind tk_get (fun _ => tk_bind (tk_selectF _) (fun _ => ?_))
  split
  exact tk_modify (fun σ => TR.of_eq rfl rfl rfl rfl rfl)

end Comb

section CombE
variable {c : ObjRef} {ε : Type}

theorem tke_bind {α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β} (hm : TKE E c m)
    (hg : ∀ a, TKE E c (g a)) : TKE E c (m >>= g) := by
  unfold TKE; rw [ExceptT.run_bind]
  refine tk_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact tk_pure _

theorem tke_pure {α : Type} (a : α) : TKE E c (pure a : NonDetE (State Unit) ε α) := tk_pure _

theorem tke_returnOk {α : Type} (a : α) : TKE E c (NonDetE.returnOk a : NonDetE (State Unit) ε α) := tk_pure _

theorem tke_throw {α : Type} (e : ε) : TKE E c (NonDetE.throwError e : NonDetE (State Unit) ε α) := tk_pure _

theorem tke_throw' {α : Type} (e : ε) : TKE E c (throw e : NonDetE (State Unit) ε α) := tk_pure _

theorem tke_liftE {α : Type} {m : NonDet (State Unit) α} (h : TK E c m) : TKE E c (NonDetE.liftE (ε := ε) m) := by
  unfold TKE NonDetE.liftE; rw [ExceptT.run_lift]
  exact tk_bind h fun _ => tk_pure _

theorem tke_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : TKE E c m1)
    (h2 : TKE E c m2) : TKE E c (if P then m1 else m2) := by
  split <;> assumption

theorem tke_whenE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : TKE E c m) :
    TKE E c (NonDetE.whenE P m) := by
  unfold NonDetE.whenE; exact tke_ite P h (tke_pure _)

theorem tke_unlessE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : TKE E c m) :
    TKE E c (NonDetE.unlessE P m) := by
  unfold NonDetE.unlessE; exact tke_ite P (tke_pure _) h

theorem tke_throwOpt {α : Type} (e : ε) (o : Option α) : TKE E c (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact tke_throw' e
  · exact tke_pure _

theorem tke_assertE (P : Prop) : TKE E c (NonDetE.assertE P : NonDetE (State Unit) ε Unit) :=
  tke_liftE (tk_assert P)

theorem tk_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : TKE E c m)
    (hh : ∀ e, TK E c (h e)) : TK E c (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine tk_bind' hm fun r => ?_
  cases r with
  | ok a => exact tk_pure' _
  | error e => exact hh e

theorem tke_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : TKE E c m) (hh : ∀ e, TKE E c (h e)) : TKE E c (NonDetE.handleE m h) := by
  unfold NonDetE.handleE TKE
  rw [ExceptT.run_mk]
  refine tk_bind' hm fun r => ?_
  cases r with
  | ok a => exact tk_pure' _
  | error e => exact hh e

theorem tke_liftME {α β : Type} (f : α → β) {m : NonDetE (State Unit) ε α} (h : TKE E c m) :
    TKE E c (NonDetE.liftME f m) := by
  unfold NonDetE.liftME; exact tke_bind h fun _ => tke_pure _

end CombE

/-- One step of a `TK` proof. -/
macro "tk_step0" : tactic => `(tactic| first
  | with_reducible exact tk_pure _ | with_reducible exact tk_pure' _ | with_reducible exact tk_fail
  | with_reducible exact tk_gets _ | with_reducible exact tk_get
  | with_reducible exact tk_assert _ | with_reducible exact tk_assertOpt _
  | with_reducible exact tk_getsThe _
  | with_reducible exact tk_selectF _ | with_reducible exact tk_select _
  | ((with_reducible apply tk_modify); intro _; exact TR.of_eq rfl rfl rfl rfl rfl)
  | ((with_reducible apply tk_get_put); intro _; exact TR.of_eq rfl rfl rfl rfl rfl)
  | (exact tk_get_put' (fun _ => TR.of_eq rfl rfl rfl rfl rfl))
  | (exact tk_get_put (fun _ => TR.of_eq rfl rfl rfl rfl rfl))
  | with_reducible exact tk_getObject _
  | with_reducible exact tk_doMachineOp _ | with_reducible exact tk_doExtendedOp _
  | (with_reducible refine tk_bind ?_ (fun _ => ?_))
  | (with_reducible refine tk_bind' ?_ (fun _ => ?_))
  | (with_reducible apply tk_ite) | (with_reducible apply tk_when) | (with_reducible apply tk_unless)
  | (with_reducible refine tk_maybeM (fun _ => ?_) _) | (with_reducible apply tk_liftM)
  | (with_reducible refine tk_whileLoop (fun _ => ?_) _)
  | (with_reducible refine tk_mapMx (fun _ => ?_) _)
  | (with_reducible refine tk_mapM (fun _ => ?_) _)
  | (with_reducible refine tk_forMx (fun _ => ?_) _)
  | with_reducible exact tke_pure _ | with_reducible exact tke_returnOk _ | with_reducible exact tke_throw _
  | with_reducible exact tke_throw' _ | with_reducible exact tke_throwOpt _ _ | with_reducible exact tke_assertE _
  | (with_reducible refine tke_bind ?_ (fun _ => ?_))
  | (with_reducible apply tke_liftE) | (with_reducible apply tke_ite) | (with_reducible apply tke_whenE)
  | (with_reducible apply tke_unlessE) | (with_reducible refine tk_catch ?_ (fun _ => ?_))
  | (with_reducible refine tke_handleE ?_ (fun _ => ?_)) | (with_reducible apply tke_liftME)
  | split
  | (dsimp only)
  | (simp only [letFun])
  | (dsimp only [letFun])
  | (with_reducible exact tk_pure _)
  | (exact tk_pure _))

/-- A `TK` lemma of a spec function (extended below, one rule per lemma). -/
syntax "tk_leaf" : tactic
macro_rules | `(tactic| tk_leaf) => `(tactic| fail "no tk_leaf")

macro "tk_auto" : tactic => `(tactic| repeat' (first | tk_leaf | tk_step0))

/-! ## Object steps -/

section Obj
variable {c : ObjRef}

/-- `set_object` of an object neither an SC nor a TCB. -/
theorem tk_setObject (p : ObjRef) (o : KernelObject) (h1 : ∀ y n, o ≠ .schedContext y n)
    (h2 : ∀ t, o ≠ .tcb t) : TK E c (setObject (Z := Unit) p o) := by
  intro σ _ x hx
  obtain ⟨k, -, -, e⟩ := MaxK.mk_setObject_mem hx
  rw [e]
  refine ⟨rfl, rfl, rfl, fun u hu => hu, fun y n hy ha => ?_, fun u xt hu hs _ => ?_⟩
  · by_cases hq : σ.curSc = p
    · rw [hq] at hy; simp only [Function.update_self, Option.some.injEq] at hy; exact absurd hy (h1 y n)
    · simp only [Function.update_of_ne hq] at hy; exact ⟨y, n, hy, ha, rfl⟩
  · by_cases hq : u = p
    · subst hq; simp only [Function.update_self, Option.some.injEq] at hu; exact absurd hu (h2 xt)
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs⟩

theorem getTcb_kh {σ : State Unit} {t : ObjRef} {x : Tcb} (h : getTcb (Z := Unit) t σ = some x) :
    σ.kheap t = some (.tcb x) := by
  cases hk : σ.kheap t with
  | none => simp [getTcb, readObject, hk] at h
  | some k => cases k <;> simp_all [getTcb, readObject]

/-- The outcome of `thread_set`. -/
theorem threadSet_mem {σ : State Unit} {t : ObjRef} {f : Tcb → Tcb} {x : Unit × State Unit}
    (hx : x ∈ (threadSet (Z := Unit) f t σ).1) :
    ∃ x0, σ.kheap t = some (.tcb x0) ∧ x.2 = { σ with kheap := Function.update σ.kheap t (some (.tcb (f x0))) } := by
  unfold threadSet at hx
  obtain ⟨y, hy, hx⟩ := hx
  unfold NonDet.getsThe at hy
  cases hg : getTcb (Z := Unit) t σ with
  | none => rw [hg] at hy; exact hy.elim
  | some x0 =>
    rw [hg] at hy
    obtain rfl : y = (x0, σ) := hy
    obtain ⟨-, -, -, e⟩ := MaxK.mk_setObject_mem hx
    exact ⟨x0, getTcb_kh hg, e⟩

/-- `thread_set` keeping the TCB's SC link or clearing it. -/
theorem tk_threadSet (f : Tcb → Tcb) (t : ObjRef)
    (hf : ∀ x, (f x).tcbSchedContext = x.tcbSchedContext ∨ (f x).tcbSchedContext = none) :
    TK E c (threadSet (Z := Unit) f t) := by
  intro σ _ x hx
  obtain ⟨x0, hk, e⟩ := threadSet_mem hx
  rw [e]
  refine ⟨rfl, rfl, rfl, fun u hu => hu, fun y n hy ha => ?_, fun u xt hu hs _ => ?_⟩
  · by_cases hq : σ.curSc = t
    · rw [hq] at hy; simp at hy
    · simp only [Function.update_of_ne hq] at hy; exact ⟨y, n, hy, ha, rfl⟩
  · by_cases hq : u = t
    · subst hq; simp only [Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hu
      subst hu
      rcases hf x0 with h | h
      · exact Or.inr ⟨x0, hk, by rw [← h]; exact hs⟩
      · rw [h] at hs; cases hs
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs⟩

/-- Any `thread_set` of a thread in `E`. -/
theorem tk_threadSet_E (f : Tcb → Tcb) (t : ObjRef) (hE : E t) : TK E c (threadSet (Z := Unit) f t) := by
  intro σ _ x hx
  obtain ⟨x0, hk, e⟩ := threadSet_mem hx
  rw [e]
  refine ⟨rfl, rfl, rfl, fun u hu => hu, fun y n hy ha => ?_, fun u xt hu hs _ => ?_⟩
  · by_cases hq : σ.curSc = t
    · rw [hq] at hy; simp at hy
    · simp only [Function.update_of_ne hq] at hy; exact ⟨y, n, hy, ha, rfl⟩
  · by_cases hq : u = t
    · subst hq; exact Or.inl hE
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs⟩

/-- `update_sched_context` keeping an active SC's activity and head. -/
theorem tk_updateSchedContext (q : ObjRef) (f : SchedContext → SchedContext)
    (hf : ∀ y, scActive (f y) = true → scActive y = true ∧ refillHd (f y) = refillHd y) :
    TK E c (updateSchedContext (Z := Unit) q f) := by
  intro σ _ x hx
  obtain ⟨y0, n0, hk, e⟩ := MaxK.updSc_mem hx
  rw [e]
  refine ⟨rfl, rfl, rfl, fun u hu => hu, fun y n hy ha => ?_, fun u xt hu hs _ => ?_⟩
  · by_cases hq : σ.curSc = q
    · rw [hq] at hy ⊢
      simp only [Function.update_self, Option.some.injEq, KernelObject.schedContext.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      obtain ⟨h1, h2⟩ := hf y0 ha
      exact ⟨y0, _, hk, h1, h2⟩
    · simp only [Function.update_of_ne hq] at hy; exact ⟨y, n, hy, ha, rfl⟩
  · by_cases hq : u = q
    · subst hq; simp at hu
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs⟩

/-- Any `update_sched_context` of an SC other than the current one. -/
theorem tk_updateSchedContext_ne (q : ObjRef) (f : SchedContext → SchedContext) (hq : q ≠ c) :
    TK E c (updateSchedContext (Z := Unit) q f) := by
  intro σ hc x hx
  obtain ⟨y0, n0, hk, e⟩ := MaxK.updSc_mem hx
  rw [e]
  refine ⟨rfl, rfl, rfl, fun u hu => hu, fun y n hy ha => ?_, fun u xt hu hs _ => ?_⟩
  · have hq' : σ.curSc ≠ q := fun h => hq (by rw [← hc, h])
    simp only [Function.update_of_ne hq'] at hy; exact ⟨y, n, hy, ha, rfl⟩
  · by_cases hq : u = q
    · subst hq; simp at hu
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs⟩

/-- The CNode steps (`CnK`: every SC kept, every TCB's SC link kept). -/
theorem tk_of_nkn {α : Type} {m : NonDet (State Unit) α} (h : Ipc.NKN m) : TK E c m := by
  intro σ _ x hx
  have hk := PPK.of_cnK (h σ x hx)
  exact ⟨hk.cons, hk.time, hk.csc, hk.rel, fun y n hy ha => ⟨y, n, hk.sc _ y n hy, ha, rfl⟩,
    fun u xt hu hs _ => let ⟨x0, h0, e⟩ := hk.tcb u xt hu; Or.inr ⟨x0, h0, by rw [e]; exact hs⟩⟩

/-- The arch finalisation (`archF`: every non-arch object kept, the
scheduler's fields kept). -/
theorem tk_of_archF {α : Type} {m : NonDet (State Unit) α} (h : Vs.FK archF m) : TK E c m := by
  intro σ _ x hx
  have e := h σ x hx
  simp only [archF, Prod.mk.injEq] at e
  obtain ⟨e1, -, -, -, -, -, e5, e6, e7, -, -, -, -, e12, -, -, -⟩ := e
  have k : ∀ q o, (∀ a, o ≠ KernelObject.archObj a) → x.2.kheap q = some o → σ.kheap q = some o := by
    intro q o ho hq
    have := congrFun e1 q
    try simp only at this
    rw [hq] at this
    cases o with
    | archObj a => exact absurd rfl (ho a)
    | _ =>
      cases hσ : σ.kheap q with
      | none => rw [hσ] at this; simp [eraseA] at this
      | some k => rw [hσ] at this; cases k <;> simp_all [eraseA]
  refine ⟨e5, e6, e7, fun u hu => by rw [e12] at hu; exact hu, fun y n hy ha => ?_, fun u xt hu hs _ => ?_⟩
  · exact ⟨y, n, k _ _ (fun _ h => by cases h) hy, ha, rfl⟩
  · exact Or.inr ⟨xt, k _ _ (fun _ h => by cases h) hu, hs⟩

end Obj

/-! ## Reading a TCB, then writing it back with its SC link -/

section Tka
variable {c : ObjRef}

/-- From a state where `t` holds the TCB `x`. -/
def TKA (E : ObjRef → Prop) (c t : ObjRef) (x : Tcb) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, σ.curSc = c → σ.kheap t = some (.tcb x) → ∀ z, z ∈ (m σ).1 → TR E σ z.2

theorem tr_setTcb {σ : State Unit} {t : ObjRef} {x y : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hs : y.tcbSchedContext = x.tcbSchedContext) :
    TR E σ { σ with kheap := Function.update σ.kheap t (some (.tcb y)) } := by
  refine ⟨rfl, rfl, rfl, fun u hu => hu, fun y' n hy ha => ?_, fun u xt hu hs' _ => ?_⟩
  · by_cases hq : σ.curSc = t
    · rw [hq] at hy; simp at hy
    · simp only [Function.update_of_ne hq] at hy; exact ⟨y', n, hy, ha, rfl⟩
  · by_cases hq : u = t
    · subst hq; simp only [Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hu
      subst hu
      exact Or.inr ⟨x, hk, by rw [← hs]; exact hs'⟩
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs'⟩

theorem tka_getTcb {t : ObjRef} {α : Type} {g : Tcb → NonDet (State Unit) α} (h : ∀ x, TKA E c t x (g x)) :
    TK E c (NonDet.getsThe (getTcb (Z := Unit) t) >>= g) := by
  intro σ hc z ⟨y, hy, hz⟩
  unfold NonDet.getsThe at hy
  cases hg : getTcb (Z := Unit) t σ with
  | none => rw [hg] at hy; exact hy.elim
  | some x0 =>
    rw [hg] at hy
    obtain rfl : y = (x0, σ) := hy
    exact h x0 σ hc (getTcb_kh hg) z hz

theorem tka_pure_bind {t : ObjRef} {x : Tcb} {α β : Type} {a : α} {g : α → NonDet (State Unit) β}
    (h : TKA E c t x (g a)) : TKA E c t x ((pure a : NonDet (State Unit) α) >>= g) := by
  intro σ hc hk z ⟨y, hy, hz⟩
  obtain rfl : y = (a, σ) := hy
  exact h σ hc hk z hz

theorem tka_selectF_bind {t : ObjRef} {x : Tcb} {α β : Type} {S : Set α × Prop} {g : α → NonDet (State Unit) β}
    (h : ∀ a, TKA E c t x (g a)) : TKA E c t x (NonDet.selectF S >>= g) := by
  intro σ hc hk z ⟨y, hy, hz⟩
  obtain ⟨-, e⟩ := hy
  obtain ⟨a, s⟩ := y
  simp only at e; subst e
  exact h a _ hc hk z hz

theorem tka_setObject {t : ObjRef} {x y : Tcb} (hs : y.tcbSchedContext = x.tcbSchedContext) :
    TKA E c t x (setObject (Z := Unit) t (.tcb y)) := by
  intro σ _ hk z hz
  obtain ⟨-, -, -, e⟩ := MaxK.mk_setObject_mem hz
  rw [e]; exact tr_setTcb hk hs

theorem tka_setObject_bind {t : ObjRef} {x y : Tcb} {β : Type} {g : Unit → NonDet (State Unit) β}
    (hs : y.tcbSchedContext = x.tcbSchedContext) (h : ∀ u, TK E c (g u)) :
    TKA E c t x (setObject (Z := Unit) t (.tcb y) >>= g) := by
  intro σ hc hk z ⟨w, hw, hz⟩
  have h1 := tka_setObject (E := E) (c := c) hs σ hc hk w hw
  exact h1.trans (h w.1 w.2 (h1.csc.trans hc) z hz)

end Tka

/-! ## A thread outside the release queue (`reply_remove`'s donation) -/

section Tkn
variable {c : ObjRef}

/-- From a state where `t` is outside the release queue. -/
def TKN (E : ObjRef → Prop) (c t : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, σ.curSc = c → t ∉ σ.releaseQueue → ∀ x, x ∈ (m σ).1 → TR E σ x.2

theorem tkn_of {t : ObjRef} {α : Type} {m : NonDet (State Unit) α} (h : TK E c m) : TKN E c t m :=
  fun σ hc _ x hx => h σ hc x hx

theorem tkn_bind {t : ObjRef} {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : TKN E c t m) (hg : ∀ a, TKN E c t (g a)) : TKN E c t (m >>= g) := by
  intro σ hc ht x ⟨y, hy, hx⟩
  have h1 := hm σ hc ht y hy
  exact h1.trans (hg y.1 y.2 (h1.csc.trans hc) (fun h => ht (h1.rel t h)) x hx)

theorem tkn_when {t : ObjRef} (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : TKN E c t m) :
    TKN E c t (NonDet.when P m) := by
  unfold NonDet.when; split
  · exact h
  · exact tkn_of (tk_pure' _)

/-- Any `thread_set` of `t`, outside the release queue. -/
theorem tkn_threadSet (f : Tcb → Tcb) (t : ObjRef) : TKN E c t (threadSet (Z := Unit) f t) := by
  intro σ _ ht x hx
  obtain ⟨x0, hk, e⟩ := threadSet_mem hx
  rw [e]
  refine ⟨rfl, rfl, rfl, fun u hu => hu, fun y n hy ha => ?_, fun u xt hu hs hr => ?_⟩
  · by_cases hq : σ.curSc = t
    · rw [hq] at hy; simp at hy
    · simp only [Function.update_of_ne hq] at hy; exact ⟨y, n, hy, ha, rfl⟩
  · by_cases hq : u = t
    · subst hq; exact absurd hr ht
    · simp only [Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs⟩

end Tkn

/-! ## The leaves -/

section Leaves
variable {c : ObjRef}

/-- The two shapes of "not this constructor" side goals. -/
macro "tk_neq" : tactic => `(tactic| first | (intro _ _ h; cases h) | (intro _ h; cases h))

macro_rules | `(tactic| tk_leaf) => `(tactic| ((with_reducible refine tk_setObject _ _ ?_ ?_) <;> tk_neq))
macro_rules | `(tactic| tk_leaf) => `(tactic|
  ((with_reducible refine tk_threadSet _ _ ?_); intro _; first | exact Or.inl rfl | exact Or.inr rfl))
macro_rules | `(tactic| tk_leaf) => `(tactic|
  ((with_reducible refine tk_updateSchedContext _ _ ?_); intro _ h; exact ⟨h, rfl⟩))
macro_rules | `(tactic| tk_leaf) => `(tactic|
  (with_reducible refine tk_updateSchedContext_ne _ _ ?_; assumption))

theorem tk_setCap (cp : Cap) (sl : CslotPtr) : TK E c (setCap (Z := Unit) cp sl) := tk_of_nkn (Ipc.nkn_setCap _ _)
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setCap _ _)

theorem tk_getCap (sl : CslotPtr) : TK E c (getCap (Z := Unit) sl) := tk_of_nkn (Ipc.nkn_getCap _)
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getCap _)

theorem tk_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α)
    (h1 : ∀ y n, C e ≠ .schedContext y n) (h2 : ∀ t, C e ≠ .tcb t) : TK E c (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo
  exact tk_bind (tk_getObject _) fun _ => tk_bind (tk_assert _) fun _ => tk_bind (tk_assert _) fun _ =>
    tk_setObject _ _ h1 h2
macro_rules | `(tactic| tk_leaf) => `(tactic| ((with_reducible refine tk_setSimpleKo' _ _ _ ?_ ?_) <;> tk_neq))

theorem tk_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    TK E c (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getSimpleKo' _ _)

theorem tk_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef)
    (h1 : ∀ e y n, C e ≠ .schedContext y n) (h2 : ∀ e t, C e ≠ .tcb t) :
    TK E c (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef
  exact tk_bind (tk_getSimpleKo' _ _) fun _ => tk_setSimpleKo' _ _ _ (h1 _) (h2 _)
macro_rules | `(tactic| tk_leaf) => `(tactic|
  ((with_reducible refine tk_updateSkObjRef' _ _ _ _ ?_ ?_) <;> first | (intro _ _ _ h; cases h) | (intro _ _ h; cases h)))

theorem tk_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : TK E c (threadGet (Z := Unit) f t) := by
  unfold threadGet; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_threadGet' _ _)

theorem tk_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : TK E c (asUser (Z := Unit) t u) := by
  unfold asUser
  refine tka_getTcb fun x => ?_
  refine tka_pure_bind ?_
  refine tka_selectF_bind fun z => ?_
  obtain ⟨a, uc'⟩ := z
  refine tka_pure_bind ?_
  exact tka_setObject_bind rfl fun _ => tk_pure _
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_asUser' _ _)

theorem tk_archThreadSet' (f : ArchTcb → ArchTcb) (t : ObjRef) : TK E c (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  exact tka_getTcb fun x => tka_setObject rfl
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_archThreadSet' _ _)

theorem tk_zipWithMx' {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, TK E c (g a b)) :
    ∀ l1 l2, TK E c (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => tk_bind (h a b) (fun _ => tk_zipWithMx' h l1 l2)
  | [], _ => tk_pure' _
  | _ :: _, [] => tk_pure' _
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible refine tk_zipWithMx' (fun _ _ => ?_) _ _)

theorem tk_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : TK E c (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_storeWordOffs' _ _ _)

theorem tk_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : TK E c (setMrs (Z := Unit) t b m) := by
  unfold setMrs
  refine tka_getTcb fun x => ?_
  refine tka_pure_bind ?_
  refine tka_pure_bind ?_
  refine tka_setObject_bind rfl fun _ => ?_
  tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setMrs' _ _ _)

/-- `tcb_release_remove`: the queue filtered. -/
theorem tk_tcbReleaseRemove' (t : ObjRef) : TK E c (tcbReleaseRemove (Z := Unit) t) := by
  intro σ _ x hx
  unfold tcbReleaseRemove at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain rfl : y = (σ.releaseQueue, σ) := hy
  obtain ⟨z, hz, hx⟩ := hx
  have hz2 : z.2.releaseQueue = σ.releaseQueue ∧ z.2.kheap = σ.kheap ∧ z.2.curSc = σ.curSc ∧
      z.2.curTime = σ.curTime ∧ z.2.consumedTime = σ.consumedTime := by
    unfold NonDet.when at hz
    split at hz
    · rw [Set.mem_singleton_iff.1 hz]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · rw [Set.mem_singleton_iff.1 hz]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨w, hw, hx⟩ := hx
  obtain rfl : w = (tcbSchedDequeue t σ.releaseQueue, z.2) := hw
  rw [Set.mem_singleton_iff.1 hx]
  obtain ⟨e1, e2, e3, e4, e5⟩ := hz2
  refine ⟨e5, e4, e3, fun u hu => ?_, fun y n hy ha => ⟨y, n, by rw [← e2]; exact hy, ha, rfl⟩,
    fun u xt hu hs _ => Or.inr ⟨xt, by rw [← e2]; exact hu, hs⟩⟩
  exact (List.mem_filter.1 hu).1
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_tcbReleaseRemove' _)

/-- `sched_context_set_inactive`: the SC inactive after. -/
theorem tk_schedContextSetInactive' (p : ObjRef) : TK E c (schedContextSetInactive (Z := Unit) p) := by
  intro σ _ x hx
  have hk : ∃ y0 n0, σ.kheap p = some (.schedContext y0 n0) := by
    unfold schedContextSetInactive at hx
    obtain ⟨y, hy, -⟩ := hx
    obtain ⟨y0, n0, hk, -⟩ := MaxK.updSc_mem hy
    exact ⟨y0, n0, hk⟩
  obtain ⟨y0, n0, hk⟩ := hk
  rw [Sched.setInactive_eq hk] at hx
  rw [Set.mem_singleton_iff.1 hx]
  refine ⟨rfl, rfl, rfl, fun u hu => hu, fun y n hy ha => ?_, fun u xt hu hs _ => ?_⟩
  · by_cases hq : σ.curSc = p
    · rw [hq] at hy; simp [Notif.updK] at hy
      obtain ⟨rfl, -⟩ := hy
      exact absurd ha (by rw [show scActive (Sched.inactSc y0) = false from rfl]; decide)
    · simp [Notif.updK, Function.update_of_ne hq] at hy; exact ⟨y, n, hy, ha, rfl⟩
  · by_cases hq : u = p
    · subst hq; simp [Notif.updK] at hu
    · simp [Notif.updK, Function.update_of_ne hq] at hu; exact Or.inr ⟨xt, hu, hs⟩
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_schedContextSetInactive' _)

theorem tk_getThreadState' (t : ObjRef) : TK E c (getThreadState (Z := Unit) t) := by
  unfold getThreadState; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getThreadState' _)

theorem tk_setThreadState' (t : ObjRef) (ts : ThreadState) : TK E c (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setThreadState' _ _)

theorem tk_getSchedContext' (q : ObjRef) : TK E c (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getSchedContext' _)

theorem tk_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) :
    TK E c (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getSkObjRef' _ _ _)

theorem tk_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : TK E c (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getScObjRef' _ _)

theorem tk_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : TK E c (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getTcbObjRef' _ _)

theorem tk_replyUnlinkTcb' (t r : ObjRef) : TK E c (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_replyUnlinkTcb' _ _)

theorem tk_getIrqSlot' (irq : Irq) : TK E c (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getIrqSlot' _)

theorem tk_isFinalCap' (cp : Cap) : TK E c (isFinalCap (Z := Unit) cp) := by
  unfold isFinalCap; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_isFinalCap' _)

theorem tk_setIoportMask' (f l : IoPort) (val : Bool) : TK E c (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setIoportMask' _ _ _)

theorem tk_setOriginal' (slot : CslotPtr) (v : Bool) : TK E c (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setOriginal' _ _)

theorem tk_updateCdt' (f : Cdt → Cdt) : TK E c (updateCdt (Z := Unit) f) := by
  unfold updateCdt setCdt; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_updateCdt' _)

theorem tk_freeIoportRange' (f l : IoPort) : TK E c (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_freeIoportRange' _ _)

theorem tk_archPostCapDeletion' (cp : ArchCap) : TK E c (archPostCapDeletion (Z := Unit) cp) := by
  unfold archPostCapDeletion; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_archPostCapDeletion' _)

theorem tk_setIrqState' (i : IrqState) (irq : Irq) : TK E c (setIrqState (Z := Unit) i irq) := by
  unfold setIrqState; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setIrqState' _ _)

theorem tk_deletedIrqHandler' (irq : Irq) : TK E c (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_deletedIrqHandler' _)

theorem tk_lookupIpcBuffer' (b : Bool) (t : ObjRef) : TK E c (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_lookupIpcBuffer' _ _)

theorem tk_setMessageInfo' (t : ObjRef) (i : MessageInfo) : TK E c (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setMessageInfo' _ _)

theorem tk_saveFpuState' (t : ObjRef) : TK E c (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_saveFpuState' _)

theorem tk_loadFpuState' (t : ObjRef) : TK E c (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_loadFpuState' _)

theorem tk_setX64CurrentFpuOwner' (o : Option ObjRef) : TK E c (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setX64CurrentFpuOwner' _)

theorem tk_switchLocalFpuOwner' (o : Option ObjRef) : TK E c (switchLocalFpuOwner (Z := Unit) o) := by
  unfold switchLocalFpuOwner; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_switchLocalFpuOwner' _)

theorem tk_getTcbQueue' (d : Domain) (p : Priority) : TK E c (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getTcbQueue' _ _)

theorem tk_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : TK E c (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setTcbQueue' _ _ _)

theorem tk_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    TK E c (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_tcbSchedAction' _ _)

theorem tk_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : TK E c (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getScRefillSufficient' _ _)

theorem tk_getScRefillReady' (sc : ObjRef) : TK E c (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getScRefillReady' _)

theorem tk_rescheduleRequired' : TK E c (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired setSchedulerAction; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_rescheduleRequired')

theorem tk_possibleSwitchTo' (t : ObjRef) : TK E c (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo setSchedulerAction; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_possibleSwitchTo' _)

theorem tk_testReschedule' (t : ObjRef) : TK E c (testReschedule (Z := Unit) t) := by
  unfold testReschedule; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_testReschedule' _)

theorem tk_tcbEpDequeue' (t e : ObjRef) : TK E c (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_tcbEpDequeue' _ _)

theorem tk_tcbNtfnDequeue' (t n : ObjRef) : TK E c (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_tcbNtfnDequeue' _ _)

theorem tk_isRoundRobin' (sc : ObjRef) : TK E c (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_isRoundRobin' _)

theorem tk_getRefillHead' (sc : ObjRef) : TK E c (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_getRefillHead' _)

/-- The sporadic unblock check of an SC other than the current one. -/
theorem tk_refillUnblockCheck_ne (sc : ObjRef) (h : sc ≠ c) : TK E c (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck refillHeadOverlappingLoop mergeOverlappingRefills refillPopHead updateRefillHd
  tk_auto

/-- `if_sporadic_cur_sc_assert_refill_unblock_check`: the check only of an SC
other than the current one. -/
theorem tk_gets_curSc_bind {α : Type} {g : ObjRef → NonDet (State Unit) α} (h : TK E c (g c)) :
    TK E c (NonDet.gets (fun s : State Unit => s.curSc) >>= g) := by
  intro σ hc x ⟨y, hy, hx⟩
  obtain rfl : y = (σ.curSc, σ) := hy
  simp only at hx
  rw [hc] at hx
  exact h σ hc x hx

theorem tk_when_cond (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : P → TK E c m) :
    TK E c (NonDet.when P m) := by
  unfold NonDet.when; split
  · exact h ‹P›
  · exact tk_pure' _

theorem tk_ifSporadicCurScAssertRefillUnblockCheck' (o : Option ObjRef) :
    TK E c (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScAssertRefillUnblockCheck ifCondRefillUnblockCheck
  refine tk_maybeM (fun scp => ?_) o
  refine tk_bind (tk_getSchedContext' _) fun _ => ?_
  refine tk_gets_curSc_bind ?_
  refine tk_bind (tk_pure _) fun _ => tk_when _ (tk_when_cond _ fun hP => ?_)
  exact tk_refillUnblockCheck_ne scp (hP rfl)
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_ifSporadicCurScAssertRefillUnblockCheck' _)

theorem tk_replyUnlinkSc' (sc r : ObjRef) : TK E c (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_replyUnlinkSc' _ _)

theorem tk_schedContextUpdateConsumed' (sc : ObjRef) : TK E c (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_schedContextUpdateConsumed' _)

theorem tk_replyFromKernel' (t : ObjRef) (x : Data × List Data) : TK E c (replyFromKernel (Z := Unit) t x) := by
  unfold replyFromKernel; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_replyFromKernel' _ _)

theorem tk_setConsumed' (sc t : ObjRef) : TK E c (setConsumed (Z := Unit) sc t) := by
  unfold setConsumed; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_setConsumed' _ _)

theorem tk_schedContextCancelYieldTo' (t : ObjRef) : TK E c (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_schedContextCancelYieldTo' _)

theorem tk_fpuRelease' (t : ObjRef) : TK E c (fpuRelease (Z := Unit) t) := by
  unfold fpuRelease; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_fpuRelease' _)

theorem tk_cancelIpc' (t : ObjRef) : TK E c (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc blockedCancelIpc getBlockingObject cancelSignal replyRemoveTcb
  tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_cancelIpc' _)

theorem tk_suspend' (t : ObjRef) : TK E c (suspend (Z := Unit) t) := by
  unfold suspend updateRestartPc; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_suspend' _)

theorem tk_restartThreadIfNoFault' (t : ObjRef) : TK E c (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_restartThreadIfNoFault' _)

theorem tk_removeAndRestartEpQueuedThread' (t e : ObjRef) :
    TK E c (removeAndRestartEpQueuedThread (Z := Unit) t e) := by
  unfold removeAndRestartEpQueuedThread; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_removeAndRestartEpQueuedThread' _ _)

theorem tk_removeAndRestartNtfnQueuedThread' (t n : ObjRef) :
    TK E c (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_removeAndRestartNtfnQueuedThread' _ _)

theorem tk_postCapDeletion' (cp : Cap) : TK E c (postCapDeletion (Z := Unit) cp) := by
  unfold postCapDeletion; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_postCapDeletion' _)

theorem tk_emptySlot' (sl : CslotPtr) (cp : Cap) : TK E c (emptySlot (Z := Unit) sl cp) := by
  unfold emptySlot; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_emptySlot' _ _)

theorem tk_cancelAllIpc' (e : ObjRef) : TK E c (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_cancelAllIpc' _)

theorem tk_schedContextMaybeUnbindNtfn' (n : ObjRef) : TK E c (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_schedContextMaybeUnbindNtfn' _)

theorem tk_unbindMaybeNotification' (n : ObjRef) : TK E c (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_unbindMaybeNotification' _)

theorem tk_cancelAllSignals' (n : ObjRef) : TK E c (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_cancelAllSignals' _)

theorem tk_unbindNotification' (t : ObjRef) : TK E c (unbindNotification (Z := Unit) t) := by
  unfold unbindNotification; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_unbindNotification' _)

theorem tk_schedContextUnbindTcb' (sc : ObjRef) : TK E c (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_schedContextUnbindTcb' _)

theorem tk_completeYieldTo' (t : ObjRef) : TK E c (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_completeYieldTo' _)

theorem tk_unbindFromSc' (t : ObjRef) : TK E c (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_unbindFromSc' _)

theorem tk_schedContextUnbindAllTcbs' (sc : ObjRef) : TK E c (schedContextUnbindAllTcbs (Z := Unit) sc) := by
  unfold schedContextUnbindAllTcbs; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_schedContextUnbindAllTcbs' _)

theorem tk_schedContextUnbindNtfn' (sc : ObjRef) : TK E c (schedContextUnbindNtfn (Z := Unit) sc) := by
  unfold schedContextUnbindNtfn; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_schedContextUnbindNtfn' _)

theorem tk_schedContextUnbindReply' (sc : ObjRef) : TK E c (schedContextUnbindReply (Z := Unit) sc) := by
  unfold schedContextUnbindReply; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_schedContextUnbindReply' _)

theorem tk_schedContextUnbindYieldFrom' (sc : ObjRef) : TK E c (schedContextUnbindYieldFrom (Z := Unit) sc) := by
  unfold schedContextUnbindYieldFrom; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_schedContextUnbindYieldFrom' _)

theorem tk_prepareThreadDelete' (t : ObjRef) : TK E c (prepareThreadDelete (Z := Unit) t) := by
  unfold prepareThreadDelete; tk_auto
macro_rules | `(tactic| tk_leaf) => `(tactic| with_reducible exact tk_prepareThreadDelete' _)

/-- `sched_context_donate` to a thread outside the release queue. -/
theorem tkn_schedContextDonate (sc t : ObjRef) : TKN E c t (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate
  refine tkn_bind (tkn_of (tk_getScObjRef' _ _)) fun _ => tkn_bind (tkn_of (by tk_auto)) fun _ =>
    tkn_bind (tkn_of (by tk_auto)) fun _ => tkn_threadSet _ _

/-- One step of a `TKN` proof. -/
macro "tkn_step" : tactic => `(tactic| first
  | with_reducible exact tkn_schedContextDonate _ _
  | (with_reducible refine tkn_when _ ?_)
  | (with_reducible refine tkn_bind ?_ (fun _ => ?_))
  | split
  | (simp only [letFun])
  | exact tkn_of (by tk_auto))

/-- `reply_remove` of a caller outside the release queue. -/
theorem tkn_replyRemove (t r : ObjRef) : TKN E c t (replyRemove (Z := Unit) t r) := by
  unfold replyRemove
  repeat' tkn_step

end Leaves

/-! ## From an `Inv` state: the reply's caller outside the release queue -/

section Tks
variable {c : ObjRef}

/-- Every thread in the release queue is runnable (`Inv.rel`). -/
def RQRun (σ : State Unit) : Prop :=
  ∀ u ∈ σ.releaseQueue, ∃ x, σ.kheap u = some (.tcb x) ∧ runnable x.tcbState = true

theorem rqRun_of_inv {σ : State Unit} (h : Sched.Inv σ) : RQRun σ := fun u hu =>
  let ⟨x, _, _, _, hk, _, hr, _⟩ := h.rel u hu; ⟨x, hk, hr⟩

/-- From a state satisfying `P`. -/
def TKS (E : ObjRef → Prop) (c : ObjRef) (P : State Unit → Prop) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, σ.curSc = c → P σ → ∀ x, x ∈ (m σ).1 → TR E σ x.2

variable {P : State Unit → Prop}

theorem tks_of {α : Type} {m : NonDet (State Unit) α} (h : TK E c m) : TKS E c P m :=
  fun σ hc _ x hx => h σ hc x hx

theorem tks_bind_tk {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : TKS E c P m) (hg : ∀ a, TK E c (g a)) : TKS E c P (m >>= g) := by
  intro σ hc hP x ⟨y, hy, hx⟩
  have h1 := hm σ hc hP y hy
  exact h1.trans (hg y.1 y.2 (h1.csc.trans hc) x hx)

/-- A read (the state kept) then a `TKS` step. -/
theorem tks_read_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : Vs.FK (fun s : State Unit => s) m) (hg : ∀ a, TKS E c P (g a)) : TKS E c P (m >>= g) := by
  intro σ hc hP x ⟨y, hy, hx⟩
  have e : y.2 = σ := hm σ y hy
  rw [← e] at hc hP ⊢
  exact hg y.1 y.2 hc hP x hx

theorem tks_ite {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDet (State Unit) α} (h1 : TKS E c P m1)
    (h2 : TKS E c P m2) : TKS E c P (if Q then m1 else m2) := by
  split <;> assumption

theorem tks_when (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : TKS E c P m) :
    TKS E c P (NonDet.when Q m) := by
  unfold NonDet.when; exact tks_ite Q h (tks_of (tk_pure' _))

theorem tks_unless (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : TKS E c P m) :
    TKS E c P (NonDet.unless Q m) := by
  unfold NonDet.unless; exact tks_ite Q (tks_of (tk_pure' _)) h

theorem tks_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : TKS E c P m) :
    TKS E c P (NonDet.liftM g m) := tks_bind_tk h fun _ => tk_pure' _

theorem fk_getReplyTcb (r : ObjRef) : Vs.FK (fun s : State Unit => s) (getReplyTcb (Z := Unit) r) := by
  show Vs.FK _ (NonDet.liftM Reply.replyTcb (getSimpleKo KernelObject.reply r))
  unfold getSimpleKo; dk_auto0

theorem getThreadState_mem {σ : State Unit} {t : ObjRef} {w : ThreadState × State Unit}
    (hw : w ∈ (getThreadState (Z := Unit) t σ).1) :
    w.2 = σ ∧ ∃ xt, σ.kheap t = some (.tcb xt) ∧ xt.tcbState = w.1 := by
  unfold getThreadState threadGet at hw
  obtain ⟨y, hy, hw⟩ := hw
  unfold NonDet.getsThe at hy
  cases hg : getTcb (Z := Unit) t σ with
  | none => rw [hg] at hy; exact hy.elim
  | some x0 =>
    rw [hg] at hy
    obtain rfl : y = (x0, σ) := hy
    obtain rfl : w = (x0.tcbState, σ) := hw
    exact ⟨rfl, x0, getTcb_kh hg, rfl⟩

/-- **A final reply cap's work** (`finalise_cap`'s and `fast_finalise`'s):
`reply_remove` of a caller blocked on the reply, outside the release queue
(`RQRun`), or `cancel_ipc`. -/
theorem tks_replyBody (r : ObjRef) : TKS E c RQRun (do
    let tptr ← getReplyTcb (Z := Unit) r
    match tptr with
    | none => return ()
    | some tp => do
      let state ← getThreadState tp
      match state with
      | .blockedOnReply r => replyRemove tp r
      | _ => cancelIpc tp) := by
  refine tks_read_bind (fk_getReplyTcb r) fun tptr => ?_
  cases tptr with
  | none => exact tks_of (tk_pure _)
  | some tp =>
    intro σ hc hR x ⟨w, hw, hx⟩
    obtain ⟨e, xt, hk, hst⟩ := getThreadState_mem hw
    obtain ⟨st, s⟩ := w
    simp only at e hst hx
    subst e
    cases st with
    | blockedOnReply r' =>
      refine tkn_replyRemove (E := E) tp r' s hc (fun h => ?_) x hx
      obtain ⟨x', hk', hr'⟩ := hR tp h
      rw [hk] at hk'; cases hk'
      rw [hst] at hr'; cases hr'
    | _ => exact tk_cancelIpc' tp s hc x hx

theorem tks_fastFinalise (cp : Cap) (b : Bool) : TKS E c RQRun (fastFinalise (Z := Unit) cp b) := by
  cases cp <;> simp only [fastFinalise] <;>
    first | exact tks_when _ (tks_replyBody _) | exact tks_of (by tk_auto)

theorem tks_capDeleteOne (sl : CslotPtr) : TKS E c RQRun (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne
  refine tks_read_bind (fk_getCapG _ _) fun cp => tks_unless _ ?_
  refine tks_read_bind (Vs.dk_gets _) fun b => ?_
  exact tks_bind_tk (tks_fastFinalise _ _) fun _ => tk_emptySlot' _ _

theorem tks_deletingIrqHandler (irq : Irq) : TKS E c RQRun (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler getIrqSlot
  exact tks_read_bind (Vs.dk_gets _) fun _ => tks_capDeleteOne _

/-- **Every outcome of `finalise_cap`** from a state with `RQRun`. -/
theorem tks_finaliseCap (cp : Cap) (b : Bool) : TKS E c RQRun (finaliseCap (Z := Unit) cp b) := by
  cases cp with
  | replyCap r _ =>
    simp only [finaliseCap]
    exact tks_liftM _ (tks_when _ (tks_replyBody r))
  | irqHandlerCap irq =>
    simp only [finaliseCap]
    exact tks_ite _ (tks_bind_tk (tks_deletingIrqHandler irq) fun _ => tk_pure _) (tks_of (tk_pure _))
  | archObjectCap a =>
    simp only [finaliseCap]
    exact tks_of (tk_of_archF (fa_archFinaliseCap a b))
  | _ => exact tks_of (by simp only [finaliseCap]; tk_auto)

end Tks

/-! ## `PPR0` kept -/

theorem PPR0.of_tr {σ σ' : State Unit} (hP : PPR0 σ) (h : TR (fun _ => False) σ σ')
    (hct : σ'.curThread = σ.curThread) (hid : σ'.idleThread = σ.idleThread)
    (hns : (∀ u, σ.schedulerAction ≠ .switchThread u) → ∀ u, σ'.schedulerAction ≠ .switchThread u) : PPR0 σ' := by
  refine ⟨⟨by rw [hct, hid]; exact hP.1.1, hns hP.1.2⟩, fun h0 => ?_⟩
  rw [h.cons] at h0
  obtain ⟨h1, h2⟩ := hP.2 h0
  refine ⟨fun y n hy ha => ?_, fun u xt hu hs hr => ?_⟩
  · rw [h.csc] at hy
    obtain ⟨y0, n0, hy0, ha0, e⟩ := h.sc y n hy ha
    rw [h.time, e]; exact h1 y0 n0 hy0 ha0
  · rw [h.csc] at hs
    rcases h.own u xt hu hs hr with h' | ⟨x0, hx0, hs0⟩
    · exact h'.elim
    · exact h2 u x0 hx0 hs0 (h.rel u hr)

/-- **`finalise_cap` keeps `PPR0`** from an `Inv` state (module docstring;
the current and idle threads and no pending switch kept: `hct`/`hid`/`hns`,
from VsDom's `DK`, SpecGlobFK's `GK` and SpecNoSwitch's `AK` at the caller). -/
theorem ppr0_finaliseCap {cp : Cap} {b : Bool} {σ : State Unit} {x : (Cap × Cap) × State Unit}
    (hI : Sched.Inv σ) (hx : x ∈ (finaliseCap (Z := Unit) cp b σ).1) (hP : PPR0 σ)
    (hct : x.2.curThread = σ.curThread) (hid : x.2.idleThread = σ.idleThread)
    (hns : (∀ u, σ.schedulerAction ≠ .switchThread u) → ∀ u, x.2.schedulerAction ≠ .switchThread u) : PPR0 x.2 :=
  PPR0.of_tr hP (tks_finaliseCap (E := fun _ => False) cp b σ rfl (rqRun_of_inv hI) x hx) hct hid hns

end

end Fl4Proofs.P3.PPS
