/-
P3 (DESIGN.md §9), VSpace: **spec frames by a kept projection**: `FK f m`,
every outcome of `m` keeps `f` (any `f : State Unit → β`), built from the
monad's combinators (generic in `f`; `dk_auto`, as ScPres's `pres_auto`).
`DK := FK schedF`: the spec's arch invocations, deletions and TCB/CNode
invocations (VsDomOps, DomRecDel, TcbDom, AllDom) keep the domain schedule
(`domain_list`, `domain_start_index`; for `DomFrame`) and `cur_thread`
(`schedTailXHypJ`): `DK.dom`, `DK.ct`.
-/
import Fl4Spec.Ext.Invocation
import Fl4Spec.Ext.VSpace
open Classical

namespace Fl4Proofs.P3.Vs
open Fl4Spec

noncomputable section

/-- Every outcome of `m` keeps `f`. -/
def FK {β : Type} (f : State Unit → β) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, x ∈ (m σ).1 → f x.2 = f σ

/-- The fields `DK` keeps: the domain schedule and the current thread. -/
def schedF (σ : State Unit) : List (Domain × DomainDuration) × Nat × ObjRef :=
  (σ.domainList, σ.domainStartIndex, σ.curThread)

/-- Every outcome of `m` keeps the domain schedule and the current thread. -/
abbrev DK {α : Type} (m : NonDet (State Unit) α) : Prop := FK schedF m

theorem DK.dom {α : Type} {m : NonDet (State Unit) α} (h : DK m) {σ : State Unit} {x : α × State Unit}
    (hx : x ∈ (m σ).1) : x.2.domainList = σ.domainList ∧ x.2.domainStartIndex = σ.domainStartIndex := by
  have e := h σ x hx; simp only [schedF, Prod.mk.injEq] at e; exact ⟨e.1, e.2.1⟩

theorem DK.ct {α : Type} {m : NonDet (State Unit) α} (h : DK m) {σ : State Unit} {x : α × State Unit}
    (hx : x ∈ (m σ).1) : x.2.curThread = σ.curThread := by
  have e := h σ x hx; simp only [schedF, Prod.mk.injEq] at e; exact e.2.2

section Comb
variable {β : Type} {f : State Unit → β}

theorem dk_bind {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : FK f m)
    (hg : ∀ a, FK f (g a)) : FK f (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hg y.1 y.2 x hx).trans (hm σ y hy)

theorem dk_bind' {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : FK f m)
    (hg : ∀ a, FK f (g a)) : FK f (NonDet.bind m g) := dk_bind hm hg

theorem dk_pure {α : Type} (a : α) : FK f (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]

theorem dk_pure' {α : Type} (a : α) : FK f (NonDet.pure a : NonDet (State Unit) α) := dk_pure a

theorem dk_gets {α : Type} (g : State Unit → α) : FK f (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]

theorem dk_get : FK f (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]

theorem dk_assert (P : Prop) : FK f (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; rfl

theorem dk_fail {α : Type} : FK f (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem dk_assertOpt {α : Type} (o : Option α) : FK f (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact dk_fail
  · exact dk_pure' _

theorem dk_getsThe {α : Type} (g : State Unit → Option α) : FK f (NonDet.getsThe g) := by
  intro σ x hx; exact dk_assertOpt (g σ) σ x hx

theorem dk_selectF {α : Type} (S : Set α × Prop) : FK f (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]

theorem dk_select {α : Type} (S : Set α) : FK f (NonDet.select S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]

theorem dk_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : FK f m1)
    (h2 : FK f m2) : FK f (if P then m1 else m2) := by
  split <;> assumption

theorem dk_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : FK f m) :
    FK f (NonDet.when P m) := by
  unfold NonDet.when; exact dk_ite P h (dk_pure' _)

theorem dk_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : FK f m) :
    FK f (NonDet.unless P m) := by
  unfold NonDet.unless; exact dk_ite P (dk_pure' _) h

theorem dk_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, FK f (g a)) (o : Option α) :
    FK f (NonDet.maybeM g o) := by
  cases o
  · exact dk_pure' _
  · exact h _

theorem dk_liftM {α γ : Type} (g : α → γ) {m : NonDet (State Unit) α} (h : FK f m) :
    FK f (NonDet.liftM g m) := dk_bind' h fun _ => dk_pure' _

theorem dk_modify {g : State Unit → State Unit} (hg : ∀ σ, f (g σ) = f σ) : FK f (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hg σ

theorem dk_get_put {g : State Unit → State Unit} (hg : ∀ σ, f (g σ) = f σ) :
    FK f (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hg σ

theorem dk_get_put' {g : State Unit → State Unit} (hg : ∀ σ, f (g σ) = f σ) :
    FK f (do let s ← NonDet.get; NonDet.put (g s)) := dk_get_put hg

theorem dk_getObject (p : ObjRef) : FK f (getObject (Z := Unit) p) := dk_getsThe _

theorem dk_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, FK f (B r)) (r : α) : FK f (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => rfl
  | step _ hm _ ih => exact ih.trans (hB _ _ _ hm)

theorem dk_mapMx {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, FK f (g a)) (xs : List α) :
    FK f (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact dk_pure' _
  | cons a xs' ih => exact dk_bind' (h a) fun _ => ih

theorem dk_forMx {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, FK f (g a)) (xs : List α) :
    FK f (NonDet.forMx xs g) := dk_mapMx h xs

theorem dk_mapM {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, FK f (g a)) (xs : List α) :
    FK f (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact dk_pure' _
  | cons a xs' ih => exact dk_bind' (h a) fun _ => dk_bind' ih fun _ => dk_pure' _

end Comb

theorem dk_doMachineOp {α : Type} (mop : NonDet MachineState α) : DK (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)

theorem dk_doExtendedOp (eop : DetExtMonad Unit) : DK (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine dk_bind dk_get (fun _ => dk_bind (dk_selectF _) (fun _ => ?_))
  split
  exact dk_modify (fun σ => rfl)

/-- `FK` for the exception monad. -/
def FKE {β : Type} (f : State Unit → β) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop :=
  FK f (ExceptT.run m)

/-- `DK` for the exception monad. -/
abbrev DKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := FKE schedF m

section CombE
variable {β : Type} {f : State Unit → β} {ε : Type}

theorem dke_bind {α γ : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε γ} (hm : FKE f m)
    (hg : ∀ a, FKE f (g a)) : FKE f (m >>= g) := by
  unfold FKE; rw [ExceptT.run_bind]
  refine dk_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact dk_pure _

theorem dke_pure {α : Type} (a : α) : FKE f (pure a : NonDetE (State Unit) ε α) := dk_pure _

theorem dke_returnOk {α : Type} (a : α) : FKE f (NonDetE.returnOk a : NonDetE (State Unit) ε α) := dk_pure _

theorem dke_throw {α : Type} (e : ε) : FKE f (NonDetE.throwError e : NonDetE (State Unit) ε α) := dk_pure _

theorem dke_throw' {α : Type} (e : ε) : FKE f (throw e : NonDetE (State Unit) ε α) := dk_pure _

theorem dke_liftE {α : Type} {m : NonDet (State Unit) α} (h : FK f m) : FKE f (NonDetE.liftE (ε := ε) m) := by
  unfold FKE NonDetE.liftE; rw [ExceptT.run_lift]
  exact dk_bind h fun _ => dk_pure _

theorem dke_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : FKE f m1)
    (h2 : FKE f m2) : FKE f (if P then m1 else m2) := by
  split <;> assumption

theorem dke_whenE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : FKE f m) :
    FKE f (NonDetE.whenE P m) := by
  unfold NonDetE.whenE; exact dke_ite P h (dke_pure _)

theorem dke_unlessE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : FKE f m) :
    FKE f (NonDetE.unlessE P m) := by
  unfold NonDetE.unlessE; exact dke_ite P (dke_pure _) h

theorem dke_throwOpt {α : Type} (e : ε) (o : Option α) : FKE f (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact dke_throw' e
  · exact dke_pure _

theorem dke_assertE (P : Prop) : FKE f (NonDetE.assertE P : NonDetE (State Unit) ε Unit) :=
  dke_liftE (dk_assert P)

theorem dk_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : FKE f m)
    (hh : ∀ e, FK f (h e)) : FK f (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine dk_bind' hm fun r => ?_
  cases r with
  | ok a => exact dk_pure' _
  | error e => exact hh e

theorem dke_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : FKE f m) (hh : ∀ e, FKE f (h e)) : FKE f (NonDetE.handleE m h) := by
  unfold NonDetE.handleE FKE
  rw [ExceptT.run_mk]
  refine dk_bind' hm fun r => ?_
  cases r with
  | ok a => exact dk_pure' _
  | error e => exact hh e

theorem dke_liftME {α γ : Type} (g : α → γ) {m : NonDetE (State Unit) ε α} (h : FKE f m) :
    FKE f (NonDetE.liftME g m) := by
  unfold NonDetE.liftME; exact dke_bind h fun _ => dke_pure _

theorem dke_mapMEx {α γ : Type} {F : α → NonDetE (State Unit) ε γ} (h : ∀ a, FKE f (F a)) :
    ∀ xs : List α, FKE f (NonDetE.mapMEx F xs)
  | [] => by unfold NonDetE.mapMEx; exact dke_pure _
  | a :: as => by unfold NonDetE.mapMEx; exact dke_bind (h a) fun _ => dke_mapMEx h as

theorem dke_mapME {α γ : Type} {F : α → NonDetE (State Unit) ε γ} (h : ∀ a, FKE f (F a)) :
    ∀ xs : List α, FKE f (NonDetE.mapME F xs)
  | [] => by unfold NonDetE.mapME; exact dke_pure _
  | a :: as => by
    unfold NonDetE.mapME; exact dke_bind (h a) fun _ => dke_bind (dke_mapME h as) fun _ => dke_pure _

end CombE

/-- One step of a `DK` proof. -/
macro "dk_step0" : tactic => `(tactic| first
  | with_reducible exact dk_pure _ | with_reducible exact dk_pure' _ | with_reducible exact dk_fail
  | with_reducible exact dk_gets _ | with_reducible exact dk_get
  | with_reducible exact dk_assert _ | with_reducible exact dk_assertOpt _
  | with_reducible exact dk_getsThe _
  | with_reducible exact dk_selectF _ | with_reducible exact dk_select _
  | ((with_reducible apply dk_modify); intro _; exact rfl)
  | ((with_reducible apply dk_get_put); intro _; exact rfl)
  | (exact dk_get_put' (fun _ => rfl))
  | (exact dk_get_put (fun _ => rfl))
  | with_reducible exact dk_getObject _
  | with_reducible exact dk_doMachineOp _ | with_reducible exact dk_doExtendedOp _
  | (with_reducible refine dk_bind ?_ (fun _ => ?_))
  | (with_reducible refine dk_bind' ?_ (fun _ => ?_))
  | (with_reducible apply dk_ite) | (with_reducible apply dk_when) | (with_reducible apply dk_unless)
  | (with_reducible refine dk_maybeM (fun _ => ?_) _) | (with_reducible apply dk_liftM)
  | (with_reducible refine dk_whileLoop (fun _ => ?_) _)
  | (with_reducible refine dk_mapMx (fun _ => ?_) _)
  | (with_reducible refine dk_mapM (fun _ => ?_) _)
  | (with_reducible refine dk_forMx (fun _ => ?_) _)
  | with_reducible exact dke_pure _ | with_reducible exact dke_returnOk _ | with_reducible exact dke_throw _
  | with_reducible exact dke_throw' _ | with_reducible exact dke_throwOpt _ _ | with_reducible exact dke_assertE _
  | (with_reducible refine dke_bind ?_ (fun _ => ?_))
  | (with_reducible apply dke_liftE) | (with_reducible apply dke_ite) | (with_reducible apply dke_whenE)
  | (with_reducible apply dke_unlessE) | (with_reducible refine dk_catch ?_ (fun _ => ?_))
  | (with_reducible refine dke_handleE ?_ (fun _ => ?_)) | (with_reducible apply dke_liftME)
  | (with_reducible refine dke_mapMEx (fun _ => ?_) _) | (with_reducible refine dke_mapME (fun _ => ?_) _)
  | split
  | (dsimp only)
  | (simp only [letFun])
  | (dsimp only [letFun])
  | (with_reducible exact dk_pure _)
  | (exact dk_pure _))

macro "dk_auto0" : tactic => `(tactic| repeat' dk_step0)

/-- A `DK` lemma of a spec function (extended below, one rule per lemma). -/
syntax "dk_leaf" : tactic
macro_rules | `(tactic| dk_leaf) => `(tactic| fail "no dk_leaf")

macro "dk_auto" : tactic => `(tactic| repeat' (first | dk_leaf | dk_step0))

theorem dke_pure_run {ε α : Type} (a : α) : DK (ExceptT.run (pure a : NonDetE (State Unit) ε α)) := dk_pure _

theorem dk_setObject (p : ObjRef) (o : KernelObject) : DK (setObject (Z := Unit) p o) := by
  unfold setObject; dk_auto0
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setObject _ _)

theorem dk_setCap (c : Cap) (sl : CslotPtr) : DK (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl; unfold setCap; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_setCap _ _)

theorem dk_getCap (sl : CslotPtr) : DK (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_getCap _)

theorem dk_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) :
    DK (portOut (Z := Unit) f w) := by
  unfold portOut; dk_auto
macro_rules | `(tactic| dk_leaf) => `(tactic| with_reducible exact dk_portOut _ _)

end

end Fl4Proofs.P3.Vs
