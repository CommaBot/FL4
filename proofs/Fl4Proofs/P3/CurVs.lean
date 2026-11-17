/-
P3 (DESIGN.md §9): **the spec keeps `cur_thread`** (`CTK`), a mechanical copy
of VsDom's `DK` (the domain schedule) for `cur_thread`: no step of the
arch invocations, the deletions or `install_tcb_cap` writes it.
-/
import Fl4Spec.Ext.Invocation
import Fl4Spec.Ext.VSpace
open Classical

namespace Fl4Proofs.P3.Vs.CurK
open Fl4Spec

noncomputable section

/-- Every outcome of `m` keeps the domain schedule. -/
def CTK {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, x ∈ (m σ).1 → x.2.curThread = σ.curThread ∧ x.2.curThread = σ.curThread

section Comb

theorem ctk_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : CTK m)
    (hg : ∀ a, CTK (g a)) : CTK (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨a1, a2⟩ := hm σ y hy
  obtain ⟨b1, b2⟩ := hg y.1 y.2 x hx
  exact ⟨b1.trans a1, b2.trans a2⟩

theorem ctk_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : CTK m)
    (hg : ∀ a, CTK (g a)) : CTK (NonDet.bind m g) := ctk_bind hm hg

theorem ctk_pure {α : Type} (a : α) : CTK (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ⟨rfl, rfl⟩

theorem ctk_pure' {α : Type} (a : α) : CTK (NonDet.pure a : NonDet (State Unit) α) := ctk_pure a

theorem ctk_gets {α : Type} (g : State Unit → α) : CTK (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ⟨rfl, rfl⟩

theorem ctk_get : CTK (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ⟨rfl, rfl⟩

theorem ctk_assert (P : Prop) : CTK (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact ⟨rfl, rfl⟩

theorem ctk_fail {α : Type} : CTK (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem ctk_assertOpt {α : Type} (o : Option α) : CTK (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact ctk_fail
  · exact ctk_pure' _

theorem ctk_getsThe {α : Type} (g : State Unit → Option α) : CTK (NonDet.getsThe g) := by
  intro σ x hx; exact ctk_assertOpt (g σ) σ x hx

theorem ctk_selectF {α : Type} (S : Set α × Prop) : CTK (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact ⟨rfl, rfl⟩

theorem ctk_select {α : Type} (S : Set α) : CTK (NonDet.select S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact ⟨rfl, rfl⟩

theorem ctk_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : CTK m1)
    (h2 : CTK m2) : CTK (if P then m1 else m2) := by
  split <;> assumption

theorem ctk_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : CTK m) :
    CTK (NonDet.when P m) := by
  unfold NonDet.when; exact ctk_ite P h (ctk_pure' _)

theorem ctk_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : CTK m) :
    CTK (NonDet.unless P m) := by
  unfold NonDet.unless; exact ctk_ite P (ctk_pure' _) h

theorem ctk_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, CTK (g a)) (o : Option α) :
    CTK (NonDet.maybeM g o) := by
  cases o
  · exact ctk_pure' _
  · exact h _

theorem ctk_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : CTK m) :
    CTK (NonDet.liftM g m) := ctk_bind' h fun _ => ctk_pure' _

theorem ctk_modify {g : State Unit → State Unit}
    (hg : ∀ σ, (g σ).curThread = σ.curThread ∧ (g σ).curThread = σ.curThread) :
    CTK (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hg σ

theorem ctk_put_of {σ0 : State Unit} : CTK (NonDet.put σ0) ∨ True := Or.inr trivial

theorem ctk_get_put {g : State Unit → State Unit}
    (hg : ∀ σ, (g σ).curThread = σ.curThread ∧ (g σ).curThread = σ.curThread) :
    CTK (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hg σ

theorem ctk_get_put' {g : State Unit → State Unit}
    (hg : ∀ σ, (g σ).curThread = σ.curThread ∧ (g σ).curThread = σ.curThread) :
    CTK (do let s ← NonDet.get; NonDet.put (g s)) := ctk_get_put hg

theorem ctk_getObject (p : ObjRef) : CTK (getObject (Z := Unit) p) := ctk_getsThe _

theorem ctk_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, CTK (B r)) (r : α) : CTK (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => exact ⟨rfl, rfl⟩
  | step _ hm _ ih =>
    obtain ⟨a1, a2⟩ := hB _ _ _ hm
    exact ⟨ih.1.trans a1, ih.2.trans a2⟩

theorem ctk_mapMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, CTK (g a)) (xs : List α) :
    CTK (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact ctk_pure' _
  | cons a xs' ih => exact ctk_bind' (h a) fun _ => ih

theorem ctk_forMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, CTK (g a)) (xs : List α) :
    CTK (NonDet.forMx xs g) := ctk_mapMx h xs

theorem ctk_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, CTK (g a)) (xs : List α) :
    CTK (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact ctk_pure' _
  | cons a xs' ih => exact ctk_bind' (h a) fun _ => ctk_bind' ih fun _ => ctk_pure' _

theorem ctk_doMachineOp {α : Type} (mop : NonDet MachineState α) : CTK (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine ctk_bind (ctk_gets _) (fun _ => ctk_bind (ctk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact ctk_bind (ctk_modify (fun σ => ⟨rfl, rfl⟩)) (fun _ => ctk_pure _)

theorem ctk_doExtendedOp (eop : DetExtMonad Unit) : CTK (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine ctk_bind ctk_get (fun _ => ctk_bind (ctk_selectF _) (fun _ => ?_))
  split
  exact ctk_modify (fun σ => ⟨rfl, rfl⟩)

end Comb

/-- `CTK` for the exception monad. -/
def CTKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := CTK (ExceptT.run m)

section CombE
variable {ε : Type}

theorem ctke_bind {α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β} (hm : CTKE m)
    (hg : ∀ a, CTKE (g a)) : CTKE (m >>= g) := by
  unfold CTKE; rw [ExceptT.run_bind]
  refine ctk_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact ctk_pure _

theorem ctke_pure {α : Type} (a : α) : CTKE (pure a : NonDetE (State Unit) ε α) := ctk_pure _

theorem ctke_returnOk {α : Type} (a : α) : CTKE (NonDetE.returnOk a : NonDetE (State Unit) ε α) := ctk_pure _

theorem ctke_throw {α : Type} (e : ε) : CTKE (NonDetE.throwError e : NonDetE (State Unit) ε α) := ctk_pure _

theorem ctke_throw' {α : Type} (e : ε) : CTKE (throw e : NonDetE (State Unit) ε α) := ctk_pure _

theorem ctke_liftE {α : Type} {m : NonDet (State Unit) α} (h : CTK m) : CTKE (NonDetE.liftE (ε := ε) m) := by
  unfold CTKE NonDetE.liftE; rw [ExceptT.run_lift]
  exact ctk_bind h fun _ => ctk_pure _

theorem ctke_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : CTKE m1)
    (h2 : CTKE m2) : CTKE (if P then m1 else m2) := by
  split <;> assumption

theorem ctke_whenE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : CTKE m) :
    CTKE (NonDetE.whenE P m) := by
  unfold NonDetE.whenE; exact ctke_ite P h (ctke_pure _)

theorem ctke_unlessE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : CTKE m) :
    CTKE (NonDetE.unlessE P m) := by
  unfold NonDetE.unlessE; exact ctke_ite P (ctke_pure _) h

theorem ctke_throwOpt {α : Type} (e : ε) (o : Option α) : CTKE (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact ctke_throw' e
  · exact ctke_pure _

theorem ctke_assertE (P : Prop) : CTKE (NonDetE.assertE P : NonDetE (State Unit) ε Unit) :=
  ctke_liftE (ctk_assert P)

theorem ctk_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : CTKE m)
    (hh : ∀ e, CTK (h e)) : CTK (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine ctk_bind' hm fun r => ?_
  cases r with
  | ok a => exact ctk_pure' _
  | error e => exact hh e

theorem ctke_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : CTKE m) (hh : ∀ e, CTKE (h e)) : CTKE (NonDetE.handleE m h) := by
  unfold NonDetE.handleE CTKE
  rw [ExceptT.run_mk]
  refine ctk_bind' hm fun r => ?_
  cases r with
  | ok a => exact ctk_pure' _
  | error e => exact hh e

theorem ctke_liftME {α β : Type} (f : α → β) {m : NonDetE (State Unit) ε α} (h : CTKE m) :
    CTKE (NonDetE.liftME f m) := by
  unfold NonDetE.liftME; exact ctke_bind h fun _ => ctke_pure _

theorem ctke_mapMEx {α β : Type} {f : α → NonDetE (State Unit) ε β} (h : ∀ a, CTKE (f a)) :
    ∀ xs : List α, CTKE (NonDetE.mapMEx f xs)
  | [] => by unfold NonDetE.mapMEx; exact ctke_pure _
  | a :: as => by unfold NonDetE.mapMEx; exact ctke_bind (h a) fun _ => ctke_mapMEx h as

theorem ctke_mapME {α β : Type} {f : α → NonDetE (State Unit) ε β} (h : ∀ a, CTKE (f a)) :
    ∀ xs : List α, CTKE (NonDetE.mapME f xs)
  | [] => by unfold NonDetE.mapME; exact ctke_pure _
  | a :: as => by
    unfold NonDetE.mapME; exact ctke_bind (h a) fun _ => ctke_bind (ctke_mapME h as) fun _ => ctke_pure _

end CombE

/-- One step of a `CTK` proof. -/
macro "ctk_step0" : tactic => `(tactic| first
  | with_reducible exact ctk_pure _ | with_reducible exact ctk_pure' _ | with_reducible exact ctk_fail
  | with_reducible exact ctk_gets _ | with_reducible exact ctk_get
  | with_reducible exact ctk_assert _ | with_reducible exact ctk_assertOpt _
  | with_reducible exact ctk_getsThe _
  | with_reducible exact ctk_selectF _ | with_reducible exact ctk_select _
  | ((with_reducible apply ctk_modify); intro _; exact ⟨rfl, rfl⟩)
  | ((with_reducible apply ctk_get_put); intro _; exact ⟨rfl, rfl⟩)
  | (exact ctk_get_put' (fun _ => ⟨rfl, rfl⟩))
  | (exact ctk_get_put (fun _ => ⟨rfl, rfl⟩))
  | with_reducible exact ctk_getObject _
  | with_reducible exact ctk_doMachineOp _ | with_reducible exact ctk_doExtendedOp _
  | (with_reducible refine ctk_bind ?_ (fun _ => ?_))
  | (with_reducible refine ctk_bind' ?_ (fun _ => ?_))
  | (with_reducible apply ctk_ite) | (with_reducible apply ctk_when) | (with_reducible apply ctk_unless)
  | (with_reducible refine ctk_maybeM (fun _ => ?_) _) | (with_reducible apply ctk_liftM)
  | (with_reducible refine ctk_whileLoop (fun _ => ?_) _)
  | (with_reducible refine ctk_mapMx (fun _ => ?_) _)
  | (with_reducible refine ctk_mapM (fun _ => ?_) _)
  | (with_reducible refine ctk_forMx (fun _ => ?_) _)
  | with_reducible exact ctke_pure _ | with_reducible exact ctke_returnOk _ | with_reducible exact ctke_throw _
  | with_reducible exact ctke_throw' _ | with_reducible exact ctke_throwOpt _ _ | with_reducible exact ctke_assertE _
  | (with_reducible refine ctke_bind ?_ (fun _ => ?_))
  | (with_reducible apply ctke_liftE) | (with_reducible apply ctke_ite) | (with_reducible apply ctke_whenE)
  | (with_reducible apply ctke_unlessE) | (with_reducible refine ctk_catch ?_ (fun _ => ?_))
  | (with_reducible refine ctke_handleE ?_ (fun _ => ?_)) | (with_reducible apply ctke_liftME)
  | (with_reducible refine ctke_mapMEx (fun _ => ?_) _) | (with_reducible refine ctke_mapME (fun _ => ?_) _)
  | split
  | (dsimp only)
  | (simp only [letFun])
  | (dsimp only [letFun])
  | (with_reducible exact ctk_pure _)
  | (exact ctk_pure _))

macro "ctk_auto0" : tactic => `(tactic| repeat' ctk_step0)

/-- A `CTK` lemma of a spec function (extended below, one rule per lemma). -/
syntax "ctk_leaf" : tactic
macro_rules | `(tactic| ctk_leaf) => `(tactic| fail "no ctk_leaf")

macro "ctk_auto" : tactic => `(tactic| repeat' (first | ctk_leaf | ctk_step0))

theorem ctke_pure_run {ε α : Type} (a : α) : CTK (ExceptT.run (pure a : NonDetE (State Unit) ε α)) := ctk_pure _

theorem ctk_setObject (p : ObjRef) (o : KernelObject) : CTK (setObject (Z := Unit) p o) := by
  unfold setObject; ctk_auto0
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setObject _ _)

theorem ctk_setCap (c : Cap) (sl : CslotPtr) : CTK (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl; unfold setCap; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_setCap _ _)

theorem ctk_getCap (sl : CslotPtr) : CTK (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_getCap _)

theorem ctk_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) :
    CTK (portOut (Z := Unit) f w) := by
  unfold portOut; ctk_auto
macro_rules | `(tactic| ctk_leaf) => `(tactic| with_reducible exact ctk_portOut _ _)

end

end Fl4Proofs.P3.Vs.CurK
