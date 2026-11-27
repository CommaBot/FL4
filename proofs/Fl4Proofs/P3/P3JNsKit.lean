/-
P3 (p3J gen 24): **the "no signal line" invariant's kit** (spec side only; outside the `JAtZ` cone), a scripted
copy of irqfix's SpecInvIrqBoundKit (`scratch/p3J/genNs.py`: `GKB` ↦ `GKN`, `WLB` ↦ `WLN`) **without** the
bounded `set_irq_state` leaf `sisB`: `WLN P` asks `set_irq_state` only of `IRQInactive`.

* **`NoSig σ`**: no IRQ line is `IRQSignal`. Only `set_irq_state` writes the IRQ states, and only the IRQ-control
  issues (`invoke_irq_control`, `arch_invoke_irq_control`, FL4's remapped IOAPIC issue) write `IRQSignal`; every
  other writer (`deleting_irq_handler`) writes `IRQInactive`. **`wln_noSig`**: `NoSig` has the leaves.
* `GKN m := ∀ P, WLN P → IK P m` and its combinators / leaves (the Kit's, renamed).

No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.SpecInvValidMachineTime
import Fl4Proofs.P3.SpecInvValidIrqHandlers

open Classical

namespace Fl4Proofs.P3.SInvNs
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.Vs Fl4Proofs.P3.MachF Fl4Proofs.P3.MachT Fl4Proofs.P3.SInvV

noncomputable section

/-! ## The leaves -/

/-- invB's `WL` with `set_irq_state` only for `IRQInactive`. -/
structure WLN (P : State Unit → Prop) : Prop where
  view : ∀ σ σ', vw σ' = vw σ → P σ → P σ'
  uts : IK P (updateTimeStamp (Z := Unit))
  sisI : ∀ i, IK P (setIrqState (Z := Unit) .irqInactive i)
  msk : ∀ {α : Type} (mop : NonDet MachineState α), MaskT mop → IK P (doMachineOp (Z := Unit) mop)
  ack : ∀ i, IK P (doMachineOp (Z := Unit) (maskInterrupt false i))

/-- Kept by every predicate with the bounded leaves. -/
def GKN {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ P, WLN P → IK P m

/-- `GKN` for the exception monad. -/
def GKNE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := GKN (ExceptT.run m)

theorem GKN.ik {P : State Unit → Prop} (L : WLN P) {α : Type} {m : NonDet (State Unit) α} (h : GKN m) : IK P m :=
  h P L

/-! ## Frames -/

theorem gkn_of_fk {α : Type} {m : NonDet (State Unit) α} (h : FK vw m) : GKN m :=
  fun _ L σ hP x hx => L.view σ x.2 (h σ x hx) hP

theorem gkn_of_mtk {α : Type} {m : NonDet (State Unit) α} (h : MTK m) : GKN m :=
  gkn_of_fk fun σ x hx => vw_of_msFT (h σ x hx)

theorem gkne_of_mtke {ε α : Type} {m : NonDetE (State Unit) ε α} (h : MTKE m) : GKNE m :=
  gkn_of_mtk h

/-! ## Combinators -/

section Comb

theorem gkn_bind {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : GKN m)
    (hg : ∀ a, GKN (g a)) : GKN (m >>= g) := by
  intro P L σ h x ⟨y, hy, hx⟩
  exact hg y.1 P L y.2 (hm P L σ h y hy) x hx

theorem gkn_bind' {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : GKN m)
    (hg : ∀ a, GKN (g a)) : GKN (NonDet.bind m g) := gkn_bind hm hg

theorem gkn_pure {α : Type} (a : α) : GKN (pure a : NonDet (State Unit) α) := gkn_of_fk (dk_pure a)

theorem gkn_pure' {α : Type} (a : α) : GKN (NonDet.pure a : NonDet (State Unit) α) := gkn_of_fk (dk_pure a)

theorem gkn_gets {α : Type} (g : State Unit → α) : GKN (NonDet.gets g) := gkn_of_fk (dk_gets g)

theorem gkn_get : GKN (NonDet.get : NonDet (State Unit) (State Unit)) := gkn_of_fk dk_get

theorem gkn_assert (P : Prop) : GKN (NonDet.assert P : NonDet (State Unit) Unit) := gkn_of_fk (dk_assert P)

theorem gkn_fail {α : Type} : GKN (NonDet.fail : NonDet (State Unit) α) := gkn_of_fk dk_fail

theorem gkn_assertOpt {α : Type} (o : Option α) : GKN (NonDet.assertOpt o : NonDet (State Unit) α) :=
  gkn_of_fk (dk_assertOpt o)

theorem gkn_getsThe {α : Type} (g : State Unit → Option α) : GKN (NonDet.getsThe g) := gkn_of_fk (dk_getsThe g)

theorem gkn_selectF {α : Type} (S : Set α × Prop) : GKN (NonDet.selectF S : NonDet (State Unit) α) :=
  gkn_of_fk (dk_selectF S)

theorem gkn_select {α : Type} (S : Set α) : GKN (NonDet.select S : NonDet (State Unit) α) := gkn_of_fk (dk_select S)

theorem gkn_ite {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDet (State Unit) α} (h1 : GKN m1)
    (h2 : GKN m2) : GKN (if Q then m1 else m2) := by
  split <;> assumption

theorem gkn_when (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : GKN m) : GKN (NonDet.when Q m) := by
  unfold NonDet.when; exact gkn_ite Q h (gkn_pure' _)

theorem gkn_unless (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : GKN m) :
    GKN (NonDet.unless Q m) := by
  unfold NonDet.unless; exact gkn_ite Q (gkn_pure' _) h

theorem gkn_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, GKN (g a)) (o : Option α) :
    GKN (NonDet.maybeM g o) := by
  cases o
  · exact gkn_pure' _
  · exact h _

theorem gkn_liftM {α γ : Type} (g : α → γ) {m : NonDet (State Unit) α} (h : GKN m) : GKN (NonDet.liftM g m) :=
  gkn_bind' h fun _ => gkn_pure' _

theorem gkn_modify {g : State Unit → State Unit} (hg : ∀ σ, vw (g σ) = vw σ) : GKN (NonDet.modify g) :=
  gkn_of_fk (dk_modify hg)

theorem gkn_get_put {g : State Unit → State Unit} (hg : ∀ σ, vw (g σ) = vw σ) :
    GKN (NonDet.get >>= fun s => NonDet.put (g s)) := gkn_of_fk (dk_get_put hg)

theorem gkn_get_put' {g : State Unit → State Unit} (hg : ∀ σ, vw (g σ) = vw σ) :
    GKN (do let s ← NonDet.get; NonDet.put (g s)) := gkn_get_put hg

theorem gkn_getObject (p : ObjRef) : GKN (getObject (Z := Unit) p) := gkn_getsThe _

theorem gkn_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, GKN (B r)) (r : α) : GKN (NonDet.whileLoop C B r) := by
  intro P L σ h x hx
  induction hx with
  | done _ => exact h
  | step _ hm _ ih => exact ih (hB _ P L _ h _ hm)

theorem gkn_mapMx {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, GKN (g a)) (xs : List α) :
    GKN (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact gkn_pure' _
  | cons a xs' ih => exact gkn_bind' (h a) fun _ => ih

theorem gkn_forMx {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, GKN (g a)) (xs : List α) :
    GKN (NonDet.forMx xs g) := gkn_mapMx h xs

theorem gkn_mapM {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, GKN (g a)) (xs : List α) :
    GKN (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact gkn_pure' _
  | cons a xs' ih => exact gkn_bind' (h a) fun _ => gkn_bind' ih fun _ => gkn_pure' _

end Comb

section CombE
variable {ε : Type}

theorem gkne_bind {α γ : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε γ} (hm : GKNE m)
    (hg : ∀ a, GKNE (g a)) : GKNE (m >>= g) := by
  unfold GKNE; rw [ExceptT.run_bind]
  refine gkn_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact gkn_pure _

theorem gkne_pure {α : Type} (a : α) : GKNE (pure a : NonDetE (State Unit) ε α) := gkn_pure _

theorem gkne_returnOk {α : Type} (a : α) : GKNE (NonDetE.returnOk a : NonDetE (State Unit) ε α) := gkn_pure _

theorem gkne_throw {α : Type} (e : ε) : GKNE (NonDetE.throwError e : NonDetE (State Unit) ε α) := gkn_pure _

theorem gkne_throw' {α : Type} (e : ε) : GKNE (throw e : NonDetE (State Unit) ε α) := gkn_pure _

theorem gkne_liftE {α : Type} {m : NonDet (State Unit) α} (h : GKN m) : GKNE (NonDetE.liftE (ε := ε) m) := by
  unfold GKNE NonDetE.liftE; rw [ExceptT.run_lift]
  exact gkn_bind h fun _ => gkn_pure _

theorem gkne_ite {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDetE (State Unit) ε α} (h1 : GKNE m1)
    (h2 : GKNE m2) : GKNE (if Q then m1 else m2) := by
  split <;> assumption

theorem gkne_whenE (Q : Prop) [Decidable Q] {m : NonDetE (State Unit) ε Unit} (h : GKNE m) :
    GKNE (NonDetE.whenE Q m) := by
  unfold NonDetE.whenE; exact gkne_ite Q h (gkne_pure _)

theorem gkne_unlessE (Q : Prop) [Decidable Q] {m : NonDetE (State Unit) ε Unit} (h : GKNE m) :
    GKNE (NonDetE.unlessE Q m) := by
  unfold NonDetE.unlessE; exact gkne_ite Q (gkne_pure _) h

theorem gkne_throwOpt {α : Type} (e : ε) (o : Option α) : GKNE (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact gkne_throw' e
  · exact gkne_pure _

theorem gkne_assertE (Q : Prop) : GKNE (NonDetE.assertE Q : NonDetE (State Unit) ε Unit) :=
  gkne_liftE (gkn_assert Q)

theorem gkn_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : GKNE m)
    (hh : ∀ e, GKN (h e)) : GKN (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine gkn_bind' hm fun r => ?_
  cases r with
  | ok a => exact gkn_pure' _
  | error e => exact hh e

theorem gkne_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : GKNE m) (hh : ∀ e, GKNE (h e)) : GKNE (NonDetE.handleE m h) := by
  unfold NonDetE.handleE GKNE
  rw [ExceptT.run_mk]
  refine gkn_bind' hm fun r => ?_
  cases r with
  | ok a => exact gkn_pure' _
  | error e => exact hh e

theorem gkne_liftME {α γ : Type} (g : α → γ) {m : NonDetE (State Unit) ε α} (h : GKNE m) :
    GKNE (NonDetE.liftME g m) := by
  unfold NonDetE.liftME; exact gkne_bind h fun _ => gkne_pure _

theorem gkne_mapMEx {α γ : Type} {F : α → NonDetE (State Unit) ε γ} (h : ∀ a, GKNE (F a)) :
    ∀ xs : List α, GKNE (NonDetE.mapMEx F xs)
  | [] => by unfold NonDetE.mapMEx; exact gkne_pure _
  | a :: xs => by unfold NonDetE.mapMEx; exact gkne_bind (h a) fun _ => gkne_mapMEx h xs

theorem gkne_mapME {α γ : Type} {F : α → NonDetE (State Unit) ε γ} (h : ∀ a, GKNE (F a)) :
    ∀ xs : List α, GKNE (NonDetE.mapME F xs)
  | [] => by unfold NonDetE.mapME; exact gkne_pure _
  | a :: xs => by
    unfold NonDetE.mapME; exact gkne_bind (h a) fun _ => gkne_bind (gkne_mapME h xs) fun _ => gkne_pure _

theorem gkne_withoutPreemption {α : Type} {m : SMonad Unit α} (h : GKN m) :
    GKNE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; exact gkne_liftE h

theorem gkne_capFaultOnFailure {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : GKNE m) :
    GKNE (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact gkne_handleE h fun _ => gkne_throw _

theorem gkne_lookupErrorOnFailure {α : Type} (b : Bool) {m : LFMonad Unit α} (h : GKNE m) :
    GKNE (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact gkne_handleE h fun _ => gkne_throw _

theorem gkne_unifyFailure {F α : Type} {m : NonDetE (State Unit) F α} (h : GKNE m) :
    GKNE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact gkne_handleE h fun _ => gkne_throw _

theorem gkn_emptyOnFailure {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : GKNE m) :
    GKN (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact gkn_catch h fun _ => gkn_pure' _

theorem gkn_constOnFailure {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : GKNE m) :
    GKN (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact gkn_catch h fun _ => gkn_pure' _

end CombE

/-! ## The writer leaves -/

theorem gkn_doMachineOp {α : Type} {mop : NonDet MachineState α} (h : MaskT mop) :
    GKN (doMachineOp (Z := Unit) mop) := fun _ L => L.msk mop h

theorem gkn_updateTimeStamp : GKN (updateTimeStamp (Z := Unit)) := fun _ L => L.uts

theorem gkn_setIrqState_in (i : Irq) : GKN (setIrqState (Z := Unit) .irqInactive i) := fun _ L => L.sisI i

theorem gkn_ack (i : Irq) : GKN (doMachineOp (Z := Unit) (maskInterrupt false i)) := fun _ L => L.ack i

/-- One step of a `GKN` proof. -/
macro "gkn_step0" : tactic => `(tactic| first
  | with_reducible exact gkn_pure _ | with_reducible exact gkn_pure' _ | with_reducible exact gkn_fail
  | with_reducible exact gkn_gets _ | with_reducible exact gkn_get
  | with_reducible exact gkn_assert _ | with_reducible exact gkn_assertOpt _
  | with_reducible exact gkn_getsThe _
  | with_reducible exact gkn_selectF _ | with_reducible exact gkn_select _
  | ((with_reducible apply gkn_modify); intro _; exact rfl)
  | ((with_reducible apply gkn_get_put); intro _; exact rfl)
  | (exact gkn_get_put' (fun _ => rfl))
  | (exact gkn_get_put (fun _ => rfl))
  | with_reducible exact gkn_getObject _
  | with_reducible exact gkn_updateTimeStamp | with_reducible exact gkn_setIrqState_in _
  | with_reducible exact gkn_ack _
  | with_reducible exact gkn_of_mtk (mtk_performPml4Flush _)
  | ((with_reducible refine gkn_doMachineOp ?_); mt_auto; done)
  | (with_reducible refine gkn_bind ?_ (fun _ => ?_))
  | (with_reducible refine gkn_bind' ?_ (fun _ => ?_))
  | (with_reducible apply gkn_ite) | (with_reducible apply gkn_when) | (with_reducible apply gkn_unless)
  | (with_reducible refine gkn_maybeM (fun _ => ?_) _) | (with_reducible apply gkn_liftM)
  | (with_reducible refine gkn_whileLoop (fun _ => ?_) _)
  | (with_reducible refine gkn_mapMx (fun _ => ?_) _)
  | (with_reducible refine gkn_mapM (fun _ => ?_) _)
  | (with_reducible refine gkn_forMx (fun _ => ?_) _)
  | with_reducible exact gkne_pure _ | with_reducible exact gkne_returnOk _ | with_reducible exact gkne_throw _
  | with_reducible exact gkne_throw' _ | with_reducible exact gkne_throwOpt _ _ | with_reducible exact gkne_assertE _
  | (with_reducible refine gkne_bind ?_ (fun _ => ?_))
  | (with_reducible apply gkne_liftE) | (with_reducible apply gkne_ite) | (with_reducible apply gkne_whenE)
  | (with_reducible apply gkne_unlessE) | (with_reducible refine gkn_catch ?_ (fun _ => ?_))
  | (with_reducible refine gkne_handleE ?_ (fun _ => ?_)) | (with_reducible apply gkne_liftME)
  | (with_reducible refine gkne_mapMEx (fun _ => ?_) _) | (with_reducible refine gkne_mapME (fun _ => ?_) _)
  | (with_reducible apply gkne_withoutPreemption) | (with_reducible apply gkne_capFaultOnFailure)
  | (with_reducible apply gkne_lookupErrorOnFailure) | (with_reducible apply gkne_unifyFailure)
  | (with_reducible apply gkn_emptyOnFailure) | (with_reducible apply gkn_constOnFailure)
  | split
  | (dsimp only)
  | (simp only [letFun])
  | (dsimp only [letFun])
  | (with_reducible exact gkn_pure _)
  | (exact gkn_pure _))

/-- A `GKN` lemma of a spec function (extended by the generated family, one
rule per lemma). -/
syntax "gkn_leaf" : tactic
macro_rules | `(tactic| gkn_leaf) => `(tactic| fail "no gkn_leaf")

/-- `GKN` from MachFieldFamT's `MTK` family, else one step. -/
macro "gkn_auto" : tactic => `(tactic| repeat' (first
  | gkn_leaf
  | gkn_step0
  | ((with_reducible apply gkn_of_mtk); mtk_leaf; done)
  | ((with_reducible apply gkne_of_mtke); mtk_leaf; done)))

/-! ## No signal line -/

/-- **No IRQ line is `IRQSignal`** (module docstring). -/
def NoSig (σ : State Unit) : Prop := ∀ irq : Irq, σ.interruptStates irq ≠ .irqSignal

theorem ik_dmo_noSig {α : Type} (mop : NonDet MachineState α) : IK NoSig (doMachineOp (Z := Unit) mop) := by
  intro σ h x hx
  unfold doMachineOp at hx
  obtain ⟨⟨ms0, s1⟩, h1, ⟨⟨r, ms'⟩, s2⟩, h2, ⟨u, s3⟩, h3, hx⟩ := hx
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h1)
  obtain ⟨-, e2⟩ := h2
  dsimp only at e2
  subst e2
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h3)
  rw [Set.mem_singleton_iff.1 hx]
  exact h

theorem ik_sis_noSig (i : Irq) : IK NoSig (setIrqState (Z := Unit) .irqInactive i) := by
  intro σ h x hx
  unfold setIrqState at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hx
  refine ik_dmo_noSig _ _ ?_ x hx
  intro irq
  show Function.update σ.interruptStates i .irqInactive irq ≠ .irqSignal
  by_cases e : irq = i
  · subst e
    rw [Function.update_self]
    exact fun h' => by cases h'
  · rw [Function.update_of_ne e]; exact h irq

/-- **`NoSig` has the leaves** (`set_irq_state` of `IRQInactive` only). -/
theorem wln_noSig : WLN NoSig where
  view σ σ' e h := by
    unfold vw at e; simp only [Prod.mk.injEq] at e
    intro irq; rw [e.2.2.1]; exact h irq
  uts σ h x hx := by
    obtain ⟨-, -, e, -⟩ := uts_out hx
    intro irq; rw [e]; exact h irq
  sisI i := ik_sis_noSig i
  msk mop _ := ik_dmo_noSig mop
  ack i := ik_dmo_noSig _

end

end Fl4Proofs.P3.SInvNs
