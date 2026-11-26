/-
P3 (line irqfix, gen 2): **the IRQ handler cap bound `IrqCapBound` and its kit** (spec side only; outside
the `JAtZ` cone: SpecInvValidMachineTimeKit and SpecInvValidIrqHandlers).

* **`IrqCapBound σ`** (l4v `valid_cap` for `IRQHandlerCap irq`, Isabelle
  `proof/invariant-abstract/Invariants_AI.thy` `valid_cap_def`: `IRQHandlerCap irq ⇒ irq ≤ maxIRQ`, read
  through `valid_objs` / `caps_of_state`): every IRQ handler cap readable in a slot (`capOpt`, what
  `get_cap` returns) names a line `≤ maxIRQ`.
* `IrqStB σ`: every line above `maxIRQ` is `IRQInactive` (l4v: `init_irqs` leaves every line inactive,
  `invoke_irq_control` / `arch_invoke_irq_control` set `IRQSignal` only on a line their decode bounded,
  `arch_check_irq` / the `maxUserIRQ - minUserIRQ` range check; `deleted_irq_handler` sets `IRQInactive`).
  **`ValidIrqHandlers σ ∧ IrqStB σ → IrqCapBound σ`** (`irqCapBound_of`): a handler cap's line is not
  inactive (`valid_irq_handlers`), so it is `≤ maxIRQ`. `IrqStB` is the inductive part: it reads only the
  IRQ states, and only `set_irq_state` writes them.
* `WLB P`: invB's `WL` (`vw`-predicates: time, IRQ states, masks) with `set_irq_state` only for
  `IRQInactive` (`sisI`) or a line `≤ maxIRQ` (`sisB`). `GKB m := ∀ P, WLB P → IK P m`, combinators
  (invB's `GK` kit renamed, scratch/irqfix2), `gkb_of_mtk` (MachFieldFamT's `MTK` family keeps `vw`).
  `wlb_irqStB`: `IrqStB` has the leaves.
-/
import Fl4Proofs.P3.SpecInvValidMachineTime
import Fl4Proofs.P3.SpecInvValidIrqHandlers

open Classical

namespace Fl4Proofs.P3.SInvIB
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.Vs Fl4Proofs.P3.MachF Fl4Proofs.P3.MachT Fl4Proofs.P3.SInvV

noncomputable section

/-! ## The invariants -/

/-- **l4v `valid_cap` for IRQ handler caps** (module docstring): every handler cap in a slot names a line
`≤ maxIRQ`. -/
def IrqCapBound (σ : State Unit) : Prop :=
  ∀ p cref irq, capOpt (σ.kheap p) cref = some (.irqHandlerCap irq) → irq ≤ maxIRQ

/-- Every line above `maxIRQ` is inactive (module docstring). -/
def IrqStB (σ : State Unit) : Prop :=
  ∀ irq : Irq, maxIRQ < irq → σ.interruptStates irq = .irqInactive

/-- **`ValidIrqHandlers` and `IrqStB` give `IrqCapBound`.** -/
theorem irqCapBound_of {σ : State Unit} (hv : ValidIrqHandlers σ) (hb : IrqStB σ) : IrqCapBound σ := by
  intro p cref irq hc
  by_contra hn
  exact hv p cref irq hc (hb irq (BitVec.not_le.1 hn))

/-! ## The leaves -/

/-- invB's `WL` with `set_irq_state` only for `IRQInactive` or a line `≤ maxIRQ`. -/
structure WLB (P : State Unit → Prop) : Prop where
  view : ∀ σ σ', vw σ' = vw σ → P σ → P σ'
  uts : IK P (updateTimeStamp (Z := Unit))
  sisI : ∀ i, IK P (setIrqState (Z := Unit) .irqInactive i)
  sisB : ∀ st i, i ≤ maxIRQ → IK P (setIrqState (Z := Unit) st i)
  msk : ∀ {α : Type} (mop : NonDet MachineState α), MaskT mop → IK P (doMachineOp (Z := Unit) mop)
  ack : ∀ i, IK P (doMachineOp (Z := Unit) (maskInterrupt false i))

/-- Kept by every predicate with the bounded leaves. -/
def GKB {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ P, WLB P → IK P m

/-- `GKB` for the exception monad. -/
def GKBE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := GKB (ExceptT.run m)

theorem GKB.ik {P : State Unit → Prop} (L : WLB P) {α : Type} {m : NonDet (State Unit) α} (h : GKB m) : IK P m :=
  h P L

/-! ## Frames -/

theorem gkb_of_fk {α : Type} {m : NonDet (State Unit) α} (h : FK vw m) : GKB m :=
  fun _ L σ hP x hx => L.view σ x.2 (h σ x hx) hP

theorem gkb_of_mtk {α : Type} {m : NonDet (State Unit) α} (h : MTK m) : GKB m :=
  gkb_of_fk fun σ x hx => vw_of_msFT (h σ x hx)

theorem gkbe_of_mtke {ε α : Type} {m : NonDetE (State Unit) ε α} (h : MTKE m) : GKBE m :=
  gkb_of_mtk h

/-! ## Combinators -/

section Comb

theorem gkb_bind {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : GKB m)
    (hg : ∀ a, GKB (g a)) : GKB (m >>= g) := by
  intro P L σ h x ⟨y, hy, hx⟩
  exact hg y.1 P L y.2 (hm P L σ h y hy) x hx

theorem gkb_bind' {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : GKB m)
    (hg : ∀ a, GKB (g a)) : GKB (NonDet.bind m g) := gkb_bind hm hg

theorem gkb_pure {α : Type} (a : α) : GKB (pure a : NonDet (State Unit) α) := gkb_of_fk (dk_pure a)

theorem gkb_pure' {α : Type} (a : α) : GKB (NonDet.pure a : NonDet (State Unit) α) := gkb_of_fk (dk_pure a)

theorem gkb_gets {α : Type} (g : State Unit → α) : GKB (NonDet.gets g) := gkb_of_fk (dk_gets g)

theorem gkb_get : GKB (NonDet.get : NonDet (State Unit) (State Unit)) := gkb_of_fk dk_get

theorem gkb_assert (P : Prop) : GKB (NonDet.assert P : NonDet (State Unit) Unit) := gkb_of_fk (dk_assert P)

theorem gkb_fail {α : Type} : GKB (NonDet.fail : NonDet (State Unit) α) := gkb_of_fk dk_fail

theorem gkb_assertOpt {α : Type} (o : Option α) : GKB (NonDet.assertOpt o : NonDet (State Unit) α) :=
  gkb_of_fk (dk_assertOpt o)

theorem gkb_getsThe {α : Type} (g : State Unit → Option α) : GKB (NonDet.getsThe g) := gkb_of_fk (dk_getsThe g)

theorem gkb_selectF {α : Type} (S : Set α × Prop) : GKB (NonDet.selectF S : NonDet (State Unit) α) :=
  gkb_of_fk (dk_selectF S)

theorem gkb_select {α : Type} (S : Set α) : GKB (NonDet.select S : NonDet (State Unit) α) := gkb_of_fk (dk_select S)

theorem gkb_ite {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDet (State Unit) α} (h1 : GKB m1)
    (h2 : GKB m2) : GKB (if Q then m1 else m2) := by
  split <;> assumption

theorem gkb_when (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : GKB m) : GKB (NonDet.when Q m) := by
  unfold NonDet.when; exact gkb_ite Q h (gkb_pure' _)

theorem gkb_unless (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : GKB m) :
    GKB (NonDet.unless Q m) := by
  unfold NonDet.unless; exact gkb_ite Q (gkb_pure' _) h

theorem gkb_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, GKB (g a)) (o : Option α) :
    GKB (NonDet.maybeM g o) := by
  cases o
  · exact gkb_pure' _
  · exact h _

theorem gkb_liftM {α γ : Type} (g : α → γ) {m : NonDet (State Unit) α} (h : GKB m) : GKB (NonDet.liftM g m) :=
  gkb_bind' h fun _ => gkb_pure' _

theorem gkb_modify {g : State Unit → State Unit} (hg : ∀ σ, vw (g σ) = vw σ) : GKB (NonDet.modify g) :=
  gkb_of_fk (dk_modify hg)

theorem gkb_get_put {g : State Unit → State Unit} (hg : ∀ σ, vw (g σ) = vw σ) :
    GKB (NonDet.get >>= fun s => NonDet.put (g s)) := gkb_of_fk (dk_get_put hg)

theorem gkb_get_put' {g : State Unit → State Unit} (hg : ∀ σ, vw (g σ) = vw σ) :
    GKB (do let s ← NonDet.get; NonDet.put (g s)) := gkb_get_put hg

theorem gkb_getObject (p : ObjRef) : GKB (getObject (Z := Unit) p) := gkb_getsThe _

theorem gkb_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, GKB (B r)) (r : α) : GKB (NonDet.whileLoop C B r) := by
  intro P L σ h x hx
  induction hx with
  | done _ => exact h
  | step _ hm _ ih => exact ih (hB _ P L _ h _ hm)

theorem gkb_mapMx {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, GKB (g a)) (xs : List α) :
    GKB (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact gkb_pure' _
  | cons a xs' ih => exact gkb_bind' (h a) fun _ => ih

theorem gkb_forMx {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, GKB (g a)) (xs : List α) :
    GKB (NonDet.forMx xs g) := gkb_mapMx h xs

theorem gkb_mapM {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, GKB (g a)) (xs : List α) :
    GKB (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact gkb_pure' _
  | cons a xs' ih => exact gkb_bind' (h a) fun _ => gkb_bind' ih fun _ => gkb_pure' _

end Comb

section CombE
variable {ε : Type}

theorem gkbe_bind {α γ : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε γ} (hm : GKBE m)
    (hg : ∀ a, GKBE (g a)) : GKBE (m >>= g) := by
  unfold GKBE; rw [ExceptT.run_bind]
  refine gkb_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact gkb_pure _

theorem gkbe_pure {α : Type} (a : α) : GKBE (pure a : NonDetE (State Unit) ε α) := gkb_pure _

theorem gkbe_returnOk {α : Type} (a : α) : GKBE (NonDetE.returnOk a : NonDetE (State Unit) ε α) := gkb_pure _

theorem gkbe_throw {α : Type} (e : ε) : GKBE (NonDetE.throwError e : NonDetE (State Unit) ε α) := gkb_pure _

theorem gkbe_throw' {α : Type} (e : ε) : GKBE (throw e : NonDetE (State Unit) ε α) := gkb_pure _

theorem gkbe_liftE {α : Type} {m : NonDet (State Unit) α} (h : GKB m) : GKBE (NonDetE.liftE (ε := ε) m) := by
  unfold GKBE NonDetE.liftE; rw [ExceptT.run_lift]
  exact gkb_bind h fun _ => gkb_pure _

theorem gkbe_ite {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDetE (State Unit) ε α} (h1 : GKBE m1)
    (h2 : GKBE m2) : GKBE (if Q then m1 else m2) := by
  split <;> assumption

theorem gkbe_whenE (Q : Prop) [Decidable Q] {m : NonDetE (State Unit) ε Unit} (h : GKBE m) :
    GKBE (NonDetE.whenE Q m) := by
  unfold NonDetE.whenE; exact gkbe_ite Q h (gkbe_pure _)

theorem gkbe_unlessE (Q : Prop) [Decidable Q] {m : NonDetE (State Unit) ε Unit} (h : GKBE m) :
    GKBE (NonDetE.unlessE Q m) := by
  unfold NonDetE.unlessE; exact gkbe_ite Q (gkbe_pure _) h

theorem gkbe_throwOpt {α : Type} (e : ε) (o : Option α) : GKBE (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact gkbe_throw' e
  · exact gkbe_pure _

theorem gkbe_assertE (Q : Prop) : GKBE (NonDetE.assertE Q : NonDetE (State Unit) ε Unit) :=
  gkbe_liftE (gkb_assert Q)

theorem gkb_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : GKBE m)
    (hh : ∀ e, GKB (h e)) : GKB (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine gkb_bind' hm fun r => ?_
  cases r with
  | ok a => exact gkb_pure' _
  | error e => exact hh e

theorem gkbe_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : GKBE m) (hh : ∀ e, GKBE (h e)) : GKBE (NonDetE.handleE m h) := by
  unfold NonDetE.handleE GKBE
  rw [ExceptT.run_mk]
  refine gkb_bind' hm fun r => ?_
  cases r with
  | ok a => exact gkb_pure' _
  | error e => exact hh e

theorem gkbe_liftME {α γ : Type} (g : α → γ) {m : NonDetE (State Unit) ε α} (h : GKBE m) :
    GKBE (NonDetE.liftME g m) := by
  unfold NonDetE.liftME; exact gkbe_bind h fun _ => gkbe_pure _

theorem gkbe_mapMEx {α γ : Type} {F : α → NonDetE (State Unit) ε γ} (h : ∀ a, GKBE (F a)) :
    ∀ xs : List α, GKBE (NonDetE.mapMEx F xs)
  | [] => by unfold NonDetE.mapMEx; exact gkbe_pure _
  | a :: xs => by unfold NonDetE.mapMEx; exact gkbe_bind (h a) fun _ => gkbe_mapMEx h xs

theorem gkbe_mapME {α γ : Type} {F : α → NonDetE (State Unit) ε γ} (h : ∀ a, GKBE (F a)) :
    ∀ xs : List α, GKBE (NonDetE.mapME F xs)
  | [] => by unfold NonDetE.mapME; exact gkbe_pure _
  | a :: xs => by
    unfold NonDetE.mapME; exact gkbe_bind (h a) fun _ => gkbe_bind (gkbe_mapME h xs) fun _ => gkbe_pure _

theorem gkbe_withoutPreemption {α : Type} {m : SMonad Unit α} (h : GKB m) :
    GKBE (withoutPreemption (Z := Unit) m) := by
  unfold withoutPreemption; exact gkbe_liftE h

theorem gkbe_capFaultOnFailure {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : GKBE m) :
    GKBE (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact gkbe_handleE h fun _ => gkbe_throw _

theorem gkbe_lookupErrorOnFailure {α : Type} (b : Bool) {m : LFMonad Unit α} (h : GKBE m) :
    GKBE (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact gkbe_handleE h fun _ => gkbe_throw _

theorem gkbe_unifyFailure {F α : Type} {m : NonDetE (State Unit) F α} (h : GKBE m) :
    GKBE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact gkbe_handleE h fun _ => gkbe_throw _

theorem gkb_emptyOnFailure {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : GKBE m) :
    GKB (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact gkb_catch h fun _ => gkb_pure' _

theorem gkb_constOnFailure {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : GKBE m) :
    GKB (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact gkb_catch h fun _ => gkb_pure' _

end CombE

/-! ## The writer leaves -/

theorem gkb_doMachineOp {α : Type} {mop : NonDet MachineState α} (h : MaskT mop) :
    GKB (doMachineOp (Z := Unit) mop) := fun _ L => L.msk mop h

theorem gkb_updateTimeStamp : GKB (updateTimeStamp (Z := Unit)) := fun _ L => L.uts

theorem gkb_setIrqState_in (i : Irq) : GKB (setIrqState (Z := Unit) .irqInactive i) := fun _ L => L.sisI i

theorem gkb_setIrqState_le (st : IrqState) (i : Irq) (h : i ≤ maxIRQ) : GKB (setIrqState (Z := Unit) st i) :=
  fun _ L => L.sisB st i h

theorem gkb_ack (i : Irq) : GKB (doMachineOp (Z := Unit) (maskInterrupt false i)) := fun _ L => L.ack i

/-- One step of a `GKB` proof. -/
macro "gkb_step0" : tactic => `(tactic| first
  | with_reducible exact gkb_pure _ | with_reducible exact gkb_pure' _ | with_reducible exact gkb_fail
  | with_reducible exact gkb_gets _ | with_reducible exact gkb_get
  | with_reducible exact gkb_assert _ | with_reducible exact gkb_assertOpt _
  | with_reducible exact gkb_getsThe _
  | with_reducible exact gkb_selectF _ | with_reducible exact gkb_select _
  | ((with_reducible apply gkb_modify); intro _; exact rfl)
  | ((with_reducible apply gkb_get_put); intro _; exact rfl)
  | (exact gkb_get_put' (fun _ => rfl))
  | (exact gkb_get_put (fun _ => rfl))
  | with_reducible exact gkb_getObject _
  | with_reducible exact gkb_updateTimeStamp | with_reducible exact gkb_setIrqState_in _
  | ((with_reducible refine gkb_setIrqState_le _ _ ?_); assumption)
  | with_reducible exact gkb_ack _
  | with_reducible exact gkb_of_mtk (mtk_performPml4Flush _)
  | ((with_reducible refine gkb_doMachineOp ?_); mt_auto; done)
  | (with_reducible refine gkb_bind ?_ (fun _ => ?_))
  | (with_reducible refine gkb_bind' ?_ (fun _ => ?_))
  | (with_reducible apply gkb_ite) | (with_reducible apply gkb_when) | (with_reducible apply gkb_unless)
  | (with_reducible refine gkb_maybeM (fun _ => ?_) _) | (with_reducible apply gkb_liftM)
  | (with_reducible refine gkb_whileLoop (fun _ => ?_) _)
  | (with_reducible refine gkb_mapMx (fun _ => ?_) _)
  | (with_reducible refine gkb_mapM (fun _ => ?_) _)
  | (with_reducible refine gkb_forMx (fun _ => ?_) _)
  | with_reducible exact gkbe_pure _ | with_reducible exact gkbe_returnOk _ | with_reducible exact gkbe_throw _
  | with_reducible exact gkbe_throw' _ | with_reducible exact gkbe_throwOpt _ _ | with_reducible exact gkbe_assertE _
  | (with_reducible refine gkbe_bind ?_ (fun _ => ?_))
  | (with_reducible apply gkbe_liftE) | (with_reducible apply gkbe_ite) | (with_reducible apply gkbe_whenE)
  | (with_reducible apply gkbe_unlessE) | (with_reducible refine gkb_catch ?_ (fun _ => ?_))
  | (with_reducible refine gkbe_handleE ?_ (fun _ => ?_)) | (with_reducible apply gkbe_liftME)
  | (with_reducible refine gkbe_mapMEx (fun _ => ?_) _) | (with_reducible refine gkbe_mapME (fun _ => ?_) _)
  | (with_reducible apply gkbe_withoutPreemption) | (with_reducible apply gkbe_capFaultOnFailure)
  | (with_reducible apply gkbe_lookupErrorOnFailure) | (with_reducible apply gkbe_unifyFailure)
  | (with_reducible apply gkb_emptyOnFailure) | (with_reducible apply gkb_constOnFailure)
  | split
  | (dsimp only)
  | (simp only [letFun])
  | (dsimp only [letFun])
  | (with_reducible exact gkb_pure _)
  | (exact gkb_pure _))

/-- A `GKB` lemma of a spec function (extended by the generated family, one
rule per lemma). -/
syntax "gkb_leaf" : tactic
macro_rules | `(tactic| gkb_leaf) => `(tactic| fail "no gkb_leaf")

/-- `GKB` from MachFieldFamT's `MTK` family, else one step. -/
macro "gkb_auto" : tactic => `(tactic| repeat' (first
  | gkb_leaf
  | gkb_step0
  | ((with_reducible apply gkb_of_mtk); mtk_leaf; done)
  | ((with_reducible apply gkbe_of_mtke); mtk_leaf; done)))

/-! ## `IrqStB` has the leaves -/

theorem irqStB_ms {σ : State Unit} (h : IrqStB σ) (ms : MachineState) : IrqStB { σ with machineState := ms } := h

theorem ik_dmo_irqStB {α : Type} (mop : NonDet MachineState α) : IK IrqStB (doMachineOp (Z := Unit) mop) := by
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

theorem ik_sis_irqStB (st : IrqState) (i : Irq) (hb : st = .irqInactive ∨ i ≤ maxIRQ) :
    IK IrqStB (setIrqState (Z := Unit) st i) := by
  intro σ h x hx
  unfold setIrqState at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hx
  refine ik_dmo_irqStB _ _ ?_ x hx
  intro irq hirq
  show Function.update σ.interruptStates i st irq = .irqInactive
  by_cases e : irq = i
  · subst e
    rw [Function.update_self]
    rcases hb with hb | hb
    · exact hb
    · exact absurd hirq (BitVec.not_lt.2 hb)
  · rw [Function.update_of_ne e]; exact h irq hirq

/-- **`IrqStB` has the bounded leaves.** -/
theorem wlb_irqStB : WLB IrqStB where
  view σ σ' e h := by
    unfold vw at e; simp only [Prod.mk.injEq] at e
    intro irq hi; rw [e.2.2.1]; exact h irq hi
  uts σ h x hx := by
    obtain ⟨-, -, e, -⟩ := uts_out hx
    intro irq hi; rw [e]; exact h irq hi
  sisI i := ik_sis_irqStB _ i (Or.inl rfl)
  sisB st i hi := ik_sis_irqStB st i (Or.inr hi)
  msk mop _ := ik_dmo_irqStB mop
  ack i := ik_dmo_irqStB _

/-- **`IrqStB` at boot** (`initASt`: every line inactive). -/
theorem boot_irqStB : IrqStB (initASt (Z := Unit)) := fun _ _ => rfl

end

end Fl4Proofs.P3.SInvIB
