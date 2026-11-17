/-
P3 (DESIGN.md §9), scheduler: **`OffOK` after `sc_and_timer`**
(`OffOK.scAndTimer`), spec side only: `switch_sched_context` commits the
time (`consumed_time := 0`) whenever the timer is to be reprogrammed, which
it is whenever the SC changes (`RK`: a set reprogram flag stays set through
the refill unblock check); otherwise nothing it reads changes;
`set_next_interrupt` changes the machine state only (`MSO`).
-/
import Fl4Proofs.P3.ScFieldKeep
import Fl4Proofs.P3.ScSchedRun
import Fl4Proofs.P3.ScCharge8
import Fl4Proofs.P3.ScMidKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

/-- A set reprogram flag stays set. -/
def RK (σ σ' : State Unit) : Prop := σ.reprogramTimer = true → σ'.reprogramTimer = true

theorem RK.refl (σ : State Unit) : RK σ σ := id

theorem RK.trans {σ1 σ2 σ3 : State Unit} (h1 : RK σ1 σ2) (h2 : RK σ2 σ3) : RK σ1 σ3 :=
  fun h => h2 (h1 h)

/-- Every outcome keeps a set reprogram flag set. -/
def RKA {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → RK σ x.2

theorem RKA.of_eq {α : Type} {m : NonDet (State Unit) α} (hP : RKA m) {σ σ' : State Unit} {a : α} {X : Prop}
    (h : m σ = ({(a, σ')}, X)) : RK σ σ' :=
  hP σ (a, σ') (by rw [h]; exact Set.mem_singleton _)

section Comb

theorem rk_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : RKA m)
    (hg : ∀ a, RKA (g a)) : RKA (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem rk_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : RKA m)
    (hg : ∀ a, RKA (g a)) : RKA (NonDet.bind m g) := rk_bind hm hg

theorem rk_same {α : Type} {m : NonDet (State Unit) α} (h : ∀ σ x, x ∈ (m σ).1 → x.2 = σ) : RKA m := by
  intro σ x hx; rw [h σ x hx]; exact RK.refl σ

theorem rk_pure {α : Type} (a : α) : RKA (pure a : NonDet (State Unit) α) :=
  rk_same fun _ x hx => by rw [Set.mem_singleton_iff.1 hx]

theorem rk_pure' {α : Type} (a : α) : RKA (NonDet.pure a : NonDet (State Unit) α) := rk_pure a

theorem rk_gets {α : Type} (g : State Unit → α) : RKA (NonDet.gets g) :=
  rk_same fun _ x hx => by rw [Set.mem_singleton_iff.1 hx]

theorem rk_get : RKA (NonDet.get : NonDet (State Unit) (State Unit)) :=
  rk_same fun _ x hx => by rw [Set.mem_singleton_iff.1 hx]

theorem rk_assert (P : Prop) : RKA (NonDet.assert P : NonDet (State Unit) Unit) :=
  rk_same fun _ x hx => by obtain ⟨-, rfl⟩ := hx; rfl

theorem rk_fail {α : Type} : RKA (NonDet.fail : NonDet (State Unit) α) := fun _ _ hx => hx.elim

theorem rk_assertOpt {α : Type} (o : Option α) : RKA (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact rk_fail
  · exact rk_pure' _

theorem rk_getsThe {α : Type} (g : State Unit → Option α) : RKA (NonDet.getsThe g) := by
  intro σ x hx; exact rk_assertOpt (g σ) σ x hx

theorem rk_selectF {α : Type} (S : Set α × Prop) : RKA (NonDet.selectF S : NonDet (State Unit) α) :=
  rk_same fun _ x hx => by obtain ⟨-, h⟩ := hx; exact h

theorem rk_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : RKA m1)
    (h2 : RKA m2) : RKA (if P then m1 else m2) := by
  split <;> assumption

theorem rk_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : RKA m) : RKA (NonDet.when P m) := by
  unfold NonDet.when; exact rk_ite P h (rk_pure' _)

theorem rk_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : RKA m) :
    RKA (NonDet.unless P m) := by
  unfold NonDet.unless; exact rk_ite P (rk_pure' _) h

theorem rk_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, RKA (g a)) (o : Option α) :
    RKA (NonDet.maybeM g o) := by
  cases o
  · exact rk_pure' _
  · exact h _

theorem rk_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : RKA m) : RKA (NonDet.liftM g m) :=
  rk_bind' h fun _ => rk_pure' _

theorem rk_modify {g : State Unit → State Unit} (hg : ∀ σ, RK σ (g σ)) : RKA (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hg σ

theorem rk_get_put {g : State Unit → State Unit} (hg : ∀ σ, RK σ (g σ)) :
    RKA (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hg σ

theorem rk_getObject (p : ObjRef) : RKA (getObject (Z := Unit) p) := rk_getsThe _

theorem rk_setObject (p : ObjRef) (o : KernelObject) : RKA (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨k, -, -, e⟩ := setObject_mem hx
  rw [e]; exact id

theorem rk_doExtendedOp (eop : DetExtMonad Unit) : RKA (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine rk_bind rk_get (fun _ => rk_bind (rk_selectF _) (fun _ => ?_))
  split
  exact rk_modify (fun σ => id)

theorem rk_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, RKA (B r)) (r : α) : RKA (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => exact fun h => h
  | step _ hm _ ih => exact (hB _ _ _ hm).trans ih

theorem rk_mapMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, RKA (g a)) (xs : List α) :
    RKA (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact rk_pure' _
  | cons a xs' ih => exact rk_bind' (h a) fun _ => ih

theorem rk_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, RKA (g a)) (xs : List α) :
    RKA (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact rk_pure' _
  | cons a xs' ih => exact rk_bind' (h a) fun _ => rk_bind' ih fun _ => rk_pure' _

end Comb

macro "rk_step0" : tactic => `(tactic| first
  | with_reducible exact rk_pure _ | with_reducible exact rk_pure' _ | with_reducible exact rk_fail
  | with_reducible exact rk_gets _ | with_reducible exact rk_get
  | with_reducible exact rk_assert _ | with_reducible exact rk_assertOpt _
  | with_reducible exact rk_getObject _ | with_reducible exact rk_getsThe _
  | with_reducible exact rk_selectF _ | with_reducible exact rk_setObject _ _
  | ((with_reducible apply rk_modify); intro _; first | exact id | exact fun _ => rfl)
  | ((with_reducible apply rk_get_put); intro _; first | exact id | exact fun _ => rfl)
  | with_reducible exact rk_doExtendedOp _
  | (with_reducible refine rk_bind ?_ (fun _ => ?_))
  | (with_reducible refine rk_bind' ?_ (fun _ => ?_))
  | (with_reducible apply rk_ite) | (with_reducible apply rk_when) | (with_reducible apply rk_unless)
  | (with_reducible refine rk_maybeM (fun _ => ?_) _) | (with_reducible apply rk_liftM)
  | (with_reducible refine rk_whileLoop (fun _ => ?_) _)
  | (with_reducible refine rk_mapMx (fun _ => ?_) _)
  | (with_reducible refine rk_mapM (fun _ => ?_) _)
  | split
  | (dsimp only))

section Ops

theorem rk_threadSet (g : Tcb → Tcb) (p : ObjRef) : RKA (threadSet (Z := Unit) g p) := by
  unfold threadSet; repeat rk_step0

theorem rk_threadGet {α : Type} (g : Tcb → α) (p : ObjRef) : RKA (threadGet (Z := Unit) g p) := by
  unfold threadGet; repeat rk_step0

theorem rk_getSchedContext (p : ObjRef) : RKA (getSchedContext (Z := Unit) p) := by
  unfold getSchedContext; repeat rk_step0

theorem rk_updateSchedContext (p : ObjRef) (g : SchedContext → SchedContext) :
    RKA (updateSchedContext (Z := Unit) p g) := by
  unfold updateSchedContext; repeat rk_step0

theorem rk_getSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (p : ObjRef) :
    RKA (getSimpleKo (Z := Unit) C p) := by
  unfold getSimpleKo; repeat rk_step0

theorem rk_setSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (p : ObjRef) (e : α) :
    RKA (setSimpleKo (Z := Unit) C p e) := by
  unfold setSimpleKo; repeat rk_step0

theorem rk_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject)
    (g : (Option ObjRef → Option ObjRef) → α → α) (p : ObjRef) (new : Option ObjRef) :
    RKA (updateSkObjRef (Z := Unit) C g p new) := by
  unfold updateSkObjRef
  exact rk_bind (rk_getSimpleKo _ _) fun _ => rk_setSimpleKo _ _ _

end Ops

macro "rk_step" : tactic => `(tactic| first
  | with_reducible exact rk_threadGet _ _ | with_reducible exact rk_threadSet _ _
  | with_reducible exact rk_getSchedContext _ | with_reducible exact rk_updateSchedContext _ _
  | with_reducible exact rk_getSimpleKo _ _ | with_reducible exact rk_setSimpleKo _ _ _
  | with_reducible exact rk_updateSkObjRef _ _ _ _
  | rk_step0)

theorem rk_refillUnblockCheck (p : ObjRef) : RKA (refillUnblockCheck (Z := Unit) p) := by
  unfold refillUnblockCheck isRoundRobin getScRefillReady refillHeadOverlappingLoop mergeOverlappingRefills
    refillPopHead updateRefillHd getRefillHead
  refine rk_bind (rk_bind (rk_getSchedContext _) fun _ => rk_pure _) fun _ => ?_
  repeat rk_step

theorem rk_ifCondRefillUnblockCheck (o : Option ObjRef) (a b : Option Bool) :
    RKA (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck
  refine rk_maybeM (fun _ => ?_) _
  exact rk_bind (rk_getSchedContext _) fun _ => rk_bind (rk_gets _) fun _ =>
    rk_bind (rk_pure _) fun _ => rk_when _ (rk_when _ (rk_refillUnblockCheck _))

/-! ## Triples -/

/-- Every outcome of `m` from a state satisfying `P` satisfies `Q`. -/
def Hoa {α : Type} (P : State Unit → Prop) (m : NonDet (State Unit) α) (Q : α → State Unit → Prop) : Prop :=
  ∀ σ, P σ → ∀ x, x ∈ (m σ).1 → Q x.1 x.2

theorem hoa_bind {α β : Type} {P : State Unit → Prop} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    {Q : α → State Unit → Prop} {R : β → State Unit → Prop} (h1 : Hoa P m Q) (h2 : ∀ a, Hoa (Q a) (g a) R) :
    Hoa P (m >>= g) R := by
  intro σ hσ x ⟨y, hy, hx⟩
  exact h2 y.1 y.2 (h1 σ hσ y hy) x hx

theorem hoa_bind' {α β : Type} {P : State Unit → Prop} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    {Q : α → State Unit → Prop} {R : β → State Unit → Prop} (h1 : Hoa P m Q) (h2 : ∀ a, Hoa (Q a) (g a) R) :
    Hoa P (NonDet.bind m g) R := hoa_bind h1 h2

theorem hoa_rdo {α : Type} {P : State Unit → Prop} {m : NonDet (State Unit) α} (hm : RdO m) :
    Hoa P m (fun _ => P) := by
  intro σ hσ x hx; rw [hm σ x hx]; exact hσ

theorem hoa_gets {α : Type} {P : State Unit → Prop} (f : State Unit → α) :
    Hoa P (NonDet.gets f) (fun a σ => P σ ∧ a = f σ) := by
  intro σ hσ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ⟨hσ, rfl⟩

theorem hoa_modify {P : State Unit → Prop} (g : State Unit → State Unit) :
    Hoa P (NonDet.modify g) (fun _ σ => ∃ σ0, P σ0 ∧ σ = g σ0) := by
  intro σ hσ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ⟨σ, hσ, rfl⟩

theorem hoa_mono {α : Type} {P P' : State Unit → Prop} {m : NonDet (State Unit) α} {Q Q' : α → State Unit → Prop}
    (h : Hoa P m Q) (hP : ∀ σ, P' σ → P σ) (hQ : ∀ a σ, Q a σ → Q' a σ) : Hoa P' m Q' :=
  fun σ hσ x hx => hQ _ _ (h σ (hP σ hσ) x hx)

theorem hoa_pure {α : Type} {P : State Unit → Prop} (a : α) : Hoa P (pure a : NonDet (State Unit) α) (fun _ => P) :=
  hoa_rdo (rdo_pure a)

theorem hoa_pure' {α : Type} {P : State Unit → Prop} (a : α) :
    Hoa P (NonDet.pure a : NonDet (State Unit) α) (fun _ => P) := hoa_rdo (rdo_pure' a)

theorem hoa_doMachineOp {α : Type} {P : State Unit → Prop} (mop : NonDet MachineState α)
    (hP : ∀ σ ms, P σ → P { σ with machineState := ms }) : Hoa P (doMachineOp (Z := Unit) mop) (fun _ => P) := by
  intro σ hσ x hx
  obtain ⟨ms, -, e⟩ := doMachineOp_mem2 (r := x.1) (σ' := x.2) hx
  rw [e]; exact hP σ ms hσ

theorem rdo_threadGet {α : Type} (f : Tcb → α) (p : ObjRef) : RdO (threadGet (Z := Unit) f p) := by
  unfold threadGet; exact rdo_bind (rdo_getsThe _) fun _ => rdo_pure _

theorem rdo_getSchedContext (p : ObjRef) : RdO (getSchedContext (Z := Unit) p) := by
  unfold getSchedContext getObject
  refine rdo_bind (rdo_getsThe _) fun o => ?_
  split
  · exact rdo_pure _
  · exact rdo_fail

theorem hoa_rka {α : Type} {m : NonDet (State Unit) α} (h : RKA m) :
    Hoa (fun σ => σ.reprogramTimer = true) m (fun _ σ => σ.reprogramTimer = true) :=
  fun σ hσ x hx => h σ x hx hσ

/-- `commit_time` ends with no consumed time. -/
theorem hoa_commitTime {P : State Unit → Prop} :
    Hoa P (commitTime (Z := Unit)) (fun _ σ => σ.consumedTime = 0) := by
  intro σ _ x hx
  rw [commitTime_eq] at hx
  obtain ⟨y, -, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hx]

theorem hinv_bind {α β : Type} {P : State Unit → Prop} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (h1 : Hoa P m (fun _ => P)) (h2 : ∀ a, Hoa P (g a) (fun _ => P)) : Hoa P (m >>= g) (fun _ => P) :=
  hoa_bind h1 h2

theorem hinv_bind' {α β : Type} {P : State Unit → Prop} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (h1 : Hoa P m (fun _ => P)) (h2 : ∀ a, Hoa P (g a) (fun _ => P)) : Hoa P (NonDet.bind m g) (fun _ => P) :=
  hoa_bind h1 h2

/-- `set_next_interrupt` changes the machine state only. -/
theorem hoa_setNextInterrupt {P : State Unit → Prop} (hP : ∀ σ ms, P σ → P { σ with machineState := ms }) :
    Hoa P (setNextInterrupt (Z := Unit)) (fun _ => P) := by
  unfold setNextInterrupt getTcbObjRef getRefillHead
  repeat' (first
    | exact hoa_doMachineOp _ hP
    | (with_reducible refine hinv_bind ?_ (fun _ => ?_))
    | (with_reducible refine hinv_bind' ?_ (fun _ => ?_))
    | exact hoa_rdo (rdo_gets _) | exact hoa_rdo (rdo_getsThe _) | exact hoa_rdo (rdo_assertOpt _)
    | exact hoa_rdo (rdo_threadGet _ _) | exact hoa_pure _ | exact hoa_pure' _
    | (dsimp only)
    | split)

theorem OffOK.ms {σ : State Unit} (ms : MachineState) (h : OffOK σ) : OffOK { σ with machineState := ms } := h

set_option maxHeartbeats 1000000 in
/-- **`OffOK` after `sc_and_timer`** (module docstring). -/
theorem OffOK.scAndTimer {σ3 σ' : State Unit} (h : OffOK σ3)
    (he : Fl4Spec.scAndTimer (Z := Unit) { σ3 with schedulerAction := .resumeCurThread } = ({((), σ')}, False)) :
    OffOK σ' := by
  set A0 : State Unit := { σ3 with schedulerAction := .resumeCurThread } with hA0
  have h0 : OffOK A0 := h
  have hm : ((), σ') ∈ (Fl4Spec.scAndTimer (Z := Unit) A0).1 := by rw [he]; exact Set.mem_singleton _
  suffices H : Hoa (fun σ => σ = A0) (Fl4Spec.scAndTimer (Z := Unit)) (fun _ σ => OffOK σ) from H A0 rfl _ hm
  unfold Fl4Spec.scAndTimer switchSchedContext
  refine hoa_bind' (Q := fun _ σ => OffOK σ) ?_ fun _ => ?_
  · refine hoa_bind (hoa_gets _) fun c0 => ?_
    refine hoa_bind (hoa_rdo (rdo_gets _)) fun _ => ?_
    refine hoa_bind (hoa_rdo (rdo_threadGet _ _)) fun _ => ?_
    refine hoa_bind (hoa_rdo (rdo_assertOpt _)) fun scp => ?_
    refine hoa_bind (hoa_rdo (rdo_getSchedContext _)) fun _ => ?_
    refine hoa_bind (Q := fun _ σ => (σ = A0 ∧ c0 = A0.curSc ∧ scp = c0) ∨ σ.reprogramTimer = true) ?_ fun _ => ?_
    · unfold NonDet.when
      split
      · refine hoa_bind (hoa_modify _) fun _ => ?_
        exact hoa_mono (hoa_rka (rk_ifCondRefillUnblockCheck _ _ _)) (fun σ ⟨_, _, e⟩ => by rw [e]) fun _ _ h => Or.inr h
      · rename_i hne
        exact hoa_mono (hoa_pure' _) (fun σ h => h) fun _ σ ⟨e1, e2⟩ => Or.inl ⟨e1, by subst e1; exact e2, not_not.1 hne⟩
    refine hoa_bind (hoa_gets _) fun r => ?_
    refine hoa_bind (Q := fun _ σ => (σ = A0 ∧ c0 = A0.curSc ∧ scp = c0) ∨ σ.consumedTime = 0) ?_ fun _ => ?_
    · unfold NonDet.when
      split
      · exact hoa_mono (hoa_commitTime (P := fun _ => True)) (fun σ _ => trivial) fun _ _ h => Or.inr h
      · rename_i hr
        refine hoa_mono (hoa_pure' _) (fun σ h => h) fun _ σ ⟨h1, e⟩ => ?_
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · rw [← e] at h1; exact absurd h1 hr
    refine hoa_mono (hoa_modify _) (fun σ h => h) fun _ σ ⟨σ0, h1, e⟩ => ?_
    rw [e]
    rcases h1 with ⟨rfl, e1, e2⟩ | h1
    · rw [e2, e1]; exact h0
    · intro hc
      exact absurd hc (by show ¬ (0 < σ0.consumedTime); rw [h1]; decide)
  · refine hoa_bind (hoa_rdo (rdo_gets _)) fun _ => ?_
    unfold NonDet.when
    split
    · refine hoa_bind (hoa_setNextInterrupt fun σ ms h => h.ms ms) fun _ => ?_
      exact hoa_mono (hoa_modify _) (fun σ h => h) fun _ σ ⟨σ0, h1, e⟩ => by rw [e]; exact h1
    · exact hoa_pure' _

end

end Fl4Proofs.P3.Sched
