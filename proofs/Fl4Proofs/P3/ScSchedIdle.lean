/-
P3 (DESIGN.md §9), scheduler: **the spec's `schedule` keeps the idle
thread** (`ik_schedule`), spec side only: no spec function writes
`idle_thread`; the combinators of `IKA` (ScSchedRun) for the state and the
exception monads, `sc_and_timer` by `ik_scAndTimer`, the rest by `FKA`
(ScFieldKeep) or by unfolding.
-/
import Fl4Proofs.P3.ScSchedRun
open Classical

namespace Fl4Proofs.P3.Sched
open Fl4Spec

noncomputable section

section Comb

theorem ik_pure {α : Type} (a : α) : IKA (pure a : NonDet (State Unit) α) := IKA.of_fk (fk_pure a)
theorem ik_pure' {α : Type} (a : α) : IKA (NonDet.pure a : NonDet (State Unit) α) := IKA.of_fk (fk_pure' a)
theorem ik_fail {α : Type} : IKA (NonDet.fail : NonDet (State Unit) α) := IKA.of_fk fk_fail
theorem ik_gets {α : Type} (g : State Unit → α) : IKA (NonDet.gets g) := IKA.of_fk (fk_gets g)
theorem ik_get : IKA (NonDet.get : NonDet (State Unit) (State Unit)) := IKA.of_fk fk_get
theorem ik_assert (P : Prop) : IKA (NonDet.assert P : NonDet (State Unit) Unit) := IKA.of_fk (fk_assert P)
theorem ik_assertOpt {α : Type} (o : Option α) : IKA (NonDet.assertOpt o : NonDet (State Unit) α) :=
  IKA.of_fk (fk_assertOpt o)
theorem ik_getsThe {α : Type} (g : State Unit → Option α) : IKA (NonDet.getsThe g) := IKA.of_fk (fk_getsThe g)
theorem ik_selectF {α : Type} (S : Set α × Prop) : IKA (NonDet.selectF S : NonDet (State Unit) α) :=
  IKA.of_fk (fk_selectF S)

theorem ik_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : IKA m1)
    (h2 : IKA m2) : IKA (if P then m1 else m2) := by
  split <;> assumption

theorem ik_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, IKA (g a)) (o : Option α) :
    IKA (NonDet.maybeM g o) := by
  cases o
  · exact ik_pure' _
  · exact h _

theorem ik_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, IKA (B r)) (r : α) : IKA (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => rfl
  | step _ hm _ ih => exact ih.trans (hB _ _ _ hm)

end Comb

/-- `IKA` for the exception monad. -/
def IKAE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKA (ExceptT.run m)

section CombE
variable {ε : Type}

theorem ike_bind {α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β} (hm : IKAE m)
    (hg : ∀ a, IKAE (g a)) : IKAE (m >>= g) := by
  unfold IKAE; rw [ExceptT.run_bind]
  refine ik_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact ik_pure _

theorem ike_pure {α : Type} (a : α) : IKAE (pure a : NonDetE (State Unit) ε α) := ik_pure _
theorem ike_returnOk {α : Type} (a : α) : IKAE (NonDetE.returnOk a : NonDetE (State Unit) ε α) := ik_pure _
theorem ike_throw {α : Type} (e : ε) : IKAE (NonDetE.throwError e : NonDetE (State Unit) ε α) := ik_pure _

theorem ike_liftE {α : Type} {m : NonDet (State Unit) α} (h : IKA m) : IKAE (NonDetE.liftE (ε := ε) m) := by
  unfold IKAE NonDetE.liftE; rw [ExceptT.run_lift]
  exact ik_bind h fun _ => ik_pure _

theorem ike_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : IKAE m1)
    (h2 : IKAE m2) : IKAE (if P then m1 else m2) := by
  split <;> assumption

theorem ike_whenE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : IKAE m) :
    IKAE (NonDetE.whenE P m) := by
  unfold NonDetE.whenE; exact ike_ite P h (ike_pure _)

theorem ike_assertE (P : Prop) : IKAE (NonDetE.assertE P : NonDetE (State Unit) ε Unit) :=
  ike_liftE (ik_assert P)

theorem ik_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : IKAE m)
    (hh : ∀ e, IKA (h e)) : IKA (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine ik_bind' hm fun r => ?_
  cases r with
  | ok a => exact ik_pure' _
  | error e => exact hh e

end CombE

/-- One step of an `IKA` proof. -/
macro "ik_step0" : tactic => `(tactic| first
  | with_reducible exact ik_pure _ | with_reducible exact ik_pure' _ | with_reducible exact ik_fail
  | with_reducible exact ik_gets _ | with_reducible exact ik_get
  | with_reducible exact ik_assert _ | with_reducible exact ik_assertOpt _
  | with_reducible exact ik_getsThe _ | with_reducible exact ik_selectF _
  | with_reducible exact IKA.of_fk (fk_doMachineOp _)
  | with_reducible exact IKA.of_fk (fk_setObject _ _)
  | with_reducible exact IKA.of_fk (fk_getObject _)
  | with_reducible exact IKA.of_fk (fk_threadGet _ _)
  | with_reducible exact IKA.of_fk (fk_getSchedContext _)
  | with_reducible exact IKA.of_fk (fk_doExtendedOp _)
  | ((with_reducible apply ik_modify); intro _; rfl)
  | (with_reducible refine ik_bind ?_ (fun _ => ?_))
  | (with_reducible refine ik_bind' ?_ (fun _ => ?_))
  | (with_reducible apply ik_ite) | (with_reducible apply ik_when)
  | (with_reducible refine ik_maybeM (fun _ => ?_) _)
  | (with_reducible refine ik_whileLoop (fun _ => ?_) _)
  | with_reducible exact ike_pure _ | with_reducible exact ike_returnOk _ | with_reducible exact ike_throw _
  | with_reducible exact ike_assertE _
  | (with_reducible refine ike_bind ?_ (fun _ => ?_))
  | (with_reducible apply ike_liftE) | (with_reducible apply ike_ite) | (with_reducible apply ike_whenE)
  | (with_reducible refine ik_catch ?_ (fun _ => ?_))
  | split
  | (dsimp only))

/-- An `IKA` lemma of a spec function (extended below, one rule per lemma). -/
syntax "ik_leaf" : tactic
macro_rules | `(tactic| ik_leaf) => `(tactic| fail "no ik_leaf")

macro "ik_auto" : tactic => `(tactic| repeat' (first | ik_leaf | ik_step0))

section Leaves

macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_scAndTimer)

theorem ik_tcbSchedAction (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    IKA (tcbSchedAction (Z := Unit) f t) := IKA.of_fk (by fk_auto)
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_tcbSchedAction _ _)
theorem ik_rescheduleRequired : IKA (rescheduleRequired (Z := Unit)) := IKA.of_fk (by fk_auto)
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_rescheduleRequired)
theorem ik_setSchedulerAction (a : SchedulerAction) : IKA (setSchedulerAction (Z := Unit) a) :=
  IKA.of_fk (by fk_auto)
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_setSchedulerAction _)
theorem ik_tcbReleaseRemove (t : ObjRef) : IKA (tcbReleaseRemove (Z := Unit) t) := IKA.of_fk (by fk_auto)
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_tcbReleaseRemove _)
theorem ik_possibleSwitchTo (t : ObjRef) : IKA (possibleSwitchTo (Z := Unit) t) := IKA.of_fk (by fk_auto)
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_possibleSwitchTo _)

theorem ik_awaken : IKA (awaken (Z := Unit)) := by
  unfold awaken tcbReleaseDequeue; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_awaken)
theorem ik_checkDomainTime : IKA (checkDomainTime (Z := Unit)) := by
  unfold checkDomainTime; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_checkDomainTime)

theorem ik_getCap (sl : CslotPtr) : IKA (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_getCap _)
theorem ik_getAsidPool (p : ObjRef) : IKA (getAsidPool (Z := Unit) p) := by
  unfold getAsidPool; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_getAsidPool _)
theorem ik_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : IKA (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_archThreadSet _ _)
theorem ik_asUser {α : Type} (p : ObjRef) (u : UserMonad α) : IKA (asUser (Z := Unit) p u) := by
  unfold asUser; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_asUser _ _)
theorem ik_saveFpuState (t : ObjRef) : IKA (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_saveFpuState _)
theorem ik_loadFpuState (t : ObjRef) : IKA (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_loadFpuState _)
theorem ik_setX64CurrentFpuOwner (o : Option ObjRef) : IKA (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_setX64CurrentFpuOwner _)
theorem ik_switchLocalFpuOwner (o : Option ObjRef) : IKA (switchLocalFpuOwner (Z := Unit) o) := by
  unfold switchLocalFpuOwner; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_switchLocalFpuOwner _)
theorem ik_lazyFpuRestore (t : ObjRef) : IKA (lazyFpuRestore (Z := Unit) t) := by
  unfold lazyFpuRestore; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_lazyFpuRestore _)
theorem ik_setCurrentCr3 (c : Cr3) : IKA (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_setCurrentCr3 _)
theorem ik_findVspaceForAsid (asid : Asid) : IKAE (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_findVspaceForAsid _)
theorem ik_setVmRoot (t : ObjRef) : IKA (setVmRoot (Z := Unit) t) := by
  unfold setVmRoot getCurrentCr3 setCurrentVspaceRoot; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_setVmRoot _)
theorem ik_switchToThread (t : ObjRef) : IKA (switchToThread (Z := Unit) t) := by
  unfold switchToThread archSwitchToThread; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_switchToThread _)
theorem ik_switchToIdleThread : IKA (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread archSwitchToIdleThread; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_switchToIdleThread)
theorem ik_guardedSwitchTo (t : ObjRef) : IKA (guardedSwitchTo (Z := Unit) t) := by
  unfold guardedSwitchTo; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_guardedSwitchTo _)
theorem ik_chooseThread : IKA (chooseThread (Z := Unit)) := by
  unfold chooseThread; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_chooseThread)
theorem ik_scheduleChooseNewThread : IKA (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread archPrepareNextDomain nextDomain; ik_auto
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_scheduleChooseNewThread)
theorem ik_scheduleSwitchThreadFastfail (ct it : ObjRef) (p q : Priority) :
    IKA (scheduleSwitchThreadFastfail (Z := Unit) ct it p q) := by
  unfold scheduleSwitchThreadFastfail; exact ik_pure _
macro_rules | `(tactic| ik_leaf) => `(tactic| with_reducible exact ik_scheduleSwitchThreadFastfail _ _ _ _)

/-- **The spec's `schedule` keeps the idle thread.** -/
theorem ik_schedule : IKA (schedule (Z := Unit)) := by
  unfold schedule; ik_auto

end Leaves

end

end Fl4Proofs.P3.Sched
