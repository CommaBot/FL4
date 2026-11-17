/-
P3 (DESIGN.md §9), scheduler: **the spec's `schedule` cuts no links**
(`lkm_schedule`: `LKM` with nothing excepted): no TCB's SC, no SC's TCB or
notification and no notification's SC is set to anything but its old value
or none. With `LKM`'s exception-monad combinators (`LKME`) and
`doMachineOp`, the scheduler's operations bottom-up as `MaxK.mk_schedule`.
-/
import Fl4Proofs.P3.ScLinkKeep
import Fl4Proofs.P3.ScSchedBsa
open Classical

namespace Fl4Proofs.P3.Sched
open Fl4Spec

noncomputable section

section Comb
variable {W : ObjRef → Prop}

theorem lkm_doMachineOp {α : Type} (mop : NonDet MachineState α) : LKM W (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine lkm_bind (lkm_gets _) (fun _ => lkm_bind (lkm_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact lkm_bind (lkm_modify (fun σ => rfl)) (fun _ => lkm_pure _)

/-- `LKM` for the exception monad. -/
def LKME {ε α : Type} (W : ObjRef → Prop) (m : NonDetE (State Unit) ε α) : Prop := LKM W (ExceptT.run m)

variable {ε : Type}

theorem lkme_bind {α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β} (hm : LKME W m)
    (hg : ∀ a, LKME W (g a)) : LKME W (m >>= g) := by
  unfold LKME; rw [ExceptT.run_bind]
  refine lkm_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact lkm_pure _

theorem lkme_pure {α : Type} (a : α) : LKME W (pure a : NonDetE (State Unit) ε α) := lkm_pure _
theorem lkme_returnOk {α : Type} (a : α) : LKME W (NonDetE.returnOk a : NonDetE (State Unit) ε α) := lkm_pure _
theorem lkme_throw {α : Type} (e : ε) : LKME W (NonDetE.throwError e : NonDetE (State Unit) ε α) := lkm_pure _
theorem lkme_throw' {α : Type} (e : ε) : LKME W (throw e : NonDetE (State Unit) ε α) := lkm_pure _

theorem lkme_liftE {α : Type} {m : NonDet (State Unit) α} (h : LKM W m) : LKME W (NonDetE.liftE (ε := ε) m) := by
  unfold LKME NonDetE.liftE; rw [ExceptT.run_lift]
  exact lkm_bind h fun _ => lkm_pure _

theorem lkme_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : LKME W m1)
    (h2 : LKME W m2) : LKME W (if P then m1 else m2) := by
  split <;> assumption

theorem lkme_whenE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : LKME W m) :
    LKME W (NonDetE.whenE P m) := by
  unfold NonDetE.whenE; exact lkme_ite P h (lkme_pure _)

theorem lkme_unlessE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : LKME W m) :
    LKME W (NonDetE.unlessE P m) := by
  unfold NonDetE.unlessE; exact lkme_ite P (lkme_pure _) h

theorem lkme_throwOpt {α : Type} (e : ε) (o : Option α) :
    LKME W (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact lkme_throw' e
  · exact lkme_pure _

theorem lkme_assertE (P : Prop) : LKME W (NonDetE.assertE P : NonDetE (State Unit) ε Unit) :=
  lkme_liftE (lkm_assert P)

theorem lkm_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : LKME W m)
    (hh : ∀ e, LKM W (h e)) : LKM W (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine lkm_bind' hm fun r => ?_
  cases r with
  | ok a => exact lkm_pure' _
  | error e => exact hh e

theorem lkme_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : LKME W m) (hh : ∀ e, LKME W (h e)) : LKME W (NonDetE.handleE m h) := by
  unfold NonDetE.handleE LKME
  rw [ExceptT.run_mk]
  refine lkm_bind' hm fun r => ?_
  cases r with
  | ok a => exact lkm_pure' _
  | error e => exact hh e

theorem lkme_liftME {α β : Type} (f : α → β) {m : NonDetE (State Unit) ε α} (h : LKME W m) :
    LKME W (NonDetE.liftME f m) := by
  unfold NonDetE.liftME; exact lkme_bind h fun _ => lkme_pure _

end Comb

/-- One step of an `LKM` proof through the scheduler's operations. -/
macro "lk_step3" : tactic => `(tactic| first
  | with_reducible exact lkm_doMachineOp _
  | with_reducible exact lkme_pure _ | with_reducible exact lkme_returnOk _ | with_reducible exact lkme_throw _
  | with_reducible exact lkme_throw' _ | with_reducible exact lkme_throwOpt _ _ | with_reducible exact lkme_assertE _
  | (with_reducible refine lkme_bind ?_ (fun _ => ?_))
  | (with_reducible apply lkme_liftE) | (with_reducible apply lkme_ite) | (with_reducible apply lkme_whenE)
  | (with_reducible apply lkme_unlessE) | (with_reducible refine lkm_catch ?_ (fun _ => ?_))
  | (with_reducible refine lkme_handleE ?_ (fun _ => ?_)) | (with_reducible apply lkme_liftME)
  | lkm_step2
  | (simp only [letFun])
  | (dsimp only [letFun]))

/-- An `LKM` lemma of a spec function (extended below, one rule per lemma). -/
syntax "lk_leaf" : tactic
macro_rules | `(tactic| lk_leaf) => `(tactic| fail "no lk_leaf")

macro "lk_auto2" : tactic => `(tactic| repeat' (first | lk_leaf | lk_step3 | fk_unf | sched_unf))

section
variable {W : ObjRef → Prop}

theorem lkm_asUserS {α : Type} (t : ObjRef) (u : UserMonad α) : LKM W (asUser (Z := Unit) t u) := by
  unfold asUser
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getsThe_getTcb_mem hy
  rw [hs] at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy1] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  obtain ⟨-, h2⟩ := hy2
  rw [h2] at hx
  obtain ⟨y3, hy3, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy3] at hx
  obtain ⟨y4, hy4, hx⟩ := hx
  obtain ⟨k, hk', -, e⟩ := setObject_mem hy4
  rw [hk] at hk'; cases hk'
  rw [Set.mem_singleton_iff.1 hx]
  show LK W σ y4.2
  rw [e]; exact LK.upd hk (Or.inr (LObj.tcb (Or.inl rfl)))
macro_rules | `(tactic| lk_leaf) => `(tactic| with_reducible exact lkm_asUserS _ _)

theorem lkm_archThreadSetS (f : ArchTcb → ArchTcb) (t : ObjRef) : LKM W (archThreadSet (Z := Unit) f t) :=
  lk_tcb_rw (g := fun tcb => { tcb with tcbArch := f tcb.tcbArch }) (Or.inr fun _ => LObj.tcb (Or.inl rfl))
macro_rules | `(tactic| lk_leaf) => `(tactic| with_reducible exact lkm_archThreadSetS _ _)

theorem lkm_getCapS (sl : CslotPtr) : LKM W (getCap (Z := Unit) sl) := by
  unfold getCap; lk_auto2
macro_rules | `(tactic| lk_leaf) => `(tactic| with_reducible exact lkm_getCapS _)

set_option maxHeartbeats 2000000 in
theorem lkm_setVmRootS (t : ObjRef) : LKM W (setVmRoot (Z := Unit) t) := by
  unfold setVmRoot; lk_auto2
macro_rules | `(tactic| lk_leaf) => `(tactic| with_reducible exact lkm_setVmRootS _)

set_option maxHeartbeats 2000000 in
theorem lkm_lazyFpuRestoreS (t : ObjRef) : LKM W (lazyFpuRestore (Z := Unit) t) := by
  unfold lazyFpuRestore; lk_auto2
macro_rules | `(tactic| lk_leaf) => `(tactic| with_reducible exact lkm_lazyFpuRestoreS _)

set_option maxHeartbeats 2000000 in
theorem lkm_switchToThreadS (t : ObjRef) : LKM W (switchToThread (Z := Unit) t) := by
  unfold switchToThread; lk_auto2
macro_rules | `(tactic| lk_leaf) => `(tactic| with_reducible exact lkm_switchToThreadS _)

set_option maxHeartbeats 2000000 in
theorem lkm_switchToIdleThreadS : LKM W (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread; lk_auto2
macro_rules | `(tactic| lk_leaf) => `(tactic| with_reducible exact lkm_switchToIdleThreadS)

set_option maxHeartbeats 2000000 in
theorem lkm_guardedSwitchToS (t : ObjRef) : LKM W (guardedSwitchTo (Z := Unit) t) := by
  unfold guardedSwitchTo; lk_auto2
macro_rules | `(tactic| lk_leaf) => `(tactic| with_reducible exact lkm_guardedSwitchToS _)

set_option maxHeartbeats 2000000 in
theorem lkm_chooseThreadS : LKM W (chooseThread (Z := Unit)) := by
  unfold chooseThread; lk_auto2
macro_rules | `(tactic| lk_leaf) => `(tactic| with_reducible exact lkm_chooseThreadS)

set_option maxHeartbeats 2000000 in
theorem lkm_scheduleChooseNewThreadS : LKM W (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread; lk_auto2
macro_rules | `(tactic| lk_leaf) => `(tactic| with_reducible exact lkm_scheduleChooseNewThreadS)

set_option maxHeartbeats 2000000 in
theorem lkm_awakenS : LKM W (awaken (Z := Unit)) := by
  unfold awaken; lk_auto2
macro_rules | `(tactic| lk_leaf) => `(tactic| with_reducible exact lkm_awakenS)

set_option maxHeartbeats 2000000 in
theorem lkm_setNextInterruptS : LKM W (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt; lk_auto2
macro_rules | `(tactic| lk_leaf) => `(tactic| with_reducible exact lkm_setNextInterruptS)

set_option maxHeartbeats 2000000 in
theorem lkm_scAndTimerS : LKM W (scAndTimer (Z := Unit)) := by
  unfold scAndTimer; lk_auto2
macro_rules | `(tactic| lk_leaf) => `(tactic| with_reducible exact lkm_scAndTimerS)

set_option maxHeartbeats 2000000 in
/-- **The spec's `schedule` cuts no links.** -/
theorem lkm_schedule : LKM W (schedule (Z := Unit)) := by
  unfold schedule; lk_auto2

end

end

end Fl4Proofs.P3.Sched
