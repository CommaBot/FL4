/-
P3 (issue #16, fb3i): **the frame batch after the spec's `Restart`** (spec
side only; KENTRY-PLAN fb3h, lead decision (a)).

`Restart` of `σ` (`set_thread_state ct Restart`, `Notif.stsAct` of the TCB
update) is `fbsM ct Restart a σ` for the scheduler action `a` it sets
(`stsAct_updK_fbsM`). The batch keeps the scheduler action, the current
thread, the release queue (SpecFbSim `fbsF_performFrameBatch`) and every
object's scheduler view (SpecInvRdFb `svfb_performFrameBatch`), so the
action `Restart` sets after the batch is the one it set before
(`fbs_schedulable`), and SpecFbSim's `performFrameBatch_fbsM` gives:

* **`performFrameBatch_restart`**: an outcome `(r, τ)` of the batch from `σ`
  (the current thread's TCB at `ct`) gives the outcome `(r, Restart τ)` from
  `Restart σ`; `τ` holds a TCB at `ct` with the same SC.
-/
import Fl4Proofs.P3.SpecFbSim
import Fl4Proofs.P3.SpecInvRdFb
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

theorem stsAct_updK_fbsM {σ : State Unit} {ct : ObjRef} {x : Tcb} (hk : σ.kheap ct = some (.tcb x)) :
    Notif.stsAct (Notif.updK σ ct (.tcb { x with tcbState := .restart })) ct =
      fbsM ct .restart (Notif.stsAct (Notif.updK σ ct (.tcb { x with tcbState := .restart })) ct).schedulerAction σ := by
  have hK : Function.update σ.kheap ct (some (.tcb { x with tcbState := .restart })) =
      fun q => (σ.kheap q).map (fbsK ct .restart q) := by
    funext q
    by_cases hq : q = ct
    · subst hq; simp [hk, fbsK, fbsTo]
    · rw [Function.update_of_ne hq]
      cases σ.kheap q with
      | none => rfl
      | some o => exact congrArg some (fbsK_ne o hq).symm
  unfold Notif.stsAct Notif.updK fbsM
  split_ifs <;> simp only [hK]

/-- A scheduling context's `REFILL_MAX`, seen through `sv`. -/
theorem fbs_scRM_sv (A : State Unit) (p : ObjRef) :
    Option.map SchedContext.scRefillMax (scsOf A p) =
      if (SVK.sv (A.kheap p)).1 = 2 then some (SVK.sv (A.kheap p)).2.2.2.1 else none := by
  simp only [scsOfKh, optMap, scOf]
  cases A.kheap p with
  | none => rfl
  | some ko => cases ko <;> rfl

theorem fbs_schedulable {A B : State Unit} {t : ObjRef} {ya yb : Tcb} (ha : A.kheap t = some (.tcb ya))
    (hb : B.kheap t = some (.tcb yb)) (hr : runnable ya.tcbState = runnable yb.tcbState)
    (hs : ya.tcbSchedContext = yb.tcbSchedContext) (hv : ∀ q, SVK.sv (A.kheap q) = SVK.sv (B.kheap q))
    (hq : A.releaseQueue = B.releaseQueue) : schedulable t A = schedulable t B := by
  have ta : tcbsOf A t = some ya := by simp only [tcbsOfKh, optMap, tcbOf, ha]
  have tb : tcbsOf B t = some yb := by simp only [tcbsOfKh, optMap, tcbOf, hb]
  have hsc : ∀ p, Option.map scActive (scsOf A p) = Option.map scActive (scsOf B p) := by
    intro p
    have e : Option.map SchedContext.scRefillMax (scsOf A p) = Option.map SchedContext.scRefillMax (scsOf B p) := by
      rw [fbs_scRM_sv, fbs_scRM_sv, hv p]
    have h1 : ∀ o : Option SchedContext,
        Option.map scActive o = Option.map activeSc (Option.map SchedContext.scRefillMax o) := by
      intro o; cases o <;> rfl
    rw [h1, h1, e]
  unfold schedulable
  apply decide_eq_decide.2
  rw [hq]
  simp only [optPred, optMapSome, optMap, ta, tb, hr, hs]
  cases hsc' : yb.tcbSchedContext with
  | none => simp
  | some p =>
    have := hsc p
    cases e1 : scsOf A p <;> cases e2 : scsOf B p <;> simp_all

/-- The scheduler action `stsAct` sets. -/
theorem fbs_stsAct_sa (s : State Unit) (t : ObjRef) : (Notif.stsAct s t).schedulerAction =
    if t = s.curThread ∧ s.schedulerAction = .resumeCurThread ∧ ¬ schedulable t s = true then .chooseNewThread
    else s.schedulerAction := by
  unfold Notif.stsAct; split_ifs <;> rfl

/-- **The batch after `Restart`.** -/
theorem performFrameBatch_restart (b : Fl4FrameBatchInvocation) {σ τ : State Unit} {ct : ObjRef} {x : Tcb}
    (hk : σ.kheap ct = some (.tcb x)) {r : List Data} (hx : (r, τ) ∈ (performFrameBatch (Z := Unit) b σ).1) :
    ∃ y, τ.kheap ct = some (.tcb y) ∧ y.tcbSchedContext = x.tcbSchedContext ∧
      (r, Notif.stsAct (Notif.updK τ ct (.tcb { y with tcbState := .restart })) ct) ∈
        (performFrameBatch (Z := Unit) b (Notif.stsAct (Notif.updK σ ct (.tcb { x with tcbState := .restart })) ct)).1 := by
  have hsv := SInvR.A13b.svfb_performFrameBatch b σ _ hx
  have hF := fbsF_performFrameBatch b σ _ hx
  simp only [fbsF, Prod.mk.injEq] at hF
  obtain ⟨hF1, hF2, hF3⟩ := hF
  have h1 : SVK.sv (τ.kheap ct) = (1, x.tcbSchedContext, [], 0, none, 0) := by
    rw [hsv.1 ct, hk]; rfl
  obtain ⟨y, hy, hysc⟩ := SVK.sv_tcb h1
  refine ⟨y, hy, hysc, ?_⟩
  rw [stsAct_updK_fbsM hk, stsAct_updK_fbsM hy]
  have hsa : (Notif.stsAct (Notif.updK τ ct (.tcb { y with tcbState := .restart })) ct).schedulerAction =
      (Notif.stsAct (Notif.updK σ ct (.tcb { x with tcbState := .restart })) ct).schedulerAction := by
    have hsch : schedulable ct (Notif.updK τ ct (.tcb { y with tcbState := .restart })) =
        schedulable ct (Notif.updK σ ct (.tcb { x with tcbState := .restart })) := by
      refine fbs_schedulable (ya := { y with tcbState := .restart }) (yb := { x with tcbState := .restart })
        (by simp [Notif.updK]) (by simp [Notif.updK]) rfl hysc (fun q => ?_) hF3
      by_cases hq : q = ct
      · subst hq; simp [Notif.updK, SVK.sv, hysc]
      · simp only [Notif.updK, Function.update_of_ne hq]; exact hsv.1 q
    have c1 : (Notif.updK τ ct (.tcb { y with tcbState := .restart })).curThread = σ.curThread := hF2
    have c2 : (Notif.updK σ ct (.tcb { x with tcbState := .restart })).curThread = σ.curThread := rfl
    have c3 : (Notif.updK τ ct (.tcb { y with tcbState := .restart })).schedulerAction = σ.schedulerAction := hF1
    have c4 : (Notif.updK σ ct (.tcb { x with tcbState := .restart })).schedulerAction = σ.schedulerAction := rfl
    rw [fbs_stsAct_sa, fbs_stsAct_sa]
    simp only [hsch, c1, c2, c3, c4]
  rw [hsa]
  exact performFrameBatch_fbsM ct b σ .restart _ (r, τ) hx

end

end Fl4Proofs.P3.SInv
