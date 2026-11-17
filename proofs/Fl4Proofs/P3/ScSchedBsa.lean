/-
P3 (DESIGN.md §9), scheduler: **`BlockedScActive` after `schedule`**
(`bsa_schedule`), spec side only: `schedule` keeps every SC's `REFILL_MAX`
and bound thread (`MaxK.mk_schedule`) and every thread's state (`SchS`), so
it is a `BK` step keeping the call stacks.
-/
import Fl4Proofs.P3.ScMaxKeep
import Fl4Proofs.P3.ScSchedSpec
import Fl4Proofs.P3.ScFieldKeep
import Fl4Proofs.P3.ScBsaOps
open Classical

namespace Fl4Proofs.P3.MaxK
open Fl4Spec

noncomputable section

/-- The scheduler's operations unfolded down to `MK`'s leaves. -/
macro "sched_unf" : tactic => `(tactic| first
  | unfold awaken | unfold tcbReleaseDequeue | unfold scheduleChooseNewThread | unfold archPrepareNextDomain
  | unfold nextDomain | unfold chooseThread | unfold guardedSwitchTo | unfold switchToThread
  | unfold switchToIdleThread | unfold archSwitchToThread | unfold archSwitchToIdleThread | unfold scAndTimer
  | unfold switchSchedContext | unfold ifConstantBandwidthRefillUnblockCheck | unfold setNextInterrupt
  | unfold scheduleSwitchThreadFastfail | unfold setVmRoot | unfold getCurrentCr3 | unfold setCurrentVspaceRoot
  | unfold setCurrentCr3 | unfold findVspaceForAsid | unfold lazyFpuRestore | unfold switchLocalFpuOwner
  | unfold setX64CurrentFpuOwner | unfold saveFpuState | unfold loadFpuState | unfold checkDomainTime
  | unfold getAsidPool)

macro "mk_auto2" : tactic => `(tactic| repeat' (first | mk_leaf | mk_step0 | fk_unf | sched_unf))

set_option maxHeartbeats 2000000 in
theorem mk_commitTimeS : MK (commitTime (Z := Unit)) := by
  unfold commitTime
  mk_auto2
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_commitTimeS)

set_option maxHeartbeats 2000000 in
theorem mk_setVmRootS (t : ObjRef) : MK (setVmRoot (Z := Unit) t) := by
  unfold setVmRoot
  mk_auto2
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_setVmRootS _)

set_option maxHeartbeats 2000000 in
theorem mk_lazyFpuRestoreS (t : ObjRef) : MK (lazyFpuRestore (Z := Unit) t) := by
  unfold lazyFpuRestore
  mk_auto2
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_lazyFpuRestoreS _)

set_option maxHeartbeats 2000000 in
theorem mk_switchToThreadS (t : ObjRef) : MK (switchToThread (Z := Unit) t) := by
  unfold switchToThread
  mk_auto2
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_switchToThreadS _)

set_option maxHeartbeats 2000000 in
theorem mk_switchToIdleThreadS : MK (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread
  mk_auto2
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_switchToIdleThreadS)

set_option maxHeartbeats 2000000 in
theorem mk_guardedSwitchToS (t : ObjRef) : MK (guardedSwitchTo (Z := Unit) t) := by
  unfold guardedSwitchTo
  mk_auto2
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_guardedSwitchToS _)

set_option maxHeartbeats 2000000 in
theorem mk_chooseThreadS : MK (chooseThread (Z := Unit)) := by
  unfold chooseThread
  mk_auto2
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_chooseThreadS)

set_option maxHeartbeats 2000000 in
theorem mk_scheduleChooseNewThreadS : MK (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread
  mk_auto2
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_scheduleChooseNewThreadS)

set_option maxHeartbeats 2000000 in
theorem mk_awakenS : MK (awaken (Z := Unit)) := by
  unfold awaken
  mk_auto2
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_awakenS)

set_option maxHeartbeats 2000000 in
theorem mk_setNextInterruptS : MK (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt
  mk_auto2
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_setNextInterruptS)

set_option maxHeartbeats 2000000 in
theorem mk_scAndTimerS : MK (scAndTimer (Z := Unit)) := by
  unfold scAndTimer
  mk_auto2
macro_rules | `(tactic| mk_leaf) => `(tactic| with_reducible exact mk_scAndTimerS)

set_option maxHeartbeats 2000000 in
/-- **The spec's `schedule` keeps every SC's `REFILL_MAX` and bound thread.** -/
theorem mk_schedule : MK (schedule (Z := Unit)) := by
  unfold schedule
  mk_auto2

end

end Fl4Proofs.P3.MaxK

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

/-- **A scheduler step keeping the SCs' `REFILL_MAX` and bound threads is a
`BK` step.** -/
theorem BK.of_sch {σ σ' : State Unit} (hK : SchStep (fun _ => False) σ σ') (hm : MaxK.SCK σ σ') : BK σ σ' := by
  refine ⟨fun t x hx hq => ?_, fun p y n hp ha => ?_⟩
  · have hk := hK.kh t
    rw [hx] at hk
    cases h0 : σ.kheap t with
    | none => rw [h0] at hk; exact hk.elim
    | some o =>
      rw [h0] at hk
      rcases hk with e | ⟨x0, z, e1, e2, -, hs⟩ | ⟨_, _, _, -, e⟩ | ⟨_, _, -, e, -⟩ | ⟨_, _, -, e, -⟩
      · subst e; exact ⟨x, rfl, hq⟩
      · cases e2
        subst e1
        rcases hs with hs | ⟨hf, -⟩
        · exact ⟨x0, rfl, by rw [← hs]; exact hq⟩
        · exact hf.elim
      all_goals cases e
  · obtain ⟨y0, hp0, e1, e2⟩ := hm p y n hp
    exact ⟨y0, hp0, by simpa [scActive, e1] using ha, fun t e => Or.inl (e2 ▸ e)⟩

/-- **`BlockedScActive` after the spec's `schedule`.** -/
theorem bsa_schedule {σ σ' : State Unit} (h : BlockedScActive σ)
    (hsc : Fl4Spec.schedule (Z := Unit) σ = ({((), σ')}, False)) : BlockedScActive σ' := by
  have hm : ((), σ') ∈ (Fl4Spec.schedule (Z := Unit) σ).1 := by rw [hsc]; exact Set.mem_singleton _
  have hS := schs_schedule σ _ hm
  exact h.bk (BK.of_sch hS.1 (MaxK.mk_schedule σ _ hm)) hS.2

end

end Fl4Proofs.P3.Sched
