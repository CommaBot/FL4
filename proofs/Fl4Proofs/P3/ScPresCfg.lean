/-
P3 (DESIGN.md §9), scheduling contexts: **`Pres` for SchedControl
`ConfigureFlags`** (ScPres.lean): `invoke_sched_control_configure_flags`
keeps the CNodes, the TCBs' caps and MCPs, the objects' kinds and SC sizes,
the CDT and the domain schedule (and the yield-to links and call stacks).
-/
import Fl4Proofs.P3.ScPresOps
import Fl4Spec.Ipc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

section
variable (f : Bool × Bool)

theorem pres_commitTime : Pres f (commitTime (Z := Unit)) := by
  unfold commitTime refillBudgetCheckRoundRobin refillBudgetCheck
  repeat (first | unfold updateRefillHd | unfold updateRefillTl | unfold refillAddTail | unfold refillPopHead | unfold getRefillHead | unfold getRefills | unfold getRefillTail | unfold refillFull | unfold refillSingle | unfold refillSize | unfold scheduleUsed | unfold chargeEntireHeadRefill | unfold handleOverrun | unfold headInsufficientLoop | unfold mergeNonoverlappingHeadRefill | unfold isRoundRobin | unfold getScActive | unfold getScRefillReady | unfold maybeAddEmptyTail)
  pres_auto

theorem pres_refillNew (p : ObjRef) (m : Nat) (b per : Ticks) : Pres f (refillNew (Z := Unit) p m b per) := by
  unfold refillNew
  repeat (first | unfold updateRefillHd | unfold updateRefillTl | unfold refillAddTail | unfold refillPopHead | unfold getRefillHead | unfold getRefills | unfold getRefillTail | unfold refillFull | unfold refillSingle | unfold refillSize | unfold scheduleUsed | unfold chargeEntireHeadRefill | unfold handleOverrun | unfold headInsufficientLoop | unfold mergeNonoverlappingHeadRefill | unfold isRoundRobin | unfold getScActive | unfold getScRefillReady | unfold maybeAddEmptyTail)
  pres_auto

theorem pres_refillUpdate (p : ObjRef) (per b : Ticks) (m : Nat) : Pres f (refillUpdate (Z := Unit) p per b m) := by
  unfold refillUpdate
  repeat (first | unfold updateRefillHd | unfold updateRefillTl | unfold refillAddTail | unfold refillPopHead | unfold getRefillHead | unfold getRefills | unfold getRefillTail | unfold refillFull | unfold refillSingle | unfold refillSize | unfold scheduleUsed | unfold chargeEntireHeadRefill | unfold handleOverrun | unfold headInsufficientLoop | unfold mergeNonoverlappingHeadRefill | unfold isRoundRobin | unfold getScActive | unfold getScRefillReady | unfold maybeAddEmptyTail)
  pres_auto

theorem pres_possibleSwitchTo (t : ObjRef) : Pres f (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo getTcbObjRef setSchedulerAction
  refine pres_bind (pres_threadGet f _ _) fun _ => pres_bind (pres_gets _) fun _ => pres_when _ ?_
  refine pres_bind (pres_gets _) fun _ => pres_bind (pres_threadGet f _ _) fun _ => pres_bind (pres_gets _)
    fun _ => ?_
  split
  · exact pres_tcbSchedAction f _ _
  · split
    · exact pres_bind (pres_rescheduleRequired f) fun _ => pres_tcbSchedAction f _ _
    · pres_auto

end

/-- One step of a `Pres` proof, with the configure lemmas. -/
macro "pres_step2" : tactic => `(tactic| first
  | with_reducible exact pres_commitTime _ | with_reducible exact pres_refillNew _ _ _ _ _
  | with_reducible exact pres_refillUpdate _ _ _ _ _ | with_reducible exact pres_possibleSwitchTo _ _
  | with_reducible exact pres_rescheduleRequired _ | with_reducible exact pres_schedContextResume _ _
  | with_reducible exact pres_tcbReleaseRemove _ _ | pres_step)

/-- **SchedControl `ConfigureFlags` keeps `SOK`.** -/
theorem pres_invokeSchedControlConfigureFlags (f : Bool × Bool) (iv : SchedControlInvocation) :
    Pres f (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags getThreadState getScActive
  repeat pres_step2

end

end Fl4Proofs.P3.Sched
