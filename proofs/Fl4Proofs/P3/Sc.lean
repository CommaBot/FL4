/-
P3 (DESIGN.md §9), scheduling contexts (MCS): top module.

* ScRel: the SC relation `ScRel1` (FL4 SC object ↔ l4v `sched_context`).
* ScFrame, ScSpec: frame lemmas for SC writes, spec-side unfolding lemmas.
* ScUnblock: `refill_unblock_check`; ScNtfn: `unblock_sporadic`
  (`WakeHyps.unblock`).
* ScReturn, ScReady, ScReturnRef: `maybe_return_sched_context`, given
  `ActReady`; `ActReady.transfer`.
* ScDonate: `refill_ready`, `refill_sufficient`, the no-donation cases of
  `maybe_donate_sched_context`.
* ScTails: `RecvHyps`' receive/complete tails and `WakeHyps` from the
  donation hypothesis `DonateHyp`.
* ScRelease: the release queue (`SchedRel.rstep`, `release_enqueue_refines`).
* ScResume: `postpone`, `sched_context_resume`.
* ScDonateRef: the donation branch (`donate_refines`, `maybe_donate_refines`,
  `ActReady.donate`).
* ScHyps: `RecvHyps.returnSc` discharged (`returnSc_of`), `DonateHyp` and
  `WakeHyps` from state facts (`DonatePre`).
* ScRing, ScBudgetSpec, ScBudget, ScBudgetTop: `refill_budget_check`
  (`loop0_refines`, `loop1_refines`, `budget_check_refines`).
* ScInv, ScInvQ, ScInvU, ScInvD, ScInvD2, ScInvR: the scheduler invariant
  `Inv` (fragments of l4v `valid_sched`, `valid_refills`, `heap_refs_inv`)
  and its preservation by the refined operations.
* ScInvSR: `SchedHyps` and `RecvHyps` for `SRI` (`SchedRel` ∧ `Inv` ∧ `NSC`).
* ScInvB: `budget_check`'s refill facts from `Inv`, and `Inv` after it.
* ScCharge1–ScCharge6: `charge_budget` (`charge_budget_refines`), with
  `end_timeslice` (`end_timeslice_refines`) restoring `Inv`.
* ScCharge7: `check_budget`, `check_budget_restart`.
* ScCharge8: `commit_time` (`InvBut` for the current thread).
* ScConsumed: `update_consumed` (`sched_context_update_consumed`).
* ScCur: the current-thread invariant `CurInv` (l4v `cur_sc_tcb_are_bound`,
  `cur_sc_active`, `ct_not_in_release_q`, current thread not blocked) and
  its preservation steps; `HeadKeeps`.
* ScTime: `update_timestamp` (`update_time_stamp`); `Inv` under a later time.
* ScEntry: the budget path at kernel entry (`budget_ok_refines`,
  `entry_check_budget_refines`) from `Inv` and `CurInv`, ending in `Inv`.
* ScUpdate: `refill_update` (SchedControl `Configure`'s ring update); the SC
  footprint is the object (`ScObj`), so `REFILL_MAX` may change.
* ScHead, ScOffset: the head after a sufficient charge; l4v
  `cur_sc_offset_ready/sufficient` (`OffOK`) and `commit_time_inv`.
* ScSwitch: `switch_sched_context` (unblock check of the incoming SC,
  `commit_time` of the outgoing one), keeping `Inv` and establishing `CurInv`.
* ScSwitchTo: `switch_to_thread`, `switch_to_idle_thread` (arch switch as a
  hypothesis); writing `CUR_THREAD`.
* ScSchedule: `check_domain_time` (one domain), `guarded_switch_to` of a
  ready-queue head, `choose_thread`.
* ScAwaken: `release_remove` of the release queue's head, `awaken` (after
  FL4's TCB timers, a hypothesis), `Calm`, `SchedPre`.
* ScScheduleTop: the switch-thread branch, `schedule` (`schedule_refines`),
  ending in `Inv` and `CurInv`.
-/
import Fl4Proofs.P3.ScBudgetTop
import Fl4Proofs.P3.ScInvB
import Fl4Proofs.P3.ScCharge8
import Fl4Proofs.P3.ScConsumed
import Fl4Proofs.P3.ScEntry
import Fl4Proofs.P3.ScSchedule
import Fl4Proofs.P3.ScScheduleTop
