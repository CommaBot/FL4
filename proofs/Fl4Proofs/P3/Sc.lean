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
-/
import Fl4Proofs.P3.ScBudgetTop
import Fl4Proofs.P3.ScInvB
