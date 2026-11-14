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
-/
import Fl4Proofs.P3.ScTails
