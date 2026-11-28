/-
P3 (DESIGN.md §9): **the current SC's threads are out of the release queue
at a preemption hole** (KENTRY-PLAN kp11, (2b) step 1; l4v
`cur_sc_not_in_release_q` / `cur_sc_in_release_q_imp_zero_consumed` at the
preemption point).

`charge_budget` from a hole without `CurInv` charges the current SC through
its OWNER, not the current thread: ScCharge2's `Inv.refillUpd` (the release
queue stays sorted) needs the owner out of the release queue. No `[J]` fact
is needed for it:

* `CurScFree σ`: no thread bound to the current SC is in the release queue.
* `curScFree_of`: from `Inv`, `JAtZ`'s `CurOwnW` and ScPPR's `PPR0` at one
  state. A positive consumed time: `CurOwn`'s release-queue clause, the
  owner being the only thread bound to the SC (`Inv.back`); an unowned SC
  has no bound thread (`Inv.back`). A zero consumed time: `PPR0`'s second
  clause (carried by the deletion and reset loops from `Entered`, where
  `CurInv.notRel` gives it).
* `jAtPre_holeO`: `jAtPre_holeTN` with `CurScFree` at the hole (since kp11
  `JAtPre` carries all of `PPR0` at the base; the preemption point changes
  neither the heap, the current SC nor the release queue, `pp_err_eq`).

The unconditional form ("the owner of an active SC is not in the release
queue") is false (every queued thread owns an active SC); so is the form at
every `JAtZ` state (after the entry's `check_budget_restart` postpones the
current thread its SC's owner is queued at a zero consumed time): the fact is
a property of a preemption hole, from the loop's `PPR0`.
-/
import Fl4Proofs.P3.XTopJointPreemptI
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **No thread bound to the current SC is in the release queue** (module
docstring). -/
def CurScFree (σ : Fl4Spec.State Unit) : Prop :=
  ∀ u xt, σ.kheap u = some (.tcb xt) → xt.tcbSchedContext = some σ.curSc → u ∉ σ.releaseQueue

/-- **`CurScFree` from `Inv`, `CurOwnW` and `PPR0`** (module docstring). -/
theorem curScFree_of {T C : Set U64} {σ : Fl4Spec.State Unit} (hI : Inv σ) (hO : CurOwnW T C σ)
    (hp : PPR0 σ) : CurScFree σ := by
  intro u xt hu hs hr
  by_cases h0 : σ.consumedTime = 0
  · exact (hp.2 h0).2 u xt hu hs hr
  · obtain ⟨y, n, hky, hyt⟩ := hI.back u xt σ.curSc hu hs
    rcases hO with ⟨w, -, xw, -, -, hown, hnr⟩ | ⟨-, hun⟩
    · have e := hown y n hky
      rw [hyt] at e
      cases e
      exact hnr (by bv_omega) hr
    · rw [hun y n hky] at hyt; cases hyt

end

end Fl4Proofs.P3
