/-
P3 (line mmuAD, gen 36): **why gen 35's [J] `SigVmTailJ3` is false as stated** (P3/JAtZV3SigVm), the formal core of
the counterexample.

`SigVmTailJ3` asks, from any `JAtZV3` state where `t` is `running` and `n` is idle and bound to `t`, for one outcome
of `sigVmTailS n t` at which `JAtZV3` holds again, hence `Sched.Inv` and its sorted release queue (`Inv.sorted`,
l4v `sorted_release_q`). `running` does not keep `t` out of the release queue: a runnable thread whose budget ran
out is postponed there (`postpone`) and keeps its state, and `Inv.rel` / `Inv.rd` / `RelIfBound` allow a member's
head refill to be ready (between the kernel entry's `update_timestamp` and `schedule`'s `awaken`; FL4's
`handle_interrupt_entry` is `update_timestamp; check_budget; handle_interrupt; finish`, so a device IRQ's
`send_signal` runs before `awaken`).

Counterexample shape: `σ.releaseQueue = t :: b :: rest`; `t`'s SC `p` is `n`'s SC (donated earlier: `scTcb = t`,
`ntfnSc = p`), active, sporadic (`scSporadic`, `scPeriod ≠ 0`), not `curSc`, head ready (`rTime ≤ curTime`); `b`'s
SC `q ≠ p` has head `rTime_b` with `rTime_t ≤ rTime_b < curTime` (e.g. 100, 105, 110). In `sigVmTailS`:
`maybeDonateSc` does nothing (`t` has an SC); `schedulable t` is false (`t` is in the release queue), so no
switch; `scOpt = ntfnScp = some p`, active, sporadic, `p ≠ curSc`, so `refillUnblockCheck p` runs; it sets `p`'s
head `rTime := curTime` and leaves the queue, so `t` (now `curTime`) precedes `b` (`rTime_b < curTime`): the
release queue is no longer sorted (`v3_unblock_unsorted` below). FL4's `send_signal` (notification.rs l.106-114)
and seL4's (`src/object/notification.c` l.102-118 at c98d70ad, VT-x, unverified upstream) do the same; both states relate, but no state
after satisfies `JAtZV3`. With `t`'s pre-report state `runningVM` (VCPU without a pending exit, affinity = this
core) the same state is a counterexample to gen 35's `signalVmJ` conclusion without its [J].

* **`v3_unblock_unsorted`**: every outcome of `refillUnblockCheck p` from such a state has an unsorted release queue.

No premise. No existing statement changed.
-/
import Fl4Proofs.P3.ScInvU
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

open Fl4Spec

/-- **`refillUnblockCheck` of a release-queued thread's ready sporadic SC unsorts the release queue** (module
docstring). -/
theorem v3_unblock_unsorted {σ σ' : State Unit} {p q t b : ObjRef} {y yb : SchedContext} {n nb : Nat}
    {xt xb : Tcb} {rest : List ObjRef}
    (hk : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills ≠ [])
    (hrdy : refillReady σ.curTime (refillHd y) = true) (hper : y.scPeriod ≠ 0)
    (hkt : σ.kheap t = some (.tcb xt)) (hts : xt.tcbSchedContext = some p)
    (hkb : σ.kheap b = some (.tcb xb)) (hbs : xb.tcbSchedContext = some q)
    (hkq : σ.kheap q = some (.schedContext yb nb)) (hneb : yb.scRefills ≠ []) (hqp : q ≠ p)
    (hlt : (refillHd yb).rTime < σ.curTime) (hrq : σ.releaseQueue = t :: b :: rest)
    (hm : ((), σ') ∈ (refillUnblockCheck (Z := Unit) p σ).1) :
    ¬ σ'.releaseQueue.Pairwise (fun u w => specRt σ' u ≤ specRt σ' w) := by
  rcases unblock_result hk hne hm with ⟨-, hn⟩ | ⟨z, rfl, -, hzt, -, -, hzne, -⟩
  · exact (hn ⟨hrdy, by simpa using hper⟩).elim
  intro hP
  have htp : t ≠ p := by rintro rfl; rw [hk] at hkt; cases hkt
  have hbp : b ≠ p := by rintro rfl; rw [hk] at hkb; cases hkb
  have hkt' : (updSc { σ with reprogramTimer := true } p z n).kheap t = some (.tcb xt) := by
    simp [updK, htp, hkt]
  have hkb' : (updSc { σ with reprogramTimer := true } p z n).kheap b = some (.tcb xb) := by
    simp [updK, hbp, hkb]
  have hkp' : (updSc { σ with reprogramTimer := true } p z n).kheap p = some (.schedContext z n) := by
    simp [updK]
  have hkq' : (updSc { σ with reprogramTimer := true } p z n).kheap q = some (.schedContext yb nb) := by
    simp [updK, hqp, hkq]
  have e1 := specRt_eq hkt' hts hkp' hzne
  have e2 := specRt_eq hkb' hbs hkq' hneb
  have hq' : (updSc { σ with reprogramTimer := true } p z n).releaseQueue = t :: b :: rest := hrq
  rw [hq'] at hP
  have h := (List.pairwise_cons.1 hP).1 b (List.mem_cons_self ..)
  rw [e1, e2, hzt] at h
  rw [BitVec.le_def] at h
  rw [BitVec.lt_def] at hlt
  omega

end

end Fl4Proofs.P3.Sched
