/-
P3 (DESIGN.md §9), scheduling contexts: **the spec's `reschedule_required`
and `possible_switch_to` have one outcome**, which keeps the heap, given
`ActReady` (the refill part of l4v's `valid_sched_action` for the switch
target: a schedulable switch-to candidate's SC is sufficient and ready, what
`reschedule_required`'s assertion checks before enqueueing it). For the
CSpace side's `SchedOutHyp`.
-/
import Fl4Proofs.P3.ScInvQ
import Fl4Proofs.P3.SchedSwitch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- **`reschedule_required` has one outcome**, with the heap, the release
queue and the current time kept. -/
theorem rescheduleRequired_some {σ : State Unit} (hA : ActReady σ) :
    ∃ σ', rescheduleRequired (Z := Unit) σ = ({((), σ')}, False) ∧ σ'.kheap = σ.kheap ∧
      σ'.releaseQueue = σ.releaseQueue ∧ σ'.curTime = σ.curTime := by
  obtain ⟨σ1, he, hq⟩ := rescheduleRequired_qchange hA
  exact ⟨σ1, he, hq.1, hq.2.1, hq.2.2.1⟩

/-- **`possible_switch_to` of a TCB has one outcome**, with the heap, the
release queue and the current time kept. -/
theorem possibleSwitchTo_some {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hA : ActReady σ) :
    ∃ σ', possibleSwitchTo (Z := Unit) t σ = ({((), σ')}, False) ∧ σ'.kheap = σ.kheap ∧
      σ'.releaseQueue = σ.releaseQueue ∧ σ'.curTime = σ.curTime := by
  rw [possibleSwitchTo_unfold hk]
  split_ifs
  · exact ⟨_, tcbSchedAction_gen hk _, rfl, rfl, rfl⟩
  · obtain ⟨σ1, he, hk1, hr1, ht1⟩ := rescheduleRequired_some hA
    have hk' : σ1.kheap t = some (.tcb x) := by rw [hk1]; exact hk
    refine ⟨setQ σ1 x.tcbDomain x.tcbPriority
      (tcbSchedEnqueue t (σ1.readyQueues x.tcbDomain x.tcbPriority)), ?_, hk1, hr1, ht1⟩
    rw [nd_bind_one he, tcbSchedAction_gen hk' _]
  · exact ⟨_, setAction_eq σ _, rfl, rfl, rfl⟩
  · exact ⟨σ, rfl, rfl, rfl, rfl⟩

end Spec

end

end Fl4Proofs.P3.Sched
