/-
P3 (DESIGN.md §9), scheduling contexts: **ready-queue steps keep `Inv`**.

`QChange σ σ'`: the heap, release queue and time are unchanged, and a new
ready-queue member is schedulable. `tcb_sched_action` (enqueue of a
schedulable thread, dequeue), `set_thread_state_act`, `reschedule_required`
and `possible_switch_to` (of a schedulable thread) are `QChange`s, which keep
`Inv` (`Inv.qchange`).
-/
import Fl4Proofs.P3.ScInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- A ready-queue step (see the module docstring). -/
def QChange (σ σ' : State Unit) : Prop :=
  σ'.kheap = σ.kheap ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.curTime = σ.curTime ∧
    ∀ d p u, u ∈ σ'.readyQueues d p → u ∈ σ.readyQueues d p ∨ schedulable u σ = true

theorem QChange.refl (σ : State Unit) : QChange σ σ := ⟨rfl, rfl, rfl, fun _ _ _ h => Or.inl h⟩

theorem schedulable_heap {σ σ' : State Unit} (hk : σ'.kheap = σ.kheap) (hr : σ'.releaseQueue = σ.releaseQueue)
    (u : ObjRef) : schedulable u σ' = schedulable u σ :=
  schedulable_congr (by simp only [tcbsOfKh, hk]) (fun p => by simp only [scsOfKh, hk]) hr

theorem QChange.trans {σ σ1 σ2 : State Unit} (h1 : QChange σ σ1) (h2 : QChange σ1 σ2) : QChange σ σ2 := by
  refine ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, fun d p u hu => ?_⟩
  rcases h2.2.2.2 d p u hu with hm | hs
  · exact h1.2.2.2 d p u hm
  · rw [schedulable_heap h1.1 h1.2.1] at hs; exact Or.inr hs

theorem Inv.qchange {σ σ' : State Unit} (h : Inv σ) (hq : QChange σ σ') : Inv σ' := by
  obtain ⟨hk, hr, ht, hm⟩ := hq
  refine h.congr' hk (fun d p u hu => ?_) hr ht
  rcases hm d p u hu with hu | hs
  · exact h.rq d p u hu
  · obtain ⟨x, scp, y, n, h1, h2, h3, -⟩ := schedulable_inv hs
    exact ⟨x, scp, h1, h2, h3⟩

/-- The state with ready queue `(d, p)` set to `q`. -/
def setQ (σ : State Unit) (d : Domain) (p : Priority) (q : List ObjRef) : State Unit :=
  { σ with readyQueues := fun d' p' => if d' = d ∧ p' = p then q else σ.readyQueues d' p' }

/-- `tcb_sched_action` on any domain. -/
theorem tcbSchedAction_gen {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (f : ObjRef → List ObjRef → List ObjRef) :
    tcbSchedAction (Z := Unit) f t σ = ({((), setQ σ x.tcbDomain x.tcbPriority (f t (σ.readyQueues x.tcbDomain x.tcbPriority)))}, False) := by
  unfold tcbSchedAction
  rw [nd_bind_one (threadGet_eq _ hk), nd_bind_one (threadGet_eq _ hk), nd_bind_one (getTcbQueue_eq _ _ _),
    nd_pure_bind']
  rfl

theorem qchange_tcbSchedAction {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (f : ObjRef → List ObjRef → List ObjRef)
    (hf : ∀ u ∈ f t (σ.readyQueues x.tcbDomain x.tcbPriority),
      u ∈ σ.readyQueues x.tcbDomain x.tcbPriority ∨ schedulable u σ = true) :
    QChange σ (setQ σ x.tcbDomain x.tcbPriority (f t (σ.readyQueues x.tcbDomain x.tcbPriority))) := by
  refine ⟨rfl, rfl, rfl, fun d p u hu => ?_⟩
  simp only [setQ] at hu
  split at hu
  · rename_i e; obtain ⟨rfl, rfl⟩ := e; exact hf u hu
  · exact Or.inl hu

theorem qchange_enqueue {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hs : schedulable t σ = true) :
    QChange σ (setQ σ x.tcbDomain x.tcbPriority (tcbSchedEnqueue t (σ.readyQueues x.tcbDomain x.tcbPriority))) :=
  qchange_tcbSchedAction hk _ fun u hu => by
    unfold tcbSchedEnqueue at hu
    split at hu
    · rcases List.mem_cons.1 hu with rfl | hu
      · exact Or.inr hs
      · exact Or.inl hu
    · exact Or.inl hu

theorem qchange_dequeue {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) :
    QChange σ (setQ σ x.tcbDomain x.tcbPriority (tcbSchedDequeue t (σ.readyQueues x.tcbDomain x.tcbPriority))) :=
  qchange_tcbSchedAction hk _ fun u hu => Or.inl (List.mem_of_mem_filter hu)

theorem qchange_action (σ : State Unit) (a : SchedulerAction) : QChange σ { σ with schedulerAction := a } :=
  ⟨rfl, rfl, rfl, fun _ _ _ h => Or.inl h⟩

theorem qchange_stsAct (σ : State Unit) (t : ObjRef) : QChange σ (stsAct σ t) := by
  unfold stsAct; split_ifs
  · exact qchange_action σ _
  · exact QChange.refl σ

theorem the_result {σ σ1 σ2 : State Unit} {m : NonDet (State Unit) Unit} (h1 : m σ = ({((), σ1)}, False))
    (h2 : m σ = ({((), σ2)}, False)) : σ2 = σ1 := by
  rw [h1] at h2
  exact ((Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst h2))).2).symm

theorem pair_eq {a b : State Unit}
    (he : (({((), a)}, False) : Set (Unit × State Unit) × Prop) = ({((), b)}, False)) : b = a :=
  ((Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he))).2).symm

/-- `reschedule_required` has one outcome, a `QChange`, given `ActReady`. -/
theorem rescheduleRequired_qchange {σ : State Unit} (hA : ActReady σ) :
    ∃ σ1, rescheduleRequired (Z := Unit) σ = ({((), σ1)}, False) ∧ QChange σ σ1 := by
  cases ha : σ.schedulerAction with
  | switchThread t =>
    by_cases hs : schedulable t σ = true
    · obtain ⟨x, -, -, -, hk, -⟩ := schedulable_inv hs
      have he := tcbSchedAction_gen hk tcbSchedEnqueue
      refine ⟨_, rescheduleRequired_sched ha hs hA he, (qchange_enqueue hk hs).trans (qchange_action _ _)⟩
    · exact ⟨_, rescheduleRequired_notsched ha (by simpa using hs), qchange_action _ _⟩
  | resumeCurThread =>
    exact ⟨_, rescheduleRequired_noswitch (fun t h => by rw [ha] at h; cases h), qchange_action _ _⟩
  | chooseNewThread =>
    exact ⟨_, rescheduleRequired_noswitch (fun t h => by rw [ha] at h; cases h), qchange_action _ _⟩

theorem QChange.actReady {σ σ' : State Unit} (h : Inv σ) (hq : QChange σ σ') : ActReady σ' :=
  (h.qchange hq).actReady

/-- **`possible_switch_to` of a schedulable thread is a `QChange`.** -/
theorem possibleSwitchTo_qchange {σ σ' : State Unit} (h : Inv σ) {t : ObjRef} (hs : schedulable t σ = true)
    (he : possibleSwitchTo (Z := Unit) t σ = ({((), σ')}, False)) : QChange σ σ' := by
  obtain ⟨x, -, -, -, hk, -⟩ := schedulable_inv hs
  rw [possibleSwitchTo_unfold hk] at he
  split_ifs at he
  · rw [tcbSchedAction_gen hk] at he
    rw [pair_eq he]; exact qchange_enqueue hk hs
  · obtain ⟨σ1, h1, hq1⟩ := rescheduleRequired_qchange h.actReady
    rw [nd_bind_one h1] at he
    have hk1 : σ1.kheap t = some (.tcb x) := by rw [hq1.1]; exact hk
    rw [tcbSchedAction_gen hk1] at he
    rw [pair_eq he]
    refine hq1.trans (qchange_enqueue hk1 ?_)
    rw [schedulable_heap hq1.1 hq1.2.1]; exact hs
  · rw [setAction_eq] at he
    rw [pair_eq he]; exact qchange_action _ _
  · rw [pair_eq he]; exact QChange.refl σ

end Spec

end

end Fl4Proofs.P3.Sched
