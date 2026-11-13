/-
P3 (DESIGN.md §9), scheduler: **`sched::append` refines
`tcb_sched_action tcb_sched_append`** (seL4 `tcbSchedAppend`; FL4's
`schedule` uses it). Separate from SchedQueue.lean because P1's `append`
lemmas are in P1/QueueCallers.lean.
-/
import Fl4Proofs.P3.SchedQueue
import Fl4Proofs.P1.QueueCallers
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **`append` refines `tcb_sched_action tcb_sched_append`**, for a thread
that is queued already or not in the release queue. -/
theorem append_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (t : U64) (ht : t ∈ T)
    (hr : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    sched.append st s t ⦃ s' => ∃ σ', Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedAppend t.bv σ =
      ({((), σ')}, False) ∧ σ'.kheap = σ.kheap ∧ σ'.releaseQueue = σ.releaseQueue ∧
      FootEq N T (L.mem s) (L.mem s') ∧ SchedRel st N T C c s' σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hp := hc.prio t ht
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hR1 : ReadyQueues st T s (L.mem s (affA t)) Q := by rw [haf]; exact hc.ready
  have hnq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → ∀ p : U64, p.val < 256 → t ∉ Q p := by
    intro h0 p hp' hm
    have e := hc.inQ p hp' t hm
    exact ((hc.queued t ht).2 (by rw [e]; exact hm)) h0
  obtain ⟨x, hk, hd, -, -, hpr⟩ := hs.tcb t ht
  have h1 := sched.append.ready s t Q hT ht hp hN hN' hR1 hnq
  have h2 := sched.append.foot s t _ hT ht hp hN hN' (hR1.1.rel _ hp) (fun h0 => hnq h0 _ hp)
  refine WP.spec_mono (WP.spec_and h1 h2) ?_
  rintro s' ⟨hRc, hw, hinq⟩
  rw [haf] at hRc hw
  have hW : ∀ w ∈ t :: Q (L.mem s (prioA t)), w ∈ T := by
    intro w hw'; rcases List.mem_cons.1 hw' with rfl | hw'
    · exact ht
    · exact (hc.ready.1.rel _ hp).mem w hw'
  have hspec := tcbSchedAction_eq hk hd Fl4Spec.tcbSchedAppend
  rw [← specPrio_eq hpr, hs.rq _ hp] at hspec
  by_cases hqd : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
  · simp only [hqd, ne_eq, not_false_eq_true, ↓reduceIte] at hRc hinq
    have htq := (hc.queued t ht).1 hqd
    have hst := hS.qstep hc hs ht (W := t :: Q _) (xs' := Q (L.mem s (prioA t))) (tIn := True)
      (fun w hw => List.mem_cons.1 hw) (fun _ => hc.excl t ht htq) hw (by rw [Function.update_eq_self]; exact hRc)
      (fun y => by by_cases e : y = t <;> simp [e, htq]) (by rw [hinq]; simpa using hqd) (by rw [hinq])
      (fun _ => hc.excl t ht htq)
    refine ⟨_, hspec, rfl, rfl, qfoot_footEq hS hc ht hW hw, ?_⟩
    have : Fl4Spec.tcbSchedAppend t.bv ((Q (L.mem s (prioA t))).map UScalar.bv) =
        (Q (L.mem s (prioA t))).map UScalar.bv := by
      unfold Fl4Spec.tcbSchedAppend; rw [ite_f (by rw [not_not, mem_map_bv]; exact htq)]
    rw [this]; exact hst
  · have hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := not_not.1 hqd
    simp only [hqd, ↓reduceIte] at hRc hinq
    have htq := hnq hq0 _ hp
    have hnr : t ∉ R := fun hm => ((hc.released t ht).2 hm) (hr hq0)
    have hst := hS.qstep hc hs ht (W := t :: Q _) (xs' := Q (L.mem s (prioA t)) ++ [t]) (tIn := True)
      (fun w hw => List.mem_cons.1 hw) (fun _ => hnr) hw hRc
      (fun y => by by_cases e : y = t <;> simp [e])
      (by rw [hinq, or_qq_qq]; simp) (by rw [hinq, or_qq_qr]) (fun _ => hnr)
    refine ⟨_, hspec, rfl, rfl, qfoot_footEq hS hc ht hW hw, ?_⟩
    have : Fl4Spec.tcbSchedAppend t.bv ((Q (L.mem s (prioA t))).map UScalar.bv) =
        (Q (L.mem s (prioA t)) ++ [t]).map UScalar.bv := by
      unfold Fl4Spec.tcbSchedAppend; rw [ite_t (by rw [mem_map_bv]; exact htq)]; simp
    rw [this]; exact hst

end

end

end Fl4Proofs.P3.Sched
