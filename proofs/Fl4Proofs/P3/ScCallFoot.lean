/-
P3 (DESIGN.md §9), scheduling contexts: **scheduler footprints**: the
queue operations, `reschedule_required` and the TCB-word writes write only
words of the TCBs and of the node (`SFoot`), so they keep the call-stack
words (`callWords_of_sfoot`).
-/
import Fl4Proofs.P3.ScCallOps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem SFoot.ksb {T : Set U64} {c : U64} {s s' : S} (h : L.ksb s' = L.ksb s) {b : U64} :
    SFoot st T c s' b ↔ SFoot st T c s b := by
  simp only [SFoot, LawfulStore.nodeBase, h]

theorem WritesIn.sfoot_trans {T : Set U64} {c : U64} {s s1 s2 : S} (h1 : WritesIn st s s1 (SFoot st T c s))
    (h2 : WritesIn st s1 s2 (SFoot st T c s1)) : WritesIn st s s2 (SFoot st T c s) :=
  (h1.trans h2).mono fun b hb => by
    rcases hb with hb | hb
    · exact hb
    · exact (SFoot.ksb h1.1).1 hb

/-- A word of a TCB is in the footprint. -/
theorem sfoot_tcb {T : Set U64} {c : U64} {s : S} {y K : U64} (hT : TcbPlaced T) (hy : y ∈ T) (hK : K.val < 4096) :
    SFoot st T c s (core.num.U64.wrapping_add y K) :=
  Or.inl ⟨y, hy, by rw [tfield_val (hT y hy) hK]; omega, by rw [tfield_val (hT y hy) hK]; omega⟩

theorem writesIn_tcb {T : Set U64} {c : U64} {s : S} {y K : U64} (hT : TcbPlaced T) (hy : y ∈ T)
    (hK : K.val < 4096) (hK8 : K.val % 8 = 0) (v : U64) :
    WritesIn st s (L.wr s (core.num.U64.wrapping_add y K) v) (SFoot st T c s) :=
  (writesIn_wr (field_aligned (hT y hy) hK hK8)).mono fun b hb => hb ▸ sfoot_tcb hT hy hK

/-- A queue footprint is in the scheduler footprint. -/
theorem qfoot_sfoot {T : Set U64} {c : U64} {s : S} {W : List U64} {P : Nat → Prop} {t b : U64}
    (hT : TcbPlaced T) (hW : ∀ w ∈ W, w ∈ T) (ht : t ∈ T) (hN : NodePlaced st T s c) (hcpu : L.cpu s = c)
    (h : L.QFoot s W c P t b) : SFoot st T c s b := by
  rcases h with ⟨w, hw, e | e⟩ | ⟨o, -, ho, -, e⟩ | e | ⟨o, -, ho, -, e⟩
  · refine Or.inl ⟨w, hW w hw, ?_, ?_⟩ <;> rw [e, nextA_val (hT w (hW w hw))] <;> simp [nextOff] <;> omega
  · refine Or.inl ⟨w, hW w hw, ?_, ?_⟩ <;> rw [e, prevA_val (hT w (hW w hw))] <;> simp [prevOff] <;> omega
  · exact Or.inr ⟨by rw [e, nodeAt_val hN ho]; omega, by rw [e, nodeAt_val hN ho]; omega⟩
  · exact Or.inl ⟨t, ht, by rw [e, inqA_val (hT t ht)]; omega, by rw [e, inqA_val (hT t ht)]; omega⟩
  · rw [hcpu] at e
    exact Or.inr ⟨by rw [e, nodeAt_val hN ho]; omega, by rw [e, nodeAt_val hN ho]; omega⟩

/-- **`dequeue`'s footprint.** -/
theorem dequeue_sfoot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) :
    sched.dequeue st s t ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hp := hc.prio t ht
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hR1 : ReadyQueues st T s (L.mem s (affA t)) Q := by rw [haf]; exact hc.ready
  refine WP.spec_mono (sched.dequeue.foot s t _ hc.tcbs ht hp hN hN' (hR1.1.rel _ hp) (hc.queued t ht).1) ?_
  rintro s' ⟨hw, -⟩
  rw [haf] at hw
  exact hw.mono fun b hb => qfoot_sfoot hc.tcbs (fun w hw' => (hc.ready.1.rel _ hp).mem w hw') ht hc.node hc.cur hb

/-- **`enqueue`'s footprint**, for a thread that is queued or not released. -/
theorem enqueue_sfoot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) :
    sched.enqueue st s t ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hp := hc.prio t ht
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hR1 : ReadyQueues st T s (L.mem s (affA t)) Q := by rw [haf]; exact hc.ready
  have hnq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → t ∉ Q (L.mem s (prioA t)) :=
    fun h0 hm => ((hc.queued t ht).2 hm) h0
  refine WP.spec_mono (sched.enqueue.foot s t _ hc.tcbs ht hp hN hN' (hR1.1.rel _ hp) hnq) ?_
  rintro s' ⟨hw, -⟩
  rw [haf] at hw
  refine hw.mono fun b hb => qfoot_sfoot hc.tcbs (fun w hw' => ?_) ht hc.node hc.cur hb
  rcases List.mem_cons.1 hw' with rfl | hw'
  · exact ht
  · exact (hc.ready.1.rel _ hp).mem w hw'

/-- **`release_remove`'s footprint.** -/
theorem release_remove_sfoot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) :
    sched.release_remove st s t ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hrel : QueueRel (L.mem s) T .Sched (L.relQ s (L.mem s (affA t))) R := by rw [haf]; exact hc.release
  refine WP.spec_mono (sched.release_remove.foot s t _ hc.tcbs ht hN hN' hrel (hc.released t ht).1) ?_
  rintro s' ⟨hw, -⟩
  rw [haf] at hw
  exact hw.mono fun b hb => qfoot_sfoot hc.tcbs (fun w hw' => hc.release.mem w hw') ht hc.node hc.cur hb

/-- **`reschedule_required`'s footprint.** -/
theorem reschedule_required_sfoot {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) :
    sched.reschedule_required st s ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN := hc.node
  have hact : ∀ s1 : S, WritesIn st s s1 (SFoot st T c s) →
      sched.set_action st s1 sched.ACTION_CHOOSE_NEW ⦃ s' => WritesIn st s s' (SFoot st T c s) ⦄ := by
    intro s1 h1
    refine WP.spec_mono (sched.set_action.spec' s1 _) ?_
    rintro s' rfl
    refine WritesIn.sfoot_trans h1 ((writesIn_wr ?_).mono fun b hb => ?_)
    · rw [nodeAt_ksb h1.1, h1.2.1, hc.cur]; exact nodeAt_aligned hN (by simp [layout.node.SCHED_ACTION])
        (by simp [layout.node.SCHED_ACTION])
    · rw [hb, nodeAt_ksb h1.1, h1.2.1, hc.cur]
      have ho : (layout.node.SCHED_ACTION).val < 4288 := by simp [layout.node.SCHED_ACTION]
      refine (SFoot.ksb h1.1).2 (Or.inr ⟨by rw [nodeAt_val hN ho]; omega, by rw [nodeAt_val hN ho]; omega⟩)
  unfold sched.reschedule_required
  step with sched.action.spec' as ⟨act, hact'⟩
  rw [hc.cur] at hact'
  have e0 : sched.ACTION_RESUME_CURRENT = 0#u64 := by unfold sched.ACTION_RESUME_CURRENT; rfl
  have e1 : sched.ACTION_CHOOSE_NEW = 1#u64 := by unfold sched.ACTION_CHOOSE_NEW; rfl
  by_cases h1 : act = sched.ACTION_RESUME_CURRENT
  · have : (act != sched.ACTION_RESUME_CURRENT) = false := by simpa using h1
    simp only [this, Bool.false_eq_true, ↓reduceIte, bind_ok]; exact hact s (WritesIn.refl _ _)
  have g1 : (act != sched.ACTION_RESUME_CURRENT) = true := by simpa using h1
  by_cases h2 : act = sched.ACTION_CHOOSE_NEW
  · have : (act != sched.ACTION_CHOOSE_NEW) = false := by simpa using h2
    simp only [g1, this, Bool.false_eq_true, ↓reduceIte, bind_ok]; exact hact s (WritesIn.refl _ _)
  have g2 : (act != sched.ACTION_CHOOSE_NEW) = true := by simpa using h2
  simp only [g1, g2, ↓reduceIte]
  have hT : act ∈ T := by
    rw [hact']
    rcases hS.actW with h | h | h
    · rw [hact', h] at h1; exact absurd e0.symm h1
    · rw [hact', h] at h2; exact absurd e1.symm h2
    · exact h
  step with sched.is_schedulable.spec' as ⟨b, _hb⟩
  by_cases hb : b = true
  · rw [if_pos hb]; exact WP.spec_bind (enqueue_sfoot hS hT) hact
  · rw [if_neg hb]; simp only [bind_ok]; exact hact s (WritesIn.refl _ _)

end

end

end Fl4Proofs.P3.Sched
