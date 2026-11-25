/-
P1 (p1dom): **`DomInv` through the scheduler-queue operations**: `enqueue`,
`dequeue`, `release_remove`, `set_action`, `reschedule_required` and
`possible_switch_to` write no `DOMAIN` word and not `CUR_DOMAIN`
(`DomFree`: their queue footprints `QFoot` and the node words lie outside both).
These are the pieces of `awaken`'s release loop and of the wakes under
`timer::fire` (the `hR` premise of P2's `AllCores.schedE`: under `DomInv`,
`possible_switch_to`'s domain-mismatch branch (sched.rs:369) is never taken
for a TCB, `DomInv.cur`).
-/
import Fl4Proofs.P1.DomInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Cs Ω : Set U64} {H : Heap}

/-- A word that is neither the `CUR_DOMAIN` word nor a `DOMAIN` word of `T`. -/
def DomFree (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s : S) (b : U64) : Prop :=
  b ≠ cdomA st s ∧ ∀ y ∈ T, b ≠ domA y

theorem DomInv.free {s s' : S} {A : U64 → Prop} (h : DomInv st T s) (w : WritesIn st s s' A) (hT : TcbPlaced T)
    (hka : Aligned (cdomA st s)) (hA : ∀ b, A b → DomFree st T s b) : DomInv st T s' :=
  h.writesIn w hT hka (fun hc => (hA _ hc).1 rfl) (fun y hy hd => (hA _ hd).2 y hy rfl)

theorem cdomA_valN {s : S} {c : U64} (hN : NodePlaced st T s c) : (cdomA st s).val = (L.ksb s).val + 8 := by
  have hf := hN.fits
  simp only [LawfulStore.nodeBase] at hf
  unfold cdomA
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, layout.ks.CUR_DOMAIN]; omega

theorem cdomA_alignedN {s : S} {c : U64} (hN : NodePlaced st T s c) : Aligned (cdomA st s) := by
  have := hN.align
  simp only [LawfulStore.nodeBase] at this
  unfold Aligned; rw [cdomA_valN hN]; omega

theorem node_domFree {s : S} {c o : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s c) (ho : o.val < 4288) :
    DomFree st T s (L.nodeAt s c o) := by
  refine ⟨fun e => ?_, fun y hy e => node_ne_field (K := 3432#u64) hN ho hy (hT y hy) (by simp) e⟩
  have hv := congrArg UScalar.val e
  rw [nodeAt_val hN ho, cdomA_valN hN] at hv
  simp only [LawfulStore.nodeBase] at hv
  omega

theorem field_domFree {s : S} {c y K : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s c) (hy : y ∈ T)
    (hko : y.val + 2 ^ 12 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ y.val) (hK : K.val < 4096)
    (hne : K.val ≠ 3432) : DomFree st T s (core.num.U64.wrapping_add y K) := by
  refine ⟨fun e => ?_, fun z hz e =>
    field_ne (K2 := 3432#u64) (hT y hy) (hT z hz) hK (by simp) (fun _ => by simpa using hne) e⟩
  have hv := congrArg UScalar.val e
  rw [field_val (hT y hy) hK, cdomA_valN hN] at hv
  omega

/-- A scheduler queue footprint writes no `DOMAIN` word and not `CUR_DOMAIN`. -/
theorem QFoot.domFree {s : S} {W : List U64} {c t : U64} {P : Nat → Prop} {b : U64} (hT : TcbPlaced T)
    (hN : NodePlaced st T s c) (hN' : NodePlaced st T s (L.cpu s)) (hW : ∀ w ∈ W, w ∈ T) (ht : t ∈ T)
    (hko : ∀ y ∈ T, y.val + 2 ^ 12 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ y.val)
    (hb : L.QFoot s W c P t b) : DomFree st T s b := by
  rcases hb with ⟨w, hw, e | e⟩ | ⟨o, -, ho, -, e⟩ | e | ⟨o, -, ho, -, e⟩ <;> subst e
  · exact field_domFree hT hN (hW w hw) (hko w (hW w hw)) (by simp [nextOff]) (by simp [nextOff])
  · exact field_domFree hT hN (hW w hw) (hko w (hW w hw)) (by simp [prevOff]) (by simp [prevOff])
  · exact node_domFree hT hN ho
  · exact field_domFree hT hN ht (hko t ht) (by simp) (by simp)
  · exact node_domFree hT hN' ho

section queues
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

theorem sched.enqueue.domInv (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (hD : DomInv st T s) : sched.enqueue st s t ⦃ s' => DomInv st T s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  refine WP.spec_mono (sched.enqueue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (fun h0 => h.notQ ht h0 hc hp)) fun s' hh => hD.free hh.1 h.tcbs (cdomA_alignedN (h.nodes _ h.cur))
      fun b hb => QFoot.domFree h.tcbs (h.nodes _ hc) (h.nodes _ h.cur) ?_ ht h.ksOut hb
  intro w hw
  rcases List.mem_cons.1 hw with rfl | hw
  · exact ht
  · exact (hR1.1.rel _ hp).mem w hw

theorem sched.dequeue.domInv (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (hD : DomInv st T s) : sched.dequeue st s t ⦃ s' => DomInv st T s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  exact WP.spec_mono (sched.dequeue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (h.queued t ht).1) fun s' hh => hD.free hh.1 h.tcbs (cdomA_alignedN (h.nodes _ h.cur))
      fun b hb => QFoot.domFree h.tcbs (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp).mem ht h.ksOut hb

theorem sched.release_remove.domInv (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (ht : t ∈ T) (hD : DomInv st T s) : sched.release_remove st s t ⦃ s' => DomInv st T s' ⦄ := by
  have hc := h.aff t ht
  exact WP.spec_mono (sched.release_remove.foot s t _ h.tcbs ht (h.nodes _ hc) (h.nodes _ h.cur) (h.release _ hc)
    (h.released t ht).1) fun s' hh => hD.free hh.1 h.tcbs (cdomA_alignedN (h.nodes _ h.cur))
      fun b hb => QFoot.domFree h.tcbs (h.nodes _ hc) (h.nodes _ h.cur) (h.release _ hc).mem ht h.ksOut hb

theorem sched.set_action.domInv (s : S) (v : U64) (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s))
    (hD : DomInv st T s) : sched.set_action st s v ⦃ s' => DomInv st T s' ⦄ :=
  WP.spec_mono (sched.set_action.spec s v) fun s' e => by
    subst e
    refine hD.free (writesIn_wr (nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val]))) hT
      (cdomA_alignedN hN) fun b hb => ?_
    subst hb
    exact node_domFree hT hN (by rw [act_val]; omega)

theorem sched.reschedule_required.domInv (s : S) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hD : DomInv st T s) : sched.reschedule_required st s ⦃ s' => DomInv st T s' ⦄ := by
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, act_post⟩
  refine WP.spec_bind (Pₘ := fun s1 => DomInv st T s1 ∧
    FootB st T Cs (∅ : Set U64) (∅ : Set U64) (fun _ => 0) (∅ : Set U64) s s1) ?_ fun s1 hs1 => ?_
  · split
    · split
      · rename_i h1 h2
        have hT : act ∈ T := by
          rcases h.action with e | e | e
          · rw [← act_post] at e; exfalso; rw [e, resume_val] at h1; simp at h1
          · rw [← act_post] at e; exfalso; rw [e, choose_val] at h2; simp at h2
          · rw [← act_post] at e; exact e
        step with sched.is_schedulable.spec as ⟨b, hb⟩
        split
        · exact WP.spec_and (sched.enqueue.domInv s act h hT hD) (sched.enqueue.kwB s act h hT)
        · exact (WP.spec_ok _).2 ⟨hD, FootB.refl _⟩
      · exact (WP.spec_ok _).2 ⟨hD, FootB.refl _⟩
    · exact (WP.spec_ok _).2 ⟨hD, FootB.refl _⟩
  · obtain ⟨hD1, f1⟩ := hs1
    exact sched.set_action.domInv s1 _ h.tcbs (by rw [f1.2.1]; exact (h.nodes _ h.cur).ksb f1.1) hD1

/-- **`possible_switch_to` keeps `DomInv`.** -/
theorem sched.possible_switch_to.domInv (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (ht : t ∈ T) (hD : DomInv st T s) : sched.possible_switch_to st s t ⦃ s' => DomInv st T s' ⦄ := by
  have hST : P0.StoreTotal st := L.total
  unfold sched.possible_switch_to sched.cur_domain
  step as ⟨i, ei⟩
  split
  · exact (WP.spec_ok _).2 hD
  step as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 hD
  step as ⟨i1, ei1⟩
  step as ⟨i2, ei2⟩
  split
  · exact sched.enqueue.domInv s t h ht hD
  step as ⟨i3, ei3⟩
  step as ⟨i4, ei4⟩
  split
  · exact sched.enqueue.domInv s t h ht hD
  step as ⟨i5, ei5⟩
  split
  · refine WP.spec_bind (WP.spec_and (sched.reschedule_required.inv s Q R h)
      (sched.reschedule_required.domInv s h hD)) ?_
    rintro s1 ⟨⟨⟨Q1, h1⟩, -, -⟩, d1⟩
    exact sched.enqueue.domInv s1 t h1 ht d1
  · exact sched.set_action.domInv s _ h.tcbs (h.nodes _ h.cur) hD

end queues

end

end Fl4Proofs.P1
