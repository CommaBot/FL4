/-
P3 (DESIGN.md §9), endpoints: **`ep_dequeue` of a queued thread refines
l4v `tcb_ep_dequeue`** (`ep_dequeue_rel`): the thread leaves the queue; the
endpoint becomes idle if the queue is now empty and keeps its state
otherwise. Single spec outcome; FL4 changes no TCB field
(`TF`), only the endpoint words and `Ep` links.

`dequeued_not_queued`: afterwards the thread is in no endpoint queue.
-/
import Fl4Proofs.P3.EpXfer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- The TCB fields of all TCBs. -/
def AllTF (T : Set U64) (b : U64) : Prop := ∃ y ∈ T, TF y b

theorem ep_dequeue_rel (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hSR : SR s σ) {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint}
    (hk : σ.kheap e.bv = some (.endpoint x)) {d : U64} (hd : d.bv ∈ x.epQueue) :
    endpoint.ep_dequeue st s e d ⦃ s' =>
      Fl4Spec.tcbEpDequeue (Z := Unit) d.bv e.bv σ = ({((), updK σ e.bv (.endpoint (epDeq x d.bv)))}, False) ∧
      EpStateRel T E R B (L.mem s') (updK σ e.bv (.endpoint (epDeq x d.bv))) ∧
      SR s' (updK σ e.bv (.endpoint (epDeq x d.bv))) ∧
      Agree (L.mem s) (L.mem s') (AllTF T) ⦄ := by
  have hx := hR.at_ep he hk
  obtain ⟨xs, hQ, hxs, hB⟩ := hx.queue
  have hdx : d ∈ xs := by
    rw [hxs, List.mem_map] at hd
    obtain ⟨y, hy, ey⟩ := hd
    rw [← eq_of_bv ey]; exact hy
  refine WP.spec_mono (ep_dequeue_full hP s he d xs hQ hdx) ?_
  rintro s' ⟨hQ', hst', hA, hW, -, -⟩
  have hfield : Agree (L.mem s) (L.mem s') (AllTF T) := by
    intro b hb ⟨y, hy, hf⟩
    refine hA b hb ⟨fun hw => ?_, fun ⟨w, hw, hl⟩ => ?_⟩
    · have := hf.range; have := hP.et e he y hy; unfold EW at hw; omega
    · have hwT := hQ.mem w hw
      by_cases ew : w = y
      · subst ew; exact hl.not_tf hf
      · exact notTF_tcb hP hy hwT ew (Or.inr hl) hf
  refine ⟨tcbEpDequeue_eq hk hd, ?_, hH.stable _ _ _ _ hSR hW (EpStep.ep hk), hfield⟩
  refine hR.upd_ep hP he _ (hA.mono fun b ⟨h1, h2, h3⟩ => ⟨h2, fun ⟨w, hw, hl⟩ => h3 ⟨w, hQ.mem w hw, (hB w hw).1, hl⟩⟩) ?_
  have hrm : Fl4Spec.removeAll d.bv x.epQueue = (xs.erase d).map UScalar.bv := by rw [hxs]; exact removeAll_map hQ.nodup d
  have hmem : ∀ y ∈ xs.erase d, L.mem s' (tStA y) = L.mem s (tStA y) ∧ L.mem s' (tBlockA y) = L.mem s (tBlockA y) := by
    intro y hy
    have hy' := (List.erase_subset hy)
    have hya := hP.tcb y (hQ.mem y hy')
    have nst : ¬ EW e (tStA y) ∧ ¬ ∃ w ∈ xs, TL w (tStA y) := by
      refine ⟨fun hw => ?_, fun ⟨w, hw, hl⟩ => ?_⟩
      · have := hP.et e he y (hQ.mem y hy'); unfold EW at hw; rw [val_st hya] at hw; omega
      · by_cases ew : w = y
        · subst ew; exact hl.not_tf (a_st hya).2
        · have := tcb_disj hP (hQ.mem w hw) (hQ.mem y hy') (Ne.symm ew); unfold TL at hl; rw [val_st hya] at hl; omega
    have nbl : ¬ EW e (tBlockA y) ∧ ¬ ∃ w ∈ xs, TL w (tBlockA y) := by
      refine ⟨fun hw => ?_, fun ⟨w, hw, hl⟩ => ?_⟩
      · have := hP.et e he y (hQ.mem y hy'); unfold EW at hw; rw [val_blk hya] at hw; omega
      · by_cases ew : w = y
        · subst ew; exact hl.not_tf (a_blk hya).2
        · have := tcb_disj hP (hQ.mem w hw) (hQ.mem y hy') (Ne.symm ew); unfold TL at hl; rw [val_blk hya] at hl; omega
    exact ⟨hA _ (a_st hya).1 nst, hA _ (a_blk hya).1 nbl⟩
  unfold epDeq
  rw [hrm]
  by_cases hemp : xs.erase d = []
  · rw [hemp]
    refine ⟨by rw [hst', if_pos hemp], ?_⟩
    rw [← hemp]; exact hQ'
  · have hne : (xs.erase d).map UScalar.bv ≠ [] := by simpa using hemp
    obtain ⟨h, tl, hht⟩ := List.exists_cons_of_ne_nil hne
    rw [hht]
    simp only
    rw [← hht]
    cases x with
    | idleEP => simp [Fl4Spec.Endpoint.epQueue] at hd
    | sendEP q =>
      obtain ⟨hx1, xs', -, hq', hQ'', h3⟩ := hx
      have e' : xs' = xs := hQ''.unique hP.tcb hQ
      subst e'
      refine ⟨by rw [hst', if_neg hemp]; exact hx1, xs'.erase d, hemp, rfl, hQ', fun y hy => ?_⟩
      obtain ⟨c1, c2⟩ := h3 y (List.erase_subset hy)
      exact ⟨by rw [(hmem y hy).1]; exact c1, by rw [(hmem y hy).2]; exact c2⟩
    | recvEP q =>
      obtain ⟨hx1, xs', -, hq', hQ'', h3⟩ := hx
      have e' : xs' = xs := hQ''.unique hP.tcb hQ
      subst e'
      refine ⟨by rw [hst', if_neg hemp]; exact hx1, xs'.erase d, hemp, rfl, hQ', fun y hy => ?_⟩
      obtain ⟨c1, c2⟩ := h3 y (List.erase_subset hy)
      exact ⟨by rw [(hmem y hy).1]; exact c1, by rw [(hmem y hy).2]; exact c2⟩

/-- After its dequeue, a thread blocked on `e` is in no endpoint queue. -/
theorem dequeued_not_queued {m : U64 → U64} {σ : Fl4Spec.State Unit} (hR : EpStateRel T E R B m σ)
    {e d : U64} (he : e ∈ E) (hb : m (tBlockA d) = e) {x : Fl4Spec.Endpoint}
    (hk : σ.kheap e.bv = some (.endpoint x)) (hnd : d.bv ∉ x.epQueue) :
    ∀ e' ∈ E, ∀ z, σ.kheap e'.bv = some (.endpoint z) → d.bv ∉ z.epQueue := by
  intro e' he' z hz hm
  obtain ⟨-, hb'⟩ := (hR.at_ep he' hz).blocked hm
  have : e' = e := hb'.symm.trans hb
  subst this
  rw [hk] at hz; cases hz
  exact hnd hm

theorem epDeq_not_mem {x : Fl4Spec.Endpoint} (d : Fl4Spec.ObjRef) : d ∉ (epDeq x d).epQueue := by
  unfold epDeq
  split
  · simp [Fl4Spec.Endpoint.epQueue]
  · cases x <;> simp [Fl4Spec.updateEpQueue, Fl4Spec.Endpoint.epQueue, Fl4Spec.removeAll]

end

end

end Fl4Proofs.P3.Endp
