/-
P3 (DESIGN.md §9), scheduling contexts: **`maybe_donate_sc` keeps `Inv`**
(`Inv.donate`), for a runnable thread in no queue (l4v's preconditions of
`maybe_donate_sc_valid_sched`: `not_queued`, `not_in_release_q`,
`st_tcb_at runnable`).

The spec side: `schedContextDonate_eq`, `postpone_eq`, and the ordered
insertion keeps the release queue sorted (`specInsT_sorted`).
-/
import Fl4Proofs.P3.ScInvU
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

theorem schedContextDonate_eq {σ : State Unit} {p t : ObjRef} {ys : SchedContext} {ns : Nat} {xt : Tcb}
    (hks : σ.kheap p = some (.schedContext ys ns)) (hnone : ys.scTcb = none) (hkt : σ.kheap t = some (.tcb xt))
    (hpt : p ≠ t) : schedContextDonate (Z := Unit) p t σ = ({((), donSt σ p t ys ns xt)}, False) := by
  have hg : getScObjRef (Z := Unit) SchedContext.scTcb p σ = ({(ys.scTcb, σ)}, False) := by
    unfold getScObjRef; rw [nd_bind_one (getSchedContext_eq hks)]; rfl
  have hkt1 : (updSc σ p { ys with scTcb := some t } ns).kheap t = some (.tcb xt) := by
    simp [updK, Ne.symm hpt, hkt]
  unfold schedContextDonate
  rw [nd_bind_one hg, hnone]
  simp only [NonDet.when, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [nd_bind_one (show NonDet.pure (σ := State Unit) () σ = ({((), σ)}, False) from rfl)]
  show (updateSchedContext p _ >>= _) σ = _
  rw [nd_bind_one (updateSchedContext_eq hks _)]
  rw [show scTcbUpdate (fun _ => some t) ys = { ys with scTcb := some t } from rfl]
  show threadSet _ t _ = _
  rw [threadSet_eq _ hkt1]
  rfl

theorem mem_specInsT {l : List ObjRef} {g : ObjRef → Time} {t u : ObjRef} :
    u ∈ specInsT l g t ↔ u = t ∨ u ∈ l := by
  unfold specInsT
  constructor
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact Or.inr ((List.takeWhile_sublist _).subset h)
    · rcases List.mem_cons.1 h with h | h
      · exact Or.inl h
      · exact Or.inr ((List.dropWhile_sublist _).subset h)
  · rintro (rfl | h)
    · simp
    · rw [← List.takeWhile_append_dropWhile (p := fun y => @decide (g y ≤ g t) (Classical.propDecidable _)) (l := l)] at h
      rcases List.mem_append.1 h with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

/-- **Ordered insertion keeps a list sorted.** -/
theorem specInsT_sorted {l : List ObjRef} (g : ObjRef → Time) (t : ObjRef)
    (hs : l.Pairwise (fun a b => g a ≤ g b)) : (specInsT l g t).Pairwise (fun a b => g a ≤ g b) := by
  unfold specInsT
  set P : ObjRef → Bool := fun y => @decide (g y ≤ g t) (Classical.propDecidable _)
  have hsplit := List.takeWhile_append_dropWhile (p := P) (l := l)
  have hs' := hsplit ▸ hs
  rw [List.pairwise_append] at hs'
  obtain ⟨h1, h2, h3⟩ := hs'
  have ht1 : ∀ a ∈ l.takeWhile P, g a ≤ g t := fun a ha => by
    have := List.mem_takeWhile_imp ha; simpa [P] using this
  have ht2 : ∀ b ∈ l.dropWhile P, g t ≤ g b := by
    intro b hb
    cases hd : l.dropWhile P with
    | nil => rw [hd] at hb; cases hb
    | cons c rest =>
      have hc : ¬ g c ≤ g t := by
        have := List.head_dropWhile_not P (l := l) (by rw [hd]; simp)
        simp only [hd, List.head_cons, P] at this; simpa using this
      have hct : g t ≤ g c := by
        rw [BitVec.le_def]; rw [BitVec.le_def] at hc; omega
      rw [hd] at hb h2
      rcases List.mem_cons.1 hb with rfl | hb
      · exact hct
      · have := List.rel_of_pairwise_cons h2 hb
        rw [BitVec.le_def] at this hct ⊢; omega
  rw [List.pairwise_append]
  refine ⟨h1, List.pairwise_cons.2 ⟨ht2, h2⟩, fun a ha b hb => ?_⟩
  rcases List.mem_cons.1 hb with rfl | hb
  · exact ht1 a ha
  · exact h3 a ha b hb


/-- `postpone` of a bound SC. -/
theorem postpone_eq {σ : State Unit} {p t : ObjRef} {y : SchedContext} {n : Nat} {x : Tcb}
    (hk : σ.kheap p = some (.schedContext y n)) (htc : y.scTcb = some t) (hkt : σ.kheap t = some (.tcb x))
    (g : ObjRef → Time) (hg : ∀ u, u = t ∨ u ∈ σ.releaseQueue → ∃ xu scp yu nu, σ.kheap u = some (.tcb xu) ∧
      xu.tcbSchedContext = some scp ∧ σ.kheap scp = some (.schedContext yu nu) ∧ yu.scRefills ≠ [] ∧
      g u = (refillHd yu).rTime) :
    ∃ b, postpone (Z := Unit) p σ = ({((), { setRel (setQ σ x.tcbDomain x.tcbPriority
      (tcbSchedDequeue t (σ.readyQueues x.tcbDomain x.tcbPriority))) (specInsT σ.releaseQueue g t) b with
        reprogramTimer := true })}, False) := by
  have hg' : getScObjRef (Z := Unit) SchedContext.scTcb p σ = ({(y.scTcb, σ)}, False) := by
    unfold getScObjRef; rw [nd_bind_one (getSchedContext_eq hk)]; rfl
  set σq := setQ σ x.tcbDomain x.tcbPriority (tcbSchedDequeue t (σ.readyQueues x.tcbDomain x.tcbPriority))
  have hg2 : ∀ u, u = t ∨ u ∈ σq.releaseQueue → readTcbReadyTime (Z := Unit) u σq = some (g u) := by
    intro u hu
    obtain ⟨xu, scp, yu, nu, h1, h2, h3, h4, h5⟩ := hg u hu
    rw [h5]; exact readTcbReadyTime_eq h1 h2 h3 h4
  obtain ⟨b, hb⟩ := tcbReleaseEnqueue_eq (σ := σq) t g (hg2 t (Or.inl rfl)) (fun u hu => hg2 u (Or.inr hu))
  refine ⟨b, ?_⟩
  unfold postpone
  rw [nd_bind_one hg', htc,
    nd_bind_one (show NonDet.assertOpt (σ := State Unit) (some t) σ = ({(t, σ)}, False) from rfl),
    nd_bind_one (tcbSchedAction_gen hkt _), nd_bind_one hb]
  rfl

end Spec

end

end Fl4Proofs.P3.Sched
