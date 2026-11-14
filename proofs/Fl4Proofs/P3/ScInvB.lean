/-
P3 (DESIGN.md §9), scheduling contexts: `budget_check`'s refill facts from
the invariant (`budget_check_refines_inv`): an active current SC's refills
are positive, sum below `2 ^ 64` and to at least `MIN_BUDGET` (`Inv.refills`).
What remains are `commit_time`'s own branch conditions (the current SC is
active and not round-robin), the platform constants, and the current SC
being one of `C`.
-/
import Fl4Proofs.P3.ScInvSR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- **`refill_budget_check` keeps the invariant**, except `rd` for the SC's
owner (whose budget it charges; seL4 then postpones it in `charge_budget`
if needed), if the owner is not in the release queue. -/
theorem Inv.budgetPost {σ σ' : State Unit} (h : Inv σ) {p u0 : ObjRef} {y : SchedContext} {m : Nat}
    (hk : σ.kheap p = some (.schedContext y m)) (hpost : BudgetPost σ σ' p) (hown : y.scTcb = some u0)
    (hnr : u0 ∉ σ.releaseQueue) : InvBut σ' u0 := by
  obtain ⟨y', rfl, hy', hne', hpos', hsum', hmin'⟩ := hpost y m hk
  have hkp : ∀ q, q ≠ p → (updSc σ p y' m).kheap q = σ.kheap q := fun q hq => by simp [updK, hq]
  have hky : (updSc σ p y' m).kheap p = some (.schedContext y' m) := by simp [updK]
  have hown' : ∀ u x, σ.kheap u = some (.tcb x) → x.tcbSchedContext = some p → u = u0 := fun u x hx hp => by
    obtain ⟨w, n, h1, h2⟩ := h.back u x p hx hp
    rw [hk] at h1; cases h1; rw [hown] at h2; cases h2; rfl
  have hnr' : ∀ u ∈ σ.releaseQueue, ∀ x, σ.kheap u = some (.tcb x) → x.tcbSchedContext ≠ some p :=
    fun u hu x hx hp => hnr (hown' u x hx hp ▸ hu)
  have htcb : ∀ u x, (updSc σ p y' m).kheap u = some (.tcb x) → σ.kheap u = some (.tcb x) := fun u x hx => by
    by_cases e : u = p
    · subst e; rw [hky] at hx; cases hx
    · rw [hkp u e] at hx; exact hx
  have hact : scActive y' = scActive y := by rw [hy']
  refine ⟨fun d q u hu => ?_, fun u hu => ?_, ?_, fun u x hu0 hx hc => ?_, fun q w n hw ha => ?_,
    fun u x q hx hq => ?_, fun q x q' hx hq => ?_, fun q w n hw => ?_⟩
  · obtain ⟨x, scp, h1, h2, h3⟩ := h.rq d q u hu
    have : u ≠ p := by rintro rfl; rw [hk] at h1; cases h1
    exact ⟨x, scp, by rw [hkp u this]; exact h1, h2, h3⟩
  · obtain ⟨x, scp, w, n, h1, h2, h3, h4, h5⟩ := h.rel u hu
    have hup : u ≠ p := by rintro rfl; rw [hk] at h1; cases h1
    have hsp : scp ≠ p := fun e => hnr' u hu x h1 (e ▸ h2)
    exact ⟨x, scp, w, n, by rw [hkp u hup]; exact h1, h2, h3, by rw [hkp scp hsp]; exact h4, h5⟩
  · show σ.releaseQueue.Pairwise _
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    obtain ⟨xa, pa, ya, na, h1, h2, -, h4, h5⟩ := h.rel a ha
    obtain ⟨xb, pb, yb, nb, g1, g2, -, g4, g5⟩ := h.rel b hb
    have hap : a ≠ p := by rintro rfl; rw [hk] at h1; cases h1
    have hbp : b ≠ p := by rintro rfl; rw [hk] at g1; cases g1
    have hpa : pa ≠ p := fun e => hnr' a ha xa h1 (e ▸ h2)
    have hpb : pb ≠ p := fun e => hnr' b hb xb g1 (e ▸ g2)
    rw [specRt_eq (by rw [hkp a hap]; exact h1) h2 (by rw [hkp pa hpa]; exact h4) (h.ne _ _ _ h4),
      specRt_eq (by rw [hkp b hbp]; exact g1) g2 (by rw [hkp pb hpb]; exact g4) (h.ne _ _ _ g4)]
    rw [specRt_eq h1 h2 h4 (h.ne _ _ _ h4), specRt_eq g1 g2 g4 (h.ne _ _ _ g4)] at hab
    exact hab
  · have hx0 := htcb u x hx
    intro x' scp w n h1 h2 h3 h4 h5
    rw [hx] at h1; cases h1
    have hsp : scp ≠ p := fun e => hu0 (hown' u x hx0 (e ▸ h2))
    rw [hkp scp hsp] at h3
    exact h.rd u x hx0 hc x scp w n hx0 h2 h3 h4 h5
  · by_cases e : q = p
    · subst e; rw [hky] at hw; cases hw; exact ⟨hne', hpos', hsum', hmin'⟩
    · rw [hkp q e] at hw; exact h.refills q w n hw ha
  · obtain ⟨w, n, h1, h2⟩ := h.back u x q (htcb u x hx) hq
    by_cases e : q = p
    · subst e; rw [hk] at h1; cases h1
      exact ⟨y', m, hky, by rw [hy']; exact h2⟩
    · exact ⟨w, n, by rw [hkp q e]; exact h1, h2⟩
  · have hx0 : σ.kheap q = some (.notification x) := by
      by_cases e : q = p
      · subst e; rw [hky] at hx; cases hx
      · rw [hkp q e] at hx; exact hx
    obtain ⟨w, n, h1⟩ := h.ntfnSc q x q' hx0 hq
    by_cases e : q' = p
    · subst e; exact ⟨y', m, hky⟩
    · exact ⟨w, n, by rw [hkp q' e]; exact h1⟩
  · by_cases e : q = p
    · subst e; rw [hky] at hw; cases hw; exact hne'
    · rw [hkp q e] at hw; exact h.ne q w n hw

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`budget_check` refines `refill_budget_check`**, its refill facts from
the invariant. -/
theorem budget_check_refines_inv {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hI : Inv σ) (hcC : nodeW st s c layout.node.CUR_SC ∈ C)
    (hact : ∀ x n, σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) → Fl4Spec.scActive x = true)
    (hmrt : sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hrr : L.rperiod s (nodeW st s c layout.node.CUR_SC) ≠ 0#u64) (usage : U64)
    {u0 : Fl4Spec.ObjRef} (hown : ∀ y m, σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext y m) →
      y.scTcb = some u0) (hnr : u0 ∉ σ.releaseQueue) :
    sporadic.budget_check st ar s a usage ⦃ s' => ∃ σ', Fl4Spec.refillBudgetCheck (Z := Unit) usage.bv σ =
      ({((), σ')}, False) ∧ FootEq N T (L.mem s) (L.mem s') ∧ KView σ σ' ∧ SchedRel st N T C c s' σ' ∧
      InvBut σ' u0 ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hcC
  obtain ⟨hne, hpos, hsum, hmin⟩ := hI.refills _ x n hk (hact x n hk)
  have hl := lsum_eq_map (L.refills s (nodeW st s c layout.node.CUR_SC))
  rw [← hx.refills] at hl
  refine WP.spec_mono (budget_check_refines s a σ hS hcC hmrt hmb hrr ?_ (by rw [hl]; exact hsum) ?_ usage) ?_
  rotate_left 2
  · rintro s' ⟨σ', h1, h2, h3, h4, h5⟩
    exact ⟨σ', h1, h2, h3, h4, hI.budgetPost hk h5 (hown x n hk) hnr⟩
  · intro r hr
    have := hpos (toRefill r) (by rw [hx.refills]; exact List.mem_map_of_mem hr)
    simpa [toRefill] using this
  · rw [hl]
    have hm : (Fl4Spec.refillHd x).rAmount.toNat ≤ (x.scRefills.map fun r => r.rAmount.toNat).sum := by
      obtain ⟨q, l, e⟩ := List.exists_cons_of_ne_nil hne
      have : Fl4Spec.refillHd x = q := by unfold Fl4Spec.refillHd; rw [e]; rfl
      rw [this, e]; simp
    rw [BitVec.le_def] at hmin
    omega

end

end

end Fl4Proofs.P3.Sched
