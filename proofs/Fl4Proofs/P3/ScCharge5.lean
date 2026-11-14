/-
P3 (DESIGN.md §9), scheduling contexts: `InvBut` across the writes of
`charge_budget` that `Inv` does not read (an SC's `consumed`, the node's
consumed time): `InvBut.scUpd`, `InvBut.congr`.
-/
import Fl4Proofs.P3.ScCharge4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

theorem Inv.toBut {σ : State Unit} (h : Inv σ) (t : ObjRef) : InvBut σ t :=
  ⟨h.rq, h.rel, h.sorted, fun u x _ => h.rd u x, h.refills, h.back, h.ntfnSc, h.ne⟩

/-- `InvBut` only reads the heap, the queues and the current time. -/
theorem InvBut.congr {σ σ' : State Unit} {t : ObjRef} (h : InvBut σ t) (hk : σ'.kheap = σ.kheap)
    (hq : σ'.readyQueues = σ.readyQueues) (hr : σ'.releaseQueue = σ.releaseQueue) (ht : σ'.curTime = σ.curTime) :
    InvBut σ' t := by
  refine ⟨fun d p u hu => ?_, fun u hu => ?_, ?_, fun u x hut hx hc => ?_, fun p y n hy => ?_,
    fun u x p hx hp => ?_, fun q x p hx hp => ?_, fun p y n hy => ?_⟩
  · rw [hq] at hu; rw [hk]; exact h.rq d p u hu
  · rw [hr] at hu; rw [hk]; exact h.rel u hu
  · rw [hr]
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    obtain ⟨xa, pa, ya, na, h1, h2, -, h4, -⟩ := h.rel a ha
    obtain ⟨xb, pb, yb, nb, g1, g2, -, g4, -⟩ := h.rel b hb
    rw [specRt_eq (by rw [hk]; exact h1) h2 (by rw [hk]; exact h4) (h.ne _ _ _ h4),
      specRt_eq (by rw [hk]; exact g1) g2 (by rw [hk]; exact g4) (h.ne _ _ _ g4)]
    rw [specRt_eq h1 h2 h4 (h.ne _ _ _ h4), specRt_eq g1 g2 g4 (h.ne _ _ _ g4)] at hab
    exact hab
  · rw [hk] at hx
    intro x' scp y n h1 h2 h3 h4 h5
    rw [hk] at h1 h3; rw [hr] at h5
    rw [released_congr ht]
    exact h.rd u x hut hx hc x' scp y n h1 h2 h3 h4 h5
  · rw [hk] at hy; exact h.refills p y n hy
  · rw [hk] at hx ⊢; exact h.back u x p hx hp
  · rw [hk] at hx ⊢; exact h.ntfnSc q x p hx hp
  · rw [hk] at hy; exact h.ne p y n hy

/-- An SC replaced by one with the same refills, refill max, period and
TCB. -/
theorem InvBut.scUpd {σ : State Unit} {t p : ObjRef} (h : InvBut σ t) {y y' : SchedContext} {m : Nat}
    (hk : σ.kheap p = some (.schedContext y m)) (e1 : y'.scRefills = y.scRefills)
    (e2 : y'.scRefillMax = y.scRefillMax) (e3 : y'.scPeriod = y.scPeriod) (e4 : y'.scTcb = y.scTcb) :
    InvBut (updSc σ p y' m) t := by
  have hkp : ∀ q, q ≠ p → (updSc σ p y' m).kheap q = σ.kheap q := fun q hq => by simp [updK, hq]
  have hky : (updSc σ p y' m).kheap p = some (.schedContext y' m) := by simp [updK]
  have htcb : ∀ u x, (updSc σ p y' m).kheap u = some (.tcb x) ↔ σ.kheap u = some (.tcb x) := fun u x => by
    by_cases e : u = p
    · subst e; rw [hky, hk]; simp
    · rw [hkp u e]
  have hsc : ∀ q w n, (updSc σ p y' m).kheap q = some (.schedContext w n) →
      ∃ w0, σ.kheap q = some (.schedContext w0 n) ∧ w.scRefills = w0.scRefills ∧ w.scRefillMax = w0.scRefillMax ∧
        w.scPeriod = w0.scPeriod ∧ w.scTcb = w0.scTcb := by
    intro q w n hq
    by_cases e : q = p
    · subst e; rw [hky] at hq; cases hq; exact ⟨y, hk, e1, e2, e3, e4⟩
    · rw [hkp q e] at hq; exact ⟨w, hq, rfl, rfl, rfl, rfl⟩
  have hsc' : ∀ q w n, σ.kheap q = some (.schedContext w n) →
      ∃ w', (updSc σ p y' m).kheap q = some (.schedContext w' n) ∧ w'.scRefills = w.scRefills := by
    intro q w n hq
    by_cases e : q = p
    · subst e; rw [hk] at hq; cases hq; exact ⟨y', hky, e1⟩
    · exact ⟨w, by rw [hkp q e]; exact hq, rfl⟩
  have hrt : ∀ u ∈ σ.releaseQueue, specRt (updSc σ p y' m) u = specRt σ u := by
    intro u hu
    obtain ⟨xu, pu, yu, nu, h1, h2, -, h4, -⟩ := h.rel u hu
    obtain ⟨w', hw', hr'⟩ := hsc' pu yu nu h4
    rw [specRt_eq ((htcb u xu).2 h1) h2 hw' (by rw [hr']; exact h.ne _ _ _ h4), specRt_eq h1 h2 h4 (h.ne _ _ _ h4)]
    unfold refillHd; rw [hr']
  refine ⟨fun d q u hu => ?_, fun u hu => ?_, ?_, fun u x hut hx hc => ?_, fun q w n hw ha => ?_,
    fun u x q hx hq => ?_, fun q x q' hx hq => ?_, fun q w n hw => ?_⟩
  · obtain ⟨x, scp, h1, h2, h3⟩ := h.rq d q u hu
    exact ⟨x, scp, (htcb u x).2 h1, h2, h3⟩
  · obtain ⟨x, scp, w, n, h1, h2, h3, h4, h5⟩ := h.rel u hu
    obtain ⟨w', hw', -⟩ := hsc' scp w n h4
    obtain ⟨w0, hw0, -, hm, -, -⟩ := hsc scp w' n hw'
    rw [h4] at hw0; cases hw0
    exact ⟨x, scp, w', n, (htcb u x).2 h1, h2, h3, hw', by simpa [scActive, hm] using h5⟩
  · show σ.releaseQueue.Pairwise _
    exact List.Pairwise.imp_of_mem (fun {a b} ha hb hab => by rw [hrt a ha, hrt b hb]; exact hab) h.sorted
  · have hx0 := (htcb u x).1 hx
    intro x' scp w n h1 h2 h3 h4 h5
    rw [hx] at h1; cases h1
    obtain ⟨w0, hw0, hr, hm, -, -⟩ := hsc scp w n h3
    have := h.rd u x hut hx0 hc x scp w0 n hx0 h2 hw0 (by simpa [scActive, hm] using h4) h5
    unfold released refillHd at this ⊢; rw [hr]; exact this
  · obtain ⟨w0, hw0, hr, hm, hp, -⟩ := hsc q w n hw
    intro hper
    have := h.refills q w0 n hw0 (by simpa [scActive, hm] using ha) (hp ▸ hper)
    unfold RefOK refillHd at this ⊢; rw [hr]; exact this
  · obtain ⟨w, n, h1, h2⟩ := h.back u x q ((htcb u x).1 hx) hq
    obtain ⟨w', hw', -⟩ := hsc' q w n h1
    obtain ⟨w0, hw0, -, -, -, ht⟩ := hsc q w' n hw'
    rw [h1] at hw0; cases hw0
    exact ⟨w', n, hw', ht.trans h2⟩
  · have hx0 : σ.kheap q = some (.notification x) := by
      by_cases e : q = p
      · subst e; rw [hky] at hx; cases hx
      · rw [hkp q e] at hx; exact hx
    obtain ⟨w, n, h1⟩ := h.ntfnSc q x q' hx0 hq
    obtain ⟨w', hw', -⟩ := hsc' q' w n h1
    exact ⟨w', n, hw'⟩
  · obtain ⟨w0, hw0, hr, -⟩ := hsc q w n hw
    rw [hr]; exact h.ne q w0 n hw0

end Spec

end

end Fl4Proofs.P3.Sched
