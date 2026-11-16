/-
P3 (DESIGN.md §9), scheduling contexts: `Inv` across `maybe_return_sc`
(`Inv.ret`, for a thread that is not runnable) and the sporadic checks of
the receive/wake tails (`Inv.specUnblock`, `Inv.completeCheck`: the check
runs on the thread's own SC, which by `back` no other release-queue member
is bound to; the thread itself is in the release queue only with a head
that is not ready).
-/
import Fl4Proofs.P3.ScInvD2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

theorem mem_pure {σ σ' : State Unit} (h : ((), σ') ∈ (NonDet.pure (σ := State Unit) () σ).1) : σ' = σ := by
  have := Set.mem_singleton_iff.1 h; cases this; rfl

theorem Inv.notQueued {σ : State Unit} (h : Inv σ) {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hnr : runnable x.tcbState = false) : NotQueued σ t := by
  refine ⟨fun d p hm => ?_, fun hm => ?_⟩
  · obtain ⟨x', -, -, -, h1, -, h3, -⟩ := h.rq d p t hm
    rw [hk] at h1; cases h1; rw [hnr] at h3; cases h3
  · obtain ⟨x', -, -, -, h1, -, h3, -⟩ := h.rel t hm
    rw [hk] at h1; cases h1; rw [hnr] at h3; cases h3

/-- Unbinding a thread in no queue from its SC keeps the invariant. -/
theorem Inv.unbound {σ : State Unit} (h : Inv σ) {t p : ObjRef} {xt : Tcb} {ys : SchedContext} {ns : Nat}
    (hkt : σ.kheap t = some (.tcb xt)) (hsc : xt.tcbSchedContext = some p)
    (hks : σ.kheap p = some (.schedContext ys ns)) (hnq : NotQueued σ t) :
    Inv (updSc (updK σ t (.tcb { xt with tcbSchedContext := none })) p { ys with scTcb := none } ns) := by
  have hpt : p ≠ t := by rintro rfl; rw [hkt] at hks; cases hks
  set σ2 := updSc (updK σ t (.tcb { xt with tcbSchedContext := none })) p { ys with scTcb := none } ns
  have kt : σ2.kheap t = some (.tcb { xt with tcbSchedContext := none }) := by simp [σ2, updK, Ne.symm hpt]
  have kp : σ2.kheap p = some (.schedContext { ys with scTcb := none } ns) := by simp [σ2, updK]
  have ko : ∀ q, q ≠ t → q ≠ p → σ2.kheap q = σ.kheap q := fun q h1 h2 => by simp [σ2, updK, h1, h2]
  -- only `t` is bound to `p`
  have hown : ∀ u x, σ.kheap u = some (.tcb x) → x.tcbSchedContext = some p → u = t := fun u x hx hp => by
    obtain ⟨y, m, h1, h2⟩ := h.back u x p hx hp
    obtain ⟨y', m', g1, g2⟩ := h.back t xt p hkt hsc
    rw [h1] at g1; cases g1; rw [h2] at g2; cases g2; rfl
  have tcb_b : ∀ u x, σ2.kheap u = some (.tcb x) → u ≠ t → σ.kheap u = some (.tcb x) := fun u x hx hut => by
    have : u ≠ p := by rintro rfl; rw [kp] at hx; cases hx
    rw [ko u hut this] at hx; exact hx
  have tcb_o : ∀ u x, σ.kheap u = some (.tcb x) → u ≠ t → σ2.kheap u = some (.tcb x) := fun u x hx hut => by
    have : u ≠ p := by rintro rfl; rw [hks] at hx; cases hx
    rw [ko u hut this]; exact hx
  have sc_o : ∀ q y m, σ.kheap q = some (.schedContext y m) → q ≠ p → σ2.kheap q = some (.schedContext y m) :=
    fun q y m hq hqp => by
      have : q ≠ t := by rintro rfl; rw [hkt] at hq; cases hq
      rw [ko q this hqp]; exact hq
  have sc_b : ∀ q y m, σ2.kheap q = some (.schedContext y m) →
      ∃ y0, σ.kheap q = some (.schedContext y0 m) ∧ y.scRefills = y0.scRefills ∧ y.scRefillMax = y0.scRefillMax ∧
        y.scPeriod = y0.scPeriod := by
    intro q y m hq
    by_cases e : q = p
    · subst e; rw [kp] at hq; cases hq; exact ⟨ys, hks, rfl, rfl, rfl⟩
    · have : q ≠ t := by rintro rfl; rw [kt] at hq; cases hq
      rw [ko q this e] at hq; exact ⟨y, hq, rfl, rfl, rfl⟩
  have rt_m : ∀ u ∈ σ.releaseQueue, specRt σ2 u = specRt σ u := by
    intro u hu
    obtain ⟨x, scp, y, m, h1, h2, -, h4, h5⟩ := h.rel u hu
    have hut : u ≠ t := fun e => hnq.2 (e ▸ hu)
    have hsp : scp ≠ p := fun e => hut (hown u x h1 (e ▸ h2))
    have hne := h.ne scp y m h4 h5
    rw [specRt_eq (tcb_o u x h1 hut) h2 (sc_o scp y m h4 hsp) hne, specRt_eq h1 h2 h4 hne]
  refine ⟨fun d q u hu => ?_, fun u hu => ?_, ?_, fun u x hx hc => ?_, fun q y m hy ha => ?_,
    fun u x q hx hq => ?_, fun q x q' hx hq => ?_, fun q y m hy hya => ?_, fun q y m hy ha hp0 => ?_⟩
  · obtain ⟨x, scp, y, m, h1, h2, h3, h4, h5⟩ := h.rq d q u hu
    have hut : u ≠ t := fun e => hnq.1 d q (e ▸ hu)
    exact ⟨x, scp, y, m, tcb_o u x h1 hut, h2, h3, sc_o scp y m h4 (fun e => hut (hown u x h1 (e ▸ h2))), h5⟩
  · obtain ⟨x, scp, y, m, h1, h2, h3, h4, h5⟩ := h.rel u hu
    have hut : u ≠ t := fun e => hnq.2 (e ▸ hu)
    exact ⟨x, scp, y, m, tcb_o u x h1 hut, h2, h3, sc_o scp y m h4 (fun e => hut (hown u x h1 (e ▸ h2))), h5⟩
  · show σ.releaseQueue.Pairwise _
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    rw [rt_m a ha, rt_m b hb]; exact hab
  · by_cases hut : u = t
    · subst hut; intro x' scp _ _ h1 h2; rw [kt] at h1; cases h1; cases h2
    · have hx0 := tcb_b u x hx hut
      intro x' scp y m h1 h2 h3 h4 h5
      rw [hx] at h1; cases h1
      obtain ⟨y0, hy0, hr, hm, -⟩ := sc_b scp y m h3
      have := h.rd u x hx0 hc x scp y0 m hx0 h2 hy0 (by simpa [scActive, hm] using h4) h5
      unfold released refillHd at this ⊢; rw [hr]; exact this
  · obtain ⟨y0, hy0, hr, hm, hp⟩ := sc_b q y m hy
    intro hper
    have := h.refills q y0 m hy0 (by simpa [scActive, hm] using ha) (hp ▸ hper)
    unfold RefOK refillHd at this ⊢; rw [hr]; exact this
  · by_cases e : u = t
    · subst e; rw [kt] at hx; cases hx; cases hq
    · have hx0 := tcb_b u x hx e
      obtain ⟨y, m, h1, h2⟩ := h.back u x q hx0 hq
      have : q ≠ p := fun e' => e (hown u x hx0 (e' ▸ hq))
      exact ⟨y, m, sc_o q y m h1 this, h2⟩
  · have hq0 : σ.kheap q = some (.notification x) := by
      by_cases e : q = t
      · subst e; rw [kt] at hx; cases hx
      · by_cases e2 : q = p
        · subst e2; rw [kp] at hx; cases hx
        · rw [ko q e e2] at hx; exact hx
    obtain ⟨y, m, h1⟩ := h.ntfnSc q x q' hq0 hq
    by_cases e : q' = p
    · subst e; exact ⟨_, ns, kp⟩
    · exact ⟨y, m, sc_o q' y m h1 e⟩
  · obtain ⟨y0, hy0, hr, hm, -⟩ := sc_b q y m hy
    rw [hr]; exact h.ne q y0 m hy0 (by simpa [scActive, hm] using hya)
  · obtain ⟨y0, hy0, hr, hm, hp⟩ := sc_b q y m hy
    exact (h.rr q y0 m hy0 (by simpa [scActive, hm] using ha) (hp ▸ hp0)).of_refills hr

/-- **`maybe_return_sc` keeps the invariant**, for a thread that is not
runnable. -/
theorem Inv.ret {σ σ' : State Unit} (h : Inv σ) {n t : ObjRef} {xt : Tcb} {xn : Notification}
    (hkt : σ.kheap t = some (.tcb xt)) (hkn : σ.kheap n = some (.notification xn))
    (hnr : runnable xt.tcbState = false)
    (he : ((), σ') ∈ (maybeReturnSc (Z := Unit) n t σ).1) : Inv σ' := by
  have hnq := h.notQueued hkt hnr
  unfold maybeReturnSc getTcbObjRef at he
  rw [nd_bind_one (getNtfnSc_eq hkn), nd_bind_one (threadGet_eq _ hkt)] at he
  simp only [NonDet.when] at he
  split_ifs at he with hc
  swap
  · rw [mem_pure he]; exact h
  obtain ⟨e1, e2⟩ := hc
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 e2
  rw [hp] at he
  have hsc : xt.tcbSchedContext = some p := e1 ▸ hp
  obtain ⟨ys, ns, hks, -⟩ := h.back t xt p hkt hsc
  have hpt : p ≠ t := by rintro rfl; rw [hkt] at hks; cases hks
  rw [nd_bind_one (show NonDet.assertOpt (σ := State Unit) (some p) σ = ({(p, σ)}, False) from rfl),
    nd_bind_one (threadSet_eq _ hkt)] at he
  have hks1 : (updK σ t (.tcb (tcbSchedContextUpdate (fun _ => none) xt))).kheap p =
      some (.schedContext ys ns) := by simp [updK, hpt, hks]
  change ((), σ') ∈ ((updateSchedContext p _ >>= _) _).1 at he
  rw [nd_bind_one (updateSchedContext_eq hks1 _), nd_gets_bind] at he
  have hI := h.unbound hkt hsc hks hnq
  have e3 : (updSc (updK σ t (.tcb (tcbSchedContextUpdate (fun _ => none) xt))) p
      (scTcbUpdate (fun _ => none) ys) ns) =
      updSc (updK σ t (.tcb { xt with tcbSchedContext := none })) p { ys with scTcb := none } ns := rfl
  rw [e3] at he
  split_ifs at he
  · obtain ⟨σ3, h3, hq3⟩ := rescheduleRequired_qchange hI.actReady
    rw [h3, Set.mem_singleton_iff] at he; cases he; exact hI.qchange hq3
  · rw [mem_pure he]; exact hI

/-- `refill_unblock_check` on a thread's own SC. -/
theorem Inv.unblockOwn {σ σ' : State Unit} (h : Inv σ) {t p : ObjRef} {x : Tcb} {y : SchedContext} {n : Nat}
    (hkt : σ.kheap t = some (.tcb x)) (hsc : x.tcbSchedContext = some p) (hkp : σ.kheap p = some (.schedContext y n))
    (hrq : t ∈ σ.releaseQueue → refillReady σ.curTime (refillHd y) = false ∨ y.scPeriod = 0)
    (ha : scActive y = true)
    {r : Unit} (hm : (r, σ') ∈ (refillUnblockCheck (Z := Unit) p σ).1) : Inv σ' := by
  refine h.unblock hkp (h.ne p y n hkp ha) (fun hr hper u hu xu hxu hup => ?_) hm
  obtain ⟨y1, m1, g1, g2⟩ := h.back u xu p hxu hup
  obtain ⟨y2, m2, g3, g4⟩ := h.back t x p hkt hsc
  rw [g1] at g3; cases g3; rw [g2] at g4; cases g4
  rcases hrq hu with h1 | h1
  · rw [h1] at hr; cases hr
  · exact hper h1

/-- **The sporadic check after a wake-up or an active receive.** -/
theorem Inv.unblockTail {σ σ' : State Unit} (h : Inv σ) {t : ObjRef} {x : Tcb} (hkt : σ.kheap t = some (.tcb x))
    (hrq : ∀ p y n, x.tcbSchedContext = some p → σ.kheap p = some (.schedContext y n) → t ∈ σ.releaseQueue →
      refillReady σ.curTime (refillHd y) = false ∨ y.scPeriod = 0)
    (hsa : ∀ p y n, x.tcbSchedContext = some p → σ.kheap p = some (.schedContext y n) → y.scSporadic = true →
      scActive y = true)
    (hm : ((), σ') ∈ (specUnblock t σ).1) : Inv σ' := by
  unfold specUnblock getTcbObjRef at hm
  rw [nd_bind_one (threadGet_eq _ hkt)] at hm
  cases hsc : x.tcbSchedContext with
  | none =>
    rw [hsc, ifSporadic_none, Set.mem_singleton_iff] at hm; cases hm; exact h
  | some p =>
    rw [hsc] at hm
    obtain ⟨y, n, hkp, -⟩ := h.back t x p hkt hsc
    rw [ifSporadic_some hkp] at hm
    split_ifs at hm with hg
    · exact h.unblockOwn hkt hsc hkp (hrq p y n hsc hkp) (hsa p y n hsc hkp hg.1) hm
    · rw [Set.mem_singleton_iff] at hm; cases hm; exact h

/-- **The sporadic check after `complete_signal`'s donation.** -/
theorem Inv.completeCheck {σ σ' : State Unit} (h : Inv σ) {t m : ObjRef} {x : Tcb} {xn : Notification}
    (hkt : σ.kheap t = some (.tcb x)) (hkn : σ.kheap m = some (.notification xn))
    (hrq : ∀ p y n, x.tcbSchedContext = some p → σ.kheap p = some (.schedContext y n) → t ∈ σ.releaseQueue →
      refillReady σ.curTime (refillHd y) = false ∨ y.scPeriod = 0)
    (hsa : ∀ p y n, x.tcbSchedContext = some p → σ.kheap p = some (.schedContext y n) → y.scSporadic = true →
      scActive y = true)
    (hm : ((), σ') ∈ (specCompleteCheck t m σ).1) : Inv σ' := by
  unfold specCompleteCheck getTcbObjRef at hm
  rw [nd_bind_one (threadGet_eq _ hkt)] at hm
  cases hsc : x.tcbSchedContext with
  | none =>
    rw [hsc] at hm; simp only [NonDet.maybeM] at hm
    rw [mem_pure hm]; exact h
  | some p =>
    rw [hsc] at hm
    obtain ⟨y, n, hkp, -⟩ := h.back t x p hkt hsc
    simp only [NonDet.maybeM] at hm
    rw [nd_bind_one (getSchedContext_eq hkp)] at hm
    simp only [NonDet.when] at hm
    split_ifs at hm with hg
    · rw [nd_bind_one (getNtfnSc_eq hkn), nd_gets_bind] at hm
      split_ifs at hm
      · exact h.unblockOwn hkt hsc hkp (hrq p y n hsc hkp) (hsa p y n hsc hkp hg) hm
      · rw [mem_pure hm]; exact h
    · rw [mem_pure hm]; exact h

end Spec

end

end Fl4Proofs.P3.Sched
