/-
P3 (DESIGN.md §9), scheduling contexts: `Inv` across a donation and
`sched_context_resume` (`Inv.donate`).

`InvBut σ t`: `Inv` except `rd` for `t`. A donation gives `InvBut` (the
thread now has an SC); `sched_context_resume` either leaves the thread
released, or not schedulable with an inactive SC, or postpones it into the
release queue, which keeps `InvBut` and makes `rd` for `t` vacuous.
-/
import Fl4Proofs.P3.ScInvD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- `Inv` except `rd` for `t`. -/
structure InvBut (σ : State Unit) (t : ObjRef) : Prop where
  rq : ∀ d p u, u ∈ σ.readyQueues d p → ∃ x scp y n, σ.kheap u = some (.tcb x) ∧ x.tcbSchedContext = some scp ∧
    runnable x.tcbState = true ∧ σ.kheap scp = some (.schedContext y n) ∧ scActive y = true
  rel : ∀ u ∈ σ.releaseQueue, ∃ x scp y n, σ.kheap u = some (.tcb x) ∧ x.tcbSchedContext = some scp ∧
    runnable x.tcbState = true ∧ σ.kheap scp = some (.schedContext y n) ∧ scActive y = true
  sorted : σ.releaseQueue.Pairwise (fun a b => specRt σ a ≤ specRt σ b)
  rd : ∀ u x, u ≠ t → σ.kheap u = some (.tcb x) → inClass x.tcbState → RelIfBound σ u
  refills : ∀ p y n, σ.kheap p = some (.schedContext y n) → scActive y = true → y.scPeriod ≠ 0 → RefOK y
  back : ∀ u x p, σ.kheap u = some (.tcb x) → x.tcbSchedContext = some p →
    ∃ y n, σ.kheap p = some (.schedContext y n) ∧ y.scTcb = some u
  ntfnSc : ∀ q x p, σ.kheap q = some (.notification x) → x.ntfnSc = some p →
    ∃ y n, σ.kheap p = some (.schedContext y n)
  ne : ∀ p y n, σ.kheap p = some (.schedContext y n) → y.scRefills ≠ []
  rr : ∀ p y n, σ.kheap p = some (.schedContext y n) → scActive y = true → y.scPeriod = 0 → RRok y

theorem InvBut.inv {σ : State Unit} {t : ObjRef} (h : InvBut σ t)
    (ht : ∀ x, σ.kheap t = some (.tcb x) → inClass x.tcbState → RelIfBound σ t) : Inv σ :=
  ⟨h.rq, h.rel, h.sorted, fun u x hx hc => by
    by_cases e : u = t
    · subst e; exact ht x hx hc
    · exact h.rd u x e hx hc, h.refills, h.back, h.ntfnSc, h.ne, h.rr⟩

theorem schedulable_of {σ : State Unit} {t scp : ObjRef} {x : Tcb} {y : SchedContext} {n : Nat}
    (hk : σ.kheap t = some (.tcb x)) (hsc : x.tcbSchedContext = some scp) (hr : runnable x.tcbState = true)
    (hky : σ.kheap scp = some (.schedContext y n)) (ha : scActive y = true) (hq : t ∉ σ.releaseQueue) :
    schedulable t σ = true := by
  unfold schedulable
  simp only [decide_eq_true_eq]
  refine ⟨?_, ?_, hq⟩
  · simp [optPred, optMapSome, optMap, tcbsOfKh, tcbOf, hk, hr]
  · simp [optPred, optMap, tcbsOfKh, tcbOf, hk, hsc, scsOfKh, scOf, hky, ha]

/-- The donated state: `InvBut`. -/
theorem Inv.donated {σ : State Unit} (h : Inv σ) {p t : ObjRef} {ys : SchedContext} {ns : Nat} {xt : Tcb}
    (hks : σ.kheap p = some (.schedContext ys ns)) (hnone : ys.scTcb = none) (hkt : σ.kheap t = some (.tcb xt))
    (hpt : p ≠ t) (hnq : NotQueued σ t) : InvBut (donSt σ p t ys ns xt) t := by
  set σd := donSt σ p t ys ns xt
  have kt : σd.kheap t = some (.tcb { xt with tcbSchedContext := some p }) := by simp [σd, donSt, updK]
  have kp : σd.kheap p = some (.schedContext { ys with scTcb := some t } ns) := by
    simp [σd, donSt, updK, hpt]
  have ko : ∀ q, q ≠ t → q ≠ p → σd.kheap q = σ.kheap q := fun q h1 h2 => by simp [σd, donSt, updK, h1, h2]
  -- no TCB is bound to `p`
  have hnp : ∀ u x, σ.kheap u = some (.tcb x) → x.tcbSchedContext ≠ some p := fun u x hx hp => by
    obtain ⟨y, m, h1, h2⟩ := h.back u x p hx hp
    rw [hks] at h1; cases h1; rw [hnone] at h2; cases h2
  have tcb_o : ∀ u x, σ.kheap u = some (.tcb x) → u ≠ t → σd.kheap u = some (.tcb x) := fun u x hx hut => by
    have : u ≠ p := by rintro rfl; rw [hks] at hx; cases hx
    rw [ko u hut this]; exact hx
  have tcb_b : ∀ u x, σd.kheap u = some (.tcb x) → u ≠ t → σ.kheap u = some (.tcb x) := fun u x hx hut => by
    have : u ≠ p := by rintro rfl; rw [kp] at hx; cases hx
    rw [ko u hut this] at hx; exact hx
  have sc_o : ∀ q y m, σ.kheap q = some (.schedContext y m) → q ≠ p → σd.kheap q = some (.schedContext y m) :=
    fun q y m hq hqp => by
      have : q ≠ t := by rintro rfl; rw [hkt] at hq; cases hq
      rw [ko q this hqp]; exact hq
  have sc_b : ∀ q y m, σd.kheap q = some (.schedContext y m) →
      ∃ y0, σ.kheap q = some (.schedContext y0 m) ∧ y.scRefills = y0.scRefills ∧ y.scRefillMax = y0.scRefillMax ∧
        y.scPeriod = y0.scPeriod := by
    intro q y m hq
    by_cases e : q = p
    · subst e; rw [kp] at hq; cases hq; exact ⟨ys, hks, rfl, rfl, rfl⟩
    · have : q ≠ t := by rintro rfl; rw [kt] at hq; cases hq
      rw [ko q this e] at hq; exact ⟨y, hq, rfl, rfl, rfl⟩
  have rt_m : ∀ u ∈ σ.releaseQueue, specRt σd u = specRt σ u := by
    intro u hu
    obtain ⟨x, scp, y, m, h1, h2, -, h4, h5⟩ := h.rel u hu
    have hut : u ≠ t := fun e => hnq.2 (e ▸ hu)
    have hsp : scp ≠ p := fun e => hnp u x h1 (e ▸ h2)
    have hne := h.ne scp y m h4
    rw [specRt_eq (tcb_o u x h1 hut) h2 (sc_o scp y m h4 hsp) hne, specRt_eq h1 h2 h4 hne]
  refine ⟨fun d q u hu => ?_, fun u hu => ?_, ?_, fun u x hut hx hc => ?_, fun q y m hy ha => ?_,
    fun u x q hx hq => ?_, fun q x q' hx hq => ?_, fun q y m hy => ?_, fun q y m hy ha hp0 => ?_⟩
  · obtain ⟨x, scp, y, m, h1, h2, h3, h4, h5⟩ := h.rq d q u hu
    exact ⟨x, scp, y, m, tcb_o u x h1 (fun e => hnq.1 d q (e ▸ hu)), h2, h3,
      sc_o scp y m h4 (fun e => hnp u x h1 (e ▸ h2)), h5⟩
  · obtain ⟨x, scp, y, m, h1, h2, h3, h4, h5⟩ := h.rel u hu
    exact ⟨x, scp, y, m, tcb_o u x h1 (fun e => hnq.2 (e ▸ hu)), h2, h3,
      sc_o scp y m h4 (fun e => hnp u x h1 (e ▸ h2)), h5⟩
  · show σ.releaseQueue.Pairwise _
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    rw [rt_m a ha, rt_m b hb]; exact hab
  · have hx0 := tcb_b u x hx hut
    intro x' scp y m h1 h2 h3 h4 h5
    rw [hx] at h1; cases h1
    have hsp : scp ≠ p := fun e => hnp u x hx0 (e ▸ h2)
    obtain ⟨y0, hy0, hr, hm, -⟩ := sc_b scp y m h3
    have := h.rd u x hx0 hc x scp y0 m hx0 h2 hy0 (by simpa [scActive, hm] using h4) h5
    unfold released refillHd at this ⊢; rw [hr]; exact this
  · obtain ⟨y0, hy0, hr, hm, hp⟩ := sc_b q y m hy
    intro hper
    have := h.refills q y0 m hy0 (by simpa [scActive, hm] using ha) (hp ▸ hper)
    unfold RefOK refillHd at this ⊢; rw [hr]; exact this
  · by_cases e : u = t
    · subst e; rw [kt] at hx; cases hx; cases hq; exact ⟨_, ns, kp, rfl⟩
    · have hx0 := tcb_b u x hx e
      obtain ⟨y, m, h1, h2⟩ := h.back u x q hx0 hq
      have : q ≠ p := fun e' => hnp u x hx0 (e' ▸ hq)
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
  · obtain ⟨y0, hy0, hr, -, -⟩ := sc_b q y m hy
    rw [hr]; exact h.ne q y0 m hy0
  · obtain ⟨y0, hy0, hr, hm, hp⟩ := sc_b q y m hy
    exact (h.rr q y0 m hy0 (by simpa [scActive, hm] using ha) (hp ▸ hp0)).of_refills hr

/-- Postponing the thread `t` of `InvBut` restores `Inv`. -/
theorem InvBut.postponed {σ : State Unit} {t p : ObjRef} (h : InvBut σ t) {x : Tcb} {y : SchedContext} {n : Nat}
    (hkt : σ.kheap t = some (.tcb x)) (hsc : x.tcbSchedContext = some p) (hrun : runnable x.tcbState = true)
    (hkp : σ.kheap p = some (.schedContext y n)) (ha : scActive y = true) (b : Bool) :
    Inv { setRel (setQ σ x.tcbDomain x.tcbPriority (tcbSchedDequeue t (σ.readyQueues x.tcbDomain x.tcbPriority)))
      (specInsT σ.releaseQueue (specRt σ) t) b with reprogramTimer := true } := by
  set σp := { setRel (setQ σ x.tcbDomain x.tcbPriority (tcbSchedDequeue t (σ.readyQueues x.tcbDomain x.tcbPriority)))
      (specInsT σ.releaseQueue (specRt σ) t) b with reprogramTimer := true }
  have hk : σp.kheap = σ.kheap := rfl
  have hrq : σp.releaseQueue = specInsT σ.releaseQueue (specRt σ) t := rfl
  have hfacts : ∀ u ∈ σp.releaseQueue, ∃ xu scp yu nu, σ.kheap u = some (.tcb xu) ∧
      xu.tcbSchedContext = some scp ∧ runnable xu.tcbState = true ∧ σ.kheap scp = some (.schedContext yu nu) ∧
      scActive yu = true := by
    intro u hu
    rw [hrq, mem_specInsT] at hu
    rcases hu with rfl | hu
    · exact ⟨x, p, y, n, hkt, hsc, hrun, hkp, ha⟩
    · exact h.rel u hu
  have hrt : ∀ u ∈ σp.releaseQueue, specRt σp u = specRt σ u := by
    intro u hu
    obtain ⟨xu, scp, yu, nu, h1, h2, -, h4, -⟩ := hfacts u hu
    rw [specRt_eq (σ := σp) h1 h2 h4 (h.ne _ _ _ h4), specRt_eq h1 h2 h4 (h.ne _ _ _ h4)]
  refine ⟨fun d q u hu => ?_, hfacts, ?_, fun u xu hxu hc => ?_, h.refills, h.back, h.ntfnSc, h.ne, h.rr⟩
  · simp only [σp, setRel, setQ] at hu
    split at hu
    · rename_i e; obtain ⟨rfl, rfl⟩ := e; exact h.rq _ _ u (List.mem_of_mem_filter hu)
    · exact h.rq d q u hu
  · have := specInsT_sorted (specRt σ) t h.sorted
    rw [← hrq] at this
    exact List.Pairwise.imp_of_mem (fun {a b} ha hb hab => by rw [hrt a ha, hrt b hb]; exact hab) this
  · intro x' scp yu nu h1 h2 h3 h4 h5
    by_cases e : u = t
    · subst e; exact absurd (by rw [hrq, mem_specInsT]; exact Or.inl rfl) h5
    · have := h.rd u xu e hxu hc x' scp yu nu h1 h2 h3 h4 (fun hm => h5 (by rw [hrq, mem_specInsT]; exact Or.inr hm))
      exact this

/-- **`maybe_donate_sc` keeps the invariant**, for a runnable thread in no
queue. -/
theorem Inv.donate {σ σ' : State Unit} (h : Inv σ) {t n : ObjRef} {xt : Tcb} {xn : Notification}
    (hkt : σ.kheap t = some (.tcb xt)) (hkn : σ.kheap n = some (.notification xn))
    (hrun : runnable xt.tcbState = true) (hnq : NotQueued σ t)
    (he : maybeDonateSc (Z := Unit) t n σ = ({((), σ')}, False)) :
    Inv σ' ∧ ∀ x p y m, σ'.kheap t = some (.tcb x) → x.tcbSchedContext = some p →
      σ'.kheap p = some (.schedContext y m) → t ∈ σ'.releaseQueue →
      refillReady σ'.curTime (refillHd y) = false ∨ y.scPeriod = 0 := by
  have hσ : Inv σ ∧ ∀ x p y m, σ.kheap t = some (.tcb x) → x.tcbSchedContext = some p →
      σ.kheap p = some (.schedContext y m) → t ∈ σ.releaseQueue →
      refillReady σ.curTime (refillHd y) = false ∨ y.scPeriod = 0 := ⟨h, fun _ _ _ _ _ _ _ hm => absurd hm hnq.2⟩
  have hnt : n ≠ t := by rintro rfl; rw [hkt] at hkn; cases hkn
  unfold maybeDonateSc getTcbObjRef at he
  rw [nd_bind_one (threadGet_eq _ hkt)] at he
  simp only [NonDet.when] at he
  split_ifs at he with h0
  swap
  · rw [pair_eq he]; exact hσ
  rw [nd_bind_one' (getNtfnSc_eq hkn)] at he
  cases hsc : xn.ntfnSc with
  | none => rw [hsc] at he; rw [pair_eq he]; exact hσ
  | some p =>
    rw [hsc] at he
    obtain ⟨ys, ns, hks⟩ := h.ntfnSc n xn p hkn hsc
    have hpt : p ≠ t := by rintro rfl; rw [hkt] at hks; cases hks
    simp only [NonDet.maybeM] at he
    have hg : getScObjRef (Z := Unit) SchedContext.scTcb p σ = ({(ys.scTcb, σ)}, False) := by
      unfold getScObjRef; rw [nd_bind_one (getSchedContext_eq hks)]; rfl
    rw [nd_bind_one hg] at he
    cases hst : ys.scTcb with
    | some u => rw [hst] at he; simp only [NonDet.when, reduceCtorEq, ↓reduceIte] at he; rw [pair_eq he]; exact hσ
    | none =>
      rw [hst] at he
      simp only [NonDet.when, ↓reduceIte] at he
      rw [nd_bind_one (schedContextDonate_eq hks hst hkt hpt)] at he
      have hb := h.donated hks hst hkt hpt hnq
      set σd := donSt σ p t ys ns xt
      set xt' : Tcb := { xt with tcbSchedContext := some p }
      set ys' : SchedContext := { ys with scTcb := some t }
      have kt : σd.kheap t = some (.tcb xt') := by simp [σd, donSt, updK] <;> rfl
      have kp : σd.kheap p = some (.schedContext ys' ns) := by simp [σd, donSt, updK, hpt] <;> rfl
      have hne : ys'.scRefills ≠ [] := h.ne p ys ns hks
      have hnr : t ∉ σd.releaseQueue := hnq.2
      rw [resume_spec_eq kp rfl kt hne
        (fun hs => by
          obtain ⟨x, scp, y, m, h1, h2, h3, h4, h5, -⟩ := schedulable_inv hs
          rw [kt] at h1; cases h1; cases h2; rw [kp] at h4; cases h4; exact ⟨h3, h5⟩)
        (fun _ => hnq.1 _ _)] at he
      split_ifs at he with hc
      · -- postponed
        have hact : scActive ys' = true := by
          obtain ⟨x, scp, y, m, h1, h2, -, h4, h5, -⟩ := schedulable_inv hc.1
          rw [kt] at h1; cases h1; cases h2; rw [kp] at h4; cases h4; exact h5
        obtain ⟨b, hp⟩ := postpone_eq kp rfl kt (specRt σd) (fun u hu => by
          rcases hu with rfl | hu
          · exact ⟨xt', p, ys', ns, kt, rfl, kp, hne, specRt_eq kt rfl kp hne⟩
          · obtain ⟨xu, scp, yu, nu, h1, h2, -, h4, -⟩ := hb.rel u hu
            exact ⟨xu, scp, yu, nu, h1, h2, h4, hb.ne _ _ _ h4, specRt_eq h1 h2 h4 (hb.ne _ _ _ h4)⟩)
        rw [hp] at he
        rw [pair_eq he]
        refine ⟨hb.postponed kt rfl hrun kp hact b, fun x' q y m h1 h2 h3 _ => ?_⟩
        have h1' : σd.kheap t = some (.tcb x') := h1
        have h3' : σd.kheap q = some (.schedContext y m) := h3
        rw [kt] at h1'; cases h1'; cases h2; rw [kp] at h3'; cases h3'
        show refillReady σd.curTime (refillHd ys') = false ∨ ys'.scPeriod = 0
        by_cases hper : ys.scPeriod = 0
        · exact Or.inr hper
        have hsuff := sufficient_of_refOK (h.refills p ys ns hks hact hper)
        have := hc.2
        have e : refillHd ys' = refillHd ys := rfl
        rw [e] at this ⊢
        left
        cases hr : refillReady σd.curTime (refillHd ys)
        · rfl
        · exact absurd ⟨hr, hsuff⟩ this
      · rw [pair_eq he]
        refine ⟨?_, fun _ _ _ _ _ _ _ hm => absurd hm hnr⟩
        refine hb.inv fun x hx _ => ?_
        rw [kt] at hx; cases hx
        intro x' scp y m h1 h2 h3 h4 h5
        rw [kt] at h1; cases h1; cases h2; rw [kp] at h3; cases h3
        have hs := schedulable_of kt rfl hrun kp h4 h5
        have := not_and.1 hc hs
        simpa [released] using this

end Spec

end

end Fl4Proofs.P3.Sched
