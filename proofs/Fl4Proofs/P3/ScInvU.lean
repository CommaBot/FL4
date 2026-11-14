/-
P3 (DESIGN.md §9), scheduling contexts: **`refill_unblock_check` keeps
`Inv`** (`Inv.unblock`), given that no release-queue member is bound to the
SC or the check does not fire (its head is not ready).

`unblock_result`: an outcome of `refill_unblock_check` is the state itself,
or the SC replaced by one with well-formed refills (`RefOK`) whose head is
ready now; the merge loop keeps `RefOK` (`RefOK.merge`).
-/
import Fl4Proofs.P3.ScInvQ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

theorem sufficient_of_refOK {y : SchedContext} (h : RefOK y) : refillSufficient 0 (refillHd y) = true := by
  unfold refillSufficient refillCapacity
  have h0 : ¬ (refillHd y).rAmount < 0 := by rw [BitVec.lt_def]; simp
  simp only [h0, ↓reduceIte, decide_eq_true_eq]
  have e : (refillHd y).rAmount - 0 = (refillHd y).rAmount := by bv_omega
  rw [e]; exact h.2.2.2

theorem ready_now (σ : State Unit) (r : Refill) (h : r.rTime = σ.curTime) : refillReady σ.curTime r = true := by
  show refillReady' 0 σ.curTime r = true
  unfold refillReady'; rw [h]; simp

theorem sum_cons (r : Refill) (l : List Refill) :
    ((r :: l).map fun r => r.rAmount.toNat).sum = r.rAmount.toNat + (l.map fun r => r.rAmount.toNat).sum := by simp

/-- The merge of the two head refills keeps `RefOK` and the head's time. -/
theorem RefOK.merge {y : SchedContext} (h : RefOK y) (h2 : y.scRefills.length > 1) :
    RefOK { y with scRefills := mergeHd y } ∧
      (refillHd { y with scRefills := mergeHd y }).rTime = (refillHd y).rTime := by
  obtain ⟨-, hpos, hsum, hmin⟩ := h
  obtain ⟨a, b, l, e⟩ : ∃ a b l, y.scRefills = a :: b :: l := by
    match h : y.scRefills, h2 with
    | a :: b :: l, _ => exact ⟨a, b, l, rfl⟩
  have hd : refillHd y = a := by unfold refillHd; rw [e]; rfl
  have hm : mergeHd y = mergeRefill a b :: l := by unfold mergeHd; rw [hd, e]; rfl
  rw [e] at hpos hsum
  simp only [sum_cons] at hsum
  have hno : (b.rAmount + a.rAmount).toNat = b.rAmount.toNat + a.rAmount.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hpa := hpos a (by simp)
  have hpb := hpos b (by simp)
  have hhd : refillHd { y with scRefills := mergeHd y } = mergeRefill a b := by
    unfold refillHd; simp only [hm]; rfl
  refine ⟨⟨by simp [hm], fun r hr => ?_, ?_, ?_⟩, by rw [hhd, hd]; rfl⟩
  · simp only [hm, List.mem_cons] at hr
    rcases hr with rfl | hr
    · show 0 < (b.rAmount + a.rAmount).toNat; omega
    · exact hpos r (by simp [hr])
  · simp only [hm, sum_cons]
    show (b.rAmount + a.rAmount).toNat + _ < _; omega
  · rw [hhd]; rw [hd] at hmin
    show MIN_BUDGET ≤ b.rAmount + a.rAmount
    rw [BitVec.le_def] at hmin ⊢; rw [hno]; omega

theorem mergeHd_time {y : SchedContext} (h2 : y.scRefills.length > 1) :
    (refillHd { y with scRefills := mergeHd y }).rTime = (refillHd y).rTime := by
  obtain ⟨a, b, l, e⟩ : ∃ a b l, y.scRefills = a :: b :: l := by
    match h : y.scRefills, h2 with
    | a :: b :: l, _ => exact ⟨a, b, l, rfl⟩
  have hd : refillHd y = a := by unfold refillHd; rw [e]; rfl
  unfold mergeHd; rw [hd, e]; rfl

/-- What `refill_head_overlapping_loop` leaves. -/
theorem merge_loop_result {σa : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σa.kheap p = some (.schedContext y n)) {r : Unit} {σ' : State Unit}
    (hres : NonDet.WhileResults (fun _ s => the (refillHeadOverlapping (Z := Unit) p s) = true)
      (fun _ => mergeOverlappingRefills (Z := Unit) p) () σa (r, σ')) :
    ∃ z, σ' = updSc σa p z n ∧ (RefOK y → RefOK z) ∧ (refillHd z).rTime = (refillHd y).rTime ∧
      z = { y with scRefills := z.scRefills } ∧ (y.scRefills ≠ [] → z.scRefills ≠ []) := by
  suffices key : ∀ (u : Unit) (σ1 : State Unit) (res : Unit × State Unit),
      NonDet.WhileResults (fun _ s => the (refillHeadOverlapping (Z := Unit) p s) = true)
        (fun _ => mergeOverlappingRefills (Z := Unit) p) u σ1 res →
      ∀ z, σ1 = updSc σa p z n → (RefOK y → RefOK z) → (refillHd z).rTime = (refillHd y).rTime →
        z = { y with scRefills := z.scRefills } → (y.scRefills ≠ [] → z.scRefills ≠ []) →
      ∃ z', res.2 = updSc σa p z' n ∧ (RefOK y → RefOK z') ∧ (refillHd z').rTime = (refillHd y).rTime ∧
        z' = { y with scRefills := z'.scRefills } ∧ (y.scRefills ≠ [] → z'.scRefills ≠ []) by
    have h0 : σa = updSc σa p y n := (updSc_self hk).symm
    exact key () σa (r, σ') hres y h0 id rfl rfl id
  intro u σ1 res hw
  induction hw with
  | done _ => intro z h1 h2 h3 h4 h5; exact ⟨z, h1, h2, h3, h4, h5⟩
  | step hc hm _ ih =>
    intro z h1 h2 h3 h4 _
    subst h1
    have hkz : (updSc σa p z n).kheap p = some (.schedContext z n) := by simp [updK]
    have hlen : z.scRefills.length > 1 := by
      have := hc
      rw [refillHeadOverlapping_eq hkz, the_some, decide_eq_true_iff] at this
      exact this.1
    rw [merge_eq hkz (by intro e; rw [e] at hlen; simp at hlen), Set.mem_singleton_iff] at hm
    cases hm
    refine ih { z with scRefills := mergeHd z } (updSc_updSc _ _ _ _ _ _)
      (fun hy => ((h2 hy).merge hlen).1) ((mergeHd_time hlen).trans h3) ?_ (fun _ => by simp [mergeHd])
    rw [h4]

/-- **What `refill_unblock_check` leaves.** -/
theorem unblock_result {σ : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills ≠ []) {r : Unit} {σ' : State Unit}
    (hm : (r, σ') ∈ (refillUnblockCheck (Z := Unit) p σ).1) :
    (σ' = σ ∧ ¬ (refillReady σ.curTime (refillHd y) = true ∧ ¬ decide (y.scPeriod = 0) = true)) ∨
    ∃ z, σ' = updSc { σ with reprogramTimer := true } p z n ∧ (RefOK y → RefOK z) ∧
      (refillHd z).rTime = σ.curTime ∧ z = { y with scRefills := z.scRefills } ∧
      refillReady σ.curTime (refillHd y) = true ∧ z.scRefills ≠ [] ∧ y.scPeriod ≠ 0 := by
  unfold refillUnblockCheck at hm
  rw [nd_bind_one (isRoundRobin_eq hk), nd_bind_one (getScRefillReady_eq hk hne)] at hm
  simp only [NonDet.when] at hm
  split_ifs at hm with hc
  · rw [nd_gets_bind, nd_bind_one (updateRefillHd_eq hk _)] at hm
    rw [nd_bind_one (show NonDet.modify (fun s : State Unit => { s with reprogramTimer := true })
      (updSc σ p { y with scRefills := { the y.scRefills.head? with rTime := σ.curTime } :: y.scRefills.tail } n) =
      ({((), updSc { σ with reprogramTimer := true } p
        { y with scRefills := { the y.scRefills.head? with rTime := σ.curTime } :: y.scRefills.tail } n)}, False)
      from rfl)] at hm
    set y1 : SchedContext := { y with scRefills := { the y.scRefills.head? with rTime := σ.curTime } :: y.scRefills.tail }
    have hk1 : (updSc { σ with reprogramTimer := true } p y1 n).kheap p = some (.schedContext y1 n) := by
      simp [updK]
    have hR1 : RefOK y → RefOK y1 := by
      intro hR
      obtain ⟨-, hpos, hsum, hmin⟩ := hR
      obtain ⟨a, l, e⟩ := List.exists_cons_of_ne_nil hne
      have hd : refillHd y = a := by unfold refillHd; rw [e]; rfl
      have hy1 : y1.scRefills = { a with rTime := σ.curTime } :: l := by
        show { the y.scRefills.head? with rTime := σ.curTime } :: y.scRefills.tail = _
        rw [e]; rfl
      rw [e] at hpos hsum
      refine ⟨by rw [hy1]; simp, fun q hq => ?_, ?_, ?_⟩
      · rw [hy1, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hpos a (by simp)
        · exact hpos q (by simp [hq])
      · rw [hy1]; simpa using hsum
      · have : refillHd y1 = { a with rTime := σ.curTime } := by unfold refillHd; rw [hy1]; rfl
        rw [this]; rw [hd] at hmin; exact hmin
    have ht1 : (refillHd y1).rTime = σ.curTime := by
      show (the ({ the y.scRefills.head? with rTime := σ.curTime } :: y.scRefills.tail).head?).rTime = _
      rfl
    obtain ⟨z, h1, h2, h3, h4, h5⟩ := merge_loop_result hk1 hm
    refine Or.inr ⟨z, h1.trans (updSc_updSc _ _ _ _ _ _), fun hy => h2 (hR1 hy), h3.trans ht1, ?_, hc.1,
      h5 (by simp [y1]), by simpa using hc.2⟩
    rw [h4]
  · have hm' : (r, σ') ∈ ({((), σ)} : Set (Unit × State Unit)) := hm
    rw [Set.mem_singleton_iff] at hm'
    cases hm'
    exact Or.inl ⟨rfl, hc⟩

/-- **`refill_unblock_check` keeps the invariant**, if no release-queue
member is bound to the SC. -/
theorem Inv.unblock {σ σ' : State Unit} (h : Inv σ) {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills ≠ [])
    (hnr : refillReady σ.curTime (refillHd y) = true → y.scPeriod ≠ 0 →
      ∀ u ∈ σ.releaseQueue, ∀ x, σ.kheap u = some (.tcb x) → x.tcbSchedContext ≠ some p)
    {r : Unit} (hm : (r, σ') ∈ (refillUnblockCheck (Z := Unit) p σ).1) : Inv σ' := by
  rcases unblock_result hk hne hm with ⟨rfl, -⟩ | ⟨z, rfl, hzR, hzt, hzy, hrdy, hzne, hper⟩
  · exact h
  have hnr' := hnr hrdy hper
  have hzper : z.scPeriod = y.scPeriod := by rw [hzy]
  have hkp : ∀ q, q ≠ p → (updSc { σ with reprogramTimer := true } p z n).kheap q = σ.kheap q := fun q hq => by
    simp [updK, hq]
  have hkz : (updSc { σ with reprogramTimer := true } p z n).kheap p = some (.schedContext z n) := by simp [updK]
  have hzact : scActive z = scActive y := by rw [hzy]
  have htcb : ∀ u x, (updSc { σ with reprogramTimer := true } p z n).kheap u = some (.tcb x) →
      σ.kheap u = some (.tcb x) := fun u x hx => by
    by_cases e : u = p
    · subst e; rw [hkz] at hx; cases hx
    · rw [hkp u e] at hx; exact hx
  refine ⟨fun d q u hu => ?_, fun u hu => ?_, ?_, fun u x hx hc => ?_, fun q w m hw => ?_,
    fun u x q hx hq => ?_, fun q x q' hx hq => ?_, fun q w m hw => ?_⟩
  · obtain ⟨x, scp, h1, h2, h3⟩ := h.rq d q u hu
    have : u ≠ p := by rintro rfl; rw [hk] at h1; cases h1
    exact ⟨x, scp, by rw [hkp u this]; exact h1, h2, h3⟩
  · obtain ⟨x, scp, w, m, h1, h2, h3, h4, h5⟩ := h.rel u hu
    have hup : u ≠ p := by rintro rfl; rw [hk] at h1; cases h1
    have hsp : scp ≠ p := fun e => hnr' u hu x h1 (e ▸ h2)
    exact ⟨x, scp, w, m, by rw [hkp u hup]; exact h1, h2, h3, by rw [hkp scp hsp]; exact h4, h5⟩
  · show σ.releaseQueue.Pairwise _
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    obtain ⟨xa, pa, ya, na, h1, h2, -, h4, h5⟩ := h.rel a ha
    obtain ⟨xb, pb, yb, nb, g1, g2, -, g4, g5⟩ := h.rel b hb
    have nea := h.ne _ _ _ h4
    have neb := h.ne _ _ _ g4
    have hap : a ≠ p := by rintro rfl; rw [hk] at h1; cases h1
    have hbp : b ≠ p := by rintro rfl; rw [hk] at g1; cases g1
    have hpa : pa ≠ p := fun e => hnr' a ha xa h1 (e ▸ h2)
    have hpb : pb ≠ p := fun e => hnr' b hb xb g1 (e ▸ g2)
    rw [specRt_eq (by rw [hkp a hap]; exact h1) h2 (by rw [hkp pa hpa]; exact h4) nea,
      specRt_eq (by rw [hkp b hbp]; exact g1) g2 (by rw [hkp pb hpb]; exact g4) neb]
    rw [specRt_eq h1 h2 h4 nea, specRt_eq g1 g2 g4 neb] at hab
    exact hab
  · have hx0 := htcb u x hx
    intro x' scp w m h1 h2 h3 h4 h5
    rw [hx] at h1; cases h1
    by_cases e : scp = p
    · subst e
      rw [hkz] at h3; cases h3
      exact ⟨ready_now _ _ hzt, sufficient_of_refOK (hzR (h.refills _ y n hk (hzact ▸ h4) hper))⟩
    · rw [hkp scp e] at h3
      exact h.rd u x hx0 hc x scp w m hx0 h2 h3 h4 h5
  · by_cases e : q = p
    · subst e; rw [hkz] at hw; cases hw; intro ha _; exact hzR (h.refills _ y n hk (hzact ▸ ha) hper)
    · rw [hkp q e] at hw; exact h.refills q w m hw
  · obtain ⟨w, m, h1, h2⟩ := h.back u x q (htcb u x hx) hq
    by_cases e : q = p
    · subst e; rw [hk] at h1; cases h1
      exact ⟨z, n, hkz, by rw [hzy]; exact h2⟩
    · exact ⟨w, m, by rw [hkp q e]; exact h1, h2⟩
  · have hx0 : σ.kheap q = some (.notification x) := by
      by_cases e : q = p
      · subst e; rw [hkz] at hx; cases hx
      · rw [hkp q e] at hx; exact hx
    obtain ⟨w, m, h1⟩ := h.ntfnSc q x q' hx0 hq
    by_cases e : q' = p
    · subst e; exact ⟨z, n, hkz⟩
    · exact ⟨w, m, by rw [hkp q' e]; exact h1⟩
  · by_cases e : q = p
    · subst e; rw [hkz] at hw; cases hw; exact hzne
    · rw [hkp q e] at hw; exact h.ne q w m hw

end Spec

end

end Fl4Proofs.P3.Sched
