/-
P3 (DESIGN.md §9), scheduling contexts: the round-robin refill updates on
the lists: `refill_reset_rr` (`rrResetL`, `charge_budget`) and
`refill_budget_check_round_robin` (`rrChargeL`, `commit_time`), and
`Inv` after a change of one SC's refills (`Inv.refillUpd`).
-/
import Fl4Proofs.P3.ScCharge1
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

/-- `refill_reset_rr` on the list: the tail's amount moves to the head. -/
def rrResetL (rs : List sporadic.Refill) : List sporadic.Refill :=
  ((⟨(rs.headD zR).time, core.num.U64.wrapping_add (rs.headD zR).amount (rs.getLastD zR).amount⟩ :
    sporadic.Refill) :: rs.tail).dropLast ++ [⟨(rs.getLastD zR).time, 0#u64⟩]

/-- `refill_budget_check_round_robin` on the list: `c` moves from the head
to the tail. -/
def rrChargeL (rs : List sporadic.Refill) (c : U64) : List sporadic.Refill :=
  let l : List sporadic.Refill :=
    ⟨(rs.headD zR).time, core.num.U64.wrapping_sub (rs.headD zR).amount c⟩ :: rs.tail
  l.dropLast ++ [⟨(l.getLastD zR).time, core.num.U64.wrapping_add (l.getLastD zR).amount c⟩]

section Spec
open Fl4Spec

theorem the_getLast_cons_map (X : Refill) {l : List sporadic.Refill} (hl : l ≠ []) :
    the (X :: l.map toRefill).getLast? = toRefill (l.getLastD zR) := by
  obtain ⟨b, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  rw [List.map_cons, List.getLast?_cons_cons, ← List.map_cons]
  exact the_getLast_map (by simp)

theorem refillResetRr_eq {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) {rs : List sporadic.Refill} (hx : x.scRefills = rs.map toRefill)
    (hne : rs ≠ []) :
    refillResetRr (Z := Unit) p σ = ({((), updSc σ p { x with scRefills := (rrResetL rs).map toRefill } n)}, False) := by
  have hne' : x.scRefills ≠ [] := by rw [hx]; simpa using hne
  have hd : refillHd x = toRefill (rs.headD zR) := refillHd_map hx hne
  have tl : refillTl x = toRefill (rs.getLastD zR) := by unfold refillTl; rw [hx]; exact the_getLast_map hne
  unfold refillResetRr
  rw [nd_bind_one (getRefillHead_eq hk hne'), nd_bind_one (getRefillTail_eq hk hne'), hd, tl,
    nd_bind_one (updateRefillHd_eq hk _)]
  have hk1 : ∀ z : SchedContext, (updSc σ p z n).kheap p = some (.schedContext z n) := fun z => by simp [updK]
  rw [updateRefillTl_eq (hk1 _), updSc_updSc]
  congr 4
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [hx]
  cases l with
  | nil => simp [rrResetL, the, toRefill, zR, core.num.U64.wrapping_add_bv_eq]
  | cons b l =>
    simp only [List.map_cons, List.head?_cons, the_some, List.tail_cons]
    rw [← List.map_cons, the_getLast_cons_map _ (by simp)]
    simp [rrResetL, toRefill, core.num.U64.wrapping_add_bv_eq, List.dropLast_cons_of_ne_nil]

theorem refillBudgetCheckRoundRobin_eq {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hcur : σ.curSc = p) (hk : σ.kheap p = some (.schedContext x n)) {rs : List sporadic.Refill}
    (hx : x.scRefills = rs.map toRefill) (hne : rs ≠ []) (c : U64) :
    refillBudgetCheckRoundRobin (Z := Unit) c.bv σ =
      ({((), updSc σ p { x with scRefills := (rrChargeL rs c).map toRefill } n)}, False) := by
  unfold refillBudgetCheckRoundRobin
  rw [nd_gets_bind, hcur, nd_bind_one (updateRefillHd_eq hk _)]
  have hk1 : ∀ z : SchedContext, (updSc σ p z n).kheap p = some (.schedContext z n) := fun z => by simp [updK]
  rw [updateRefillTl_eq (hk1 _), updSc_updSc]
  congr 4
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [hx]
  cases l with
  | nil => simp [rrChargeL, the, toRefill, zR, core.num.U64.wrapping_add_bv_eq, core.num.U64.wrapping_sub_bv_eq]
  | cons b l =>
    simp only [List.map_cons, List.head?_cons, the_some, List.tail_cons]
    rw [← List.map_cons, the_getLast_cons_map _ (by simp)]
    have hl : ∀ q : sporadic.Refill, (q :: b :: l).getLastD zR = (b :: l).getLastD zR := fun q => by
      simp [List.getLastD_eq_getLast?, List.getLast?_cons_cons]
    simp [rrChargeL, toRefill, hl, core.num.U64.wrapping_add_bv_eq, core.num.U64.wrapping_sub_bv_eq,
      List.dropLast_cons_of_ne_nil]

/-- **One SC's refills replaced**: `Inv` except `rd` for its owner, if the
owner is not in the release queue. -/
theorem Inv.refillUpd {σ : State Unit} (h : Inv σ) {p u0 : ObjRef} {y y' : SchedContext} {m : Nat}
    (hk : σ.kheap p = some (.schedContext y m)) (hy' : y' = { y with scRefills := y'.scRefills })
    (hne' : y'.scRefills ≠ []) (hok : scActive y' = true → y'.scPeriod ≠ 0 → RefOK y')
    (hrr : scActive y' = true → y'.scPeriod = 0 → RRok y')
    (hown : y.scTcb = some u0) (hnr : u0 ∉ σ.releaseQueue) : InvBut (updSc σ p y' m) u0 := by
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
  refine ⟨fun d q u hu => ?_, fun u hu => ?_, ?_, fun u x hu0 hx hc => ?_, fun q w n hw ha => ?_,
    fun u x q hx hq => ?_, fun q x q' hx hq => ?_, fun q w n hw => ?_, fun q w n hw => ?_⟩
  · have h0 := h.rq d q u hu
    have : u ≠ p := by obtain ⟨x, -, -, -, h1, -⟩ := h0; rintro rfl; rw [hk] at h1; cases h1
    exact RqOK.upd h0 hkp (fun y0 n0 h => by rw [hk] at h; cases h; exact ⟨_, hky, (by rw [hy'])⟩) this
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
    rw [specRt_eq (by rw [hkp a hap]; exact h1) h2 (by rw [hkp pa hpa]; exact h4) (h.ne _ _ _ h4 h5),
      specRt_eq (by rw [hkp b hbp]; exact g1) g2 (by rw [hkp pb hpb]; exact g4) (h.ne _ _ _ g4 g5)]
    rw [specRt_eq h1 h2 h4 (h.ne _ _ _ h4 h5), specRt_eq g1 g2 g4 (h.ne _ _ _ g4 g5)] at hab
    exact hab
  · have hx0 := htcb u x hx
    intro x' scp w n h1 h2 h3 h4 h5
    rw [hx] at h1; cases h1
    have hsp : scp ≠ p := fun e => hu0 (hown' u x hx0 (e ▸ h2))
    rw [hkp scp hsp] at h3
    exact h.rd u x hx0 hc x scp w n hx0 h2 h3 h4 h5
  · by_cases e : q = p
    · subst e; rw [hky] at hw; cases hw; exact hok ha
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
    · subst e; rw [hky] at hw; cases hw; exact fun _ => hne'
    · rw [hkp q e] at hw; exact h.ne q w n hw
  · by_cases e : q = p
    · subst e; rw [hky] at hw; cases hw; exact hrr
    · rw [hkp q e] at hw; exact h.rr q w n hw

end Spec

end

end Fl4Proofs.P3.Sched
