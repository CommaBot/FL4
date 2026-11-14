/-
P3 (DESIGN.md §9), scheduling contexts: **`sporadic::unblock_check`
refines l4v `refill_unblock_check`** (Sporadic_A), on related states
(`SchedRel`, whose `SchedSpec.scs` relates each SC of `C` by `ScRel1`):
round-robin SCs and SCs whose head refill is not ready are left alone;
otherwise the head is moved to the current time, `reprogram_timer` is set,
and the head is merged with the following refills while they overlap
(`refill_head_overlapping_loop`, a `whileLoop`, against FL4's loop with
fuel `REFILL_MAX + 1`, which never runs out).
-/
import Fl4Proofs.P3.ScKFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-! ## Words and lists -/

theorem u64_le_bv (a b : U64) : a ≤ b ↔ a.bv ≤ b.bv := by
  rw [UScalar.le_equiv, BitVec.le_def]; rfl

theorem refills_of {s : S} {sc : obj.Sc} {m : Nat} {g : Nat → sporadic.Refill} (hm : L.size s sc = m)
    (hg : ∀ k < m, L.rf s sc k = g k) : L.refills s sc = (List.range m).map g := by
  unfold LawfulStore.refills; rw [hm]
  exact List.map_congr_left fun k hk => hg k (List.mem_range.1 hk)

theorem refills_set_head {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) (r : sporadic.Refill) :
    (List.range (L.size s sc)).map (fun k => if k = 0 then r else L.rf s sc k) = r :: (L.refills s sc).tail := by
  rw [refills_cons hW]
  obtain ⟨m, hm⟩ : ∃ m, L.size s sc = m + 1 := ⟨L.size s sc - 1, by have := hW.size_pos; omega⟩
  rw [hm, List.range_succ_eq_map]; simp

theorem refills_pop_set {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) (h2 : 2 ≤ L.size s sc)
    (r : sporadic.Refill) :
    (List.range (L.size s sc - 1)).map (fun k => if k = 0 then r else L.rf s sc (k + 1)) =
      r :: (L.refills s sc).tail.tail := by
  unfold LawfulStore.refills
  obtain ⟨m, hm⟩ : ∃ m, L.size s sc = m + 2 := ⟨L.size s sc - 2, by omega⟩
  rw [hm, show m + 2 - 1 = m + 1 by omega, List.range_succ_eq_map, List.range_succ_eq_map]
  simp [List.range_succ_eq_map, Function.comp]

/-- Writing the head index and a refill slot stays within the SC's words. -/
theorem writesIn_putS {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) {i : U64}
    (hi : i.val < (L.rmax s sc).val) (r : sporadic.Refill) : WritesIn st s (L.putS s sc i r) (ScIn st s sc) := by
  obtain ⟨-, -, -, -, -, hin⟩ := hW.inside
  obtain ⟨h1, h2, -⟩ := hin i hi
  obtain ⟨h8, -, -⟩ := hW.bounds
  have a1 : Aligned (rtA sc i) := by unfold Aligned; rw [h1]; omega
  have a2 : Aligned (raA sc i) := by unfold Aligned; rw [h2]; omega
  have w := (writesIn_wr (st := st) (s := s) (v := r.time) a1).trans
    (writesIn_wr (st := st) (s := L.wr s (rtA sc i) r.time) (v := r.amount) a2)
  refine w.mono fun b hb => ?_
  rcases hb with rfl | rfl
  · unfold ScIn; rw [h1]; omega
  · unfold ScIn; rw [h2]; omega

theorem writesIn_head {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) (v : U64) :
    WritesIn st s (L.wr s (headA sc) v) (ScIn st s sc) := by
  obtain ⟨-, -, -, hh, -, -⟩ := hW.inside
  obtain ⟨h8, -, -⟩ := hW.bounds
  have := hW.min_le; simp at this
  refine (writesIn_wr (by unfold Aligned; rw [hh]; omega)).mono fun b hb => ?_
  subst hb; unfold ScIn; rw [hh]; omega

/-- The relation of an SC whose ring changed (header words other than the
ring indices unchanged). -/
theorem ScRel1.ring {s s' : S} {sc : obj.Sc} {x : Fl4Spec.SchedContext} {n : Nat} (h : ScRel1 st s sc x n)
    (hW : RefillsWF st s' sc n)
    (hw : ∀ K : U64, (K = 0#u64 ∨ K = 8#u64 ∨ K = 24#u64 ∨ K = 40#u64 ∨ K = 48#u64 ∨ K = 56#u64 ∨ K = 64#u64 ∨
      K = 72#u64) → L.mem s' (scW sc K) = L.mem s (scW sc K)) :
    ScRel1 st s' sc { x with scRefills := (L.refills s' sc).map toRefill } n := by
  have ep : L.rperiod s' sc = L.rperiod s sc := by
    simp only [LawfulStore.rperiod, periodA_eq]; exact hw _ (by simp)
  have em : L.rmax s' sc = L.rmax s sc := by
    simp only [LawfulStore.rmax, maxA_eq]; exact hw _ (by simp)
  exact ⟨hW, by rw [ep]; exact h.period, by rw [hw _ (by simp)]; exact h.consumed,
    by rw [hw _ (by simp)]; exact h.tcb, by rw [hw _ (by simp)]; exact h.ntfn,
    by rw [hw _ (by simp)]; exact h.badge, by rw [hw _ (by simp)]; exact h.yieldFrom,
    by rw [hw _ (by simp)]; exact h.sporadic, by rw [em]; exact h.max, rfl⟩

/-- Header words other than the ring indices, after writing the head index
and a ring slot. -/
theorem hdr_putS_head' {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) {i v : U64}
    (hi : i.val < (L.rmax s sc).val) (r : sporadic.Refill) (K : U64) (hKv : K.val < 80 ∧ K.val % 8 = 0) :
    L.mem (L.putS (L.wr s (headA sc) v) sc i r) (scW sc K) = L.mem s (scW sc K) ∧
      L.mem (L.putS s sc i r) (scW sc K) = L.mem s (scW sc K) := by
  obtain ⟨h8, hb, hfit⟩ := hW.bounds
  have := hW.min_le; simp at this
  obtain ⟨-, -, -, hh, -, hin⟩ := hW.inside
  obtain ⟨h1, h2, -⟩ := hin i hi
  have hv := scW_val (sc := sc) (K := K) (by omega)
  have ha : Aligned (scW sc K) := by unfold Aligned; rw [hv]; omega
  have a1 : Aligned (rtA sc i) := by unfold Aligned; rw [h1]; omega
  have a2 : Aligned (raA sc i) := by unfold Aligned; rw [h2]; omega
  have ah : Aligned (headA sc) := by unfold Aligned; rw [hh]; omega
  unfold LawfulStore.putS
  refine ⟨?_, ?_⟩
  · rw [L.mem_wr_ne a2 ha (by rw [h2, hv]; omega), L.mem_wr_ne a1 ha (by rw [h1, hv]; omega),
      L.mem_wr_ne ah ha (by rw [hh, hv]; omega)]
  · rw [L.mem_wr_ne a2 ha (by rw [h2, hv]; omega), L.mem_wr_ne a1 ha (by rw [h1, hv]; omega)]

theorem hdr_putS_head {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) {i v : U64}
    (hi : i.val < (L.rmax s sc).val) (r : sporadic.Refill) (K : U64)
    (hK : K = 0#u64 ∨ K = 8#u64 ∨ K = 24#u64 ∨ K = 40#u64 ∨ K = 48#u64 ∨ K = 56#u64 ∨ K = 64#u64 ∨ K = 72#u64) :
    L.mem (L.putS (L.wr s (headA sc) v) sc i r) (scW sc K) = L.mem s (scW sc K) ∧
      L.mem (L.putS s sc i r) (scW sc K) = L.mem s (scW sc K) :=
  hdr_putS_head' hW hi r K (by rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)

/-! ## The overlap test -/

theorem the_some {α : Type} [Nonempty α] (a : α) : Fl4Spec.the (some a) = a := rfl

theorem overlap_iff {s : S} {sc : obj.Sc} {n : Nat} (hW : RefillsWF st s sc n) {σ : Fl4Spec.State Unit}
    {x : Fl4Spec.SchedContext} (hk : σ.kheap sc.bv = some (.schedContext x n))
    (hx : x.scRefills = (L.refills s sc).map toRefill) :
    Fl4Spec.the (Fl4Spec.refillHeadOverlapping (Z := Unit) sc.bv σ) = true ↔ L.headOverlapping s sc = true := by
  rw [refillHeadOverlapping_eq hk, the_some, decide_eq_true_iff, hx, List.length_map, refills_length]
  unfold LawfulStore.headOverlapping
  by_cases e : L.rhead s sc = L.rtail s sc
  · have := (hW.single_iff).1 e
    simp [e, this]
  · have h2 := hW.size_two e
    have e0 : L.refill s sc (L.rhead s sc) = L.rf s sc 0 := (rf0_eq hW).symm
    have e1 : L.refill s sc (nextIdx (L.rmax s sc) (L.rhead s sc)) = L.rf s sc 1 := by
      rw [LawfulStore.rf]; congr 1; apply UScalar.eq_of_val_eq
      rw [nextIdx_val hW.head_lt, hW.ix_val]
    have hl : (L.refills s sc).map toRefill = toRefill (L.rf s sc 0) :: toRefill (L.rf s sc 1) ::
        ((List.range (L.size s sc - 2)).map (fun k => toRefill (L.rf s sc (k + 2)))) := by
      unfold LawfulStore.refills
      obtain ⟨m, hm⟩ : ∃ m, L.size s sc = m + 2 := ⟨L.size s sc - 2, by omega⟩
      rw [hm, List.range_succ_eq_map, List.range_succ_eq_map]
      simp [Function.comp]
    have hd : Fl4Spec.refillHd x = toRefill (L.rf s sc 0) := by unfold Fl4Spec.refillHd; rw [hx, hl]; rfl
    simp only [e, ite_false, e0, e1, decide_eq_true_iff, hd]
    rw [hl]
    simp only [List.tail_cons, List.head?_cons, the_some, toRefill, u64_le_bv,
      core.num.U64.wrapping_add_bv_eq, List.length_cons, List.length_map, List.length_range]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by omega, h⟩

theorem updSc_updSc (σ : Fl4Spec.State Unit) (p : Fl4Spec.ObjRef) (x y : Fl4Spec.SchedContext) (n m : Nat) :
    updSc (updSc σ p x n) p y m = updSc σ p y m := by
  simp [updK]

/-- The refills after `merge_overlapping_refills`. -/
def mergeHd (x : Fl4Spec.SchedContext) : List Fl4Spec.Refill :=
  Fl4Spec.mergeRefill (Fl4Spec.refillHd x) (Fl4Spec.the x.scRefills.tail.head?) :: x.scRefills.tail.tail

theorem merge_eq {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (hne : x.scRefills ≠ []) :
    Fl4Spec.mergeOverlappingRefills (Z := Unit) p σ =
      ({((), updSc σ p { x with scRefills := mergeHd x } n)}, False) := by
  unfold Fl4Spec.mergeOverlappingRefills
  rw [nd_bind_one (refillPopHead_eq hk hne)]
  rw [updateRefillHd_eq (x := { x with scRefills := x.scRefills.tail }) (n := n) (by simp [updK]), updSc_updSc]
  rfl

/-! ## The merge loop -/

theorem fuel_dec {f : U64} (h : f > 0#u64) : (f - 1#u64) ⦃ f1 => f1.val = f.val - 1 ⦄ := by
  step*

/-- **The merge loop** refines `refill_head_overlapping_loop`. -/
theorem unblock_loop_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) {sc : obj.Sc} (hsc : sc ∈ C) (fuel : U64)
    (hf : (∃ x n, σ.kheap sc.bv = some (.schedContext x n) ∧ ScRel1 st s sc x n ∧ L.size s sc ≤ fuel.val)) :
    sporadic.unblock_check_loop st s sc fuel ⦃ s' => ∃ σ', Fl4Spec.refillHeadOverlappingLoop (Z := Unit) sc.bv σ =
      ({((), σ')}, False) ∧ FootEq N T (L.mem s) (L.mem s') ∧ KView σ σ' ∧ SchedRel st N T C c s' σ' ⦄ := by
  unfold sporadic.unblock_check_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.val) (inv := fun x => ∃ σk xk n,
    σk.kheap sc.bv = some (.schedContext xk n) ∧ ScRel1 st x.1 sc xk n ∧ L.size x.1 sc ≤ x.2.val ∧
    SchedRel st N T C c x.1 σk ∧ Fl4Spec.refillHeadOverlappingLoop (Z := Unit) sc.bv σ =
      Fl4Spec.refillHeadOverlappingLoop (Z := Unit) sc.bv σk ∧ FootEq N T (L.mem s) (L.mem x.1) ∧ KView σ σk)
  · rintro ⟨sk, fk⟩ ⟨σk, xk, n, hk, hx, hsz, hSk, hloop, hfk, hvk⟩
    dsimp only at *
    have hW := hx.wf
    unfold sporadic.unblock_check_loop.body
    step
    by_cases hov : L.headOverlapping sk sc = true
    · rw [b_post, hov]
      simp only [↓reduceIte]
      have hne : L.rhead sk sc ≠ L.rtail sk sc := by
        intro e; simp [LawfulStore.headOverlapping, e] at hov
      have h2 := hW.size_two hne
      have hfp : fk > 0#u64 := by rw [gt_iff_val]; simp; omega
      simp only [hfp, ↓reduceIte]
      refine WP.spec_bind (fuel_dec hfp) ?_
      intro fk1 hfk1
      step with sporadic.pop_head.eq
      step
      step
      step with sporadic.set_head.eq
      obtain ⟨hW2, hn2, -, hh1, hrf⟩ := hW.pop_set hne s1_post s2_post
      have hne' : xk.scRefills ≠ [] := by rw [hx.refills]; exact refills_ne hW
      -- the new spec state
      set xk1 : Fl4Spec.SchedContext := { xk with scRefills := mergeHd xk }
      have hW1 : RefillsWF st s1 sc n := by rw [s1_post]; exact hW.wr_head (nextIdx_lt hW.head_lt)
      have hm1 : L.rmax s1 sc = L.rmax sk sc := by
        obtain ⟨h8, -, -⟩ := hW.bounds; rw [s1_post, rmax_wr_head h8]
      have hwr : WritesIn st sk s2 (ScIn st sk sc) := by
        have w1 := writesIn_head hW (nextIdx (L.rmax sk sc) (L.rhead sk sc))
        rw [← s1_post] at w1
        have w2 := writesIn_putS hW1 hW1.head_lt { old with amount := i }
        rw [← s2_post] at w2
        refine (w1.trans w2).mono fun b hb => ?_
        rcases hb with hb | hb
        · exact hb
        · exact hb.agree hm1.symm
      have hm2 : L.rmax s2 sc = L.rmax sk sc := by
        rw [← hm1]; obtain ⟨h8, -, -⟩ := hW1.bounds; have := hW1.head_lt
        rw [s2_post, rmax_putS h8 (by obtain ⟨-, hb, hfit⟩ := hW1.bounds; omega)]
      have hrs : L.refills s2 sc = { old with amount := i } :: (L.refills sk sc).tail.tail := by
        rw [refills_of hn2 (fun k hk => hrf k (by have := hW.size_le; omega)), refills_pop_set hW h2]
      have hx1 : ScRel1 st s2 sc xk1 n := by
        have hr := hx.ring hW2 (fun K hK => by
          rw [s2_post, s1_post]; exact (hdr_putS_head hW (by rw [← s1_post, ← hm1]; exact hW1.head_lt)
            _ K hK).1)
        have e : (L.refills s2 sc).map toRefill = xk1.scRefills := by
          rw [hrs]
          have e0 : old = L.rf sk sc 0 := by rw [old_post, rf0_eq hW]
          have e1 : h = L.rf sk sc 1 := by rw [h_post, hh1]
          simp only [xk1, mergeHd]
          rw [refillHd_eq hW hx.refills, hx.refills, refills_cons hW]
          obtain ⟨m, hm⟩ : ∃ m, L.size sk sc = m + 2 := ⟨L.size sk sc - 2, by omega⟩
          rw [hm, show m + 2 - 1 = m + 1 by omega, List.range_succ_eq_map]
          simp only [List.map_cons, List.map_map, List.tail_cons, List.head?_cons, the_some]
          rw [i_post, e0, e1]
          simp [toRefill, Fl4Spec.mergeRefill, core.num.U64.wrapping_add_bv_eq]
        have : xk1 = { xk with scRefills := (L.refills s2 sc).map toRefill } := by rw [e]
        rw [this]; exact hr
      have hS2 := hSk.sc_update hsc hk (hwr.mono fun b hb => hx.in_obj hb) (by
        rw [s2_post, s1_post]; exact (hdr_putS_head' hW (by rw [← s1_post, ← hm1]; exact hW1.head_lt) _ _
          (by simp)).1) xk1 hx1
      have hC : Fl4Spec.the (Fl4Spec.refillHeadOverlapping (Z := Unit) sc.bv σk) = true :=
        (overlap_iff hW hk hx.refills).2 hov
      have hB := merge_eq hk hne'
      refine ⟨⟨updSc σk sc.bv xk1 n, xk1, n, by simp [updK], hx1, ?_, hS2, ?_, ?_, ?_⟩, ?_⟩
      · rw [hn2, hfk1]; omega
      · rw [hloop]; unfold Fl4Spec.refillHeadOverlappingLoop; exact wl_step hC hB
      · exact FootEq.trans' hfk (scin_footEq hSk hsc hwr)
      · exact KView.trans hvk (KView.of_sc hk)
      · rw [hfk1]; omega
    · have hov' : L.headOverlapping sk sc = false := by simpa using hov
      rw [b_post, hov']
      simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      have hC : ¬ Fl4Spec.the (Fl4Spec.refillHeadOverlapping (Z := Unit) sc.bv σk) = true :=
        fun h => hov ((overlap_iff hW hk hx.refills).1 h)
      refine ⟨σk, ?_, hfk, hvk, hSk⟩
      rw [hloop]; unfold Fl4Spec.refillHeadOverlappingLoop; exact wl_done hC
  · obtain ⟨x, n, hk, hx, hsz⟩ := hf
    exact ⟨σ, x, n, hk, hx, hsz, hS, rfl, FootEq.rfl', KView.refl σ⟩

/-! ## `unblock_check` -/

theorem curTime_eq {T : Set U64} {c : U64} {s : S} {Q : U64 → List U64} {R : List U64}
    (hc : SchedCore st T c s Q R) : L.curTime s = nodeW st s c layout.node.CUR_TIME := by
  simp [LawfulStore.curTime, LawfulStore.nodeA, nodeW, hc.cur]

/-- The new head refill at time `t`. -/
def headAt (x : Fl4Spec.SchedContext) (t : Fl4Spec.Time) : List Fl4Spec.Refill :=
  { Fl4Spec.the x.scRefills.head? with rTime := t } :: x.scRefills.tail

/-- **`unblock_check` refines `refill_unblock_check`.** -/
theorem unblock_check_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) {sc : obj.Sc} (hsc : sc ∈ C) :
    sporadic.unblock_check st s sc ⦃ s' => ∃ σ', Fl4Spec.refillUnblockCheck (Z := Unit) sc.bv σ =
      ({((), σ')}, False) ∧ FootEq N T (L.mem s) (L.mem s') ∧ KView σ σ' ∧ SchedRel st N T C c s' σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
  have hW := hx.wf
  have hne : x.scRefills ≠ [] := by rw [hx.refills]; exact refills_ne hW
  have hrd : Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd x) =
      decide ((L.refill s sc (L.rhead s sc)).time ≤ L.curTime s) := by
    rw [refillHd_eq hW hx.refills, ← rf0_eq hW, curTime_eq hc, hs.curTime]
    unfold Fl4Spec.refillReady Fl4Spec.refillReady'
    simp only [toRefill]
    refine decide_eq_decide.2 ?_
    rw [u64_le_bv]
    exact iff_of_eq (congrArg (· ≤ _) (BitVec.add_zero _))
  have hrr : decide (x.scPeriod = 0) = decide (L.rperiod s sc = 0#u64) := by
    rw [hx.period]
    exact decide_eq_decide.2 ⟨fun h => eq_of_bv h, fun h => by rw [h]; rfl⟩
  have hspec0 : Fl4Spec.refillUnblockCheck (Z := Unit) sc.bv σ =
      (Fl4Spec.NonDet.when (decide ((L.refill s sc (L.rhead s sc)).time ≤ L.curTime s) = true ∧
        ¬ decide (L.rperiod s sc = 0#u64) = true) (do
          let ct ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curTime
          Fl4Spec.updateRefillHd sc.bv fun r => { r with rTime := ct }
          Fl4Spec.NonDet.modify fun s => { s with reprogramTimer := true }
          Fl4Spec.refillHeadOverlappingLoop sc.bv)) σ := by
    unfold Fl4Spec.refillUnblockCheck
    rw [nd_bind_one (isRoundRobin_eq hk), nd_bind_one (getScRefillReady_eq hk hne), hrd, hrr]
  unfold sporadic.unblock_check
  step
  by_cases hrob : L.rperiod s sc = 0#u64
  · have hb : b = true := by rw [b_post]; exact decide_eq_true hrob
    simp only [hb, ↓reduceIte, WP.spec_ok]
    refine ⟨σ, ?_, FootEq.rfl', KView.refl σ, hS⟩
    rw [hspec0]
    simp only [hrob, decide_true, not_true_eq_false, and_false, Fl4Spec.NonDet.when, ↓reduceIte]; rfl
  · have hb : b = false := by rw [b_post]; exact decide_eq_false hrob
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    step
    by_cases hready : (L.refill s sc (L.rhead s sc)).time ≤ L.curTime s
    · have hb1 : b1 = true := by rw [b1_post]; exact decide_eq_true hready
      simp only [hb1, ↓reduceIte]
      step
      step
      step with sporadic.set_head.eq
      step
      step
      step
      step
      -- s1: the head at `now`
      set r : sporadic.Refill := { h with time := now }
      have hW1 : RefillsWF st s1 sc n := by rw [s1_post]; exact hW.putS hW.head_lt
      have hm1 : L.rmax s1 sc = L.rmax s sc := by
        obtain ⟨h8, hb', hfit⟩ := hW.bounds; have := hW.head_lt
        rw [s1_post, rmax_putS h8 (by omega)]
      have hsz1 : L.size s1 sc = L.size s sc := by rw [s1_post, hW.size_putS hW.head_lt]
      have hrs1 : L.refills s1 sc = r :: (L.refills s sc).tail := by
        have e := refills_of (g := fun k => if k = 0 then r else L.rf s sc k) hsz1 (fun k hk => by
          subst s1_post; exact hW.rf_set_head (by have := hW.size_le; omega))
        rw [e, refills_set_head hW]
      set x1 : Fl4Spec.SchedContext := { x with scRefills := headAt x σ.curTime }
      have hx1 : ScRel1 st s1 sc x1 n := by
        have hr := hx.ring hW1 (fun K hK => by rw [s1_post]; exact (hdr_putS_head hW (v := 0#u64) hW.head_lt _ K hK).2)
        have e : (L.refills s1 sc).map toRefill = x1.scRefills := by
          simp only [x1, headAt]
          rw [hrs1, hx.refills, refills_cons hW]
          simp only [List.map_cons, List.tail_cons, List.head?_cons, the_some, r]
          rw [now_post, h_post, ← rf0_eq hW, curTime_eq hc, hs.curTime]; rfl
        have : x1 = { x with scRefills := (L.refills s1 sc).map toRefill } := by rw [e]
        rw [this]; exact hr
      have hwr1 : WritesIn st s s1 (ScIn st s sc) := by rw [s1_post]; exact writesIn_putS hW hW.head_lt r
      have hS1 := hS.sc_update hsc hk (hwr1.mono fun b hb => hx.in_obj hb) (by
        rw [s1_post]; exact (hdr_putS_head' hW (v := 0#u64) hW.head_lt _ _ (by simp)).2) x1 hx1
      -- s2: `REPROGRAM`
      have hc1 := hS1.lists.choose_spec.choose_spec.1.cur
      have hcpu : cpu = c := by rw [cpu_post]; exact hc1
      rw [hcpu] at s2_post
      obtain ⟨hS2, hf2, -⟩ := hS1.set_reprogram
      rw [← s2_post] at hS2 hf2
      set σ2 := { updSc σ sc.bv x1 n with reprogramTimer := true }
      have hk2 : σ2.kheap sc.bv = some (.schedContext x1 n) := by simp [σ2, updK]
      obtain ⟨Q2, R2, hc2, hs2⟩ := hS2.lists
      obtain ⟨x2, n2, hk2', hx2⟩ := hs2.scs sc hsc
      rw [hk2] at hk2'; cases hk2'
      have hfuel : L.size s2 sc ≤ fuel.val := by
        have := hx2.wf.size_le; have := hx2.wf.le_abs; have := absMax_lt n
        rw [fuel_post, wadd_val (by rw [i_post]; simp; omega), i_post]; simp; omega
      refine WP.spec_mono (unblock_loop_refines s2 σ2 hS2 hsc fuel ⟨x1, n, hk2, hx2, hfuel⟩) ?_
      rintro s' ⟨σ', hl, hf3, hv3, hS3⟩
      refine ⟨σ', ?_, FootEq.trans' (FootEq.trans' (scin_footEq hS hsc hwr1) hf2) hf3,
        KView.trans (KView.trans (KView.of_sc hk) (KView.of_kheap rfl)) hv3, hS3⟩
      rw [hspec0]
      simp only [hready, hrob, decide_true, decide_false, Bool.false_eq_true, not_false_eq_true, and_self,
        Fl4Spec.NonDet.when, ↓reduceIte]
      rw [nd_gets_bind, nd_bind_one (updateRefillHd_eq hk _)]
      rw [nd_bind_one (m := Fl4Spec.NonDet.modify fun s : Fl4Spec.State Unit => { s with reprogramTimer := true })
        rfl]
      exact hl
    · have hb1 : b1 = false := by rw [b1_post]; exact decide_eq_false hready
      simp only [hb1, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine ⟨σ, ?_, FootEq.rfl', KView.refl σ, hS⟩
      rw [hspec0]
      simp only [hready, decide_false, Bool.false_eq_true, false_and, Fl4Spec.NonDet.when, ↓reduceIte]; rfl

end

end

end Fl4Proofs.P3.Sched
