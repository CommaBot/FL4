/-
P3 (DESIGN.md §9), scheduling contexts: **the refill ring as a list**, for
`refill_budget_check`.

`RingAt s0 s sc n`: from `s0` to `s`, only the ring of `sc` (its head and
tail indices and refill slots, `RingW`) was written, and it is well formed.
The ring operations (`set_head`, `set_tail`, `add_tail`, `pop_head`,
`schedule_used`) keep `RingAt` and act on `L.refills` as list operations
(`schedUsedL` for `schedule_used`). `SchedRel.ringAt`: the relation for the
spec state with the SC's refills replaced.
-/
import Fl4Proofs.P3.ScHyps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- The words of `sc`'s ring: the head and tail indices and the slots. -/
def RingW (st : machine.Store S) [L : LawfulStore st] (s0 : S) (sc b : U64) : Prop :=
  b = headA sc ∨ b = tailA sc ∨ (sc.val + 96 ≤ b.val ∧ b.val < sc.val + 96 + 16 * (L.rmax s0 sc).val)

/-- Only `sc`'s ring changed since `s0`, and it is well formed. -/
structure RingAt (st : machine.Store S) [L : LawfulStore st] (s0 s : S) (sc : U64) (n : Nat) : Prop where
  w : WritesIn st s0 s (RingW st s0 sc)
  wf : RefillsWF st s sc (n + Fl4Spec.minSchedContextBits)
  mx : L.rmax s sc = L.rmax s0 sc

theorem RingAt.refl {s : S} {sc : U64} {n : Nat} (h : RefillsWF st s sc (n + Fl4Spec.minSchedContextBits)) : RingAt st s s sc n :=
  ⟨WritesIn.refl _ _, h, rfl⟩

theorem RingAt.putS {s0 s : S} {sc : U64} {n : Nat} (h : RingAt st s0 s sc n) {i : U64}
    (hi : i.val < (L.rmax s sc).val) (r : sporadic.Refill) : RingAt st s0 (L.putS s sc i r) sc n := by
  obtain ⟨-, -, -, -, -, hin⟩ := h.wf.inside
  obtain ⟨h1, h2, -⟩ := hin i hi
  obtain ⟨h8, -, -⟩ := h.wf.bounds
  have a1 : Aligned (rtA sc i) := by unfold Aligned; rw [h1]; omega
  have a2 : Aligned (raA sc i) := by unfold Aligned; rw [h2]; omega
  have w := (writesIn_wr (st := st) (s := s) (v := r.time) a1).trans
    (writesIn_wr (st := st) (s := L.wr s (rtA sc i) r.time) (v := r.amount) a2)
  have hm := h.mx
  refine ⟨(h.w.trans w).mono fun b hb => ?_, h.wf.putS hi, ?_⟩
  · rcases hb with hb | rfl | rfl
    · exact hb
    · right; right; rw [h1, ← hm]; omega
    · right; right; rw [h2, ← hm]; omega
  · rw [← hm]; exact rmax_putS h8 (by have := h.wf.bounds; omega)

theorem RingAt.wr_head {s0 s : S} {sc : U64} {n : Nat} (h : RingAt st s0 s sc n) {v : U64}
    (hv : v.val < (L.rmax s sc).val) : RingAt st s0 (L.wr s (headA sc) v) sc n := by
  obtain ⟨-, -, -, hh, -, -⟩ := h.wf.inside
  obtain ⟨h8, -, -⟩ := h.wf.bounds
  have ah : Aligned (headA sc) := by unfold Aligned; rw [hh]; omega
  exact ⟨(h.w.trans (writesIn_wr ah)).mono fun b hb => by rcases hb with hb | rfl; exact hb; exact Or.inl rfl,
    h.wf.wr_head hv, by rw [rmax_wr_head h8]; exact h.mx⟩

theorem RingAt.wr_tail {s0 s : S} {sc : U64} {n : Nat} (h : RingAt st s0 s sc n) {v : U64}
    (hv : v.val < (L.rmax s sc).val) : RingAt st s0 (L.wr s (tailA sc) v) sc n := by
  obtain ⟨-, -, -, -, ht, -⟩ := h.wf.inside
  obtain ⟨h8, -, -⟩ := h.wf.bounds
  have at' : Aligned (tailA sc) := by unfold Aligned; rw [ht]; omega
  exact ⟨(h.w.trans (writesIn_wr at')).mono fun b hb => by
      rcases hb with hb | rfl; exact hb; exact Or.inr (Or.inl rfl),
    h.wf.wr_tail hv, by rw [rmax_wr_tail h8]; exact h.mx⟩

/-! ## The list -/

/-- A default refill. -/
def zR : sporadic.Refill := ⟨0#u64, 0#u64⟩

theorem refills_tail_eq {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) :
    L.refill s sc (L.rtail s sc) = (L.refills s sc).getLastD zR := by
  unfold LawfulStore.refills
  obtain ⟨m, hm⟩ : ∃ m, L.size s sc = m + 1 := ⟨L.size s sc - 1, by have := hW.size_pos; omega⟩
  rw [hm, List.range_succ, List.map_append, List.map_singleton, List.getLastD_eq_getLast?,
    List.getLast?_append, List.getLast?_singleton]
  simp only [Option.some_or]
  rw [← hW.ix_last, hm, Nat.add_sub_cancel]; rfl

theorem refills_set_tail {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) (r : sporadic.Refill) :
    L.refills (L.putS s sc (L.rtail s sc) r) sc = (L.refills s sc).dropLast ++ [r] := by
  rw [refills_of (hW.size_putS hW.tail_lt) (fun k hk => hW.rf_set_tail (by have := hW.size_le; omega))]
  unfold LawfulStore.refills
  obtain ⟨m, hm⟩ : ∃ m, L.size s sc = m + 1 := ⟨L.size s sc - 1, by have := hW.size_pos; omega⟩
  rw [hm, List.range_succ, List.map_append, List.map_append, List.map_singleton, List.map_singleton,
    List.dropLast_concat, Nat.add_sub_cancel, if_pos rfl]
  congr 1
  exact List.map_congr_left fun k hk => by rw [if_neg (by have := List.mem_range.1 hk; omega)]

theorem refills_add {s s' : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    (hnf : L.size s sc < (L.rmax s sc).val) {r : sporadic.Refill} {nt : U64}
    (hnt : nt = nextIdx (L.rmax s sc) (L.rtail s sc)) (hs' : s' = L.putS (L.wr s (tailA sc) nt) sc nt r) :
    L.refills s' sc = L.refills s sc ++ [r] := by
  obtain ⟨hn, hrf, -, -⟩ := hW.add hnf hnt hs'
  rw [refills_of hn (fun k hk => hrf k (by omega))]
  unfold LawfulStore.refills
  rw [List.range_succ, List.map_append, List.map_singleton, if_pos rfl]
  congr 1
  exact List.map_congr_left fun k hk => by rw [if_neg (by have := List.mem_range.1 hk; omega)]

theorem refills_pop {s s' : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    (hne : L.rhead s sc ≠ L.rtail s sc)
    (hs' : s' = L.wr s (headA sc) (nextIdx (L.rmax s sc) (L.rhead s sc))) :
    L.refills s' sc = (L.refills s sc).tail := by
  obtain ⟨hn, hrf, -, -⟩ := hW.pop hne hs'
  rw [refills_of hn (fun k _ => hrf k)]
  unfold LawfulStore.refills
  obtain ⟨m, hm⟩ : ∃ m, L.size s sc = m + 1 := ⟨L.size s sc - 1, by have := hW.size_pos; omega⟩
  rw [hm, Nat.add_sub_cancel, List.range_succ_eq_map]
  simp [Function.comp]

/-! ## The ring operations -/

theorem set_head_ring {s0 s : S} {sc : U64} {n : Nat} (h : RingAt st s0 s sc n) (r : sporadic.Refill) :
    sporadic.set_head st s sc r ⦃ s' => RingAt st s0 s' sc n ∧ L.refills s' sc = r :: (L.refills s sc).tail ⦄ := by
  refine WP.spec_mono (sporadic.set_head.eq s sc r) ?_
  rintro s' rfl
  refine ⟨h.putS h.wf.head_lt r, ?_⟩
  rw [refills_of (h.wf.size_putS h.wf.head_lt) (fun k hk => h.wf.rf_set_head (by have := h.wf.size_le; omega)),
    refills_set_head h.wf]

theorem set_tail_ring {s0 s : S} {sc : U64} {n : Nat} (h : RingAt st s0 s sc n) (r : sporadic.Refill) :
    sporadic.set_tail st s sc r ⦃ s' => RingAt st s0 s' sc n ∧
      L.refills s' sc = (L.refills s sc).dropLast ++ [r] ⦄ := by
  refine WP.spec_mono (sporadic.set_tail.eq s sc r) ?_
  rintro s' rfl
  exact ⟨h.putS h.wf.tail_lt r, refills_set_tail h.wf r⟩

theorem add_tail_ring {s0 s : S} {sc : U64} {n : Nat} (h : RingAt st s0 s sc n)
    (hnf : L.size s sc < (L.rmax s sc).val) (r : sporadic.Refill) :
    sporadic.add_tail st s sc r ⦃ s' => RingAt st s0 s' sc n ∧ L.refills s' sc = L.refills s sc ++ [r] ⦄ := by
  refine WP.spec_mono (sporadic.add_tail.eq s sc r) ?_
  rintro s' rfl
  obtain ⟨h8, -, -⟩ := h.wf.bounds
  have h1 := h.wr_tail (v := nextIdx (L.rmax s sc) (L.rtail s sc)) (nextIdx_lt h.wf.tail_lt)
  exact ⟨h1.putS (by rw [rmax_wr_tail h8]; exact nextIdx_lt h.wf.tail_lt) r, refills_add h.wf hnf rfl rfl⟩

theorem pop_head_ring {s0 s : S} {sc : U64} {n : Nat} (h : RingAt st s0 s sc n)
    (hne : L.rhead s sc ≠ L.rtail s sc) :
    sporadic.pop_head st s sc ⦃ r s' => r = (L.refills s sc).headD zR ∧ RingAt st s0 s' sc n ∧
      L.refills s' sc = (L.refills s sc).tail ⦄ := by
  refine WP.spec_mono (sporadic.pop_head.eq s sc) ?_
  rintro ⟨r, s'⟩ ⟨rfl, rfl⟩
  refine ⟨?_, h.wr_head (nextIdx_lt h.wf.head_lt), refills_pop h.wf hne rfl⟩
  rw [refills_cons h.wf, ← rf0_eq h.wf]; rfl

/-- `schedule_used` on the list. -/
def schedUsedL (m : Nat) (rs : List sporadic.Refill) (new : sporadic.Refill) : List sporadic.Refill :=
  let t := rs.getLastD zR
  if new.time ≤ core.num.U64.wrapping_add t.time t.amount then
    rs.dropLast ++ [⟨t.time, core.num.U64.wrapping_add t.amount new.amount⟩]
  else if rs.length = m then
    rs.dropLast ++ [⟨core.num.U64.wrapping_sub new.time t.amount, core.num.U64.wrapping_add t.amount new.amount⟩]
  else rs ++ [new]

theorem schedule_used_ring {s0 s : S} {sc : U64} {n : Nat} (h : RingAt st s0 s sc n) (new : sporadic.Refill) :
    sporadic.schedule_used st s sc new ⦃ s' => RingAt st s0 s' sc n ∧
      L.refills s' sc = schedUsedL (L.rmax s sc).val (L.refills s sc) new ⦄ := by
  have hW := h.wf
  have htl := refills_tail_eq hW
  have hlen := refills_length (st := st) s sc
  unfold sporadic.schedule_used
  step as ⟨t, t_post⟩
  rw [htl] at t_post
  subst t_post
  step as ⟨i, i_post⟩
  split
  · rename_i hc
    step as ⟨i1, i1_post⟩
    refine WP.spec_mono (set_tail_ring h _) ?_
    rintro s' ⟨h', e⟩
    refine ⟨h', ?_⟩
    rw [e]; unfold schedUsedL
    rw [if_pos (by rw [← i_post]; exact hc), ← i1_post]
  · rename_i hc
    step as ⟨b, b_post⟩
    split
    · rename_i hb
      step as ⟨i1, i1_post⟩
      step as ⟨i2, i2_post⟩
      refine WP.spec_mono (set_tail_ring h _) ?_
      rintro s' ⟨h', e⟩
      refine ⟨h', ?_⟩
      rw [e]; unfold schedUsedL
      have hf : (L.refills s sc).length = (L.rmax s sc).val := by
        rw [hlen, ← hW.ringSize_val]; rw [b_post] at hb; have := of_decide_eq_true hb; rw [this]
      rw [if_neg (by rw [← i_post]; exact hc), if_pos hf, ← i1_post, ← i2_post]
    · rename_i hb
      have hnf : L.size s sc < (L.rmax s sc).val := by
        have := hW.size_le
        rw [b_post] at hb; have hne := of_decide_eq_false (by simpa using hb)
        rw [← hW.ringSize_val]
        have : (ringSize (L.rmax s sc) (L.rhead s sc) (L.rtail s sc)).val ≠ (L.rmax s sc).val :=
          fun e => hne e
        rw [hW.ringSize_val] at this ⊢; omega
      refine WP.spec_mono (add_tail_ring h hnf new) ?_
      rintro s' ⟨h', e⟩
      refine ⟨h', ?_⟩
      rw [e]; unfold schedUsedL
      rw [if_neg (by rw [← i_post]; exact hc), if_neg (by rw [hlen]; omega)]

/-! ## The relation after ring operations -/

theorem RingAt.hdr {s0 s : S} {sc : U64} {n : Nat} (h : RingAt st s0 s sc n) {K : U64} (hK : K.val < 80)
    (hK8 : K.val % 8 = 0) (hal : Aligned (scW sc K)) : L.mem s (scW sc K) = L.mem s0 (scW sc K) := by
  obtain ⟨h8, hb, hfit⟩ := h.wf.bounds
  obtain ⟨-, -, -, hh, ht, -⟩ := h.wf.inside
  have hv := scW_val (sc := sc) (K := K) (by omega)
  refine h.w.mem_eq hal ?_
  rintro (e | e | ⟨e1, -⟩)
  · have := congrArg UScalar.val e; rw [hv, hh] at this; omega
  · have := congrArg UScalar.val e; rw [hv, ht] at this; omega
  · rw [hv] at e1; omega

theorem headA_eq' (sc : U64) : headA sc = scW sc 80#u64 := by unfold headA scW layout.sc.REFILL_HEAD; rfl
theorem tailA_eq' (sc : U64) : tailA sc = scW sc 88#u64 := by unfold tailA scW layout.sc.REFILL_TAIL; rfl

/-- **A ring step is a `KFoot` step.** -/
theorem RingAt.kfoot {N T C : Set U64} {c : U64} {s0 s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s0 σ) {sc : U64} (hsc : sc ∈ C) {n : Nat} (h : RingAt st s0 s sc n) :
    WritesIn st s0 s (KFoot st T N C c s0 σ) :=
  h.w.mono fun b hb => by
    rcases hb with rfl | rfl | ⟨g1, g2⟩
    · rw [headA_eq']; exact KFoot.of_sw (sw_hdr hS hsc (by simp) (by simp) (by decide))
    · rw [tailA_eq']; exact KFoot.of_sw (sw_hdr hS hsc (by simp) (by simp) (by decide))
    · obtain ⟨Q, R, hc, hs⟩ := hS.lists
      obtain ⟨x, n', hk, hx⟩ := hs.scs sc hsc
      have hin : ScIn st s0 sc b := ⟨by omega, g2⟩
      refine KFoot.of_sw ⟨sc, hsc, x, n', hk, hx.in_obj hin, fun e => ?_⟩
      have hb := hx.bounds
      rw [e, scReplyA_eq', scW_val (by simp; omega)] at g1
      simp at g1

/-- **`SchedRel` after ring operations**: the spec's SC gets FL4's refills. -/
theorem SchedRel.ringAt {N T C : Set U64} {c : U64} {s0 s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s0 σ) {sc : U64} (hsc : sc ∈ C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc.bv = some (.schedContext x n)) (h : RingAt st s0 s sc n) :
    SchedRel st N T C c s (updSc σ sc.bv { x with scRefills := (L.refills s sc).map toRefill } n) ∧
      FootEq N T (L.mem s0) (L.mem s) ∧
      KView σ (updSc σ sc.bv { x with scRefills := (L.refills s sc).map toRefill } n) := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x', n', hk', hx⟩ := hs.scs sc hsc
  rw [hk] at hk'; cases hk'
  obtain ⟨h8, hb, hfit⟩ := h.wf.bounds
  have hm := h.mx
  have hhd : ∀ K : U64, K.val < 80 → K.val % 8 = 0 → L.mem s (scW sc K) = L.mem s0 (scW sc K) :=
    fun K h1 h2 => h.hdr h1 h2 (hx.hdr (by omega) h2).1
  have hwr : WritesIn st s0 s (ScIn st s0 sc) := by
    obtain ⟨-, -, -, hh, ht, -⟩ := h.wf.inside
    refine h.w.mono fun b hb' => ?_
    rcases hb' with rfl | rfl | ⟨e1, e2⟩
    · unfold ScIn; rw [hh, ← hm]; omega
    · unfold ScIn; rw [ht, ← hm]; omega
    · unfold ScIn; omega
  have hx' := hx.ring h.wf (fun K hK => hhd K (by rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    (by rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  exact ⟨hS.sc_update hsc hk (hwr.mono fun b hb => hx.in_obj hb) (hhd _ (by simp) (by simp)) _ hx', scin_footEq hS hsc hwr, KView.of_sc hk⟩

end

end

end Fl4Proofs.P3.Sched
