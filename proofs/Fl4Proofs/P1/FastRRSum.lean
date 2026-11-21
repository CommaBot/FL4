/-
# R4 of the accepted ReplyRecv fast path: `unblock_check` keeps a ready, sufficient head (FL4 #56, m65 (R-c))

`fastpath.reply_recv_found` checks `ready ∧ sufficient(usc, 0)` of the
receiver's SC at its entry state, before `do_reply_transfer`'s
`refill_unblock_check`; the general path (`do_reply_transfer`) checks them
after it. They agree when the merge loop does not wrap: `unblock_check` sets
the head's time to `now` (so it stays ready) and every merge adds the next
refill's amount to the head's (so the head's amount, which is what
`capacity(·, 0)` returns, never decreases). The amounts merged are distinct
ring entries, so the sum of the ring's amounts (`LawfulStore.amtSum`, l4v
`refills_sum`) bounds every partial sum: `amtSum < 2 ^ 64` is all that is
needed (`unblock_check_head`).

P1 does not carry a refill-sum bound (`RefillsWF` bounds the ring indices,
`SCA` asks only `RefillsWF` of an active SC). The spec side does: P3's
`SInvR.RV` / `SInvE.RPos` (l4v `valid_refills`: an active SC's amounts sum
below `2 ^ 64`, the configured budget) on the spec state. So the bound enters
the fast path as the narrow named premise `RRSum` [J] at the fast path's
entry state (see its docstring).
-/
import Fl4Proofs.P1.FastRR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- The merge loop's invariant for R4: a well-formed ring whose head starts at
`now`, holds at least `A`, and whose amounts sum below `2 ^ 64`. -/
def UbHead (s : S) (sc : obj.Sc) (sb : Nat) (now : U64) (A : Nat) : Prop :=
  RefillsWF st s sc sb ∧ (L.rf s sc 0).time = now ∧ A ≤ (L.rf s sc 0).amount.val ∧ L.amtSum s sc < 2 ^ 64

theorem sporadic.unblock_check_loop.head {s : S} {sc : obj.Sc} {sb : Nat} (now : U64) (A : Nat) (fuel : U64)
    (hI : UbHead (L := L) s sc sb now A) :
    sporadic.unblock_check_loop st s sc fuel ⦃ s' => UbHead (L := L) s' sc sb now A ⦄ := by
  unfold sporadic.unblock_check_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.val) (inv := fun x => UbHead (L := L) x.1 sc sb now A)
  · rintro ⟨x0, x1⟩ hI
    dsimp only at hI
    obtain ⟨hW, hhead, hA, hsum⟩ := hI
    unfold sporadic.unblock_check_loop.body
    step
    split
    · split
      · have hov : L.headOverlapping x0 sc = true := by simp_all
        have hne : L.rhead x0 sc ≠ L.rtail x0 sc := by
          intro e; simp [LawfulStore.headOverlapping, e] at hov
        have h2 := hW.size_two hne
        have hle := hW.size_le
        step
        step with sporadic.pop_head.eq
        step; step; step with sporadic.set_head.eq
        obtain ⟨hW2, hn2, hp2, hh1, hrf⟩ := hW.pop_set hne s1_post s2_post
        have e0 : old = L.rf x0 sc 0 := by rw [old_post, LawfulStore.rf, hW.ix_zero]
        have e1 : h = L.rf x0 sc 1 := by rw [h_post, hh1]
        have hs := sum_range_two (fun k => (L.rf x0 sc k).amount.val) h2
        unfold LawfulStore.amtSum at hsum; rw [hs] at hsum
        have hi : i.val = (L.rf x0 sc 1).amount.val + (L.rf x0 sc 0).amount.val := by
          rw [i_post, e1, e0, wadd_val (by omega)]
        have hR : ∀ k, k + 1 < L.size x0 sc →
            L.rf s2 sc k = if k = 0 then { old with amount := i } else L.rf x0 sc (k + 1) :=
          fun k hk => hrf k (by omega)
        refine ⟨⟨hW2, ?_, ?_, ?_⟩, by omega⟩
        · rw [hR 0 (by omega)]; simp only [ite_true]; rw [e0, hhead]
        · rw [hR 0 (by omega)]; simp only [ite_true]; rw [hi]; omega
        · unfold LawfulStore.amtSum
          rw [hn2, sum_range_one _ (by omega), hR 0 (by omega)]
          simp only [ite_true]
          have : ∀ k ∈ Finset.range (L.size x0 sc - 1 - 1),
              (L.rf s2 sc (k + 1)).amount.val = (L.rf x0 sc (k + 2)).amount.val := by
            intro k hk; simp at hk; rw [hR (k + 1) (by omega)]; simp
          rw [Finset.sum_congr rfl this, show L.size x0 sc - 1 - 1 = L.size x0 sc - 2 by omega]
          rw [hi]; omega
      · simp only [WP.spec_ok]; exact ⟨hW, hhead, hA, hsum⟩
    · simp only [WP.spec_ok]; exact ⟨hW, hhead, hA, hsum⟩
  · exact hI

/-- **R4, the ring part**: from a well-formed ring whose amounts sum below
`2 ^ 64` and whose head is ready, `refill_unblock_check` ends with a head that
is still ready at the entry state's current time and holds no less. -/
theorem sporadic.unblock_check.head {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    (hrep : Aligned (L.nodeA s layout.node.REPROGRAM) ∧ Outside (L.nodeA s layout.node.REPROGRAM) sc sb)
    (hsum : L.amtSum s sc < 2 ^ 64) (hrd : (L.rf s sc 0).time ≤ L.curTime s) :
    sporadic.unblock_check st s sc ⦃ s' => RefillsWF st s' sc sb ∧ (L.rf s' sc 0).time ≤ L.curTime s ∧
      (L.rf s sc 0).amount.val ≤ (L.rf s' sc 0).amount.val ⦄ := by
  unfold sporadic.unblock_check
  step
  split
  · simp only [WP.spec_ok]; exact ⟨hW, hrd, le_refl _⟩
  step
  split
  · step; step
    step with sporadic.set_head.eq
    step; step; step; step
    have hn1 := hW.size_pos
    have e0 : L.refill s sc (L.rhead s sc) = L.rf s sc 0 := by rw [LawfulStore.rf, hW.ix_zero]
    have hW1 : RefillsWF st s1 sc sb := by rw [s1_post]; exact hW.putS hW.head_lt
    have hn1' : L.size s1 sc = L.size s sc := by rw [s1_post, hW.size_putS hW.head_lt]
    have hrf1 : ∀ k, k < (L.rmax s sc).val →
        L.rf s1 sc k = if k = 0 then { h with time := now } else L.rf s sc k := by
      intro k hk; rw [s1_post]; exact hW.rf_set_head hk
    have ea : L.nodeAt s1 cpu layout.node.REPROGRAM = L.nodeA s layout.node.REPROGRAM := by
      rw [cpu_post, s1_post]; simp [LawfulStore.putS, LawfulStore.nodeA]
    rw [ea] at s2_post
    obtain ⟨hn2, hp2, hrf2⟩ := hW1.wr_out_view (v := 1#u64) hrep.1 hrep.2
    rw [← s2_post] at hn2 hp2 hrf2
    have hW2 : RefillsWF st s2 sc sb := by rw [s2_post]; exact hW1.wr_out hrep.1 hrep.2
    have hle := hW.size_le
    have hR : ∀ k, k < L.size s sc → L.rf s2 sc k = if k = 0 then { h with time := now } else L.rf s sc k :=
      fun k hk => by rw [hrf2]; exact hrf1 k (by omega)
    refine WP.spec_mono (sporadic.unblock_check_loop.head (L := L) (sb := sb) now (L.rf s sc 0).amount.val fuel ?_) ?_
    · refine ⟨hW2, ?_, ?_, ?_⟩
      · rw [hR 0 hn1]; rfl
      · rw [hR 0 hn1]; simp only [ite_true]; rw [h_post, e0]
      · unfold LawfulStore.amtSum
        rw [hn2, hn1']
        have : ∀ k ∈ Finset.range (L.size s sc),
            (L.rf s2 sc k).amount.val = (L.rf s sc k).amount.val := by
          intro k hk; simp at hk; rw [hR k hk]; split
          · rename_i hk0; subst hk0; show h.amount.val = _; rw [h_post, e0]
          · rfl
        rw [Finset.sum_congr rfl this]; exact hsum
    · rintro s3 ⟨hW3, ht3, hA3, -⟩
      refine ⟨hW3, ?_, hA3⟩
      simp only [ht3, now_post, le_refl]
  · simp only [WP.spec_ok]; exact ⟨hW, hrd, le_refl _⟩

theorem u64_sub0 (x : U64) : x - 0#u64 = ok x := by
  obtain ⟨z, hz, hv⟩ := spec_ex_fd (U64.sub_spec (x := x) (y := 0#u64) (by scalar_tac))
  rw [hz]; congr 1; apply UScalar.eq_of_val_eq; simp at hv; omega

/-- `ready` read at any state whose head starts no later than its current time. -/
theorem sporadic.ready_of {X : S} {sc : obj.Sc} (h : (L.refill X sc (L.rhead X sc)).time ≤ L.curTime X) :
    sporadic.ready st X sc = ok true := by
  rw [eq_of_spec_fd (sporadic.ready.spec (L := L) X sc)]; simp [h]

/-- `sufficient(·, 0)` is monotone in the head's amount (`capacity(·, 0)` is
the head's amount; `min_budget` reads only the Arch value). -/
theorem sporadic.sufficient_mono {A : Type _} {ar : machine.Arch A} {s X : S} {a : A} {sc : obj.Sc}
    (hs : sporadic.sufficient st ar s a sc 0#u64 = ok true)
    (hamt : (L.refill s sc (L.rhead s sc)).amount.val ≤ (L.refill X sc (L.rhead X sc)).amount.val) :
    sporadic.sufficient st ar X a sc 0#u64 = ok true := by
  unfold sporadic.sufficient sporadic.capacity at hs ⊢
  rw [eq_of_spec_fd (sporadic.head.spec (L := L) s sc)] at hs
  rw [eq_of_spec_fd (sporadic.head.spec (L := L) X sc)]
  have n0 : ∀ x : U64, ¬ (0#u64 > x) := fun x => by simp only [gt_iff_lt]; scalar_tac
  simp only [bind_ok, if_neg (n0 _), u64_sub0] at hs ⊢
  obtain ⟨mb, hmb, hs⟩ := bind_eq_ok hs
  rw [hmb]; simp only [bind_ok]
  have e := ok_inj_ff hs
  have e' : mb.val ≤ (L.refill s sc (L.rhead s sc)).amount.val := by simpa [UScalar.le_equiv] using e
  have : mb ≤ (L.refill X sc (L.rhead X sc)).amount := by simp only [UScalar.le_equiv]; omega
  simp [this]

/-- **R4**: with the ring's amounts summing below `2 ^ 64`, a head that is
ready at `s` is, after `refill_unblock_check`, still ready at `s`'s current
time and holds no less (both stated on the physical head, as `ready` /
`capacity` read it). -/
theorem unblock_check_r4 {s s' : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    (hrep : Aligned (L.nodeA s layout.node.REPROGRAM) ∧ Outside (L.nodeA s layout.node.REPROGRAM) sc sb)
    (hsum : L.amtSum s sc < 2 ^ 64) (hr : sporadic.ready st s sc = ok true)
    (hu : sporadic.unblock_check st s sc = ok s') :
    RefillsWF st s' sc sb ∧ (L.refill s' sc (L.rhead s' sc)).time ≤ L.curTime s ∧
      (L.refill s sc (L.rhead s sc)).amount.val ≤ (L.refill s' sc (L.rhead s' sc)).amount.val := by
  have e0 : L.refill s sc (L.rhead s sc) = L.rf s sc 0 := by rw [LawfulStore.rf, hW.ix_zero]
  have hrd : (L.rf s sc 0).time ≤ L.curTime s := by
    rw [eq_of_spec_fd (sporadic.ready.spec (L := L) s sc)] at hr
    rw [← e0]; simpa using ok_inj_ff hr
  have h := sporadic.unblock_check.head hW hrep hsum hrd
  rw [hu, WP.spec_ok] at h
  obtain ⟨hW', ht, ha⟩ := h
  have e1 : L.refill s' sc (L.rhead s' sc) = L.rf s' sc 0 := by rw [LawfulStore.rf, hW'.ix_zero]
  rw [e0, e1]; exact ⟨hW', ht, ha⟩

end

end Fl4Proofs.P1
