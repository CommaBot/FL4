/-
P1 (DESIGN.md §9): the refill ring of a scheduling context (sporadic.rs)
stays well formed.

The invariant follows l4v's `valid_refills` (DetSchedInvs_AI
`cfg_valid_refills`, `sp_valid_refills`; SchedContextInv_AI
`ordered_disjoint`, `no_overflow`), restricted to what FL4 stores (no
budget):

* `RefillsWF st s sc sb`, the structural part: the SC at `sc` is a
  `2 ^ sb`-byte object, aligned and not wrapping (`Placed`),
  `MIN_REFILLS ≤ refill_max ≤ refill_absolute_max sb`, and head and tail
  index the ring. Established by `refill_new` and `refill_update`, preserved
  by every operation on the ring, `refill_budget_check` and
  `refill_unblock_check`.
* `RefillsOrdered st s sc`, the ordering part for periodic SCs, on the
  refills `rf 0, ..., rf (size - 1)` from head to tail:
  `ordered_disjoint`, `no_overflow` and `window`. Established by
  `refill_new` and `refill_update` (periodic), preserved by
  `refill_unblock_check`, `schedule_used`, both loops of
  `refill_budget_check`, and `refill_budget_check` itself when there is no
  overrun; side conditions bound times away from overflow as l4v's
  `MAX_RELEASE_TIME` / `MAX_PERIOD` assumptions do.

Memory is a `LawfulStore` (Store.lean). The only word outside the SC that
the refill code writes is the current core's `REPROGRAM` (unblock_check);
the only ones it reads are the current core's `CUR_TIME` and `CUR_SC`.
Theorems that need these not to lie inside the SC say so.
-/
import Fl4Proofs.P1.Store
import Fl4Proofs.P0.Consts
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-! ## Addresses of the scheduling context fields (layout.rs `sc`) -/

def periodA (sc : obj.Sc) : U64 := core.num.U64.wrapping_add sc layout.sc.PERIOD
def maxA (sc : obj.Sc) : U64 := core.num.U64.wrapping_add sc layout.sc.REFILL_MAX
def headA (sc : obj.Sc) : U64 := core.num.U64.wrapping_add sc layout.sc.REFILL_HEAD
def tailA (sc : obj.Sc) : U64 := core.num.U64.wrapping_add sc layout.sc.REFILL_TAIL
/-- Address of refill `i`'s `time` word (`Sc::refill_addr`). -/
def rtA (sc : obj.Sc) (i : U64) : U64 :=
  core.num.U64.wrapping_add (core.num.U64.wrapping_add sc layout.sc.REFILLS)
    (core.num.U64.wrapping_mul i layout.sc.REFILL_SIZE)
/-- Address of refill `i`'s `amount` word. -/
def raA (sc : obj.Sc) (i : U64) : U64 := core.num.U64.wrapping_add (rtA sc i) 8#u64

/-- `next_index` on a ring of `m` refills. -/
def nextIdx (m i : U64) : U64 :=
  if i = core.num.U64.wrapping_sub m 1#u64 then 0#u64 else core.num.U64.wrapping_add i 1#u64

/-- Close an address side condition: alignment or distinctness of field
addresses, from linear facts about `sc` and the indices in the context. -/
macro "addr" : tactic => `(tactic| (simp [Aligned, periodA, maxA, headA, tailA, rtA, raA,
    core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def,
    UScalarTy.U64_numBits_eq, U64.numBits] <;> omega))

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-! ## The stored fields, as functions of the state -/

def LawfulStore.rperiod (s : S) (sc : obj.Sc) : U64 := L.mem s (periodA sc)
def LawfulStore.rmax (s : S) (sc : obj.Sc) : U64 := L.mem s (maxA sc)
def LawfulStore.rhead (s : S) (sc : obj.Sc) : U64 := L.mem s (headA sc)
def LawfulStore.rtail (s : S) (sc : obj.Sc) : U64 := L.mem s (tailA sc)
def LawfulStore.refill (s : S) (sc : obj.Sc) (i : U64) : sporadic.Refill :=
  { time := L.mem s (rtA sc i), amount := L.mem s (raA sc i) }
/-- The state after `put s sc i r`. -/
def LawfulStore.putS (s : S) (sc : obj.Sc) (i : U64) (r : sporadic.Refill) : S :=
  L.wr (L.wr s (rtA sc i) r.time) (raA sc i) r.amount
/-- The address of word `off` of core `cpu`'s node (`node_base`: the
nodes start at `ks::NODES` = 13568 and are `node::SIZE` = 4288 bytes). -/
def LawfulStore.nodeAt (s : S) (cpu off : U64) : U64 :=
  core.num.U64.wrapping_add
    (core.num.U64.wrapping_add (core.num.U64.wrapping_add (L.ksb s) 13568#u64)
      (core.num.U64.wrapping_mul cpu 4288#u64)) off
/-- The address of word `off` of the current core's node. -/
def LawfulStore.nodeA (s : S) (off : U64) : U64 := L.nodeAt s (L.cpu s) off
def LawfulStore.curTime (s : S) : U64 := L.mem s (L.nodeA s layout.node.CUR_TIME)

/-! ## Specs of the accessors -/

@[step] theorem obj.Sc.period.spec (s : S) (sc : obj.Sc) :
    obj.Sc.period st sc s ⦃ v => v = L.rperiod s sc ⦄ := by
  unfold obj.Sc.period; step*; simp_all [LawfulStore.rperiod, periodA]
@[step] theorem obj.Sc.refill_max.spec (s : S) (sc : obj.Sc) :
    obj.Sc.refill_max st sc s ⦃ v => v = L.rmax s sc ⦄ := by
  unfold obj.Sc.refill_max; step*; simp_all [LawfulStore.rmax, maxA]
@[step] theorem obj.Sc.refill_head.spec (s : S) (sc : obj.Sc) :
    obj.Sc.refill_head st sc s ⦃ v => v = L.rhead s sc ⦄ := by
  unfold obj.Sc.refill_head; step*; simp_all [LawfulStore.rhead, headA]
@[step] theorem obj.Sc.refill_tail.spec (s : S) (sc : obj.Sc) :
    obj.Sc.refill_tail st sc s ⦃ v => v = L.rtail s sc ⦄ := by
  unfold obj.Sc.refill_tail; step*; simp_all [LawfulStore.rtail, tailA]

@[step] theorem obj.Sc.set_period.spec (s : S) (sc : obj.Sc) (v : U64) :
    obj.Sc.set_period st sc s v ⦃ s' => s' = L.wr s (periodA sc) v ⦄ := by
  unfold obj.Sc.set_period; step*; simp_all [periodA]
@[step] theorem obj.Sc.set_refill_max.spec (s : S) (sc : obj.Sc) (v : U64) :
    obj.Sc.set_refill_max st sc s v ⦃ s' => s' = L.wr s (maxA sc) v ⦄ := by
  unfold obj.Sc.set_refill_max; step*; simp_all [maxA]
@[step] theorem obj.Sc.set_refill_head.spec (s : S) (sc : obj.Sc) (v : U64) :
    obj.Sc.set_refill_head st sc s v ⦃ s' => s' = L.wr s (headA sc) v ⦄ := by
  unfold obj.Sc.set_refill_head; step*; simp_all [headA]
@[step] theorem obj.Sc.set_refill_tail.spec (s : S) (sc : obj.Sc) (v : U64) :
    obj.Sc.set_refill_tail st sc s v ⦃ s' => s' = L.wr s (tailA sc) v ⦄ := by
  unfold obj.Sc.set_refill_tail; step*; simp_all [tailA]

@[step] theorem obj.Sc.refill_addr.spec (sc : obj.Sc) (i : U64) :
    obj.Sc.refill_addr sc i ⦃ a => a = rtA sc i ⦄ := by
  unfold obj.Sc.refill_addr; step*; simp_all [rtA]
@[step] theorem obj.Sc.r_time.spec (s : S) (sc : obj.Sc) (i : U64) :
    obj.Sc.r_time st sc s i ⦃ v => v = L.mem s (rtA sc i) ⦄ := by
  unfold obj.Sc.r_time; step*; simp_all
@[step] theorem obj.Sc.r_amount.spec (s : S) (sc : obj.Sc) (i : U64) :
    obj.Sc.r_amount st sc s i ⦃ v => v = L.mem s (raA sc i) ⦄ := by
  unfold obj.Sc.r_amount; step*; simp_all [raA]
@[step] theorem obj.Sc.set_r_time.spec (s : S) (sc : obj.Sc) (i v : U64) :
    obj.Sc.set_r_time st sc s i v ⦃ s' => s' = L.wr s (rtA sc i) v ⦄ := by
  unfold obj.Sc.set_r_time; step*; simp_all
@[step] theorem obj.Sc.set_r_amount.spec (s : S) (sc : obj.Sc) (i v : U64) :
    obj.Sc.set_r_amount st sc s i v ⦃ s' => s' = L.wr s (raA sc i) v ⦄ := by
  unfold obj.Sc.set_r_amount; step*; simp_all [raA]

@[step] theorem sporadic.get.spec (s : S) (sc : obj.Sc) (i : U64) :
    sporadic.get st s sc i ⦃ r => r = L.refill s sc i ⦄ := by
  unfold sporadic.get; step*; simp_all [LawfulStore.refill]
@[step] theorem sporadic.put.spec (s : S) (sc : obj.Sc) (i : U64) (r : sporadic.Refill) :
    sporadic.put st s sc i r ⦃ s' => s' = L.putS s sc i r ⦄ := by
  unfold sporadic.put; step*; simp_all [LawfulStore.putS]
@[step] theorem sporadic.head.spec (s : S) (sc : obj.Sc) :
    sporadic.head st s sc ⦃ r => r = L.refill s sc (L.rhead s sc) ⦄ := by
  unfold sporadic.head; step*; simp_all
@[step] theorem sporadic.tail.spec (s : S) (sc : obj.Sc) :
    sporadic.tail st s sc ⦃ r => r = L.refill s sc (L.rtail s sc) ⦄ := by
  unfold sporadic.tail; step*; simp_all
@[step] theorem sporadic.next_index.spec (s : S) (sc : obj.Sc) (i : U64) :
    sporadic.next_index st s sc i ⦃ n => n = nextIdx (L.rmax s sc) i ⦄ := by
  unfold sporadic.next_index; step* <;> subst_vars <;> simp_all [nextIdx]

end

/-! ## The structural invariant -/

/-- `refill_absolute_max` (sporadic.rs) on naturals. -/
def absMax (sb : Nat) : Nat := if 64 ≤ sb then 0 else (2 ^ sb - 96) / 16

theorem absMax_lt (sb : Nat) : absMax sb < 2 ^ 60 := by
  unfold absMax; split
  · simp
  · have : 2 ^ sb ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- The SC object at `sc` has `2 ^ sb` bytes, is aligned to its size and
does not wrap around the address space. -/
structure Placed (sc : obj.Sc) (sb : Nat) : Prop where
  lt64 : sb < 64
  align : sc.val % 2 ^ sb = 0
  fits : sc.val + 2 ^ sb ≤ 2 ^ 64

/-- `absMax` is what the kernel computes. -/
theorem sporadic.refill_absolute_max.spec (sb : U64) :
    sporadic.refill_absolute_max sb ⦃ r => r.val = absMax sb.val ⦄ := by
  unfold sporadic.refill_absolute_max
  step*
  · simp [absMax]; scalar_tac
  all_goals
    have hlt : sb.val < 64 := by scalar_tac
    have hi : i.val = sb.val := by
      rw [i_post, UScalar.val_and]
      have := Nat.and_two_pow_sub_one_eq_mod sb.val 6
      simp only [show (2 : Nat) ^ 6 - 1 = 63 from rfl] at this
      rw [show (63#u64).val = 63 from rfl, this]; omega
    have hb : bytes.val = 2 ^ sb.val := by
      rw [bytes_post, hi, Nat.one_shiftLeft, U64.size_def]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by simpa [U64.numBits] using hlt))
    simp only [absMax, show ¬ 64 ≤ sb.val by omega, ite_false]
  · simp only [UScalar.lt_equiv] at *; simp at *; omega
  · simp only [UScalar.lt_equiv] at *; simp at *; omega

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- The structural part of l4v's `valid_refills` (`cfg_valid_refills`) on
what FL4 stores: the ring size is between `MIN_REFILLS` and what fits in
the object, and head and tail index the ring. -/
structure RefillsWF (st : machine.Store S) [L : LawfulStore st] (s : S) (sc : obj.Sc) (sb : Nat) : Prop where
  placed : Placed sc sb
  min_le : sporadic.MIN_REFILLS.val ≤ (L.rmax s sc).val
  le_abs : (L.rmax s sc).val ≤ absMax sb
  head_lt : (L.rhead s sc).val < (L.rmax s sc).val
  tail_lt : (L.rtail s sc).val < (L.rmax s sc).val

/-- The linear facts about addresses that follow from placement and a ring
size `m` (`MIN_REFILLS ≤ m ≤ absMax sb`). -/
theorem Placed.bounds {sc : obj.Sc} {sb m : Nat} (hP : Placed sc sb) (h2 : 2 ≤ m)
    (hm : m ≤ absMax sb) :
    sc.val % 8 = 0 ∧ 96 + 16 * m ≤ 2 ^ sb ∧ sc.val + 2 ^ sb ≤ 2 ^ 64 := by
  have hlt := hP.lt64
  have habs : absMax sb = (2 ^ sb - 96) / 16 := by simp [absMax]; omega
  rw [habs] at hm
  have h128 : 128 ≤ 2 ^ sb := by omega
  have h7 : 7 ≤ sb := by
    by_contra hc
    have : 2 ^ sb ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨?_, by omega, hP.fits⟩
  have hd : 8 ∣ 2 ^ sb := by
    have : 2 ^ sb = 2 ^ 3 * 2 ^ (sb - 3) := by rw [← Nat.pow_add]; congr 1; omega
    rw [this]; exact Dvd.dvd.mul_right (by norm_num) _
  have := hP.align
  rw [← Nat.mod_mod_of_dvd sc.val hd, this]

theorem RefillsWF.bounds {s : S} {sc : obj.Sc} {sb : Nat} (h : RefillsWF st s sc sb) :
    sc.val % 8 = 0 ∧ 96 + 16 * (L.rmax s sc).val ≤ 2 ^ sb ∧ sc.val + 2 ^ sb ≤ 2 ^ 64 :=
  h.placed.bounds (by simpa using h.min_le) h.le_abs

/-- Every word the refill code touches lies inside the object: the header
(`PERIOD` .. `REFILL_TAIL`) and both words of each refill of the ring. -/
theorem RefillsWF.inside {s : S} {sc : obj.Sc} {sb : Nat} (h : RefillsWF st s sc sb) :
    sc.val + 96 ≤ sc.val + 2 ^ sb ∧ (periodA sc).val = sc.val ∧ (maxA sc).val = sc.val + 72 ∧
    (headA sc).val = sc.val + 80 ∧ (tailA sc).val = sc.val + 88 ∧
    ∀ i : U64, i.val < (L.rmax s sc).val →
      (rtA sc i).val = sc.val + 96 + 16 * i.val ∧ (raA sc i).val = sc.val + 104 + 16 * i.val ∧
      (raA sc i).val + 8 ≤ sc.val + 2 ^ sb := by
  obtain ⟨h8, hm, hfit⟩ := h.bounds
  have := h.min_le; simp at this
  refine ⟨by omega, by addr, by addr, by addr, by addr, fun i hi => ⟨by addr, by addr, by addr⟩⟩

/-! Writing a refill leaves the header alone. -/

section hdr
variable {s : S} {sc : obj.Sc} {i : U64} {r : sporadic.Refill}
  (h8 : sc.val % 8 = 0) (hi : sc.val + 96 + 16 * i.val + 16 ≤ 2 ^ 64)
include h8 hi

theorem rmax_putS : L.rmax (L.putS s sc i r) sc = L.rmax s sc := by
  unfold LawfulStore.rmax LawfulStore.putS
  rw [L.mem_wr_ne, L.mem_wr_ne] <;> addr
theorem rhead_putS : L.rhead (L.putS s sc i r) sc = L.rhead s sc := by
  unfold LawfulStore.rhead LawfulStore.putS
  rw [L.mem_wr_ne, L.mem_wr_ne] <;> addr
theorem rtail_putS : L.rtail (L.putS s sc i r) sc = L.rtail s sc := by
  unfold LawfulStore.rtail LawfulStore.putS
  rw [L.mem_wr_ne, L.mem_wr_ne] <;> addr
theorem rperiod_putS : L.rperiod (L.putS s sc i r) sc = L.rperiod s sc := by
  unfold LawfulStore.rperiod LawfulStore.putS
  rw [L.mem_wr_ne, L.mem_wr_ne] <;> addr
end hdr

theorem RefillsWF.putS {s : S} {sc : obj.Sc} {sb : Nat} {i : U64} {r : sporadic.Refill}
    (h : RefillsWF st s sc sb) (hi : i.val < (L.rmax s sc).val) :
    RefillsWF st (L.putS s sc i r) sc sb := by
  obtain ⟨h8, hm, hfit⟩ := h.bounds
  have hi' : sc.val + 96 + 16 * i.val + 16 ≤ 2 ^ 64 := by omega
  have := h.min_le; have := h.le_abs; have := h.head_lt; have := h.tail_lt
  exact ⟨h.placed, by rwa [rmax_putS h8 hi'], by rwa [rmax_putS h8 hi'],
    by rwa [rmax_putS h8 hi', rhead_putS h8 hi'],
    by rwa [rmax_putS h8 hi', rtail_putS h8 hi']⟩


/-! Header reads after header writes. -/

section hdrw
variable {s : S} {sc : obj.Sc} {v : U64} (h8 : sc.val % 8 = 0)
include h8

theorem rmax_wr_head : L.rmax (L.wr s (headA sc) v) sc = L.rmax s sc := by
  unfold LawfulStore.rmax; rw [L.mem_wr_ne] <;> addr
theorem rtail_wr_head : L.rtail (L.wr s (headA sc) v) sc = L.rtail s sc := by
  unfold LawfulStore.rtail; rw [L.mem_wr_ne] <;> addr
theorem rhead_wr_head : L.rhead (L.wr s (headA sc) v) sc = v := by
  unfold LawfulStore.rhead; rw [L.mem_wr_same]; addr
theorem rperiod_wr_head : L.rperiod (L.wr s (headA sc) v) sc = L.rperiod s sc := by
  unfold LawfulStore.rperiod; rw [L.mem_wr_ne] <;> addr
theorem rmax_wr_tail : L.rmax (L.wr s (tailA sc) v) sc = L.rmax s sc := by
  unfold LawfulStore.rmax; rw [L.mem_wr_ne] <;> addr
theorem rhead_wr_tail : L.rhead (L.wr s (tailA sc) v) sc = L.rhead s sc := by
  unfold LawfulStore.rhead; rw [L.mem_wr_ne] <;> addr
theorem rtail_wr_tail : L.rtail (L.wr s (tailA sc) v) sc = v := by
  unfold LawfulStore.rtail; rw [L.mem_wr_same]; addr
theorem rperiod_wr_tail : L.rperiod (L.wr s (tailA sc) v) sc = L.rperiod s sc := by
  unfold LawfulStore.rperiod; rw [L.mem_wr_ne] <;> addr
theorem rmax_wr_max : L.rmax (L.wr s (maxA sc) v) sc = v := by
  unfold LawfulStore.rmax; rw [L.mem_wr_same]; addr
theorem rhead_wr_max : L.rhead (L.wr s (maxA sc) v) sc = L.rhead s sc := by
  unfold LawfulStore.rhead; rw [L.mem_wr_ne] <;> addr
theorem rtail_wr_max : L.rtail (L.wr s (maxA sc) v) sc = L.rtail s sc := by
  unfold LawfulStore.rtail; rw [L.mem_wr_ne] <;> addr
theorem rperiod_wr_max : L.rperiod (L.wr s (maxA sc) v) sc = L.rperiod s sc := by
  unfold LawfulStore.rperiod; rw [L.mem_wr_ne] <;> addr
theorem rmax_wr_period : L.rmax (L.wr s (periodA sc) v) sc = L.rmax s sc := by
  unfold LawfulStore.rmax; rw [L.mem_wr_ne] <;> addr
theorem rhead_wr_period : L.rhead (L.wr s (periodA sc) v) sc = L.rhead s sc := by
  unfold LawfulStore.rhead; rw [L.mem_wr_ne] <;> addr
theorem rtail_wr_period : L.rtail (L.wr s (periodA sc) v) sc = L.rtail s sc := by
  unfold LawfulStore.rtail; rw [L.mem_wr_ne] <;> addr
theorem rperiod_wr_period : L.rperiod (L.wr s (periodA sc) v) sc = v := by
  unfold LawfulStore.rperiod; rw [L.mem_wr_same]; addr
end hdrw

/-- The invariant only depends on the three header words. -/
theorem RefillsWF.of_hdr {s s' : S} {sc : obj.Sc} {sb : Nat} (h : RefillsWF st s sc sb)
    (hm : L.rmax s' sc = L.rmax s sc) (hh : (L.rhead s' sc).val < (L.rmax s sc).val)
    (ht : (L.rtail s' sc).val < (L.rmax s sc).val) : RefillsWF st s' sc sb :=
  ⟨h.placed, hm ▸ h.min_le, hm ▸ h.le_abs, hm ▸ hh, hm ▸ ht⟩

theorem RefillsWF.wr_head {s : S} {sc : obj.Sc} {sb : Nat} {v : U64} (h : RefillsWF st s sc sb)
    (hv : v.val < (L.rmax s sc).val) : RefillsWF st (L.wr s (headA sc) v) sc sb := by
  obtain ⟨h8, hm, hfit⟩ := h.bounds
  have hf : sc.val + 128 ≤ 2 ^ 64 := by have := h.min_le; simp at this; omega
  refine h.of_hdr (rmax_wr_head h8) ?_ ?_
  · rw [rhead_wr_head h8]; exact hv
  · rw [rtail_wr_head h8]; exact h.tail_lt

theorem RefillsWF.wr_tail {s : S} {sc : obj.Sc} {sb : Nat} {v : U64} (h : RefillsWF st s sc sb)
    (hv : v.val < (L.rmax s sc).val) : RefillsWF st (L.wr s (tailA sc) v) sc sb := by
  obtain ⟨h8, hm, hfit⟩ := h.bounds
  have hf : sc.val + 128 ≤ 2 ^ 64 := by have := h.min_le; simp at this; omega
  refine h.of_hdr (rmax_wr_tail h8) ?_ ?_
  · rw [rhead_wr_tail h8]; exact h.head_lt
  · rw [rtail_wr_tail h8]; exact hv

theorem RefillsWF.wr_period {s : S} {sc : obj.Sc} {sb : Nat} {v : U64} (h : RefillsWF st s sc sb) :
    RefillsWF st (L.wr s (periodA sc) v) sc sb := by
  obtain ⟨h8, hm, hfit⟩ := h.bounds
  have hf : sc.val + 128 ≤ 2 ^ 64 := by have := h.min_le; simp at this; omega
  refine h.of_hdr (rmax_wr_period h8) ?_ ?_
  · rw [rhead_wr_period h8]; exact h.head_lt
  · rw [rtail_wr_period h8]; exact h.tail_lt

/-- Resetting the ring to one refill at index 0 of a ring of `m`. -/
theorem RefillsWF.reset {s : S} {sc : obj.Sc} {sb : Nat} {m : U64} (hP : Placed sc sb)
    (h2 : sporadic.MIN_REFILLS.val ≤ m.val) (hm : m.val ≤ absMax sb) :
    RefillsWF st (L.wr (L.wr (L.wr s (headA sc) 0#u64) (tailA sc) 0#u64) (maxA sc) m) sc sb := by
  simp at h2
  obtain ⟨h8, hm', hfit⟩ := hP.bounds h2 hm
  have hf : sc.val + 128 ≤ 2 ^ 64 := by omega
  refine ⟨hP, ?_, ?_, ?_, ?_⟩ <;>
    simp only [rmax_wr_max h8, rhead_wr_max h8, rtail_wr_max h8, rhead_wr_tail h8,
      rtail_wr_tail h8, rhead_wr_head h8] <;> (try simp) <;> omega

/-- A write outside the object preserves the invariant. -/
theorem RefillsWF.wr_out {s : S} {sc : obj.Sc} {sb : Nat} {a v : U64} (h : RefillsWF st s sc sb)
    (ha : Aligned a) (hout : a.val < sc.val ∨ sc.val + 2 ^ sb ≤ a.val) :
    RefillsWF st (L.wr s a v) sc sb := by
  obtain ⟨h8, hm, hfit⟩ := h.bounds
  have := h.min_le; simp at this
  have e : ∀ b, Aligned b → sc.val ≤ b.val → b.val < sc.val + 96 → L.mem (L.wr s a v) b = L.mem s b :=
    fun b hb h1 h2 => L.mem_wr_ne ha hb (by omega)
  have em : L.rmax (L.wr s a v) sc = L.rmax s sc := e _ (by addr) (by addr) (by addr)
  refine h.of_hdr em ?_ ?_
  · rw [show L.rhead (L.wr s a v) sc = L.rhead s sc from e _ (by addr) (by addr) (by addr)]
    exact h.head_lt
  · rw [show L.rtail (L.wr s a v) sc = L.rtail s sc from e _ (by addr) (by addr) (by addr)]
    exact h.tail_lt

theorem nextIdx_lt {m i : U64} (hi : i.val < m.val) : (nextIdx m i).val < m.val := by
  have hm : m.val < 2 ^ 64 := by scalar_tac
  unfold nextIdx
  split
  · simp; omega
  · rename_i hne
    have : i.val ≠ m.val - 1 := by
      intro h'; apply hne; apply UScalar.eq_of_val_eq
      simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits] at h' ⊢; omega
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega


/-! ## Specs of the read-only helpers -/

/-- `size` on a ring of `m` with head `h` and tail `t`. -/
def ringSize (m h t : U64) : U64 :=
  if h ≤ t then core.num.U64.wrapping_add (core.num.U64.wrapping_sub t h) 1#u64
  else core.num.U64.wrapping_add (core.num.U64.wrapping_add t 1#u64) (core.num.U64.wrapping_sub m h)

@[step] theorem obj.node_get.spec (s : S) (cpu off : U64) :
    obj.node_get st s cpu off ⦃ v => v = L.mem s (L.nodeAt s cpu off) ⦄ := by
  unfold obj.node_get obj.node_base; step*; simp_all [LawfulStore.nodeAt]
@[step] theorem obj.node_set.spec (s : S) (cpu off v : U64) :
    obj.node_set st s cpu off v ⦃ s' => s' = L.wr s (L.nodeAt s cpu off) v ⦄ := by
  unfold obj.node_set obj.node_base; step*; simp_all [LawfulStore.nodeAt]
@[step] theorem sporadic.cur_time.spec (s : S) :
    sporadic.cur_time st s ⦃ t => t = L.curTime s ⦄ := by
  unfold sporadic.cur_time; step*; simp_all [LawfulStore.curTime, LawfulStore.nodeA]
@[step] theorem sporadic.single.spec (s : S) (sc : obj.Sc) :
    sporadic.single st s sc ⦃ b => b = decide (L.rhead s sc = L.rtail s sc) ⦄ := by
  unfold sporadic.single; step*
@[step] theorem sporadic.is_round_robin.spec (s : S) (sc : obj.Sc) :
    sporadic.is_round_robin st s sc ⦃ b => b = decide (L.rperiod s sc = 0#u64) ⦄ := by
  unfold sporadic.is_round_robin; step*
@[step] theorem sporadic.ready.spec (s : S) (sc : obj.Sc) :
    sporadic.ready st s sc ⦃ b => b = decide ((L.refill s sc (L.rhead s sc)).time ≤ L.curTime s) ⦄ := by
  unfold sporadic.ready; step*
@[step] theorem sporadic.size.spec (s : S) (sc : obj.Sc) :
    sporadic.size st s sc ⦃ v => v = ringSize (L.rmax s sc) (L.rhead s sc) (L.rtail s sc) ⦄ := by
  unfold sporadic.size; step* <;> subst_vars <;> simp_all [ringSize]
@[step] theorem sporadic.full.spec (s : S) (sc : obj.Sc) :
    sporadic.full st s sc ⦃ b => b = decide (ringSize (L.rmax s sc) (L.rhead s sc) (L.rtail s sc) = L.rmax s sc) ⦄ := by
  unfold sporadic.full; step*

/-! ## The ring operations preserve the invariant -/

section ops
variable {s : S} {sc : obj.Sc} {sb : Nat}

@[step] theorem sporadic.set_head.wf (r : sporadic.Refill) (h : RefillsWF st s sc sb) :
    sporadic.set_head st s sc r ⦃ s' => RefillsWF st s' sc sb ⦄ := by
  unfold sporadic.set_head; step*; subst_vars; exact h.putS h.head_lt

@[step] theorem sporadic.set_tail.wf (r : sporadic.Refill) (h : RefillsWF st s sc sb) :
    sporadic.set_tail st s sc r ⦃ s' => RefillsWF st s' sc sb ⦄ := by
  unfold sporadic.set_tail; step*; subst_vars; exact h.putS h.tail_lt

@[step] theorem sporadic.pop_head.wf (h : RefillsWF st s sc sb) :
    sporadic.pop_head st s sc ⦃ _ s' => RefillsWF st s' sc sb ⦄ := by
  unfold sporadic.pop_head; step*; subst_vars
  exact h.wr_head (nextIdx_lt h.head_lt)

@[step] theorem sporadic.add_tail.wf (r : sporadic.Refill) (h : RefillsWF st s sc sb) :
    sporadic.add_tail st s sc r ⦃ s' => RefillsWF st s' sc sb ⦄ := by
  unfold sporadic.add_tail; step*; subst_vars
  have h1 := h.wr_tail (v := nextIdx (L.rmax s sc) (L.rtail s sc)) (nextIdx_lt h.tail_lt)
  obtain ⟨h8, -, -⟩ := h.bounds
  refine h1.putS ?_
  rw [rmax_wr_tail h8]; exact nextIdx_lt h.tail_lt

@[step] theorem sporadic.maybe_add_empty_tail.wf (h : RefillsWF st s sc sb) :
    sporadic.maybe_add_empty_tail st s sc ⦃ s' => RefillsWF st s' sc sb ⦄ := by
  unfold sporadic.maybe_add_empty_tail; step*

@[step] theorem sporadic.schedule_used.wf (r : sporadic.Refill) (h : RefillsWF st s sc sb) :
    sporadic.schedule_used st s sc r ⦃ s' => RefillsWF st s' sc sb ⦄ := by
  unfold sporadic.schedule_used; step*

/-- `refill_new` establishes the invariant, given a ring size in range. -/
theorem sporadic.refill_new.wf (max_refills budget period : U64) (hP : Placed sc sb)
    (h2 : sporadic.MIN_REFILLS.val ≤ max_refills.val) (hm : max_refills.val ≤ absMax sb) :
    sporadic.refill_new st s sc max_refills budget period ⦃ s' => RefillsWF st s' sc sb ⦄ := by
  unfold sporadic.refill_new
  step; step; step; step
  have hW : RefillsWF st s4 sc sb := by subst_vars; exact RefillsWF.reset hP h2 hm
  step; step
  have hW5 : RefillsWF st s5 sc sb := by
    subst s5; refine hW.putS ?_; have := hW.min_le; simp at this ⊢; omega
  step*

/-- `refill_update` establishes the invariant for the new ring size, whatever
the old state of the ring. -/
theorem sporadic.refill_update.wf (new_period new_budget new_max_refills : U64) (hP : Placed sc sb)
    (h2 : sporadic.MIN_REFILLS.val ≤ new_max_refills.val) (hm : new_max_refills.val ≤ absMax sb) :
    sporadic.refill_update st s sc new_period new_budget new_max_refills
      ⦃ s' => RefillsWF st s' sc sb ⦄ := by
  unfold sporadic.refill_update
  step; step; step; step; step
  have hW4 : RefillsWF st s4 sc sb := by subst_vars; exact RefillsWF.reset hP h2 hm
  step
  have hW5 : RefillsWF st s5 sc sb := by subst s5; exact hW4.wr_period
  step*
  split <;> step*

@[step] theorem sporadic.budget_check_loop0.wf (mrt period usage fuel : U64) (h : RefillsWF st s sc sb) :
    sporadic.budget_check_loop0 st s sc mrt period usage fuel ⦃ s' _ => RefillsWF st s' sc sb ⦄ := by
  unfold sporadic.budget_check_loop0
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val) (inv := fun x => RefillsWF st x.1 sc sb)
  · rintro ⟨x0, x1, x2⟩ hx
    unfold sporadic.budget_check_loop0.body
    step*
    split <;> step*
    p0_cases_prod; step*
  · exact h

@[step] theorem sporadic.budget_check_loop1.wf (mb fuel2 : U64) (h : RefillsWF st s sc sb) :
    sporadic.budget_check_loop1 st s sc mb fuel2 ⦃ s' => RefillsWF st s' sc sb ⦄ := by
  unfold sporadic.budget_check_loop1
  apply loop.spec_decr_nat (measure := fun x => x.2.val) (inv := fun x => RefillsWF st x.1 sc sb)
  · rintro ⟨x0, x1⟩ hx
    unfold sporadic.budget_check_loop1.body
    step*
  · exact h

/-- `head_overlapping`, as a function of the state. -/
def LawfulStore.headOverlapping (s : S) (sc : obj.Sc) : Bool :=
  if L.rhead s sc = L.rtail s sc then false
  else
    let h := L.refill s sc (L.rhead s sc)
    decide ((L.refill s sc (nextIdx (L.rmax s sc) (L.rhead s sc))).time ≤
      core.num.U64.wrapping_add h.time h.amount)

@[step] theorem sporadic.head_overlapping.spec (s : S) (sc : obj.Sc) :
    sporadic.head_overlapping st s sc ⦃ b => b = L.headOverlapping s sc ⦄ := by
  unfold sporadic.head_overlapping; step* <;> simp_all [LawfulStore.headOverlapping]

@[step] theorem sporadic.unblock_check_loop.wf (fuel : U64) (h : RefillsWF st s sc sb) :
    sporadic.unblock_check_loop st s sc fuel ⦃ s' => RefillsWF st s' sc sb ⦄ := by
  unfold sporadic.unblock_check_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.val) (inv := fun x => RefillsWF st x.1 sc sb)
  · rintro ⟨x0, x1⟩ hx
    unfold sporadic.unblock_check_loop.body
    step*
  · exact h

theorem sporadic.set_head.eq (s : S) (sc : obj.Sc) (r : sporadic.Refill) :
    sporadic.set_head st s sc r ⦃ s' => s' = L.putS s sc (L.rhead s sc) r ⦄ := by
  unfold sporadic.set_head; step*; simp_all

@[simp] theorem nodeAt_wr (s : S) (a v cpu off : U64) : L.nodeAt (L.wr s a v) cpu off = L.nodeAt s cpu off := by
  simp [LawfulStore.nodeAt]
@[simp] theorem nodeA_wr (s : S) (a v off : U64) : L.nodeA (L.wr s a v) off = L.nodeA s off := by
  simp [LawfulStore.nodeA, LawfulStore.nodeAt]
@[simp] theorem nodeA_putS (s : S) (sc : obj.Sc) (i : U64) (r : sporadic.Refill) off :
    L.nodeA (L.putS s sc i r) off = L.nodeA s off := by
  simp [LawfulStore.putS]

/-- `a` is outside the SC object. -/
def Outside (a : U64) (sc : obj.Sc) (sb : Nat) : Prop := a.val < sc.val ∨ sc.val + 2 ^ sb ≤ a.val

/-- `refill_unblock_check` preserves the invariant, if the current core's
`REPROGRAM` word (which it sets) is not inside the SC. -/
theorem sporadic.unblock_check.wf (hW : RefillsWF st s sc sb)
    (hrep : Aligned (L.nodeA s layout.node.REPROGRAM) ∧ Outside (L.nodeA s layout.node.REPROGRAM) sc sb) :
    sporadic.unblock_check st s sc ⦃ s' => RefillsWF st s' sc sb ⦄ := by
  unfold sporadic.unblock_check
  step
  split
  · simpa using hW
  step
  split
  · step; step
    step with sporadic.set_head.eq
    have hW1 : RefillsWF st s1 sc sb := by subst s1; exact hW.putS hW.head_lt
    step; step
    have hW2 : RefillsWF st s2 sc sb := by
      have e : L.nodeAt s1 cpu layout.node.REPROGRAM = L.nodeA s layout.node.REPROGRAM := by
        subst_vars; simp [LawfulStore.putS, LawfulStore.nodeA]
      subst s2; rw [e]; exact hW1.wr_out hrep.1 hrep.2
    step*
  · simpa using hW

@[step] theorem sporadic.max_release_time.ok {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (a : A) :
    sporadic.max_release_time ar a ⦃ _ => True ⦄ := by
  unfold sporadic.max_release_time sporadic.max_period_us; step*
@[step] theorem sporadic.min_budget.ok {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (a : A) :
    sporadic.min_budget ar a ⦃ _ => True ⦄ := by
  unfold sporadic.min_budget; step*

/-- `refill_budget_check` preserves the invariant of the current SC. -/
theorem sporadic.budget_check.wf {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (a : A)
    (usage : U64) (h : RefillsWF st s sc sb) (hcur : L.mem s (L.nodeA s layout.node.CUR_SC) = sc) :
    sporadic.budget_check st ar s a usage ⦃ s' => RefillsWF st s' sc sb ⦄ := by
  unfold sporadic.budget_check
  step; step
  have e : i1 = sc := by subst i_post i1_post; exact hcur
  subst e
  step*
  split
  · split <;> step*
  · step*

end ops


end

/-! ## The ring as a sequence

The refills of the ring, oldest first, are `rf 0, ..., rf (n - 1)` where
`n` is the ring's size (`sporadic::size`) and `rf k` is the refill at
physical index `(head + k) % max`. -/

/-- The number of refills of a ring of `m` with head `h` and tail `t`. -/
def ringN (m h t : Nat) : Nat := if h ≤ t then t - h + 1 else t + 1 + m - h

/-- A natural number as a `u64` (wrapping). -/
def u64 (x : Nat) : U64 := ⟨BitVec.ofNat 64 x⟩

theorem u64_val {x : Nat} (h : x < 2 ^ 64) : (u64 x).val = x := by
  show (BitVec.ofNat 64 x).toNat = x
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem mod_lt2 {x m : Nat} (h : x < 2 * m) : x % m = if x < m then x else x - m := by
  split
  · exact Nat.mod_eq_of_lt (by assumption)
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem wsub_val {x y : U64} (h : y.val ≤ x.val) : (core.num.U64.wrapping_sub x y).val = x.val - y.val := by
  have hx : x.val < 2 ^ 64 := by scalar_tac
  simp only [core.num.U64.wrapping_sub_val_eq, UScalar.size_UScalarTyU64, U64.size_def, U64.numBits,
    UScalarTy.U64_numBits_eq]
  rw [mod_lt2 (by omega)]; split <;> omega

theorem wadd_val {x y : U64} (h : x.val + y.val < 2 ^ 64) :
    (core.num.U64.wrapping_add x y).val = x.val + y.val := by
  simp only [core.num.U64.wrapping_add_val_eq, UScalar.size_UScalarTyU64, U64.size_def, U64.numBits,
    UScalarTy.U64_numBits_eq]
  exact Nat.mod_eq_of_lt h

section ring
variable {m h t : Nat} (hh : h < m) (ht : t < m)
include hh ht
set_option linter.unusedSectionVars false

theorem ringN_pos : 1 ≤ ringN m h t := by unfold ringN; split <;> omega
theorem ringN_le : ringN m h t ≤ m := by unfold ringN; split <;> omega
/-- The tail is the last refill. -/
theorem ringN_tail : (h + (ringN m h t - 1)) % m = t := by
  unfold ringN; rw [mod_lt2 (by split <;> omega)]; split <;> split <;> omega
/-- Physical indices of distinct refills are distinct. -/
theorem idx_inj {k₁ k₂ : Nat} (h₁ : k₁ < m) (h₂ : k₂ < m) (e : (h + k₁) % m = (h + k₂) % m) :
    k₁ = k₂ := by
  rw [mod_lt2 (by omega), mod_lt2 (by omega)] at e; split at e <;> split at e <;> omega
/-- After popping the head (of a ring with more than one refill). -/
theorem ringN_pop (hne : h ≠ t) : ringN m ((h + 1) % m) t = ringN m h t - 1 := by
  unfold ringN; rw [mod_lt2 (by omega)]; split <;> split <;> split <;> omega
/-- After adding a tail (to a ring that is not full). -/
theorem ringN_add (hnf : ringN m h t < m) : ringN m h ((t + 1) % m) = ringN m h t + 1 := by
  revert hnf; unfold ringN; rw [mod_lt2 (by omega)]; split <;> split <;> split <;> omega
theorem idx_add : (h + ringN m h t) % m = (t + 1) % m := by
  have e := ringN_tail hh ht
  have := ringN_pos hh ht
  rw [show h + ringN m h t = (h + (ringN m h t - 1)) + 1 by omega, Nat.add_mod, e]
  conv_rhs => rw [Nat.add_mod, Nat.mod_eq_of_lt ht]
end ring

theorem nextIdx_val {m i : U64} (hi : i.val < m.val) : (nextIdx m i).val = (i.val + 1) % m.val := by
  have hm : m.val < 2 ^ 64 := by scalar_tac
  unfold nextIdx
  split
  · rename_i he
    have := congrArg UScalar.val he
    simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits] at this
    have hi' : i.val + 1 = m.val := by omega
    rw [hi', Nat.mod_self]; rfl
  · rename_i hne
    have : i.val ≠ m.val - 1 := by
      intro h'; apply hne; apply UScalar.eq_of_val_eq
      simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits] at h' ⊢; omega
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

def LawfulStore.size (s : S) (sc : obj.Sc) : Nat :=
  ringN (L.rmax s sc).val (L.rhead s sc).val (L.rtail s sc).val
/-- Physical index of the `k`-th refill. -/
def LawfulStore.ix (s : S) (sc : obj.Sc) (k : Nat) : U64 :=
  u64 (((L.rhead s sc).val + k) % (L.rmax s sc).val)
/-- The `k`-th refill of the ring, oldest first. -/
def LawfulStore.rf (s : S) (sc : obj.Sc) (k : Nat) : sporadic.Refill := L.refill s sc (L.ix s sc k)
/-- The ring as a list, as in l4v's `sc_refills`. -/
def LawfulStore.refills (s : S) (sc : obj.Sc) : List sporadic.Refill :=
  (List.range (L.size s sc)).map (L.rf s sc)

theorem RefillsWF.ix_val {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) (k : Nat) :
    (L.ix s sc k).val = ((L.rhead s sc).val + k) % (L.rmax s sc).val := by
  have hm : (L.rmax s sc).val < 2 ^ 64 := by scalar_tac
  have := hW.min_le; simp at this
  exact u64_val (lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hm.le)

/-- Reading a refill after writing one, by physical index. -/
theorem RefillsWF.refill_putS {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    {i j : U64} {r : sporadic.Refill} (hi : i.val < (L.rmax s sc).val) (hj : j.val < (L.rmax s sc).val) :
    L.refill (L.putS s sc j r) sc i = if i.val = j.val then r else L.refill s sc i := by
  obtain ⟨h8, hm, hfit⟩ := hW.bounds
  unfold LawfulStore.refill LawfulStore.putS
  rw [L.mem_wr_val (by addr) (by addr), L.mem_wr_val (by addr) (by addr),
    L.mem_wr_val (by addr) (by addr), L.mem_wr_val (by addr) (by addr)]
  have e1 : (raA sc j).val = (rtA sc i).val ↔ False := by simp only [iff_false]; addr
  have e2 : (rtA sc j).val = (raA sc i).val ↔ False := by simp only [iff_false]; addr
  have e3 : (rtA sc j).val = (rtA sc i).val ↔ i.val = j.val := by
    constructor
    · intro he; simp [rtA, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq,
        U64.size_def, U64.numBits] at he; omega
    · intro; addr
  have e4 : (raA sc j).val = (raA sc i).val ↔ i.val = j.val := by
    constructor
    · intro he; simp [raA, rtA, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq,
        U64.size_def, U64.numBits] at he; omega
    · intro; addr
  simp only [e1, e2, e3, e4, ite_false]
  split <;> rfl


/-! Header writes leave the refills alone. -/

theorem RefillsWF.refill_wr_hdr {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    {a v i : U64} (ha : a = periodA sc ∨ a = maxA sc ∨ a = headA sc ∨ a = tailA sc)
    (hi : i.val < (L.rmax s sc).val) : L.refill (L.wr s a v) sc i = L.refill s sc i := by
  obtain ⟨h8, hm, hfit⟩ := hW.bounds
  unfold LawfulStore.refill
  rcases ha with rfl | rfl | rfl | rfl <;>
    rw [L.mem_wr_ne (by addr) (by addr) (by addr), L.mem_wr_ne (by addr) (by addr) (by addr)]

theorem RefillsWF.ix_lt {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) (k : Nat) :
    (L.ix s sc k).val < (L.rmax s sc).val := by
  rw [hW.ix_val]; have := hW.min_le; simp at this; exact Nat.mod_lt _ (by omega)

theorem RefillsWF.ix_zero {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) :
    L.ix s sc 0 = L.rhead s sc := by
  apply UScalar.eq_of_val_eq; rw [hW.ix_val, Nat.add_zero, Nat.mod_eq_of_lt hW.head_lt]

theorem RefillsWF.ix_last {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) :
    L.ix s sc (L.size s sc - 1) = L.rtail s sc := by
  apply UScalar.eq_of_val_eq; rw [hW.ix_val]; exact ringN_tail hW.head_lt hW.tail_lt

theorem RefillsWF.size_pos {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) :
    1 ≤ L.size s sc := ringN_pos hW.head_lt hW.tail_lt
theorem RefillsWF.size_le {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) :
    L.size s sc ≤ (L.rmax s sc).val := ringN_le hW.head_lt hW.tail_lt

/-- Writing the `k₀`-th refill. -/
theorem RefillsWF.rf_putS {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    {k₀ k : Nat} {r : sporadic.Refill} (hk₀ : k₀ < (L.rmax s sc).val) (hk : k < (L.rmax s sc).val) :
    L.rf (L.putS s sc (L.ix s sc k₀) r) sc k = if k = k₀ then r else L.rf s sc k := by
  obtain ⟨h8, -, -⟩ := hW.bounds
  have hix : L.ix (L.putS s sc (L.ix s sc k₀) r) sc k = L.ix s sc k := by
    have hj := hW.ix_lt k₀
    have hi' : sc.val + 96 + 16 * (L.ix s sc k₀).val + 16 ≤ 2 ^ 64 := by
      obtain ⟨-, hm, hfit⟩ := hW.bounds; omega
    generalize L.ix s sc k₀ = j at hi' ⊢
    simp only [LawfulStore.ix, rhead_putS h8 hi', rmax_putS h8 hi']
  unfold LawfulStore.rf; rw [hix, hW.refill_putS (hW.ix_lt k) (hW.ix_lt k₀)]
  rw [hW.ix_val, hW.ix_val]
  by_cases e : k = k₀
  · subst e; simp
  · have : ¬ ((L.rhead s sc).val + k) % (L.rmax s sc).val = ((L.rhead s sc).val + k₀) % (L.rmax s sc).val :=
      fun h' => e (idx_inj hW.head_lt hW.tail_lt hk hk₀ h')
    simp [this, e]

/-- `put` at the head index. -/
theorem RefillsWF.rf_set_head {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    {k : Nat} {r : sporadic.Refill} (hk : k < (L.rmax s sc).val) :
    L.rf (L.putS s sc (L.rhead s sc) r) sc k = if k = 0 then r else L.rf s sc k := by
  rw [← hW.ix_zero]; exact hW.rf_putS (by have := hW.head_lt; omega) hk

/-- `put` at the tail index. -/
theorem RefillsWF.rf_set_tail {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    {k : Nat} {r : sporadic.Refill} (hk : k < (L.rmax s sc).val) :
    L.rf (L.putS s sc (L.rtail s sc) r) sc k = if k = L.size s sc - 1 then r else L.rf s sc k := by
  rw [← hW.ix_last]; exact hW.rf_putS (by have := hW.size_le; have := hW.size_pos; omega) hk


theorem RefillsWF.rf_wr_hdr {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    {a v : U64} (ha : a = periodA sc ∨ a = maxA sc ∨ a = headA sc ∨ a = tailA sc) {k : Nat}
    (hix : L.ix (L.wr s a v) sc k = L.ix s sc k) : L.rf (L.wr s a v) sc k = L.rf s sc k := by
  unfold LawfulStore.rf; rw [hix, hW.refill_wr_hdr ha (hW.ix_lt k)]

/-- Popping the head drops the first refill. -/
theorem RefillsWF.pop {s s' : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    (hne : L.rhead s sc ≠ L.rtail s sc)
    (hs' : s' = L.wr s (headA sc) (nextIdx (L.rmax s sc) (L.rhead s sc))) :
    L.size s' sc = L.size s sc - 1 ∧ (∀ k, L.rf s' sc k = L.rf s sc (k + 1)) ∧
      L.rperiod s' sc = L.rperiod s sc ∧ L.rmax s' sc = L.rmax s sc := by
  obtain ⟨h8, -, -⟩ := hW.bounds
  have hm : L.rmax s' sc = L.rmax s sc := by rw [hs', rmax_wr_head h8]
  have hh : (L.rhead s' sc).val = ((L.rhead s sc).val + 1) % (L.rmax s sc).val := by
    rw [hs', rhead_wr_head h8]; exact nextIdx_val hW.head_lt
  have ht : L.rtail s' sc = L.rtail s sc := by rw [hs', rtail_wr_head h8]
  have hne' : (L.rhead s sc).val ≠ (L.rtail s sc).val := fun e => hne (UScalar.eq_of_val_eq e)
  refine ⟨?_, fun k => ?_, by rw [hs', rperiod_wr_head h8], hm⟩
  · simp only [LawfulStore.size, hm, hh, ht]
    exact ringN_pop hW.head_lt hW.tail_lt hne'
  · have hix : L.ix s' sc k = L.ix s sc (k + 1) := by
      simp only [LawfulStore.ix, hm, hh]
      congr 1; rw [Nat.mod_add_mod]; congr 1; omega
    unfold LawfulStore.rf; rw [hix, hs', hW.refill_wr_hdr (Or.inr (Or.inr (Or.inl rfl))) (hW.ix_lt _)]

/-- Adding a tail to a ring that is not full appends a refill. -/
theorem RefillsWF.add {s s' : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    (hnf : L.size s sc < (L.rmax s sc).val) {r : sporadic.Refill} {nt : U64}
    (hnt : nt = nextIdx (L.rmax s sc) (L.rtail s sc))
    (hs' : s' = L.putS (L.wr s (tailA sc) nt) sc nt r) :
    L.size s' sc = L.size s sc + 1 ∧
      (∀ k, k < (L.rmax s sc).val → L.rf s' sc k = if k = L.size s sc then r else L.rf s sc k) ∧
      L.rperiod s' sc = L.rperiod s sc ∧ L.rmax s' sc = L.rmax s sc := by
  obtain ⟨h8, hb, hfit⟩ := hW.bounds
  have hntv : nt.val = ((L.rtail s sc).val + 1) % (L.rmax s sc).val := by
    rw [hnt]; exact nextIdx_val hW.tail_lt
  have hntl : nt.val < (L.rmax s sc).val := by rw [hnt]; exact nextIdx_lt hW.tail_lt
  have hW1 : RefillsWF st (L.wr s (tailA sc) nt) sc sb := hW.wr_tail hntl
  have hm1 : L.rmax (L.wr s (tailA sc) nt) sc = L.rmax s sc := rmax_wr_tail h8
  have hh1 : L.rhead (L.wr s (tailA sc) nt) sc = L.rhead s sc := rhead_wr_tail h8
  have hi' : sc.val + 96 + 16 * nt.val + 16 ≤ 2 ^ 64 := by omega
  have hnt' : nt = L.ix (L.wr s (tailA sc) nt) sc (L.size s sc) := by
    apply UScalar.eq_of_val_eq
    rw [hW1.ix_val, hntv, hh1, hm1]
    exact (idx_add hW.head_lt hW.tail_lt).symm
  subst hs'
  refine ⟨?_, fun k hk => ?_, ?_, ?_⟩
  · simp only [LawfulStore.size, rmax_putS h8 hi', rhead_putS h8 hi', rtail_putS h8 hi',
      hm1, hh1, rtail_wr_tail h8, hntv]
    exact ringN_add hW.head_lt hW.tail_lt hnf
  · have e : L.putS (L.wr s (tailA sc) nt) sc nt r =
        L.putS (L.wr s (tailA sc) nt) sc (L.ix (L.wr s (tailA sc) nt) sc (L.size s sc)) r :=
      congrArg (fun j => L.putS (L.wr s (tailA sc) nt) sc j r) hnt'
    rw [e, hW1.rf_putS (by rw [hm1]; exact hnf) (by rw [hm1]; exact hk)]
    split
    · rfl
    · refine hW.rf_wr_hdr (Or.inr (Or.inr (Or.inr rfl))) ?_
      simp only [LawfulStore.ix, hh1, hm1]
  · rw [rperiod_putS h8 hi', rperiod_wr_tail h8]
  · rw [rmax_putS h8 hi', hm1]


/-! ## The ordering invariant (periodic SCs)

l4v's `sp_valid_refills` also requires `ordered_disjoint`, `no_overflow`
and `window` of the refill list; FL4 stores the list, so these are
properties of the stored state. (The parts about the budget, which FL4
does not store, and about `MIN_BUDGET`, are not included.) -/

/-- `ordered_disjoint`, `no_overflow` and `window` (SchedContextInv_AI,
DetSchedInvs_AI) of the ring `rf 0, ..., rf (size - 1)`. -/
structure RefillsOrdered (st : machine.Store S) [L : LawfulStore st] (s : S) (sc : obj.Sc) : Prop where
  disjoint : ∀ k, k + 1 < L.size s sc →
    (L.rf s sc k).time.val + (L.rf s sc k).amount.val ≤ (L.rf s sc (k + 1)).time.val
  no_overflow : ∀ k, k < L.size s sc → (L.rf s sc k).time.val + (L.rf s sc k).amount.val < 2 ^ 64
  window : (L.rf s sc (L.size s sc - 1)).time.val ≤ (L.rf s sc 0).time.val + (L.rperiod s sc).val

theorem RefillsOrdered.single {s : S} {sc : obj.Sc} (h1 : L.size s sc = 1)
    (hno : (L.rf s sc 0).time.val + (L.rf s sc 0).amount.val < 2 ^ 64) : RefillsOrdered st s sc :=
  ⟨fun k hk => by omega, fun k hk => by obtain rfl : k = 0 := by omega
                                        exact hno, by rw [h1, Nat.sub_self]; omega⟩

theorem RefillsWF.size_putS {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) {i : U64}
    {r : sporadic.Refill} (hi : i.val < (L.rmax s sc).val) : L.size (L.putS s sc i r) sc = L.size s sc := by
  obtain ⟨h8, hb, hfit⟩ := hW.bounds
  have hi' : sc.val + 96 + 16 * i.val + 16 ≤ 2 ^ 64 := by omega
  simp only [LawfulStore.size, rmax_putS h8 hi', rhead_putS h8 hi', rtail_putS h8 hi']

/-- A word outside the SC is not changed by a write inside it. -/
theorem mem_wr_inside {s : S} {sc : obj.Sc} {sb : Nat} {a b v : U64} (ha : Aligned a)
    (hin : sc.val ≤ a.val ∧ a.val < sc.val + 2 ^ sb) (hb : Aligned b ∧ Outside b sc sb) :
    L.mem (L.wr s a v) b = L.mem s b := by
  apply L.mem_wr_ne ha hb.1; unfold Outside at hb; omega

theorem mem_putS_inside {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) {i b : U64}
    {r : sporadic.Refill} (hi : i.val < (L.rmax s sc).val) (hb : Aligned b ∧ Outside b sc sb) :
    L.mem (L.putS s sc i r) b = L.mem s b := by
  obtain ⟨h8, hm, hfit⟩ := hW.bounds
  unfold LawfulStore.putS
  rw [mem_wr_inside (sb := sb) (by addr) (by constructor <;> addr) hb,
    mem_wr_inside (sb := sb) (by addr) (by constructor <;> addr) hb]

theorem sporadic.maybe_add_empty_tail.periodic (s : S) (sc : obj.Sc) (hp : L.rperiod s sc ≠ 0#u64) :
    sporadic.maybe_add_empty_tail st s sc ⦃ s' => s' = s ⦄ := by
  unfold sporadic.maybe_add_empty_tail; step*

/-- `refill_new` of a periodic SC establishes the ordering invariant, if the
current time plus the budget does not overflow and the current core's
`CUR_TIME` word is not inside the SC. -/
theorem sporadic.refill_new.ordered {s : S} {sc : obj.Sc} {sb : Nat} (max_refills budget period : U64)
    (hP : Placed sc sb) (h2 : sporadic.MIN_REFILLS.val ≤ max_refills.val)
    (hm : max_refills.val ≤ absMax sb) (hper : period ≠ 0#u64)
    (hct : Aligned (L.nodeA s layout.node.CUR_TIME) ∧ Outside (L.nodeA s layout.node.CUR_TIME) sc sb)
    (hov : (L.curTime s).val + budget.val < 2 ^ 64) :
    sporadic.refill_new st s sc max_refills budget period
      ⦃ s' => RefillsWF st s' sc sb ∧ RefillsOrdered st s' sc ⦄ := by
  have h2' := h2; simp at h2'
  obtain ⟨h8, hb, hfit⟩ := hP.bounds h2' hm
  unfold sporadic.refill_new
  step; step; step; step
  have hW : RefillsWF st s4 sc sb := by subst s4_post s3_post s2_post s1_post; exact RefillsWF.reset hP h2 hm
  have hct4 : L.curTime s4 = L.curTime s := by
    subst s4_post s3_post s2_post s1_post
    simp only [LawfulStore.curTime, nodeA_wr]
    rw [mem_wr_inside (by addr) (by constructor <;> addr) hct, mem_wr_inside (by addr) (by constructor <;> addr) hct,
      mem_wr_inside (by addr) (by constructor <;> addr) hct, mem_wr_inside (by addr) (by constructor <;> addr) hct]
  have hh4 : L.rhead s4 sc = 0#u64 := by subst s4_post s3_post s2_post s1_post; rw [rhead_wr_max h8, rhead_wr_tail h8, rhead_wr_head h8]
  have hp4 : L.rperiod s4 sc = period := by
    subst s4_post s3_post s2_post s1_post; rw [rperiod_wr_max h8, rperiod_wr_tail h8, rperiod_wr_head h8, rperiod_wr_period h8]
  have hs4 : L.size s4 sc = 1 := by
    subst s4_post s3_post s2_post s1_post; simp only [LawfulStore.size, rhead_wr_max h8, rhead_wr_tail h8, rhead_wr_head h8,
      rtail_wr_max h8, rtail_wr_tail h8]; simp [ringN]
  step; step
  have h0 : (0#u64).val < (L.rmax s4 sc).val := by have := hW.min_le; simp at this ⊢; omega
  have hW5 : RefillsWF st s5 sc sb := by subst s5; exact hW.putS h0
  have hp5 : L.rperiod s5 sc ≠ 0#u64 := by
    subst s5; rw [rperiod_putS h8 (by simp; omega), hp4]; exact hper
  step with sporadic.maybe_add_empty_tail.periodic
  subst s'_post s5_post now_post
  refine ⟨hW5, RefillsOrdered.single ?_ ?_⟩
  · rw [hW.size_putS h0, hs4]
  · rw [← hh4, hW.rf_set_head (by have := hW.min_le; simp at this; omega)]
    simp only [ite_true]; rw [hct4]; exact hov


theorem sporadic.add_tail.eq (s : S) (sc : obj.Sc) (r : sporadic.Refill) :
    sporadic.add_tail st s sc r ⦃ s' => s' = L.putS (L.wr s (tailA sc) (nextIdx (L.rmax s sc) (L.rtail s sc))) sc
      (nextIdx (L.rmax s sc) (L.rtail s sc)) r ⦄ := by
  unfold sporadic.add_tail; step*; simp_all

theorem refill_putS_same {s : S} {sc : obj.Sc} {i : U64} {r : sporadic.Refill} (h8 : sc.val % 8 = 0) :
    L.refill (L.putS s sc i r) sc i = r := by
  unfold LawfulStore.refill LawfulStore.putS
  rw [L.mem_wr_ne (by addr) (by addr) (by addr), L.mem_wr_same (by addr), L.mem_wr_same (by addr)]

theorem refill_wr_hdr' {s : S} {sc : obj.Sc} {a v i : U64} (h8 : sc.val % 8 = 0)
    (hi : sc.val + 96 + 16 * i.val + 16 ≤ 2 ^ 64)
    (ha : a = periodA sc ∨ a = maxA sc ∨ a = headA sc ∨ a = tailA sc) :
    L.refill (L.wr s a v) sc i = L.refill s sc i := by
  unfold LawfulStore.refill
  rcases ha with rfl | rfl | rfl | rfl <;>
    rw [L.mem_wr_ne (by addr) (by addr) (by addr), L.mem_wr_ne (by addr) (by addr) (by addr)]

/-- `refill_update` to a periodic configuration establishes the ordering
invariant, if the budget is at most the period, the head refill's time and
the current time plus period and budget do not overflow, and the current
core's `CUR_TIME` word is not inside the SC. -/
theorem sporadic.refill_update.ordered {s : S} {sc : obj.Sc} {sb : Nat} (new_period new_budget new_max_refills : U64)
    (hP : Placed sc sb) (h2 : sporadic.MIN_REFILLS.val ≤ new_max_refills.val)
    (hm : new_max_refills.val ≤ absMax sb) (hper : new_period ≠ 0#u64)
    (hbp : new_budget.val ≤ new_period.val)
    (hct : Aligned (L.nodeA s layout.node.CUR_TIME) ∧ Outside (L.nodeA s layout.node.CUR_TIME) sc sb)
    (hov_now : (L.curTime s).val + new_period.val + new_budget.val < 2 ^ 64)
    (hov_head : (L.refill s sc (L.rhead s sc)).time.val + new_period.val + new_budget.val < 2 ^ 64) :
    sporadic.refill_update st s sc new_period new_budget new_max_refills
      ⦃ s' => RefillsWF st s' sc sb ∧ RefillsOrdered st s' sc ⦄ := by
  have h2' := h2; simp at h2'
  obtain ⟨h8, hb, hfit⟩ := hP.bounds h2' hm
  have hi0 : sc.val + 96 + 16 * (0#u64).val + 16 ≤ 2 ^ 64 := by simp; omega
  unfold sporadic.refill_update
  step; step; step; step; step
  have hW4 : RefillsWF st s4 sc sb := by subst s4_post s3_post s2_post; exact RefillsWF.reset hP h2 hm
  step
  have hW5 : RefillsWF st s5 sc sb := by subst s5_post; exact hW4.wr_period
  have hh5 : L.rhead s5 sc = 0#u64 := by
    subst s5_post s4_post s3_post s2_post
    rw [rhead_wr_period h8, rhead_wr_max h8, rhead_wr_tail h8, rhead_wr_head h8]
  have hp5 : L.rperiod s5 sc = new_period := by subst s5_post; rw [rperiod_wr_period h8]
  have hs5 : L.size s5 sc = 1 := by
    subst s5_post s4_post s3_post s2_post
    simp only [LawfulStore.size, rhead_wr_period h8, rhead_wr_max h8, rhead_wr_tail h8, rhead_wr_head h8,
      rtail_wr_period h8, rtail_wr_max h8, rtail_wr_tail h8]; simp [ringN]
  have hr5 : L.refill s5 sc 0#u64 = h := by
    subst s5_post s4_post s3_post s2_post s1_post
    rw [refill_wr_hdr' h8 hi0 (Or.inl rfl), refill_wr_hdr' h8 hi0 (Or.inr (Or.inl rfl)),
      refill_wr_hdr' h8 hi0 (Or.inr (Or.inr (Or.inr rfl))), refill_wr_hdr' h8 hi0 (Or.inr (Or.inr (Or.inl rfl))),
      refill_putS_same h8]
  have hct5 : L.curTime s5 = L.curTime s := by
    subst s5_post s4_post s3_post s2_post s1_post
    simp only [LawfulStore.curTime, nodeA_wr, LawfulStore.putS]
    repeat rw [mem_wr_inside (by addr) (by constructor <;> addr) hct]
  step
  -- The head refill after the optional move to the current time.
  have key : (if b = true then do
        let now ← sporadic.cur_time st s5
        let r ← sporadic.head st s5 sc
        sporadic.set_head st s5 sc { r with time := now }
      else ok s5) ⦃ s6 => RefillsWF st s6 sc sb ∧ L.size s6 sc = 1 ∧ L.rperiod s6 sc = new_period ∧
        L.rhead s6 sc = 0#u64 ∧ (L.rf s6 sc 0).amount = h.amount ∧
        (L.rf s6 sc 0).time.val + new_period.val + new_budget.val < 2 ^ 64 ⦄ := by
    have h0 : (0#u64).val < (L.rmax s5 sc).val := by have := hW5.min_le; simp at this ⊢; omega
    split
    · step; step
      step with sporadic.set_head.eq
      rw [hh5] at s6_post r_post
      subst s6_post r_post now_post
      refine ⟨hW5.putS h0, by rw [hW5.size_putS h0, hs5], ?_, ?_, ?_⟩
      · rw [rperiod_putS h8 hi0, hp5]
      · rw [rhead_putS h8 hi0, hh5]
      · rw [← hh5, hW5.rf_set_head (by omega)]; simp only [ite_true]
        rw [hh5, hr5, hct5]; exact ⟨rfl, hov_now⟩
    · have e : L.rf s5 sc 0 = h := by rw [LawfulStore.rf, hW5.ix_zero, hh5, hr5]
      simp only [WP.spec_ok]
      refine ⟨hW5, hs5, hp5, hh5, by rw [e], by rw [e]; subst h_post; exact hov_head⟩
  step with key
  have hW6 := s6_post; have hs6 := s6_post1; have hp6 := new_period_post; have hh6 := s6_post2
  have ht6 := s6_post4
  have h0 : (0#u64).val < (L.rmax s6 sc).val := by have := hW6.min_le; simp at this ⊢; omega
  have ehd : L.refill s6 sc (L.rhead s6 sc) = L.rf s6 sc 0 := by rw [LawfulStore.rf, hW6.ix_zero]
  step
  rw [ehd] at hd_post
  split
  · step with sporadic.set_head.eq
    have hW7 : RefillsWF st s7 sc sb := by subst s7_post; exact hW6.putS (by rw [hh6]; exact h0)
    have hp7 : L.rperiod s7 sc ≠ 0#u64 := by
      subst s7_post; rw [hh6, rperiod_putS h8 hi0, hp6]; exact hper
    step with sporadic.maybe_add_empty_tail.periodic
    subst s'_post
    refine ⟨hW7, RefillsOrdered.single ?_ ?_⟩
    · subst s7_post; rw [hW6.size_putS (by rw [hh6]; exact h0), hs6]
    · subst s7_post; rw [hW6.rf_set_head (by omega)]; simp only [ite_true]
      subst hd_post; omega
  · rename_i hlt
    step; step
    step with sporadic.add_tail.eq
    have hnf : L.size s6 sc < (L.rmax s6 sc).val := by rw [hs6]; have := hW6.min_le; simp at this; omega
    obtain ⟨hs', hrf, hp', hm'⟩ := hW6.add hnf rfl s'_post
    have hW' : RefillsWF st s' sc sb := by
      subst s'_post; exact (hW6.wr_tail (nextIdx_lt hW6.tail_lt)).putS
        (by rw [rmax_wr_tail h8]; exact nextIdx_lt hW6.tail_lt)
    have hmax : 2 ≤ (L.rmax s6 sc).val := by have := hW6.min_le; simpa using this
    have r0 := hrf 0 (by omega); have r1 := hrf 1 (by omega)
    rw [hs6] at r0 r1; simp only [show (0 : Nat) ≠ 1 from by decide, ite_false, ite_true] at r0 r1
    rw [hs6] at hs'
    subst hd_post
    simp only [ge_iff_le, UScalar.le_equiv, not_le] at hlt
    have hT : (L.rf s6 sc 0).time.val + new_period.val < 2 ^ 64 := by omega
    have hiv : i.val = (L.rf s6 sc 0).time.val + new_period.val := by
      rw [i_post]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    refine ⟨hW', ⟨?_, ?_, ?_⟩⟩
    · intro k hk; rw [hs'] at hk; obtain rfl : k = 0 := by omega
      rw [r0, r1]; dsimp only; rw [hiv]; omega
    · intro k hk; rw [hs'] at hk
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · rw [r0]; omega
      · rw [r1]; dsimp only; rw [hiv, i1_post]; omega
    · rw [hs', r0, show 2 - 1 = 1 from rfl, r1, hp', hp6]; dsimp only; omega


theorem sporadic.pop_head.eq (s : S) (sc : obj.Sc) :
    sporadic.pop_head st s sc ⦃ r s' => r = L.refill s sc (L.rhead s sc) ∧
      s' = L.wr s (headA sc) (nextIdx (L.rmax s sc) (L.rhead s sc)) ⦄ := by
  unfold sporadic.pop_head; step*; simp_all

theorem RefillsWF.size_two {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    (hne : L.rhead s sc ≠ L.rtail s sc) : 2 ≤ L.size s sc := by
  have hne' : (L.rhead s sc).val ≠ (L.rtail s sc).val := fun e => hne (UScalar.eq_of_val_eq e)
  have := hW.head_lt; have := hW.tail_lt
  unfold LawfulStore.size ringN; split <;> omega

theorem RefillsWF.single_iff {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) :
    L.rhead s sc = L.rtail s sc ↔ L.size s sc = 1 := by
  constructor
  · intro e; simp [LawfulStore.size, ringN, e]
  · intro e; by_contra hne; have := hW.size_two hne; omega

/-- Popping the head and then rewriting the new head (the merge loops). -/
theorem RefillsWF.pop_set {s s₁ s₂ : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    (hne : L.rhead s sc ≠ L.rtail s sc)
    (hs₁ : s₁ = L.wr s (headA sc) (nextIdx (L.rmax s sc) (L.rhead s sc))) {r : sporadic.Refill}
    (hs₂ : s₂ = L.putS s₁ sc (L.rhead s₁ sc) r) :
    RefillsWF st s₂ sc sb ∧ L.size s₂ sc = L.size s sc - 1 ∧ L.rperiod s₂ sc = L.rperiod s sc ∧
      L.refill s₁ sc (L.rhead s₁ sc) = L.rf s sc 1 ∧
      ∀ k, k < (L.rmax s sc).val → L.rf s₂ sc k = if k = 0 then r else L.rf s sc (k + 1) := by
  obtain ⟨hn, hrf, hp, hm⟩ := hW.pop hne hs₁
  have hW1 : RefillsWF st s₁ sc sb := by rw [hs₁]; exact hW.wr_head (nextIdx_lt hW.head_lt)
  have hh1 : (L.rhead s₁ sc).val < (L.rmax s₁ sc).val := hW1.head_lt
  subst hs₂
  refine ⟨hW1.putS hh1, by rw [hW1.size_putS hh1, hn], ?_, ?_, fun k hk => ?_⟩
  · obtain ⟨h8, hb, hfit⟩ := hW1.bounds
    rw [rperiod_putS h8 (by omega), hp]
  · rw [← hW1.ix_zero]; exact hrf 0
  · rw [hW1.rf_set_head (by rw [hm]; exact hk), hrf]

/-- The loop that merges heads below `MIN_BUDGET` (seL4
`merge_nonoverlapping_head_refill`) preserves the ordering invariant. -/
theorem sporadic.budget_check_loop1.ordered {s : S} {sc : obj.Sc} {sb : Nat} (mb fuel2 : U64)
    (hW : RefillsWF st s sc sb) (hO : RefillsOrdered st s sc) :
    sporadic.budget_check_loop1 st s sc mb fuel2
      ⦃ s' => RefillsWF st s' sc sb ∧ RefillsOrdered st s' sc ⦄ := by
  unfold sporadic.budget_check_loop1
  apply loop.spec_decr_nat (measure := fun x => x.2.val)
    (inv := fun x => RefillsWF st x.1 sc sb ∧ RefillsOrdered st x.1 sc)
  · rintro ⟨x0, x1⟩ ⟨hW, hO⟩
    dsimp only at hW hO
    unfold sporadic.budget_check_loop1.body
    step
    split
    · step
      split
      · simp only [WP.spec_ok]; exact ⟨hW, hO⟩
      · split
        · have hne : L.rhead x0 sc ≠ L.rtail x0 sc := by intro e; simp_all
          step
          step with sporadic.pop_head.eq
          step; step; step; step with sporadic.set_head.eq
          obtain ⟨hW2, hn2, hp2, hh1, hrf⟩ := hW.pop_set hne s1_post s2_post
          refine ⟨hW2, ?_, by omega⟩
          have h2 := hW.size_two hne
          have hle := hW.size_le
          have e0 : old = L.rf x0 sc 0 := by rw [old_post, LawfulStore.rf, hW.ix_zero]
          have e1 : h = L.rf x0 sc 1 := by rw [h_post, hh1]
          have od0 := hO.disjoint 0 (by omega)
          simp only [Nat.zero_add] at od0
          have no1 := hO.no_overflow 1 (by omega)
          have hwin := hO.window
          have hi1 : i1.val = (L.rf x0 sc 1).time.val - (L.rf x0 sc 0).amount.val := by
            rw [i1_post, e1, e0, wsub_val (by omega)]
          have hi2 : i2.val = (L.rf x0 sc 1).amount.val + (L.rf x0 sc 0).amount.val := by
            rw [i2_post, e1, e0, wadd_val (by omega)]
          have hR : ∀ k, k + 1 < L.size x0 sc →
              L.rf s2 sc k = if k = 0 then { time := i1, amount := i2 } else L.rf x0 sc (k + 1) :=
            fun k hk => hrf k (by omega)
          refine ⟨fun k hk => ?_, fun k hk => ?_, ?_⟩
          · rw [hn2] at hk
            rw [hR k (by omega), hR (k + 1) (by omega)]
            have := hO.disjoint (k + 1) (by omega)
            split
            · subst k
              simp only [Nat.zero_add, show (1 : Nat) ≠ 0 from by decide, ite_false] at this ⊢
              rw [hi1, hi2]; omega
            · simp only [show k + 1 ≠ 0 by omega, ite_false]; exact this
          · rw [hn2] at hk
            rw [hR k (by omega)]
            split
            · dsimp only; rw [hi1, hi2]; omega
            · exact hO.no_overflow (k + 1) (by omega)
          · rw [hn2, hp2, hR 0 (by omega)]; simp only [ite_true]
            rw [hR _ (by omega)]
            split
            · first | omega | (dsimp only; omega)
            · rename_i hk; rw [show L.size x0 sc - 1 - 1 + 1 = L.size x0 sc - 1 by omega]
              rw [hi1]; omega
        · simp only [WP.spec_ok]; exact ⟨hW, hO⟩
    · simp only [WP.spec_ok]; exact ⟨hW, hO⟩
  · exact ⟨hW, hO⟩


/-! ### `refill_unblock_check` -/

/-- The sum of the amounts of the ring (l4v's `refills_sum`; equal to the
budget in l4v, which FL4 does not store). -/
def LawfulStore.amtSum (s : S) (sc : obj.Sc) : Nat :=
  ∑ k ∈ Finset.range (L.size s sc), (L.rf s sc k).amount.val

theorem sum_range_two (g : Nat → Nat) {n : Nat} (hn : 2 ≤ n) :
    ∑ k ∈ Finset.range n, g k = g 0 + g 1 + ∑ k ∈ Finset.range (n - 2), g (k + 2) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.add_sub_cancel]; ring

theorem sum_last (g : Nat → Nat) {n : Nat} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, g k = ∑ k ∈ Finset.range (n - 1), g k + g (n - 1) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ]; simp only [Nat.add_sub_cancel]

theorem sum_range_one (g : Nat → Nat) {n : Nat} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, g k = g 0 + ∑ k ∈ Finset.range (n - 1), g (k + 1) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ']; simp only [Nat.add_sub_cancel]; ring

/-- A write outside the object leaves the ring alone. -/
theorem RefillsWF.wr_out_view {s : S} {sc : obj.Sc} {sb : Nat} {a v : U64} (hW : RefillsWF st s sc sb)
    (ha : Aligned a) (hout : Outside a sc sb) :
    L.size (L.wr s a v) sc = L.size s sc ∧ L.rperiod (L.wr s a v) sc = L.rperiod s sc ∧
      ∀ k, L.rf (L.wr s a v) sc k = L.rf s sc k := by
  obtain ⟨h8, hm, hfit⟩ := hW.bounds
  have := hW.min_le; simp at this
  unfold Outside at hout
  have e : ∀ b, Aligned b → sc.val ≤ b.val → b.val < sc.val + 2 ^ sb → L.mem (L.wr s a v) b = L.mem s b :=
    fun b hb h1 h2 => L.mem_wr_ne ha hb (by omega)
  have em : L.rmax (L.wr s a v) sc = L.rmax s sc := e _ (by addr) (by addr) (by addr)
  have eh : L.rhead (L.wr s a v) sc = L.rhead s sc := e _ (by addr) (by addr) (by addr)
  have et : L.rtail (L.wr s a v) sc = L.rtail s sc := e _ (by addr) (by addr) (by addr)
  refine ⟨by simp only [LawfulStore.size, em, eh, et], e _ (by addr) (by addr) (by addr), fun k => ?_⟩
  have hix : L.ix (L.wr s a v) sc k = L.ix s sc k := by simp only [LawfulStore.ix, em, eh]
  have hk := hW.ix_lt k
  unfold LawfulStore.rf LawfulStore.refill; rw [hix, e _ (by addr) (by addr) (by addr), e _ (by addr) (by addr) (by addr)]

/-- The state of the merge loop of `refill_unblock_check`: the head starts
at `now`; apart from the head, the ring is ordered; the head ends before
`now` plus all the amounts, which does not overflow. -/
structure UnblockInv (st : machine.Store S) [L : LawfulStore st] (s : S) (sc : obj.Sc) (sb : Nat)
    (now : U64) (fuel : Nat) : Prop where
  wf : RefillsWF st s sc sb
  head : (L.rf s sc 0).time = now
  disjoint : ∀ k, 1 ≤ k → k + 1 < L.size s sc →
    (L.rf s sc k).time.val + (L.rf s sc k).amount.val ≤ (L.rf s sc (k + 1)).time.val
  no_overflow : ∀ k, k < L.size s sc → (L.rf s sc k).time.val + (L.rf s sc k).amount.val < 2 ^ 64
  window : (L.rf s sc (L.size s sc - 1)).time.val ≤ now.val + (L.rperiod s sc).val
  sum : now.val + L.amtSum s sc < 2 ^ 64
  fuel : L.size s sc ≤ fuel

theorem headOverlapping_false {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    (hno : (L.rf s sc 0).time.val + (L.rf s sc 0).amount.val < 2 ^ 64)
    (h : L.headOverlapping s sc = false) (h2 : 2 ≤ L.size s sc) :
    (L.rf s sc 0).time.val + (L.rf s sc 0).amount.val < (L.rf s sc 1).time.val := by
  unfold LawfulStore.headOverlapping at h
  have hne : L.rhead s sc ≠ L.rtail s sc := fun e => by have := (hW.single_iff).1 e; omega
  simp only [hne, ite_false, decide_eq_false_iff_not, not_le] at h
  have e0 : L.refill s sc (L.rhead s sc) = L.rf s sc 0 := by rw [LawfulStore.rf, hW.ix_zero]
  have e1 : L.refill s sc (nextIdx (L.rmax s sc) (L.rhead s sc)) = L.rf s sc 1 := by
    rw [LawfulStore.rf]; congr 1; apply UScalar.eq_of_val_eq
    rw [nextIdx_val hW.head_lt, hW.ix_val]
  rw [e0, e1] at h
  simp only [UScalar.lt_equiv] at h
  rw [wadd_val hno] at h; exact h

theorem sporadic.unblock_check_loop.ordered {s : S} {sc : obj.Sc} {sb : Nat} (now fuel : U64)
    (hI : UnblockInv st s sc sb now fuel.val) :
    sporadic.unblock_check_loop st s sc fuel ⦃ s' => RefillsWF st s' sc sb ∧ RefillsOrdered st s' sc ⦄ := by
  unfold sporadic.unblock_check_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.val) (inv := fun x => UnblockInv st x.1 sc sb now x.2.val)
  · rintro ⟨x0, x1⟩ hI
    dsimp only at hI
    have hW := hI.wf
    unfold sporadic.unblock_check_loop.body
    step
    split
    · split
      · -- merge the head with the next refill
        have hov : L.headOverlapping x0 sc = true := by simp_all
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
        have hsum := hI.sum
        have hs := sum_range_two (fun k => (L.rf x0 sc k).amount.val) h2
        unfold LawfulStore.amtSum at hsum; rw [hs] at hsum
        have hi : i.val = (L.rf x0 sc 1).amount.val + (L.rf x0 sc 0).amount.val := by
          rw [i_post, e1, e0, wadd_val (by omega)]
        have hR : ∀ k, k + 1 < L.size x0 sc →
            L.rf s2 sc k = if k = 0 then { old with amount := i } else L.rf x0 sc (k + 1) :=
          fun k hk => hrf k (by omega)
        have hhead := hI.head
        refine ⟨⟨hW2, ?_, ?_, ?_, ?_, ?_, ?_⟩, by omega⟩
        · rw [hR 0 (by omega)]; simp only [ite_true]; rw [e0, hhead]
        · intro k hk1 hk; rw [hn2] at hk
          rw [hR k (by omega), hR (k + 1) (by omega)]
          simp only [show k ≠ 0 by omega, show k + 1 ≠ 0 by omega, ite_false]
          exact hI.disjoint (k + 1) (by omega) (by omega)
        · intro k hk; rw [hn2] at hk
          rw [hR k (by omega)]
          split
          · dsimp only; rw [hi, e0, hhead]; omega
          · exact hI.no_overflow (k + 1) (by omega)
        · rw [hn2, hp2, hR _ (by omega)]
          split
          · rw [e0, hhead]; omega
          · rw [show L.size x0 sc - 1 - 1 + 1 = L.size x0 sc - 1 by omega]; exact hI.window
        · unfold LawfulStore.amtSum
          rw [hn2, sum_range_one _ (by omega), hR 0 (by omega)]
          simp only [ite_true]
          have : ∀ k ∈ Finset.range (L.size x0 sc - 1 - 1),
              (L.rf s2 sc (k + 1)).amount.val = (L.rf x0 sc (k + 2)).amount.val := by
            intro k hk; simp at hk; rw [hR (k + 1) (by omega)]; simp
          rw [Finset.sum_congr rfl this, show L.size x0 sc - 1 - 1 = L.size x0 sc - 2 by omega]
          rw [hi]; omega
        · rw [hn2]; have := hI.fuel; omega
      · -- out of fuel: impossible, the ring has at least two refills
        exfalso
        have hov : L.headOverlapping x0 sc = true := by simp_all
        have hne : L.rhead x0 sc ≠ L.rtail x0 sc := by
          intro e; simp [LawfulStore.headOverlapping, e] at hov
        have := hW.size_two hne; have := hI.fuel
        simp only [UScalar.lt_equiv, not_lt] at *
        simp at *; omega
    · -- no overlap: the ring is ordered
      have hov : L.headOverlapping x0 sc = false := by simp_all
      simp only [WP.spec_ok]
      refine ⟨hW, ⟨fun k hk => ?_, hI.no_overflow, ?_⟩⟩
      · by_cases hk0 : k = 0
        · subst hk0
          have := headOverlapping_false hW (hI.no_overflow 0 (by omega)) hov (by omega)
          simp only [Nat.zero_add]; omega
        · exact hI.disjoint k (by omega) hk
      · rw [hI.head]; exact hI.window
  · exact hI


/-- `refill_unblock_check` preserves the ordering invariant, if the current
time plus the sum of the amounts does not overflow (l4v: the current time
is far enough from overflow and the refills sum to the budget) and the
current core's `REPROGRAM` word is not inside the SC. -/
theorem sporadic.unblock_check.ordered {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    (hO : RefillsOrdered st s sc)
    (hrep : Aligned (L.nodeA s layout.node.REPROGRAM) ∧ Outside (L.nodeA s layout.node.REPROGRAM) sc sb)
    (hsum : (L.curTime s).val + L.amtSum s sc < 2 ^ 64) :
    sporadic.unblock_check st s sc ⦃ s' => RefillsWF st s' sc sb ∧ RefillsOrdered st s' sc ⦄ := by
  unfold sporadic.unblock_check
  step
  split
  · simp only [WP.spec_ok]; exact ⟨hW, hO⟩
  step
  split
  · rename_i hready
    step; step
    step with sporadic.set_head.eq
    step; step; step; step
    obtain ⟨h8, hb, hfit⟩ := hW.bounds
    have hmin := hW.min_le; simp at hmin
    have hn1 := hW.size_pos; have hnle := hW.size_le
    have e0 : L.refill s sc (L.rhead s sc) = L.rf s sc 0 := by rw [LawfulStore.rf, hW.ix_zero]
    have hW1 : RefillsWF st s1 sc sb := by rw [s1_post]; exact hW.putS hW.head_lt
    have hn1' : L.size s1 sc = L.size s sc := by rw [s1_post, hW.size_putS hW.head_lt]
    have hp1 : L.rperiod s1 sc = L.rperiod s sc := by
      have := hW.head_lt; rw [s1_post, rperiod_putS h8 (by omega)]
    have hrf1 : ∀ k, k < (L.rmax s sc).val →
        L.rf s1 sc k = if k = 0 then { h with time := now } else L.rf s sc k := by
      intro k hk; rw [s1_post]; exact hW.rf_set_head hk
    have ea : L.nodeAt s1 cpu layout.node.REPROGRAM = L.nodeA s layout.node.REPROGRAM := by
      rw [cpu_post, s1_post]; simp [LawfulStore.putS, LawfulStore.nodeA]
    rw [ea] at s2_post
    obtain ⟨hn2, hp2, hrf2⟩ := hW1.wr_out_view (v := 1#u64) hrep.1 hrep.2
    rw [← s2_post] at hn2 hp2 hrf2
    have hW2 : RefillsWF st s2 sc sb := by rw [s2_post]; exact hW1.wr_out hrep.1 hrep.2
    have hR : ∀ k, k < L.size s sc → L.rf s2 sc k = if k = 0 then { h with time := now } else L.rf s sc k :=
      fun k hk => by rw [hrf2]; exact hrf1 k (by omega)
    have hsum' := hsum
    unfold LawfulStore.amtSum at hsum'
    rw [sum_range_one _ hn1] at hsum'
    have hrd : (L.rf s sc 0).time.val ≤ now.val := by
      rw [b1_post] at hready
      rw [← e0, now_post]; simpa [UScalar.le_equiv] using hready
    apply sporadic.unblock_check_loop.ordered now fuel
    refine ⟨hW2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hR 0 hn1]; rfl
    · intro k hk1 hk; rw [hn2, hn1'] at hk
      rw [hR k (by omega), hR (k + 1) hk]
      simp only [show k ≠ 0 by omega, show k + 1 ≠ 0 by omega, ite_false]
      exact hO.disjoint k hk
    · intro k hk; rw [hn2, hn1'] at hk
      rw [hR k hk]
      split
      · dsimp only; rw [h_post, e0, now_post]; omega
      · exact hO.no_overflow k hk
    · rw [hn2, hn1', hp2, hp1, hR _ (by omega)]
      split
      · dsimp only; omega
      · have := hO.window; omega
    · unfold LawfulStore.amtSum
      rw [hn2, hn1', sum_range_one _ hn1, hR 0 hn1]
      have : ∀ k ∈ Finset.range (L.size s sc - 1),
          (L.rf s2 sc (k + 1)).amount.val = (L.rf s sc (k + 1)).amount.val := by
        intro k hk; simp at hk; rw [hR (k + 1) (by omega)]; simp
      rw [Finset.sum_congr rfl this]
      simp only [ite_true]; rw [h_post, e0, now_post]; omega
    · have hm2 := hW2.le_abs; have hs2 := hW2.size_le
      have := absMax_lt sb
      rw [fuel_post, wadd_val (by rw [i_post]; simp; omega), i_post]; simp; omega
  · simp only [WP.spec_ok]; exact ⟨hW, hO⟩


/-! ### `schedule_used` -/

theorem sporadic.set_tail.eq (s : S) (sc : obj.Sc) (r : sporadic.Refill) :
    sporadic.set_tail st s sc r ⦃ s' => s' = L.putS s sc (L.rtail s sc) r ⦄ := by
  unfold sporadic.set_tail; step*; simp_all

theorem RefillsWF.ringSize_val {s : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb) :
    (ringSize (L.rmax s sc) (L.rhead s sc) (L.rtail s sc)).val = L.size s sc := by
  have hh := hW.head_lt; have ht := hW.tail_lt; have := absMax_lt sb; have := hW.le_abs
  unfold ringSize LawfulStore.size ringN
  simp only [UScalar.le_equiv]
  split
  · rw [wadd_val (by rw [wsub_val (by omega)]; simp; omega), wsub_val (by omega)]; simp
  · rw [wadd_val (by rw [wadd_val (by simp; omega), wsub_val (by omega)]; simp; omega),
      wadd_val (by simp; omega), wsub_val (by omega)]; simp; omega

/-- `schedule_used` preserves the ordering invariant, if the new refill
starts within a period of the head and neither it nor the tail grown by
its amount overflows. -/
theorem sporadic.schedule_used.ordered {s : S} {sc : obj.Sc} {sb : Nat} (new : sporadic.Refill)
    (hW : RefillsWF st s sc sb) (hO : RefillsOrdered st s sc)
    (hwin : new.time.val ≤ (L.rf s sc 0).time.val + (L.rperiod s sc).val)
    (hno1 : new.time.val + new.amount.val < 2 ^ 64)
    (hno2 : (L.rf s sc (L.size s sc - 1)).time.val + (L.rf s sc (L.size s sc - 1)).amount.val +
      new.amount.val < 2 ^ 64) :
    sporadic.schedule_used st s sc new ⦃ s' => RefillsWF st s' sc sb ∧ RefillsOrdered st s' sc ∧
      L.amtSum s' sc = L.amtSum s sc + new.amount.val ∧ L.rperiod s' sc = L.rperiod s sc ⦄ := by
  obtain ⟨h8, hb, hfit⟩ := hW.bounds
  have hn1 := hW.size_pos; have hnle := hW.size_le; have ht := hW.tail_lt
  have hmin := hW.min_le; simp at hmin
  have hi' : sc.val + 96 + 16 * (L.rtail s sc).val + 16 ≤ 2 ^ 64 := by omega
  have et : L.refill s sc (L.rtail s sc) = L.rf s sc (L.size s sc - 1) := by
    rw [LawfulStore.rf, hW.ix_last]
  have tno := hO.no_overflow (L.size s sc - 1) (by omega)
  unfold sporadic.schedule_used
  step; step
  rw [et] at t_post; subst t_post
  have hiv : i.val = (L.rf s sc (L.size s sc - 1)).time.val + (L.rf s sc (L.size s sc - 1)).amount.val := by
    rw [i_post, wadd_val tno]
  -- Rewriting the tail.
  have tailcase : ∀ r : sporadic.Refill,
      (L.size s sc ≥ 2 → (L.size s sc ≥ 2 → (L.rf s sc (L.size s sc - 2)).time.val +
        (L.rf s sc (L.size s sc - 2)).amount.val ≤ r.time.val)) →
      r.time.val + r.amount.val < 2 ^ 64 →
      (L.size s sc = 1 ∨ r.time.val ≤ (L.rf s sc 0).time.val + (L.rperiod s sc).val) →
      r.amount.val = (L.rf s sc (L.size s sc - 1)).amount.val + new.amount.val →
      RefillsWF st (L.putS s sc (L.rtail s sc) r) sc sb ∧ RefillsOrdered st (L.putS s sc (L.rtail s sc) r) sc ∧
      L.amtSum (L.putS s sc (L.rtail s sc) r) sc = L.amtSum s sc + new.amount.val ∧
      L.rperiod (L.putS s sc (L.rtail s sc) r) sc = L.rperiod s sc := by
    intro r hod hno hw hamt
    have hn' : L.size (L.putS s sc (L.rtail s sc) r) sc = L.size s sc := hW.size_putS ht
    have hp' : L.rperiod (L.putS s sc (L.rtail s sc) r) sc = L.rperiod s sc := by rw [rperiod_putS h8 hi']
    have hR : ∀ k, k < L.size s sc →
        L.rf (L.putS s sc (L.rtail s sc) r) sc k = if k = L.size s sc - 1 then r else L.rf s sc k :=
      fun k hk => hW.rf_set_tail (by omega)
    refine ⟨hW.putS ht, ⟨fun k hk => ?_, fun k hk => ?_, ?_⟩, ?_, hp'⟩
    rotate_left 3
    · unfold LawfulStore.amtSum
      rw [hn', sum_last _ hn1, sum_last (fun k => (L.rf s sc k).amount.val) hn1, hR _ (by omega)]
      have : ∀ k ∈ Finset.range (L.size s sc - 1),
          (L.rf (L.putS s sc (L.rtail s sc) r) sc k).amount.val = (L.rf s sc k).amount.val := by
        intro k hk; simp at hk; rw [hR k (by omega)]; simp [show k ≠ L.size s sc - 1 by omega]
      rw [Finset.sum_congr rfl this]; simp only [ite_true]; omega
    · rw [hn'] at hk
      rw [hR k (by omega), hR (k + 1) hk]
      simp only [show k ≠ L.size s sc - 1 by omega, ite_false]
      split
      · rename_i e; have := hod (by omega) (by omega)
        rw [show L.size s sc - 2 = k by omega] at this; exact this
      · exact hO.disjoint k hk
    · rw [hn'] at hk
      rw [hR k hk]; split
      · exact hno
      · exact hO.no_overflow k hk
    · rw [hn', hp', hR _ (by omega), hR 0 (by omega)]
      simp only [ite_true]
      split
      · omega
      · rcases hw with hw | hw
        · omega
        · exact hw
  split
  · -- merge into the tail
    step; step with sporadic.set_tail.eq
    subst s'_post
    rename_i hge
    simp only [ge_iff_le, UScalar.le_equiv] at hge
    refine tailcase _ ?_ ?_ ?_ ?_
    · intro h2 _
      have := hO.disjoint (L.size s sc - 2) (by omega)
      rw [show L.size s sc - 2 + 1 = L.size s sc - 1 by omega] at this; exact this
    · dsimp only; rw [i1_post, wadd_val (by omega)]; omega
    · rcases (by omega : L.size s sc = 1 ∨ 2 ≤ L.size s sc) with h | h
      · exact Or.inl h
      · exact Or.inr (by have := hO.window; exact this)
    · dsimp only; rw [i1_post, wadd_val (by omega)]
  · rename_i hlt
    simp only [ge_iff_le, UScalar.le_equiv, not_le] at hlt
    rw [hiv] at hlt
    step
    have hfull : b = decide (L.size s sc = (L.rmax s sc).val) := by
      rw [b_post, ← hW.ringSize_val]
      simp only [decide_eq_decide]; exact ⟨fun h => by rw [h], fun h => UScalar.eq_of_val_eq h⟩
    split
    · -- full: move the tail later
      rename_i hb
      rw [hfull] at hb; simp at hb
      step; step; step with sporadic.set_tail.eq
      subst s'_post
      refine tailcase _ ?_ ?_ ?_ ?_
      · intro h2 _
        have := hO.disjoint (L.size s sc - 2) (by omega)
        rw [show L.size s sc - 2 + 1 = L.size s sc - 1 by omega] at this
        rw [i1_post, wsub_val (by omega)]; omega
      · rw [i1_post, i2_post, wsub_val (by omega), wadd_val (by omega)]; omega
      · right; rw [i1_post, wsub_val (by omega)]; omega
      · rw [i2_post, wadd_val (by omega)]
    · -- not full: add a tail
      rename_i hb
      rw [hfull] at hb; simp at hb
      have hnf : L.size s sc < (L.rmax s sc).val := by omega
      step with sporadic.add_tail.eq
      obtain ⟨hs', hrf, hp', hm'⟩ := hW.add hnf rfl s'_post
      have hW' : RefillsWF st s' sc sb := by
        subst s'_post; exact (hW.wr_tail (nextIdx_lt hW.tail_lt)).putS
          (by rw [rmax_wr_tail h8]; exact nextIdx_lt hW.tail_lt)
      have hR : ∀ k, k < L.size s sc + 1 → L.rf s' sc k = if k = L.size s sc then new else L.rf s sc k :=
        fun k hk => hrf k (by omega)
      refine ⟨hW', ⟨fun k hk => ?_, fun k hk => ?_, ?_⟩, ?_, hp'⟩
      rotate_left 3
      · unfold LawfulStore.amtSum
        rw [hs', Finset.sum_range_succ, hR _ (by omega)]
        have : ∀ k ∈ Finset.range (L.size s sc),
            (L.rf s' sc k).amount.val = (L.rf s sc k).amount.val := by
          intro k hk; simp at hk; rw [hR k (by omega)]; simp [show k ≠ L.size s sc by omega]
        rw [Finset.sum_congr rfl this]; simp only [ite_true]
      · rw [hs'] at hk
        rw [hR k (by omega), hR (k + 1) hk]
        simp only [show k ≠ L.size s sc by omega, ite_false]
        split
        · rename_i e; rw [show k = L.size s sc - 1 by omega]; omega
        · exact hO.disjoint k (by omega)
      · rw [hs'] at hk
        rw [hR k hk]; split
        · exact hno1
        · exact hO.no_overflow k (by omega)
      · rw [hs', hp', hR _ (by omega), hR 0 (by omega)]
        simp only [Nat.add_sub_cancel, ite_true, show (0 : Nat) ≠ L.size s sc by omega, ite_false]
        exact hwin


/-! ### The overrun loop of `refill_budget_check` -/

theorem RefillsOrdered.pop {s s₁ : S} {sc : obj.Sc} {sb : Nat} (hW : RefillsWF st s sc sb)
    (hO : RefillsOrdered st s sc) (hne : L.rhead s sc ≠ L.rtail s sc)
    (hs₁ : s₁ = L.wr s (headA sc) (nextIdx (L.rmax s sc) (L.rhead s sc))) :
    RefillsWF st s₁ sc sb ∧ RefillsOrdered st s₁ sc ∧
      L.amtSum s₁ sc + (L.rf s sc 0).amount.val = L.amtSum s sc ∧ L.rperiod s₁ sc = L.rperiod s sc ∧
      L.size s₁ sc = L.size s sc - 1 ∧ ∀ k, L.rf s₁ sc k = L.rf s sc (k + 1) := by
  obtain ⟨hn, hrf, hp, hm⟩ := hW.pop hne hs₁
  have h2 := hW.size_two hne
  have hW1 : RefillsWF st s₁ sc sb := by rw [hs₁]; exact hW.wr_head (nextIdx_lt hW.head_lt)
  refine ⟨hW1, ⟨fun k hk => ?_, fun k hk => ?_, ?_⟩, ?_, hp, hn, hrf⟩
  · rw [hn] at hk; rw [hrf, hrf]; exact hO.disjoint (k + 1) (by omega)
  · rw [hn] at hk; rw [hrf]; exact hO.no_overflow (k + 1) (by omega)
  · rw [hn, hrf, hrf, hp, show L.size s sc - 1 - 1 + 1 = L.size s sc - 1 by omega]
    have := hO.window; have := hO.disjoint 0 (by omega); simp only [Nat.zero_add] at this ⊢; omega
  · unfold LawfulStore.amtSum
    rw [hn, sum_range_one (fun k => (L.rf s sc k).amount.val) (by omega)]
    have : ∀ k ∈ Finset.range (L.size s sc - 1), (L.rf s₁ sc k).amount.val = (L.rf s sc (k + 1)).amount.val :=
      fun k _ => by rw [hrf]
    rw [Finset.sum_congr rfl this]; omega

/-- `handle_overrun` (the first loop of `refill_budget_check`) preserves the
ordering invariant and the sum of the amounts, if the period and the sum are
at most `B` and the maximum release time is at least `3 B` from overflow
(l4v: `period ≤ MAX_PERIOD`, budget = sum ≤ period, and
`MAX_RELEASE_TIME = max_word - 5 * MAX_PERIOD`). -/
theorem sporadic.budget_check_loop0.ordered {s : S} {sc : obj.Sc} {sb : Nat} (mrt period usage fuel : U64)
    (B : Nat) (hW : RefillsWF st s sc sb) (hO : RefillsOrdered st s sc)
    (hp : L.rperiod s sc = period) (hpB : period.val ≤ B) (hsB : L.amtSum s sc ≤ B)
    (hmrt : mrt.val + 3 * B < 2 ^ 64) :
    sporadic.budget_check_loop0 st s sc mrt period usage fuel ⦃ s' _ =>
      RefillsWF st s' sc sb ∧ RefillsOrdered st s' sc ∧ L.amtSum s' sc = L.amtSum s sc ∧
        L.rperiod s' sc = period ⦄ := by
  unfold sporadic.budget_check_loop0
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => RefillsWF st x.1 sc sb ∧ RefillsOrdered st x.1 sc ∧ L.amtSum x.1 sc = L.amtSum s sc ∧
      L.rperiod x.1 sc = period)
  · rintro ⟨x0, x1, x2⟩ ⟨hW, hO, hS, hP⟩
    dsimp only at hW hO hS hP
    unfold sporadic.budget_check_loop0.body
    have e0 : L.refill x0 sc (L.rhead x0 sc) = L.rf x0 sc 0 := by rw [LawfulStore.rf, hW.ix_zero]
    have hn1 := hW.size_pos
    step
    rw [e0] at r_post
    split
    · split
      · split
        · simp only [WP.spec_ok]; exact ⟨hW, hO, hS, hP⟩
        · rename_i hA hT hf
          simp only [UScalar.le_equiv, UScalar.lt_equiv] at hA hT
          have hsum := hS ▸ hsB
          have hA0 : (L.rf x0 sc 0).amount.val ≤ L.amtSum x0 sc := by
            unfold LawfulStore.amtSum; rw [sum_range_one _ hn1]; omega
          step; step
          split
          · -- a single refill: move it a period later
            have h1 : L.size x0 sc = 1 := (hW.single_iff).1 (by simp_all)
            step; step with sporadic.set_head.eq
            clear hp; subst_vars
            have hiv : (core.num.U64.wrapping_add (L.rf x0 sc 0).time (L.rperiod x0 sc)).val =
                (L.rf x0 sc 0).time.val + (L.rperiod x0 sc).val := wadd_val (by omega)
            have hl : (L.rhead x0 sc).val < (L.rmax x0 sc).val := hW.head_lt
            obtain ⟨h8, hb, hfit⟩ := hW.bounds
            simp only [lift, bind_ok, WP.spec_ok]
            have hs' := hW.size_putS (r := { L.rf x0 sc 0 with
              time := core.num.U64.wrapping_add (L.rf x0 sc 0).time (L.rperiod x0 sc) }) hl
            refine ⟨hW.putS hl, RefillsOrdered.single (by rw [hs', h1]) ?_, ?_, ?_, by omega⟩
            · rw [hW.rf_set_head (by omega)]; simp only [ite_true]; rw [hiv]; omega
            · unfold LawfulStore.amtSum; rw [hs', h1]
              simp only [Finset.sum_range_one]; rw [hW.rf_set_head (by omega)]; simp
              unfold LawfulStore.amtSum at hS; rw [h1] at hS; simpa using hS
            · rw [rperiod_putS h8 (by omega)]
          · -- pop the head and schedule it a period later
            have hne : L.rhead x0 sc ≠ L.rtail x0 sc := by intro e; simp_all
            have h2 := hW.size_two hne
            step with sporadic.pop_head.eq
            obtain ⟨old, s2⟩ := s1
            simp only at s1_post s1_post1 ⊢
            rw [e0] at s1_post
            subst s1_post r_post
            obtain ⟨hW2, hO2, hS2, hP2, hn2, hrf2⟩ := hO.pop hW hne s1_post1
            have od0 := hO.disjoint 0 (by omega); simp only [Nat.zero_add] at od0
            have hwin0 := hO.window
            have hPv : (L.rperiod x0 sc).val = period.val := by rw [hP]
            have hT' : (core.num.U64.wrapping_add (L.rf x0 sc 0).time period).val =
                (L.rf x0 sc 0).time.val + period.val := wadd_val (by omega)
            have htail : (L.rf x0 sc (L.size x0 sc - 1)).amount.val + (L.rf x0 sc 0).amount.val ≤
                L.amtSum x0 sc := by
              unfold LawfulStore.amtSum; rw [sum_range_one _ hn1]
              have := Finset.single_le_sum (f := fun k => (L.rf x0 sc (k + 1)).amount.val)
                (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (show L.size x0 sc - 2 < L.size x0 sc - 1 by omega))
              simp only [show L.size x0 sc - 2 + 1 = L.size x0 sc - 1 by omega] at this; omega
            simp only [lift, bind_ok]
            refine WP.spec_bind (sporadic.schedule_used.ordered _ hW2 hO2 ?_ ?_ ?_) ?_
            · rw [hT', hrf2, hP2, hP]; simp only [Nat.zero_add]; omega
            · dsimp only; rw [hT']; omega
            · rw [hn2, hrf2, show L.size x0 sc - 1 - 1 + 1 = L.size x0 sc - 1 by omega]
              dsimp only; omega
            · rintro s3 ⟨hW3, hO3, hS3, hP3⟩
              simp only [WP.spec_ok]
              refine ⟨hW3, hO3, ?_, by rw [hP3, hP2, hP], by omega⟩
              rw [hS3, ← hS]; dsimp only; omega
      · simp only [WP.spec_ok]; exact ⟨hW, hO, hS, hP⟩
    · simp only [WP.spec_ok]; exact ⟨hW, hO, hS, hP⟩
  · exact ⟨hW, hO, rfl, hp⟩


/-- How the overrun loop ends: with the head's amount above the remaining
usage or the head at or past `mrt`, unless its fuel ran out, which can only
happen if it ran at least once (so the first head's amount was at most the
usage). -/
theorem sporadic.budget_check_loop0.exit {s : S} {sc : obj.Sc} {sb : Nat} (mrt period usage fuel : U64)
    (hW : RefillsWF st s sc sb) :
    sporadic.budget_check_loop0 st s sc mrt period usage fuel ⦃ s' u' =>
      (u'.val < (L.refill s' sc (L.rhead s' sc)).amount.val ∨
        mrt.val ≤ (L.refill s' sc (L.rhead s' sc)).time.val) ∨
      fuel.val = 0 ∨ (L.refill s sc (L.rhead s sc)).amount.val ≤ usage.val ⦄ := by
  unfold sporadic.budget_check_loop0
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val)
    (inv := fun x => RefillsWF st x.1 sc sb ∧ ((x.2.2 = fuel ∧ x.1 = s ∧ x.2.1 = usage) ∨
      (L.refill s sc (L.rhead s sc)).amount.val ≤ usage.val))
  · rintro ⟨x0, x1, x2⟩ ⟨hW, hI⟩
    dsimp only at hW hI
    unfold sporadic.budget_check_loop0.body
    step
    split
    · split
      · split
        · simp only [WP.spec_ok]
          right
          rcases hI with ⟨rfl, -, -⟩ | h
          · left; simp_all
          · right; exact h
        · step*
          split <;> step*
          p0_cases_prod; step*
      · simp only [WP.spec_ok]; left; right; simp_all [UScalar.lt_equiv]
    · simp only [WP.spec_ok]; left; left; simp_all [UScalar.le_equiv]
  · exact ⟨hW, Or.inl ⟨rfl, rfl, rfl⟩⟩


theorem amt_head_tail_le {s : S} {sc : obj.Sc} (h2 : 2 ≤ L.size s sc) :
    (L.rf s sc (L.size s sc - 1)).amount.val + (L.rf s sc 0).amount.val ≤ L.amtSum s sc := by
  unfold LawfulStore.amtSum; rw [sum_range_one _ (by omega)]
  have := Finset.single_le_sum (f := fun k => (L.rf s sc (k + 1)).amount.val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (show L.size s sc - 2 < L.size s sc - 1 by omega))
  simp only [show L.size s sc - 2 + 1 = L.size s sc - 1 by omega] at this; omega

theorem amt_head_le {s : S} {sc : obj.Sc} (h1 : 1 ≤ L.size s sc) :
    (L.rf s sc 0).amount.val ≤ L.amtSum s sc := by
  unfold LawfulStore.amtSum; rw [sum_range_one _ h1]; omega

/-- `refill_budget_check` preserves the ordering invariant of the current SC
when the usage is below the head refill's amount (no overrun), the period
and the sum of the amounts are at most `B`, and the maximum release time is
at least `3 B` from overflow. (With an overrun, see `sporadic.budget_check_loop0.ordered`
and the report: the loop's fuel can run out before seL4's loop would stop.) -/
theorem sporadic.budget_check.ordered {S : Type _} {st : machine.Store S} [L : LawfulStore st] {s : S}
    {sc : obj.Sc} {sb : Nat} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (a : A)
    (usage : U64) (B : Nat) (hW : RefillsWF st s sc sb) (hO : RefillsOrdered st s sc)
    (hcur : L.mem s (L.nodeA s layout.node.CUR_SC) = sc)
    (hpB : (L.rperiod s sc).val ≤ B) (hsB : L.amtSum s sc ≤ B)
    (hmrt : sporadic.max_release_time ar a ⦃ mrt => mrt.val + 3 * B < 2 ^ 64 ⦄)
    (hno : usage.val < (L.rf s sc 0).amount.val) :
    sporadic.budget_check st ar s a usage ⦃ s' => RefillsWF st s' sc sb ∧ RefillsOrdered st s' sc ⦄ := by
  unfold sporadic.budget_check
  step; step
  have e : i1 = sc := by subst i_post i1_post; exact hcur
  subst e
  step with hmrt
  step; step; step
  have e0 : L.refill s i1 (L.rhead s i1) = L.rf s i1 0 := by rw [LawfulStore.rf, hW.ix_zero]
  have hfuel : fuel.val ≠ 0 := by
    rw [fuel_post, wadd_val (by have := absMax_lt sb; have := hW.le_abs; rw [i2_post]; simp; omega)]; simp
  step with WP.spec_and (sporadic.budget_check_loop0.ordered mrt period usage fuel B hW hO period_post.symm
    (by rw [period_post]; exact hpB) hsB mrt_post) (sporadic.budget_check_loop0.exit mrt period usage fuel hW)
  rename_i usage0 hP1
  have hW1 := s1_post; have hO1 := s1_post1; have hS1 := s1_post2
  have e1 : L.refill s1 i1 (L.rhead s1 i1) = L.rf s1 i1 0 := by rw [LawfulStore.rf, hW1.ix_zero]
  have hex := s1_post3
  rw [e1, e0] at hex
  have tail : ∀ s2, RefillsWF st s2 i1 sb → RefillsOrdered st s2 i1 →
      (do
        let mb ← sporadic.min_budget ar a
        let i3 ← obj.Sc.refill_max st i1 s2
        let fuel2 ← lift (core.num.U64.wrapping_add i3 2#u64)
        sporadic.budget_check_loop1 st s2 i1 mb fuel2) ⦃ s' => RefillsWF st s' i1 sb ∧ RefillsOrdered st s' i1 ⦄ := by
    intro s2 h1 h2
    step; step; step
    exact sporadic.budget_check_loop1.ordered _ _ h1 h2
  step
  rw [e1] at h_post
  split
  · split
    · rename_i hu hT
      simp only [UScalar.lt_equiv, gt_iff_lt] at hu hT
      have hlt : usage.val < (L.rf s1 i1 0).amount.val := by
        rcases hex with (h | h) | h | h
        · exact h
        · subst h_post; omega
        · exact absurd h hfuel
        · omega
      subst h_post
      have hPv : (L.rperiod s1 i1).val = period.val := by rw [period_post]
      have hPv' : period.val = (L.rperiod s i1).val := by rw [hP1]
      have hSB : L.amtSum s1 i1 ≤ B := by rw [hS1]; exact hsB
      have hn1 := hW1.size_pos; have hnle := hW1.size_le
      have hA0 := amt_head_le (L := L) (s := s1) (sc := i1) hn1
      have no0 := hO1.no_overflow 0 (by omega)
      have win1 := hO1.window
      have hhl := hW1.head_lt
      obtain ⟨h8, hb, hfit⟩ := hW1.bounds
      refine WP.spec_bind (Pₘ := fun s2 => RefillsWF st s2 i1 sb ∧ RefillsOrdered st s2 i1) ?_
        (fun s2 h => tail s2 h.1 h.2)
      simp only [lift, bind_ok]
      refine WP.spec_bind (sporadic.set_head.eq _ _ _) ?_
      rintro s3 rfl
      have htu : (core.num.U64.wrapping_add (L.rf s1 i1 0).time usage).val =
          (L.rf s1 i1 0).time.val + usage.val := wadd_val (by omega)
      have hau : (core.num.U64.wrapping_sub (L.rf s1 i1 0).amount usage).val =
          (L.rf s1 i1 0).amount.val - usage.val := wsub_val (by omega)
      have htp : (core.num.U64.wrapping_add (L.rf s1 i1 0).time period).val =
          (L.rf s1 i1 0).time.val + period.val := wadd_val (by omega)
      generalize hnr : ({ time := core.num.U64.wrapping_add (L.rf s1 i1 0).time usage, amount := core.num.U64.wrapping_sub (L.rf s1 i1 0).amount usage } : sporadic.Refill) = nr
      have hnt : nr.time.val = (L.rf s1 i1 0).time.val + usage.val := by rw [← hnr]; exact htu
      have hna : nr.amount.val = (L.rf s1 i1 0).amount.val - usage.val := by rw [← hnr]; exact hau
      have hW3 := hW1.putS (r := nr) hhl
      have hn3 := hW1.size_putS (r := nr) hhl
      have hp3 : L.rperiod (L.putS s1 i1 (L.rhead s1 i1) nr) i1 = L.rperiod s1 i1 :=
        rperiod_putS h8 (by omega)
      have hR : ∀ k, k < L.size s1 i1 → L.rf (L.putS s1 i1 (L.rhead s1 i1)
          nr) i1 k =
          if k = 0 then nr else L.rf s1 i1 k :=
        fun k hk => hW1.rf_set_head (by omega)
      have hO3 : RefillsOrdered st (L.putS s1 i1 (L.rhead s1 i1)
          nr) i1 := by
        refine ⟨fun k hk => ?_, fun k hk => ?_, ?_⟩
        · rw [hn3] at hk; rw [hR k (by omega), hR (k + 1) hk]
          simp only [show k + 1 ≠ 0 by omega, ite_false]
          split
          · subst k; rw [hnt, hna]
            have := hO1.disjoint 0 hk; simp only [Nat.zero_add] at this ⊢; omega
          · exact hO1.disjoint k hk
        · rw [hn3] at hk; rw [hR k hk]; split
          · rw [hnt, hna]; omega
          · exact hO1.no_overflow k hk
        · rw [hn3, hp3, hR _ (by omega), hR 0 hn1]; simp only [ite_true]
          split
          · omega
          · rw [hnt]; omega
      refine WP.spec_mono (sporadic.schedule_used.ordered _ hW3 hO3 ?_ ?_ ?_) (fun _ h => ⟨h.1, h.2.1⟩)
      · rw [hR 0 hn1, hp3]; simp only [ite_true]; rw [hnt, htp]; omega
      · dsimp only; rw [htp]; omega
      · rw [hn3, hR _ (by omega)]
        split
        · rename_i h0; (try dsimp only); rw [hnt, hna]; omega
        · have := amt_head_tail_le (L := L) (s := s1) (sc := i1) (by omega)
          (try dsimp only); omega
    · simp only [bind_ok]; exact tail s1 hW1 hO1
  · simp only [bind_ok]; exact tail s1 hW1 hO1

end
end Fl4Proofs.P1
