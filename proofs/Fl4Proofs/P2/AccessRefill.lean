/-
# P2: guarded-store lemmas for the refill code (sporadic.rs)

For the per-path obligation of `P2/PathObl.lean`: the refill-ring operations
of an SC `sc` of size `2 ^ sb`, run on `guard st R W`, are the runs on `st`,
when `R` holds every word of the SC and `W` its ring part (`InRing`: from
`REFILL_HEAD` on) and its `CONSUMED` word (`ScAcc`), and P1's ring invariant
`RefillsWF` holds at the entry state (it bounds every ring index the code
reads, so every address stays inside the SC; P1's `*.wf` lemmas carry it
along the run, and `loop_guard_congr` along the loops):

* ring operations: `sporadic.put`, `tail`, `set_head`, `set_tail`,
  `next_index`, `single`, `size`, `full`, `head_overlapping`, `pop_head`,
  `add_tail`, `schedule_used`;
* loops: `sporadic.unblock_check_loop`, `budget_check_loop0`,
  `budget_check_loop1`;
* `sporadic.unblock_check` (also the node's `CUR_TIME` read and `REPROGRAM`
  write), `sporadic.budget_check` (the node's `CUR_SC` read).

Generic over the Arch instance (no Arch premise). No premises.
-/
import Fl4Proofs.P2.AccessSched
import Fl4Proofs.P1.QueueSc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts

theorem post_of_ok {α : Type _} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) {x : α} (e : m = ok x) :
    P x := by
  obtain ⟨v, hv, hp⟩ := spec_ex_fd h
  rw [e] at hv
  rw [ok_inj_ff hv]; exact hp

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]

/-- The guarded sets hold the SC `sc` of size `2 ^ sb`: every word readable,
the ring part and `CONSUMED` writable. -/
structure ScAcc (R W : U64 → Prop) (sc : U64) (sb : Nat) : Prop where
  rd : ∀ b, InSC sc sb b → Aligned b → R b
  wr : ∀ b, InRing sc sb b → Aligned b → W b
  cons : W (core.num.U64.wrapping_add sc layout.sc.CONSUMED)

variable {s : S} {sc : obj.Sc} {sb : Nat}

theorem ScAcc.off (hS : ScAcc R W sc sb) (h : RefillsWF st s sc sb) (K : U64) (hK : K.val < 96)
    (hK8 : K.val % 8 = 0 := by simp) :
    R (core.num.U64.wrapping_add sc K) := by
  obtain ⟨h8, hm, hfit⟩ := h.bounds
  obtain ⟨h96, -⟩ := h.inside
  have e : (core.num.U64.wrapping_add sc K).val = sc.val + K.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  exact hS.rd _ ⟨by omega, by omega⟩ (by unfold Aligned; omega)

theorem ScAcc.offW (hS : ScAcc R W sc sb) (h : RefillsWF st s sc sb) (K : U64) (hK : 80 ≤ K.val)
    (hK' : K.val < 96) (hK8 : K.val % 8 = 0 := by simp) : W (core.num.U64.wrapping_add sc K) := by
  obtain ⟨h8, hm, hfit⟩ := h.bounds
  obtain ⟨h96, -⟩ := h.inside
  have e : (core.num.U64.wrapping_add sc K).val = sc.val + K.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  exact hS.wr _ ⟨by omega, by omega⟩ (by unfold Aligned; omega)

theorem ScAcc.rt (hS : ScAcc R W sc sb) (h : RefillsWF st s sc sb) {i : U64} (hi : i.val < (L.rmax s sc).val) :
    R (rtA sc i) ∧ W (rtA sc i) ∧ R (raA sc i) ∧ W (raA sc i) := by
  obtain ⟨h8, -⟩ := h.bounds
  obtain ⟨-, -, -, -, -, hin⟩ := h.inside
  obtain ⟨e1, e2, e3⟩ := hin i hi
  have a1 : Aligned (rtA sc i) := by unfold Aligned; omega
  have a2 : Aligned (raA sc i) := by unfold Aligned; omega
  exact ⟨hS.rd _ ⟨by omega, by omega⟩ a1, hS.wr _ ⟨by omega, by omega⟩ a1, hS.rd _ ⟨by omega, by omega⟩ a2,
    hS.wr _ ⟨by omega, by omega⟩ a2⟩

theorem ScAcc.head (hS : ScAcc R W sc sb) (h : RefillsWF st s sc sb) : RdHead (L := L) R s sc := by
  obtain ⟨a, -, b, -⟩ := hS.rt h h.head_lt
  exact ⟨hS.off h _ (by simp), a, b⟩

/-! ## Ring operations -/

theorem obj.Sc.set_r_time.guard (s : S) (i v : U64) (h : W (rtA sc i)) :
    obj.Sc.set_r_time (PathObl.guard st R W) sc s i v = obj.Sc.set_r_time st sc s i v := by
  unfold obj.Sc.set_r_time
  rw [eq_ok_of_spec (obj.Sc.refill_addr.spec sc i)]
  simp only [bind_ok]
  exact guard_write h

theorem obj.Sc.set_r_amount.guard (s : S) (i v : U64) (h : W (raA sc i)) :
    obj.Sc.set_r_amount (PathObl.guard st R W) sc s i v = obj.Sc.set_r_amount st sc s i v := by
  unfold obj.Sc.set_r_amount
  rw [eq_ok_of_spec (obj.Sc.refill_addr.spec sc i)]
  simp only [lift, bind_ok]
  exact guard_write_of h rfl

theorem sporadic.put.guard (s : S) (i : U64) (r : sporadic.Refill) (ht : W (rtA sc i)) (ha : W (raA sc i)) :
    sporadic.put (PathObl.guard st R W) s sc i r = sporadic.put st s sc i r := by
  unfold sporadic.put
  rw [obj.Sc.set_r_time.guard s i _ ht]
  refine bind_guard_congr rfl fun s1 _ => ?_
  exact obj.Sc.set_r_amount.guard s1 i _ ha

variable (hS : ScAcc R W sc sb)
include hS

theorem sporadic.head.guardS (h : RefillsWF st s sc sb) :
    sporadic.head (PathObl.guard st R W) s sc = sporadic.head st s sc :=
  sporadic.head.guard s sc (hS.head h)

theorem sporadic.tail.guardS (h : RefillsWF st s sc sb) :
    sporadic.tail (PathObl.guard st R W) s sc = sporadic.tail st s sc := by
  unfold sporadic.tail
  rw [obj.Sc.refill_tail.guard sc s (hS.off h _ (by simp)), eq_ok_of_spec (obj.Sc.refill_tail.spec s sc)]
  simp only [bind_ok]
  obtain ⟨a, -, b, -⟩ := hS.rt h h.tail_lt
  exact sporadic.get.guard s sc _ a b

theorem sporadic.set_head.guardS (h : RefillsWF st s sc sb) (r : sporadic.Refill) :
    sporadic.set_head (PathObl.guard st R W) s sc r = sporadic.set_head st s sc r := by
  unfold sporadic.set_head
  rw [obj.Sc.refill_head.guard sc s (hS.off h _ (by simp)), eq_ok_of_spec (obj.Sc.refill_head.spec s sc)]
  simp only [bind_ok]
  obtain ⟨-, a, -, b⟩ := hS.rt h h.head_lt
  exact sporadic.put.guard s _ r a b

theorem sporadic.set_tail.guardS (h : RefillsWF st s sc sb) (r : sporadic.Refill) :
    sporadic.set_tail (PathObl.guard st R W) s sc r = sporadic.set_tail st s sc r := by
  unfold sporadic.set_tail
  rw [obj.Sc.refill_tail.guard sc s (hS.off h _ (by simp)), eq_ok_of_spec (obj.Sc.refill_tail.spec s sc)]
  simp only [bind_ok]
  obtain ⟨-, a, -, b⟩ := hS.rt h h.tail_lt
  exact sporadic.put.guard s _ r a b

theorem sporadic.next_index.guardS (h : RefillsWF st s sc sb) (i : U64) :
    sporadic.next_index (PathObl.guard st R W) s sc i = sporadic.next_index st s sc i := by
  unfold sporadic.next_index
  rw [obj.Sc.refill_max.guard sc s (hS.off h _ (by simp))]

theorem sporadic.single.guardS (h : RefillsWF st s sc sb) :
    sporadic.single (PathObl.guard st R W) s sc = sporadic.single st s sc := by
  unfold sporadic.single
  rw [obj.Sc.refill_head.guard sc s (hS.off h _ (by simp)), obj.Sc.refill_tail.guard sc s (hS.off h _ (by simp))]

theorem sporadic.size.guardS (h : RefillsWF st s sc sb) :
    sporadic.size (PathObl.guard st R W) s sc = sporadic.size st s sc := by
  unfold sporadic.size
  rw [obj.Sc.refill_head.guard sc s (hS.off h _ (by simp)), obj.Sc.refill_tail.guard sc s (hS.off h _ (by simp)),
    obj.Sc.refill_max.guard sc s (hS.off h _ (by simp))]

theorem sporadic.full.guardS (h : RefillsWF st s sc sb) :
    sporadic.full (PathObl.guard st R W) s sc = sporadic.full st s sc := by
  unfold sporadic.full
  rw [sporadic.size.guardS hS h, obj.Sc.refill_max.guard sc s (hS.off h _ (by simp))]

theorem sporadic.head_overlapping.guardS (h : RefillsWF st s sc sb) :
    sporadic.head_overlapping (PathObl.guard st R W) s sc = sporadic.head_overlapping st s sc := by
  unfold sporadic.head_overlapping
  rw [sporadic.single.guardS hS h, sporadic.head.guardS hS h,
    obj.Sc.refill_head.guard sc s (hS.off h _ (by simp)), eq_ok_of_spec (obj.Sc.refill_head.spec s sc)]
  simp only [bind_ok, sporadic.next_index.guardS hS h]
  rw [eq_ok_of_spec (sporadic.next_index.spec s sc (L.rhead s sc))]
  simp only [bind_ok]
  obtain ⟨a, -, b, -⟩ := hS.rt h (nextIdx_lt h.head_lt)
  rw [sporadic.get.guard s sc _ a b]

theorem sporadic.pop_head.guardS (h : RefillsWF st s sc sb) :
    sporadic.pop_head (PathObl.guard st R W) s sc = sporadic.pop_head st s sc := by
  unfold sporadic.pop_head
  rw [sporadic.head.guardS hS h, obj.Sc.refill_head.guard sc s (hS.off h _ (by simp)),
    eq_ok_of_spec (obj.Sc.refill_head.spec s sc)]
  simp only [bind_ok, sporadic.next_index.guardS hS h,
    obj.Sc.set_refill_head.guard sc s _ (hS.offW h _ (by simp) (by simp))]

theorem sporadic.add_tail.guardS (h : RefillsWF st s sc sb) (r : sporadic.Refill) :
    sporadic.add_tail (PathObl.guard st R W) s sc r = sporadic.add_tail st s sc r := by
  unfold sporadic.add_tail
  rw [obj.Sc.refill_tail.guard sc s (hS.off h _ (by simp)), eq_ok_of_spec (obj.Sc.refill_tail.spec s sc)]
  simp only [bind_ok]
  rw [sporadic.next_index.guardS hS h, eq_ok_of_spec (sporadic.next_index.spec s sc _)]
  simp only [bind_ok]
  rw [obj.Sc.set_refill_tail.guard sc s _ (hS.offW h _ (by simp) (by simp))]
  refine bind_guard_congr rfl fun s1 _ => ?_
  obtain ⟨-, a, -, b⟩ := hS.rt h (nextIdx_lt h.tail_lt)
  exact sporadic.put.guard s1 _ r a b

theorem sporadic.schedule_used.guardS (h : RefillsWF st s sc sb) (r : sporadic.Refill) :
    sporadic.schedule_used (PathObl.guard st R W) s sc r = sporadic.schedule_used st s sc r := by
  unfold sporadic.schedule_used
  simp only [sporadic.tail.guardS hS h, sporadic.set_tail.guardS hS h, sporadic.full.guardS hS h,
    sporadic.add_tail.guardS hS h]

/-! ## Loops -/

theorem sporadic.unblock_check_loop.guardS (h : RefillsWF st s sc sb) (fuel : U64) :
    sporadic.unblock_check_loop (PathObl.guard st R W) s sc fuel = sporadic.unblock_check_loop st s sc fuel := by
  unfold sporadic.unblock_check_loop
  refine loop_guard_congr (fun x => RefillsWF st x.1 sc sb) (fun x => x.2.val) ?_ (s, fuel) h
  rintro ⟨x0, x1⟩ hx
  simp only at hx
  try dsimp only
  unfold sporadic.unblock_check_loop.body
  refine ⟨?_, ?_⟩
  · simp only [sporadic.head_overlapping.guardS hS hx, sporadic.pop_head.guardS hS hx]
    refine bind_guard_congr rfl fun b _ => ?_
    split
    · split
      · refine bind_guard_congr rfl fun f1 _ => ?_
        refine bind_guard_congr rfl fun p hp => ?_
        obtain ⟨old, s1⟩ := p
        have h1 : RefillsWF st s1 sc sb := post_of_ok (sporadic.pop_head.wf hx) hp
        simp only [Aeneas.Std.uncurry_apply_pair]
        simp only [sporadic.head.guardS hS h1, sporadic.set_head.guardS hS h1]
      · rfl
    · rfl
  · intro y hy
    try dsimp only at hy
    obtain ⟨b, -, hy⟩ := bind_eq_ok hy
    split at hy
    · split at hy
      · obtain ⟨f1, ef, hy⟩ := bind_eq_ok hy
        obtain ⟨p, hp, hy⟩ := bind_eq_ok hy
        obtain ⟨old, s1⟩ := p
        have h1 : RefillsWF st s1 sc sb := post_of_ok (sporadic.pop_head.wf hx) hp
        simp only [Aeneas.Std.uncurry_apply_pair] at hy
        obtain ⟨hd, -, hy⟩ := bind_eq_ok hy
        obtain ⟨i, -, hy⟩ := bind_eq_ok hy
        obtain ⟨s2, hs2, hy⟩ := bind_eq_ok hy
        have h2 : RefillsWF st s2 sc sb := post_of_ok (sporadic.set_head.wf _ h1) hs2
        cases ok_inj_ff hy
        refine ⟨h2, ?_⟩
        obtain ⟨z, hz, hv⟩ := spec_ex_fd (U64.sub_spec (x := x1) (y := 1#u64) (by scalar_tac))
        rw [hz] at ef
        cases ok_inj_ff ef
        simp only
        scalar_tac
      · simp at hy
    · simp at hy

theorem sporadic.budget_check_loop1.guardS (h : RefillsWF st s sc sb) (mb fuel2 : U64) :
    sporadic.budget_check_loop1 (PathObl.guard st R W) s sc mb fuel2 = sporadic.budget_check_loop1 st s sc mb fuel2 := by
  unfold sporadic.budget_check_loop1
  refine loop_guard_congr (fun x => RefillsWF st x.1 sc sb) (fun x => x.2.val) ?_ (s, fuel2) h
  rintro ⟨x0, x1⟩ hx
  simp only at hx
  try dsimp only
  unfold sporadic.budget_check_loop1.body
  refine ⟨?_, ?_⟩
  · simp only [sporadic.head.guardS hS hx, sporadic.single.guardS hS hx, sporadic.pop_head.guardS hS hx]
    refine bind_guard_congr rfl fun r _ => ?_
    split
    · refine bind_guard_congr rfl fun b _ => ?_
      split
      · rfl
      · split
        · refine bind_guard_congr rfl fun f1 _ => ?_
          refine bind_guard_congr rfl fun p hp => ?_
          obtain ⟨old, s1⟩ := p
          have h1 : RefillsWF st s1 sc sb := post_of_ok (sporadic.pop_head.wf hx) hp
          simp only [Aeneas.Std.uncurry_apply_pair]
          simp only [sporadic.head.guardS hS h1, sporadic.set_head.guardS hS h1]
        · rfl
    · rfl
  · intro y hy
    try dsimp only at hy
    obtain ⟨r, -, hy⟩ := bind_eq_ok hy
    split at hy
    · obtain ⟨b, -, hy⟩ := bind_eq_ok hy
      split at hy
      · simp at hy
      · split at hy
        · obtain ⟨f1, ef, hy⟩ := bind_eq_ok hy
          obtain ⟨p, hp, hy⟩ := bind_eq_ok hy
          obtain ⟨old, s1⟩ := p
          have h1 : RefillsWF st s1 sc sb := post_of_ok (sporadic.pop_head.wf hx) hp
          simp only [Aeneas.Std.uncurry_apply_pair] at hy
          obtain ⟨hd, -, hy⟩ := bind_eq_ok hy
          obtain ⟨i1, -, hy⟩ := bind_eq_ok hy
          obtain ⟨i2, -, hy⟩ := bind_eq_ok hy
          obtain ⟨s2, hs2, hy⟩ := bind_eq_ok hy
          have h2 : RefillsWF st s2 sc sb := post_of_ok (sporadic.set_head.wf _ h1) hs2
          cases ok_inj_ff hy
          refine ⟨h2, ?_⟩
          obtain ⟨z, hz, hv⟩ := spec_ex_fd (U64.sub_spec (x := x1) (y := 1#u64) (by scalar_tac))
          rw [hz] at ef
          cases ok_inj_ff ef
          simp only
          scalar_tac
        · simp at hy
    · simp at hy

theorem sporadic.budget_check_loop0.guardS (h : RefillsWF st s sc sb) (mrt period usage fuel : U64) :
    sporadic.budget_check_loop0 (PathObl.guard st R W) s sc mrt period usage fuel =
      sporadic.budget_check_loop0 st s sc mrt period usage fuel := by
  unfold sporadic.budget_check_loop0
  refine loop_guard_congr (fun x => RefillsWF st x.1 sc sb) (fun x => x.2.2.val) ?_ (s, usage, fuel) h
  rintro ⟨x0, x1, x2⟩ hx
  simp only at hx
  try dsimp only
  unfold sporadic.budget_check_loop0.body
  refine ⟨?_, ?_⟩
  · simp only [sporadic.head.guardS hS hx, sporadic.single.guardS hS hx, sporadic.set_head.guardS hS hx,
      sporadic.pop_head.guardS hS hx]
    refine bind_guard_congr rfl fun r _ => ?_
    split
    · split
      · split
        · rfl
        · split
          · rfl
          · refine bind_guard_congr rfl fun f1 _ => ?_
            refine bind_guard_congr rfl fun b _ => ?_
            refine bind_guard_congr ?_ fun s1 _ => rfl
            split
            · rfl
            · refine bind_guard_congr rfl fun p hp => ?_
              obtain ⟨old, s2⟩ := p
              have h2 : RefillsWF st s2 sc sb := post_of_ok (sporadic.pop_head.wf hx) hp
              simp only [Aeneas.Std.uncurry_apply_pair]
              simp only [sporadic.schedule_used.guardS hS h2]
      · rfl
    · rfl
  · intro y hy
    try dsimp only at hy
    obtain ⟨r, -, hy⟩ := bind_eq_ok hy
    split at hy
    · split at hy
      · split at hy
        · simp at hy
        · split at hy
          · simp at hy
          · obtain ⟨f1, ef, hy⟩ := bind_eq_ok hy
            obtain ⟨b, -, hy⟩ := bind_eq_ok hy
            obtain ⟨s1, hs1, hy⟩ := bind_eq_ok hy
            have h1 : RefillsWF st s1 sc sb := by
              split at hs1
              · obtain ⟨i1, -, hs1⟩ := bind_eq_ok hs1
                exact post_of_ok (sporadic.set_head.wf _ hx) hs1
              · obtain ⟨p, hp, hs1⟩ := bind_eq_ok hs1
                obtain ⟨old, s2⟩ := p
                have h2 : RefillsWF st s2 sc sb := post_of_ok (sporadic.pop_head.wf hx) hp
                simp only [Aeneas.Std.uncurry_apply_pair] at hs1
                obtain ⟨i1, -, hs1⟩ := bind_eq_ok hs1
                exact post_of_ok (sporadic.schedule_used.wf _ h2) hs1
            obtain ⟨u1, -, hy⟩ := bind_eq_ok hy
            cases ok_inj_ff hy
            refine ⟨h1, ?_⟩
            have hx2 : x2 ≠ 0#u64 := by assumption
            obtain ⟨z, hz, hv⟩ := spec_ex_fd (U64.sub_spec (x := x2) (y := 1#u64) (by
              have : x2.val ≠ 0 := fun e => hx2 (UScalar.eq_of_val_eq (by simpa using e))
              scalar_tac))
            rw [hz] at ef
            cases ok_inj_ff ef
            simp only
            scalar_tac
      · simp at hy
    · simp at hy

end

end Fl4Proofs.P2.PathObl
