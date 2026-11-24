/-
# P2: guarded-store lemmas for the refill ring (line p2io)

As `P2/AccessSched.lean` (line p2sl: `r_time`, `r_amount`, `get`, `head`,
`capacity`, `sufficient`, `ready`), for the remaining refill helpers of
`P1/Refill.lean`'s model: on `guard st R W` each answers as on `st`, given the
words it reads and writes, named at its entry state with P1's addresses and
stored fields (`headA`, `tailA`, `maxA`, `rtA`, `raA`; `L.rhead`, `L.rtail`,
`L.rmax`, `nextIdx`). A hypothesis may name a word a given run does not touch.

* writes: `obj.Sc.set_r_time`, `set_r_amount`, `sporadic.put` (`WrRefill`: both
  words of a refill), `sporadic.set_head`, `sporadic.set_tail`;
* reads: `sporadic.single`, `next_index`, `tail`, `size`, `full`,
  `head_overlapping`;
* `sporadic.pop_head`, `sporadic.add_tail`, `sporadic.schedule_used`.

Premises: none.
-/
import Fl4Proofs.P2.AccessCSpace
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop}

theorem obj.Sc.set_r_time.guard (sc : obj.Sc) (s : S) (i v : U64) (h : W (rtA sc i)) :
    obj.Sc.set_r_time (PathObl.guard st R W) sc s i v = obj.Sc.set_r_time st sc s i v := by
  unfold obj.Sc.set_r_time obj.Sc.refill_addr
  simp only [lift, bind_ok]
  exact guard_write_of h rfl

theorem obj.Sc.set_r_amount.guard (sc : obj.Sc) (s : S) (i v : U64) (h : W (raA sc i)) :
    obj.Sc.set_r_amount (PathObl.guard st R W) sc s i v = obj.Sc.set_r_amount st sc s i v := by
  unfold obj.Sc.set_r_amount obj.Sc.refill_addr
  simp only [lift, bind_ok]
  exact guard_write_of h rfl

/-- Both words of refill `i` are writable. -/
abbrev WrRefill (W : U64 → Prop) (sc : obj.Sc) (i : U64) : Prop := W (rtA sc i) ∧ W (raA sc i)

/-- Both words of refill `i` are readable. -/
abbrev RdRefill (R : U64 → Prop) (sc : obj.Sc) (i : U64) : Prop := R (rtA sc i) ∧ R (raA sc i)

theorem sporadic.put.guard (s : S) (sc : obj.Sc) (i : U64) (r : sporadic.Refill) (h : WrRefill W sc i) :
    sporadic.put (PathObl.guard st R W) s sc i r = sporadic.put st s sc i r := by
  unfold sporadic.put
  rw [obj.Sc.set_r_time.guard sc s i _ h.1]
  have e : ∀ s1, obj.Sc.set_r_amount (PathObl.guard st R W) sc s1 i r.amount =
      obj.Sc.set_r_amount st sc s1 i r.amount := fun s1 => obj.Sc.set_r_amount.guard sc s1 i _ h.2
  simp only [e]

section law
variable [L : LawfulStore st]

theorem rhead_ok (s : S) (sc : obj.Sc) : obj.Sc.refill_head st sc s = ok (L.rhead s sc) :=
  eq_ok_of_spec (obj.Sc.refill_head.spec (L := L) s sc)

theorem rtail_ok (s : S) (sc : obj.Sc) : obj.Sc.refill_tail st sc s = ok (L.rtail s sc) :=
  eq_ok_of_spec (obj.Sc.refill_tail.spec (L := L) s sc)

theorem rmax_ok (s : S) (sc : obj.Sc) : obj.Sc.refill_max st sc s = ok (L.rmax s sc) :=
  eq_ok_of_spec (obj.Sc.refill_max.spec (L := L) s sc)

theorem next_index_ok (s : S) (sc : obj.Sc) (i : U64) :
    sporadic.next_index st s sc i = ok (nextIdx (L.rmax s sc) i) := by
  unfold sporadic.next_index nextIdx
  rw [rmax_ok]; simp only [lift, bind_ok]
  split_ifs <;> rfl

theorem sporadic.single.guard (s : S) (sc : obj.Sc) (h1 : R (headA sc)) (h2 : R (tailA sc)) :
    sporadic.single (PathObl.guard st R W) s sc = sporadic.single st s sc := by
  unfold sporadic.single
  rw [obj.Sc.refill_head.guard sc s h1, obj.Sc.refill_tail.guard sc s h2]

theorem sporadic.next_index.guard (s : S) (sc : obj.Sc) (i : U64) (h : R (maxA sc)) :
    sporadic.next_index (PathObl.guard st R W) s sc i = sporadic.next_index st s sc i := by
  unfold sporadic.next_index
  rw [obj.Sc.refill_max.guard sc s h]

theorem sporadic.tail.guard (s : S) (sc : obj.Sc) (h1 : R (tailA sc)) (h2 : RdRefill R sc (L.rtail s sc)) :
    sporadic.tail (PathObl.guard st R W) s sc = sporadic.tail st s sc := by
  unfold sporadic.tail
  rw [obj.Sc.refill_tail.guard sc s h1, rtail_ok]
  simp only [bind_ok]
  exact sporadic.get.guard s sc _ h2.1 h2.2

theorem sporadic.size.guard (s : S) (sc : obj.Sc) (h1 : R (headA sc)) (h2 : R (tailA sc)) (h3 : R (maxA sc)) :
    sporadic.size (PathObl.guard st R W) s sc = sporadic.size st s sc := by
  unfold sporadic.size
  rw [obj.Sc.refill_head.guard sc s h1, obj.Sc.refill_tail.guard sc s h2, obj.Sc.refill_max.guard sc s h3]

theorem sporadic.full.guard (s : S) (sc : obj.Sc) (h1 : R (headA sc)) (h2 : R (tailA sc)) (h3 : R (maxA sc)) :
    sporadic.full (PathObl.guard st R W) s sc = sporadic.full st s sc := by
  unfold sporadic.full
  rw [sporadic.size.guard s sc h1 h2 h3, obj.Sc.refill_max.guard sc s h3]

theorem sporadic.set_head.guard (s : S) (sc : obj.Sc) (r : sporadic.Refill) (h1 : R (headA sc))
    (h2 : WrRefill W sc (L.rhead s sc)) :
    sporadic.set_head (PathObl.guard st R W) s sc r = sporadic.set_head st s sc r := by
  unfold sporadic.set_head
  rw [obj.Sc.refill_head.guard sc s h1, rhead_ok]
  simp only [bind_ok]
  exact sporadic.put.guard s sc _ r h2

theorem sporadic.set_tail.guard (s : S) (sc : obj.Sc) (r : sporadic.Refill) (h1 : R (tailA sc))
    (h2 : WrRefill W sc (L.rtail s sc)) :
    sporadic.set_tail (PathObl.guard st R W) s sc r = sporadic.set_tail st s sc r := by
  unfold sporadic.set_tail
  rw [obj.Sc.refill_tail.guard sc s h1, rtail_ok]
  simp only [bind_ok]
  exact sporadic.put.guard s sc _ r h2

/-- The ring's header words: `REFILL_HEAD`, `REFILL_TAIL`, `REFILL_MAX`. -/
abbrev RdHdr (R : U64 → Prop) (sc : obj.Sc) : Prop := R (headA sc) ∧ R (tailA sc) ∧ R (maxA sc)

theorem sporadic.head_overlapping.guard (s : S) (sc : obj.Sc) (hh : RdHdr R sc)
    (h1 : RdRefill R sc (L.rhead s sc))
    (h2 : RdRefill R sc (nextIdx (L.rmax s sc) (L.rhead s sc))) :
    sporadic.head_overlapping (PathObl.guard st R W) s sc = sporadic.head_overlapping st s sc := by
  obtain ⟨hH, hT, hM⟩ := hh
  unfold sporadic.head_overlapping
  rw [sporadic.single.guard s sc hH hT, sporadic.head.guard s sc ⟨hH, h1.1, h1.2⟩,
    obj.Sc.refill_head.guard sc s hH, rhead_ok]
  simp only [bind_ok]
  rw [sporadic.next_index.guard s sc _ hM, next_index_ok]
  simp only [bind_ok]
  rw [sporadic.get.guard s sc _ h2.1 h2.2]

theorem sporadic.pop_head.guard (s : S) (sc : obj.Sc) (hH : R (headA sc)) (hM : R (maxA sc))
    (hW : W (headA sc)) (h1 : RdRefill R sc (L.rhead s sc)) :
    sporadic.pop_head (PathObl.guard st R W) s sc = sporadic.pop_head st s sc := by
  unfold sporadic.pop_head
  rw [sporadic.head.guard s sc ⟨hH, h1.1, h1.2⟩, obj.Sc.refill_head.guard sc s hH, rhead_ok]
  simp only [bind_ok]
  rw [sporadic.next_index.guard s sc _ hM, next_index_ok]
  simp only [bind_ok]
  rw [obj.Sc.set_refill_head.guard sc s _ hW]

theorem sporadic.add_tail.guard (s : S) (sc : obj.Sc) (r : sporadic.Refill) (hT : R (tailA sc))
    (hM : R (maxA sc)) (hW : W (tailA sc)) (h1 : WrRefill W sc (nextIdx (L.rmax s sc) (L.rtail s sc))) :
    sporadic.add_tail (PathObl.guard st R W) s sc r = sporadic.add_tail st s sc r := by
  unfold sporadic.add_tail
  rw [obj.Sc.refill_tail.guard sc s hT, rtail_ok]
  simp only [bind_ok]
  rw [sporadic.next_index.guard s sc _ hM, next_index_ok]
  simp only [bind_ok]
  rw [obj.Sc.set_refill_tail.guard sc s _ hW]
  have e : ∀ s1, sporadic.put (PathObl.guard st R W) s1 sc (nextIdx (L.rmax s sc) (L.rtail s sc)) r =
      sporadic.put st s1 sc (nextIdx (L.rmax s sc) (L.rtail s sc)) r := fun s1 => sporadic.put.guard s1 sc _ r h1
  simp only [e]

/-- **`schedule_used`**: the header words, the tail refill (read and written)
and the refill after it (written when the ring is not full). -/
theorem sporadic.schedule_used.guard (s : S) (sc : obj.Sc) (r : sporadic.Refill) (hh : RdHdr R sc)
    (hW : W (tailA sc)) (h1 : RdRefill R sc (L.rtail s sc)) (h2 : WrRefill W sc (L.rtail s sc))
    (h3 : WrRefill W sc (nextIdx (L.rmax s sc) (L.rtail s sc))) :
    sporadic.schedule_used (PathObl.guard st R W) s sc r = sporadic.schedule_used st s sc r := by
  obtain ⟨hH, hT, hM⟩ := hh
  unfold sporadic.schedule_used
  rw [sporadic.tail.guard s sc hT h1, sporadic.full.guard s sc hH hT hM,
    sporadic.add_tail.guard s sc r hT hM hW h3]
  simp only [sporadic.set_tail.guard s sc _ hT h2]

/-! ## The merge loop of `unblock_check` -/

omit L in
/-- `unblock_check_loop` unfolded once, on any store (P1's `ucLoop_unfold`
needs a `LawfulStore`). -/
theorem ucLoop_unfold' (st' : machine.Store S) (s : S) (sc : obj.Sc) (fuel : U64) :
    sporadic.unblock_check_loop st' s sc fuel =
      (do
        let r ← sporadic.unblock_check_loop.body st' sc s fuel
        match r with
        | ControlFlow.cont x => sporadic.unblock_check_loop st' x.1 sc x.2
        | ControlFlow.done z => ok z) := by
  conv_lhs => unfold sporadic.unblock_check_loop; rw [loop]
  congr 1
  funext r
  cases r with
  | cont x => obtain ⟨a, b⟩ := x; rfl
  | done z => rfl

/-- The ring of an SC whose size is `M`: the header words readable, the head
word writable, and both words of every refill below `M` readable and
writable. State-independent, so it holds along the loop. -/
abbrev Ring (R W : U64 → Prop) (sc : obj.Sc) (M : U64) : Prop :=
  RdHdr R sc ∧ W (headA sc) ∧ ∀ i : U64, i.val < M.val → RdRefill R sc i ∧ WrRefill W sc i

theorem pop_head_ok (s : S) (sc : obj.Sc) :
    sporadic.pop_head st s sc = ok (L.refill s sc (L.rhead s sc),
      L.wr s (headA sc) (nextIdx (L.rmax s sc) (L.rhead s sc))) := by
  unfold sporadic.pop_head
  rw [eq_ok_of_spec (sporadic.head.spec (L := L) s sc), rhead_ok]
  simp only [bind_ok]
  rw [next_index_ok]
  simp only [bind_ok]
  rw [eq_ok_of_spec (obj.Sc.set_refill_head.spec (L := L) s sc _)]
  simp only [bind_ok]

theorem set_head_ok (s : S) (sc : obj.Sc) (r : sporadic.Refill) :
    sporadic.set_head st s sc r = ok (L.putS s sc (L.rhead s sc) r) := by
  unfold sporadic.set_head
  rw [rhead_ok]; simp only [bind_ok]
  exact eq_ok_of_spec (sporadic.put.spec (L := L) s sc _ r)

/-- One step of the merge loop, at a state whose ring is well formed with
size `M`. -/
theorem sporadic.unblock_check_loop.body.guard {sb : Nat} {M : U64} (s : S) (sc : obj.Sc) (fuel : U64)
    (hW : RefillsWF st s sc sb) (hM : L.rmax s sc = M) (hr : Ring R W sc M) :
    sporadic.unblock_check_loop.body (PathObl.guard st R W) sc s fuel =
      sporadic.unblock_check_loop.body st sc s fuel := by
  obtain ⟨hh, hwh, hri⟩ := hr
  have h8 := hW.bounds.1
  have hl : (L.rhead s sc).val < M.val := hM ▸ hW.head_lt
  have hn : (nextIdx M (L.rhead s sc)).val < M.val := nextIdx_lt hl
  unfold sporadic.unblock_check_loop.body
  rw [sporadic.head_overlapping.guard s sc hh (hri _ hl).1 (by rw [hM]; exact (hri _ hn).1),
    sporadic.pop_head.guard s sc hh.1 hh.2.2 hwh (hri _ hl).1, pop_head_ok]
  refine bind_guard_congr rfl (fun b _ => ?_)
  by_cases hb : b = true
  on_goal 2 => simp only [hb, Bool.false_eq_true, ↓reduceIte]
  simp only [hb, ↓reduceIte]
  by_cases hf : fuel > 0#u64
  on_goal 2 => simp only [hf, ↓reduceIte]
  simp only [hf, ↓reduceIte]
  refine bind_guard_congr rfl (fun f1 _ => ?_)
  simp only [bind_ok, Aeneas.Std.uncurry_apply_pair]
  have e1 : L.rhead (L.wr s (headA sc) (nextIdx (L.rmax s sc) (L.rhead s sc))) sc =
      nextIdx M (L.rhead s sc) := by rw [rhead_wr_head h8, hM]
  rw [sporadic.head.guard (L.wr s (headA sc) (nextIdx (L.rmax s sc) (L.rhead s sc))) sc ⟨hh.1, by rw [e1]; exact (hri _ hn).1.1, by rw [e1]; exact (hri _ hn).1.2⟩]
  refine bind_guard_congr rfl (fun h _ => ?_)
  simp only [lift, bind_ok]
  rw [sporadic.set_head.guard (L.wr s (headA sc) (nextIdx (L.rmax s sc) (L.rhead s sc))) sc _ hh.1 (by rw [e1]; exact (hri _ hn).2)]

/-- **The merge loop** (fuel induction): at a state whose ring is well formed
with size `M`, on `Ring R W sc M`. -/
theorem sporadic.unblock_check_loop.guard {sb : Nat} {M : U64} (sc : obj.Sc) (hr : Ring R W sc M) :
    ∀ (N : Nat) (s : S) (fuel : U64), fuel.val < N → RefillsWF st s sc sb → L.rmax s sc = M →
      sporadic.unblock_check_loop (PathObl.guard st R W) s sc fuel =
        sporadic.unblock_check_loop st s sc fuel := by
  intro N
  induction N with
  | zero => intro _ _ hf; omega
  | succ N ih =>
    intro s fuel hf hW hM
    rw [ucLoop_unfold', ucLoop_unfold', sporadic.unblock_check_loop.body.guard s sc fuel hW hM hr]
    refine bind_guard_congr rfl (fun y hy => ?_)
    cases y with
    | done z => rfl
    | cont x =>
      -- a continuing step: the head was popped and merged into the new head
      have h8 := hW.bounds.1
      have hl := hW.head_lt
      unfold sporadic.unblock_check_loop.body at hy
      obtain ⟨b, -, hy⟩ := bind_eq_ok hy
      split at hy
      next =>
        split at hy
        next hgt =>
          obtain ⟨f1, ef, hy⟩ := bind_eq_ok hy
          rw [pop_head_ok] at hy
          simp only [bind_ok, Aeneas.Std.uncurry_apply_pair] at hy
          obtain ⟨hd, -, hy⟩ := bind_eq_ok hy
          simp only [lift, bind_ok] at hy
          rw [set_head_ok] at hy
          simp only [bind_ok] at hy
          have e := ok_inj_ff hy
          simp only [ControlFlow.cont.injEq] at e
          subst e
          have hn := nextIdx_lt hl
          have hW1 := hW.wr_head (v := nextIdx (L.rmax s sc) (L.rhead s sc)) hn
          have hl1 : (L.rhead (L.wr s (headA sc) (nextIdx (L.rmax s sc) (L.rhead s sc))) sc).val <
              (L.rmax (L.wr s (headA sc) (nextIdx (L.rmax s sc) (L.rhead s sc))) sc).val := hW1.head_lt
          refine ih _ _ ?_ (hW1.putS hl1) ?_
          · have := sub1_lt (fun h0 => by rw [h0] at hgt; exact absurd hgt (by decide)) ef
            dsimp only
            omega
          · obtain ⟨-, hm, hfit⟩ := hW1.bounds
            rw [rmax_putS hW1.bounds.1 (by omega), rmax_wr_head h8, hM]
        next => cases ok_inj_ff hy
      next => cases ok_inj_ff hy

end law

end

end Fl4Proofs.P2.PathObl
