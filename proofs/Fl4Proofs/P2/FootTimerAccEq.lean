/-
WIP (p2lt, not imported): `ictt_body_eq` still elaborates past 10 GiB on afkprover (also with
`↓reduceIte` replaced and no `scalar_tac` over the unfolded goal); cause not yet isolated.

# P2: `in_core_timer_tree` reads only core `c`'s tree (`PathObl.acc` piece)

`in_core_timer_tree_access`: run on `guard st R W`, `localtimer.in_core_timer_tree st s c target d` ends as on
`st` when `R` holds `TreeReads` (core `c`'s `TIMER_ROOT`, `TIMER_MIN` and the `TIMER_DEADLINE` /
`TIMER_LEFT` / `TIMER_RIGHT` words of the keys of `c`'s tree, `CoreTree`). The search's stack holds keys
only (`StackOK`): a popped node is a key (`ictt_body_eq`: the guarded step is the real step) and every push
is a non-null child link of a key, a key again (`ictt_body_step`, by explicit cases on the branch:
deadline order, null children, a full stack). Composed with `PathObl.loop_guard_congr`
(`P2/AccessSched.lean`), the measure being the visits left.

No named premises.
-/
import Fl4Proofs.P2.FootTimerAcc
import Fl4Proofs.P2.AccessSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read)

/-! ## `in_core_timer_tree` -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {R Wr : U64 → Prop}

/-- The words `in_core_timer_tree` on core `c` reads, `W` the keys of `c`'s tree. -/
def TreeReads (st : machine.Store S) [L : LawfulStore st] (s : S) (c : U64) (Ks : List U64) (w : U64) : Prop :=
  w = L.nodeAt s c layout.node.TIMER_ROOT ∨ w = L.nodeAt s c layout.node.TIMER_MIN ∨
    ∃ y, (y = 0#u64 ∨ y ∈ Ks) ∧ (w = tdA y ∨ w = tlA y ∨ w = trA y)

/-- The search's stack: its first `sp` entries are keys, `sp ≤ 32`. -/
def StackOK (Ks : List U64) (a : Array U64 32#usize) (sp : Usize) : Prop :=
  sp.val ≤ 32 ∧ ∀ j (hj : j < a.val.length), j < sp.val → a.val[j] ∈ Ks

theorem StackOK.pop {Ks : List U64} {a : Array U64 32#usize} {sp sp1 : Usize} (h : StackOK Ks a sp)
    (e : sp1.val + 1 = sp.val) : StackOK Ks a sp1 :=
  ⟨by omega, fun j hj hjs => h.2 j hj (by omega)⟩

theorem StackOK.top {Ks : List U64} {a : Array U64 32#usize} {sp sp1 : Usize} (h : StackOK Ks a sp)
    (e : sp1.val + 1 = sp.val) (hl : sp1.val < a.val.length) : a.val[sp1.val] ∈ Ks :=
  h.2 _ hl (by omega)

theorem StackOK.push {Ks : List U64} {a : Array U64 32#usize} {n m : Usize} {v : U64} (h : StackOK Ks a n)
    (hn : n.val < 32) (hm : m.val = n.val + 1) (hv : v ∈ Ks) : StackOK Ks (a.set n v) m := by
  refine ⟨by omega, fun j hj hjm => ?_⟩
  simp only [Array.set_val_eq, List.getElem_set]
  split
  · exact hv
  · rename_i hne
    exact h.2 j (by simpa using hj) (by omega)

set_option maxHeartbeats 4000000 in
/-- One step of the search reads only `TreeReads` words. -/
theorem ictt_body_eq {s : S} {c target d : U64} {Ks : List U64}
    (hR : ∀ w, TreeReads st s c Ks w → R w)
    (x : Array U64 32#usize × Usize × U64 × Bool × Bool) (hx : StackOK Ks x.1 x.2.1) :
    localtimer.in_core_timer_tree_loop.body (guard st R Wr) s target d x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 =
      localtimer.in_core_timer_tree_loop.body st s target d x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  obtain ⟨stack, sp, visits, found, ov⟩ := x
  simp only at hx ⊢
  unfold localtimer.in_core_timer_tree_loop.body
  by_cases h1 : sp > 0#usize
  swap
  · rw [if_neg h1, if_neg h1]
  rw [if_pos h1, if_pos h1]
  by_cases h2 : visits < localtimer.TREE_VISITS
  swap
  · rw [if_neg h2, if_neg h2]
  rw [if_pos h2, if_pos h2]
  cases found
  swap
  · rfl
  cases ov
  swap
  · rfl
  simp only [Bool.false_eq_true, ite_false]
  have hv : visits.val < 64 := by
    have := h2; unfold localtimer.TREE_VISITS at this; scalar_tac
  obtain ⟨v1, ev1, -⟩ := spec_ex_fd (U64.add_spec (x := visits) (y := 1#u64) (by scalar_tac))
  obtain ⟨sp1, esp1, hsp1⟩ := spec_ex_fd (Usize.sub_spec (x := sp) (y := 1#usize) (by scalar_tac))
  rw [ev1, esp1]
  simp only [bind_ok]
  have hl : sp1.val < stack.length := by
    have : stack.length = 32 := by simp
    have := hx.1
    scalar_tac
  obtain ⟨i1, ei1, hi1⟩ := spec_ex_fd (Array.index_usize_spec stack sp1 hl)
  rw [ei1]
  simp only [bind_ok]
  have hi1m : i1 ∈ Ks := by rw [hi1]; exact hx.top (by scalar_tac) hl
  have rd : R (tdA i1) := hR _ (Or.inr (Or.inr ⟨i1, Or.inr hi1m, Or.inl rfl⟩))
  have rl : R (tlA i1) := hR _ (Or.inr (Or.inr ⟨i1, Or.inr hi1m, Or.inr (Or.inl rfl)⟩))
  have rr : R (trA i1) := hR _ (Or.inr (Or.inr ⟨i1, Or.inr hi1m, Or.inr (Or.inr rfl)⟩))
  rw [tdG (Wr := Wr) (s := s) rd, tlG (Wr := Wr) (s := s) rl, trG (Wr := Wr) (s := s) rr]

end

end Fl4Proofs.P2
