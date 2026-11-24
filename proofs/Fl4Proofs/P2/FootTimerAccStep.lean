/-
# P2: one step of `in_core_timer_tree`'s search keeps its stack of keys (see `P2/FootTimerAccLoop.lean`)

No named premises.
-/
import Fl4Proofs.P2.FootTimerAccEq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read)

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {R Wr : U64 → Prop}

theorem cont_inj {y z : Array U64 32#usize × Usize × U64 × Bool × Bool}
    (h : (ok (ControlFlow.cont z) : Result (ControlFlow (Array U64 32#usize × Usize × U64 × Bool × Bool) Bool)) =
      ok (ControlFlow.cont y)) : z = y := by
  have e := ok_inj_ff h
  simp only [ControlFlow.cont.injEq] at e
  exact e

/-- The right child keeps a stack of keys. -/
theorem ictRight_step {Ks : List U64} {d v1 cd r : U64} {a : Array U64 32#usize} {n : Usize}
    {y : Array U64 32#usize × Usize × U64 × Bool × Bool} (ha : StackOK Ks a n) (hn : n.val ≤ 32)
    (hr : r ≠ 0#u64 → r ∈ Ks) (h : ictRight d v1 false false (ok r) a n cd = ok (ControlFlow.cont y)) :
    StackOK Ks y.1 y.2.1 ∧ y.2.2.1 = v1 := by
  have hTS : localtimer.TREE_STACK = 32#usize := by unfold localtimer.TREE_STACK; rfl
  unfold ictRight at h
  rw [hTS] at h
  by_cases hge : d >= cd
  · rw [if_pos hge] at h
    simp only [bind_ok] at h
    by_cases hr0 : (r != 0#u64) = true
    · rw [if_pos hr0] at h
      by_cases hn32 : n = 32#usize
      · rw [if_pos hn32] at h
        rw [← cont_inj h]; exact ⟨ha, rfl⟩
      rw [if_neg hn32] at h
      have hn' : n.val < 32 := by
        have : n.val ≠ 32 := fun e => hn32 (UScalar.eq_of_val_eq (by simp [e]))
        omega
      have hl2 : n.val < a.length := by simp; omega
      obtain ⟨n1, en1, hn1⟩ := spec_ex_fd (Usize.add_spec (x := n) (y := 1#usize) (by scalar_tac))
      rw [eq_of_spec_fd (Array.update_spec a n r hl2), en1] at h
      simp only [bind_ok] at h
      rw [← cont_inj h]
      exact ⟨ha.push hn' (by scalar_tac) (hr (by simpa using hr0)), rfl⟩
    · rw [if_neg hr0] at h
      rw [← cont_inj h]; exact ⟨ha, rfl⟩
  · rw [if_neg hge] at h
    rw [← cont_inj h]; exact ⟨ha, rfl⟩

/-- The search step after the pop keeps a stack of keys, given the popped node's children are null or keys. -/
theorem ictTail_step {Ks : List U64} {i d v1 i1 cd l r : U64} {stack : Array U64 32#usize} {sp1 : Usize}
    {y : Array U64 32#usize × Usize × U64 × Bool × Bool} (hpop : StackOK Ks stack sp1) (h31 : sp1.val < 32)
    (hl : l ≠ 0#u64 → l ∈ Ks) (hr : r ≠ 0#u64 → r ∈ Ks)
    (h : ictTail i d stack sp1 v1 false false i1 (ok cd) (ok l) (ok r) = ok (ControlFlow.cont y)) :
    StackOK Ks y.1 y.2.1 ∧ y.2.2.1 = v1 := by
  have hTS : localtimer.TREE_STACK = 32#usize := by unfold localtimer.TREE_STACK; rfl
  unfold ictTail at h
  rw [eq_of_spec_fd (tcb_eq.blk _ _)] at h
  simp only [bind_ok] at h
  by_cases hb : i1 = i
  · rw [decide_eq_true hb] at h
    simp only [↓reduceIte] at h
    rw [← cont_inj h]; exact ⟨hpop, rfl⟩
  rw [decide_eq_false hb] at h
  simp only [Bool.false_eq_true, ite_false] at h
  have hs1 : ¬ sp1 = localtimer.TREE_STACK := by rw [hTS]; intro e; rw [e] at h31; simp at h31
  by_cases hdc : d <= cd
  · rw [if_pos hdc] at h
    by_cases hl0 : (l != 0#u64) = true
    · rw [if_pos hl0, if_neg hs1] at h
      have hl' : sp1.val < stack.length := by simp; omega
      obtain ⟨⟨xm, back⟩, em, hxm, hback⟩ := spec_ex_fd (Array.index_mut_usize_spec stack sp1 hl')
      obtain ⟨sp2, esp2, hsp2⟩ := spec_ex_fd (Usize.add_spec (x := sp1) (y := 1#usize) (by scalar_tac))
      rw [em, esp2] at h
      simp only [bind_ok, Bool.false_eq_true, ite_false] at h
      simp only at hback
      subst hback
      exact ictRight_step (hpop.push h31 (by scalar_tac) (hl (by simpa using hl0))) (by scalar_tac) hr h
    · rw [if_neg hl0] at h
      simp only [Bool.false_eq_true, ite_false] at h
      exact ictRight_step hpop (by omega) hr h
  · rw [if_neg hdc] at h
    simp only [Bool.false_eq_true, ite_false] at h
    exact ictRight_step hpop (by omega) hr h

/-- One step of the search (on the real store) keeps the stack of keys and counts a visit. -/
theorem ictt_body_step {s : S} {c target d : U64} {W : TRB.RBT} (ct : CoreTree st T s c W)
    (x : Array U64 32#usize × Usize × U64 × Bool × Bool) (hx : StackOK W.keys x.1 x.2.1)
    (x' : Array U64 32#usize × Usize × U64 × Bool × Bool)
    (h : localtimer.in_core_timer_tree_loop.body st s target d x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 =
      ok (ControlFlow.cont x')) :
    StackOK W.keys x'.1 x'.2.1 ∧ 64 - x'.2.2.1.val < 64 - x.2.2.1.val := by
  obtain ⟨stack, sp, visits, found, ov⟩ := x
  rw [body_split] at h
  by_cases h1 : sp > 0#usize
  swap
  · rw [if_neg h1] at h; simp at h
  rw [if_pos h1] at h
  by_cases h2 : visits < localtimer.TREE_VISITS
  swap
  · rw [if_neg h2] at h; simp at h
  rw [if_pos h2] at h
  cases found
  swap
  · simp at h
  cases ov
  swap
  · simp at h
  simp only [Bool.false_eq_true, ite_false] at h
  have hv : visits.val < 64 := by
    have := h2; unfold localtimer.TREE_VISITS at this; scalar_tac
  obtain ⟨v1, ev1, hv1⟩ := spec_ex_fd (U64.add_spec (x := visits) (y := 1#u64) (by scalar_tac))
  obtain ⟨sp1, esp1, hsp1⟩ := spec_ex_fd (Usize.sub_spec (x := sp) (y := 1#usize) (by scalar_tac))
  rw [ev1, esp1] at h
  simp only [bind_ok] at h
  have hsp32 := hx.1
  have hl : sp1.val < stack.length := by simp; scalar_tac
  have e1 : sp1.val + 1 = sp.val := by scalar_tac
  obtain ⟨i1, ei1, hi1⟩ := spec_ex_fd (Array.index_usize_spec stack sp1 hl)
  rw [ei1] at h
  simp only [bind_ok] at h
  have hi1m : i1 ∈ W.keys := by rw [hi1]; exact hx.top e1 hl
  have lk := ct.rep.links i1 hi1m
  rw [eq_of_spec_fd (obj.Tcb.timer_deadline.val (L := L) s _), eq_of_spec_fd (obj.Tcb.timer_left.val (L := L) s _),
    eq_of_spec_fd (obj.Tcb.timer_right.val (L := L) s _)] at h
  obtain ⟨hy1, hy2⟩ := ictTail_step (hx.pop e1) (by scalar_tac) (fun hne => lk.1.resolve_left hne)
    (fun hne => lk.2.1.resolve_left hne) h
  exact ⟨hy1, by rw [hy2]; scalar_tac⟩

end

end Fl4Proofs.P2
