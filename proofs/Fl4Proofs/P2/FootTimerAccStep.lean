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

set_option maxHeartbeats 2000000 in
/-- One step of the search (on the real store) keeps the stack of keys and counts a visit. -/
theorem ictt_body_step {s : S} {c target d : U64} {W : TRB.RBT} (ct : CoreTree st T s c W)
    (x : Array U64 32#usize × Usize × U64 × Bool × Bool) (hx : StackOK W.keys x.1 x.2.1)
    (x' : Array U64 32#usize × Usize × U64 × Bool × Bool)
    (h : localtimer.in_core_timer_tree_loop.body st s target d x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 =
      ok (ControlFlow.cont x')) :
    StackOK W.keys x'.1 x'.2.1 ∧ 64 - x'.2.2.1.val < 64 - x.2.2.1.val := by
  obtain ⟨stack, sp, visits, found, ov⟩ := x
  simp only at hx h ⊢
  unfold localtimer.in_core_timer_tree_loop.body at h
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
    have := h2; unfold localtimer.TREE_VISITS at this; clear h; scalar_tac
  obtain ⟨v1, ev1, hv1⟩ := spec_ex_fd (U64.add_spec (x := visits) (y := 1#u64) (by clear h; scalar_tac))
  obtain ⟨sp1, esp1, hsp1⟩ := spec_ex_fd (Usize.sub_spec (x := sp) (y := 1#usize) (by clear h; scalar_tac))
  rw [ev1, esp1] at h
  simp only [bind_ok] at h
  have hsp32 := hx.1
  have hlen : stack.length = 32 := by simp
  have hl : sp1.val < stack.length := by clear h; scalar_tac
  have e1 : sp1.val + 1 = sp.val := by clear h; scalar_tac
  obtain ⟨i1, ei1, hi1⟩ := spec_ex_fd (Array.index_usize_spec stack sp1 hl)
  rw [ei1] at h
  simp only [bind_ok] at h
  have hi1m : i1 ∈ W.keys := by rw [hi1]; exact hx.top e1 hl
  have hlt : 64 - v1.val < 64 - visits.val := by clear h; scalar_tac
  have hpop : StackOK W.keys stack sp1 := hx.pop e1
  have lk := ct.rep.links i1 hi1m
  have lkl : L.mem s (tlA i1) ≠ 0#u64 → L.mem s (tlA i1) ∈ W.keys := fun hne => lk.1.resolve_left hne
  have lkr : L.mem s (trA i1) ≠ 0#u64 → L.mem s (trA i1) ∈ W.keys := fun hne => lk.2.1.resolve_left hne
  rw [eq_of_spec_fd (tcb_eq.blk _ _)] at h
  simp only [bind_ok] at h
  rw [eq_of_spec_fd (obj.Tcb.timer_deadline.val (L := L) s _), eq_of_spec_fd (obj.Tcb.timer_left.val (L := L) s _),
    eq_of_spec_fd (obj.Tcb.timer_right.val (L := L) s _)] at h
  simp only [bind_ok] at h
  have h31 : sp1.val < 32 := by clear h; scalar_tac
  obtain ⟨⟨xm, back⟩, em, hxm, hback⟩ := spec_ex_fd (Array.index_mut_usize_spec stack sp1 hl)
  subst hback
  obtain ⟨sp2, esp2, hsp2⟩ := spec_ex_fd (Usize.add_spec (x := sp1) (y := 1#usize) (by clear h; scalar_tac))
  rw [em, esp2] at h
  simp only [bind_ok, Aeneas.Std.uncurry_apply_pair] at h
  -- every continuation is a pop, or a pop and one or two pushes of non-null children
  have fin : ∀ y : Array U64 32#usize × Usize × U64 × Bool × Bool,
      (ok (ControlFlow.cont y) : Result (ControlFlow (Array U64 32#usize × Usize × U64 × Bool × Bool) Bool)) =
        ok (ControlFlow.cont x') → StackOK W.keys y.1 y.2.1 → y.2.2.1 = v1 →
      StackOK W.keys x'.1 x'.2.1 ∧ 64 - x'.2.2.1.val < 64 - visits.val := by
    intro y hy hok hv'
    have e := ok_inj_ff hy
    simp only [ControlFlow.cont.injEq] at e
    subst e
    exact ⟨hok, by rw [hv']; exact hlt⟩
  have hTS : localtimer.TREE_STACK = 32#usize := by unfold localtimer.TREE_STACK; rfl
  simp only [hTS] at h
  have pl : ∀ (n m : Usize), StackOK W.keys stack n → n.val < 32 → m.val = n.val + 1 →
      (L.mem s (tlA i1) != 0#u64) = true → StackOK W.keys (stack.set n (L.mem s (tlA i1))) m :=
    fun n m hn h1 h2 hc => hn.push h1 h2 (lkl (by simpa using hc))
  have pr : ∀ (a : Array U64 32#usize) (n m : Usize), StackOK W.keys a n → n.val < 32 → m.val = n.val + 1 →
      (L.mem s (trA i1) != 0#u64) = true → StackOK W.keys (a.set n (L.mem s (trA i1))) m :=
    fun a n m hn h1 h2 hc => hn.push h1 h2 (lkr (by simpa using hc))
  have hs1 : ¬ sp1 = 32#usize := by intro e; rw [e] at h31; simp at h31
  -- the right child, from a stack `a` of keys at depth `n`
  have rbranch : ∀ (a : Array U64 32#usize) (n : Usize), StackOK W.keys a n → n.val ≤ 32 →
      ∀ y, (if d >= L.mem s (tdA i1) then
          (if (L.mem s (trA i1) != 0#u64) = true then
            (if n = 32#usize then ok (ControlFlow.cont (a, n, v1, false, true))
             else do
              let a1 ← Array.update a n (L.mem s (trA i1))
              let n1 ← n + 1#usize
              ok (ControlFlow.cont (a1, n1, v1, false, false)))
           else ok (ControlFlow.cont (a, n, v1, false, false)))
        else ok (ControlFlow.cont (a, n, v1, false, false)) :
          Result (ControlFlow (Array U64 32#usize × Usize × U64 × Bool × Bool) Bool)) = ok (ControlFlow.cont y) →
        StackOK W.keys y.1 y.2.1 ∧ y.2.2.1 = v1 := by
    intro a n ha hn y hy
    have fin' : ∀ z : Array U64 32#usize × Usize × U64 × Bool × Bool,
        (ok (ControlFlow.cont z) : Result (ControlFlow (Array U64 32#usize × Usize × U64 × Bool × Bool) Bool)) =
          ok (ControlFlow.cont y) → StackOK W.keys z.1 z.2.1 → z.2.2.1 = v1 →
        StackOK W.keys y.1 y.2.1 ∧ y.2.2.1 = v1 := by
      intro z hz h1 h2
      have e := ok_inj_ff hz
      simp only [ControlFlow.cont.injEq] at e
      subst e
      exact ⟨h1, h2⟩
    by_cases hge : d >= L.mem s (tdA i1)
    · rw [if_pos hge] at hy
      by_cases hr : (L.mem s (trA i1) != 0#u64) = true
      · rw [if_pos hr] at hy
        by_cases hn32 : n = 32#usize
        · rw [if_pos hn32] at hy
          exact fin' _ hy ha rfl
        rw [if_neg hn32] at hy
        have hn' : n.val < 32 := by
          have : n.val ≠ 32 := fun e => hn32 (UScalar.eq_of_val_eq (by simp [e]))
          omega
        have hl2 : n.val < a.length := by simp; omega
        obtain ⟨n1, en1, hn1⟩ := spec_ex_fd (Usize.add_spec (x := n) (y := 1#usize) (by clear hy h; scalar_tac))
        rw [eq_of_spec_fd (Array.update_spec a n (L.mem s (trA i1)) hl2), en1] at hy
        simp only [bind_ok] at hy
        exact fin' _ hy (pr a n n1 ha hn' (by clear hy h; scalar_tac) hr) rfl
      · rw [if_neg hr] at hy
        exact fin' _ hy ha rfl
    · rw [if_neg hge] at hy
      exact fin' _ hy ha rfl
  by_cases hdc : d <= L.mem s (tdA i1)
  · rw [if_pos hdc] at h
    by_cases hl0 : (L.mem s (tlA i1) != 0#u64) = true
    · rw [if_pos hl0, if_neg hs1] at h
      simp only [Bool.false_eq_true, ite_false] at h
      have hp := pl sp1 sp2 hpop h31 (by clear h; scalar_tac) hl0
      obtain ⟨hy1, hy2⟩ := rbranch _ sp2 hp (by clear h; scalar_tac) x' h
      exact ⟨hy1, by rw [hy2]; exact hlt⟩
    · rw [if_neg hl0] at h
      simp only [Bool.false_eq_true, ite_false] at h
      obtain ⟨hy1, hy2⟩ := rbranch stack sp1 hpop h31 x' h
      exact ⟨hy1, by rw [hy2]; exact hlt⟩
  · rw [if_neg hdc] at h
    simp only [Bool.false_eq_true, ite_false] at h
    obtain ⟨hy1, hy2⟩ := rbranch stack sp1 hpop h31 x' h
    exact ⟨hy1, by rw [hy2]; exact hlt⟩

end

end Fl4Proofs.P2
