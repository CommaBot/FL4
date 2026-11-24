/-
# P2: `in_core_timer_tree` reads only core `c`'s tree (`PathObl.acc` piece)

`in_core_timer_tree_access`: run on `guard st R W`, `localtimer.in_core_timer_tree st s c target d` ends as on
`st` when `R` holds `TreeReads` (core `c`'s `TIMER_ROOT`, `TIMER_MIN` and the `TIMER_DEADLINE` /
`TIMER_LEFT` / `TIMER_RIGHT` words of the keys of `c`'s tree, `CoreTree`). The search's stack holds keys
only (`StackOK`): a popped node is a key (`ictt_body_eq`: the guarded step is the real step) and every push
is a non-null child link of a key, a key again (`ictt_body_step`, by explicit cases on the branch:
deadline order, null children, a full stack). Composed with `PathObl.loop_guard_congr`
(`P2/AccessSched.lean`), the measure being the visits left.

Elaboration note: the branches where both sides are `ok (done ..)` after the flag tests are closed by
`rw [if_pos rfl, ..]`, not `rfl`: `rfl` compares the `ite`'s else branches (guarded against real reads)
before reducing the condition and ran past 9 GiB.

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
    ∃ y, y ∈ Ks ∧ (w = tdA y ∨ w = tlA y ∨ w = trA y)

/-- The search's stack: its first `sp` entries are keys, `sp ≤ 32`. -/
def StackOK (Ks : List U64) (a : Array U64 32#usize) (sp : Usize) : Prop :=
  sp.val ≤ 32 ∧ ∀ j (hj : j < a.val.length), j < sp.val → a.val[j] ∈ Ks

theorem StackOK.pop {Ks : List U64} {a : Array U64 32#usize} {sp sp1 : Usize} (h : StackOK Ks a sp)
    (e : sp1.val + 1 = sp.val) : StackOK Ks a sp1 :=
  ⟨by have := h.1; omega, fun j hj hjs => h.2 j hj (by omega)⟩

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

/-- The search step after the pop, with the popped node's three reads given as results `rd` (deadline),
`rl` (left), `rr` (right): the extracted body is the pop followed by this (`body_split`, by `rfl`), so the
guarded and the real step differ only in those three arguments. The right child: -/
def ictRight (d : U64) (visits1 : U64) (found overflow : Bool) (rr : Result U64) (a : Array U64 32#usize)
    (n : Usize) (cd : U64) : Result (ControlFlow ((Array U64 32#usize) × Usize × U64 × Bool × Bool) Bool) :=
  if d >= cd then
    Std.bind rr fun r =>
      if r != 0#u64 then
        if n = localtimer.TREE_STACK then ok (ControlFlow.cont (a, n, visits1, found, true))
        else Std.bind (Array.update a n r) fun a1 =>
          Std.bind (n + 1#usize) fun n1 => ok (ControlFlow.cont (a1, n1, visits1, found, overflow))
      else ok (ControlFlow.cont (a, n, visits1, found, overflow))
  else ok (ControlFlow.cont (a, n, visits1, found, overflow))

/-- The search step after the pop (`ictRight`: the right child of a stack `a` at depth `n`). In term
mode: the `do` elaboration of this body took ~5 GiB. -/
def ictTail (i d : U64) (stack : Array U64 32#usize) (sp1 : Usize) (visits1 : U64) (found overflow : Bool)
    (i1 : U64) (rd rl rr : Result U64) :
    Result (ControlFlow ((Array U64 32#usize) × Usize × U64 × Bool × Bool) Bool) :=
  Std.bind (obj.Tcb.Insts.CoreCmpPartialEqTcb.eq i1 i) fun b =>
  if b then ok (ControlFlow.cont (stack, sp1, visits1, true, overflow))
  else Std.bind rd fun cd =>
    if d <= cd then
      Std.bind rl fun l =>
        if l != 0#u64 then
          if sp1 = localtimer.TREE_STACK then ok (ControlFlow.cont (stack, sp1, visits1, found, true))
          else Std.bind (Array.index_mut_usize stack sp1) fun p =>
            Std.bind (sp1 + 1#usize) fun sp2 =>
              if overflow then ok (ControlFlow.cont (p.2 l, sp2, visits1, found, overflow))
              else ictRight d visits1 found overflow rr (p.2 l) sp2 cd
        else if overflow then ok (ControlFlow.cont (stack, sp1, visits1, found, overflow))
        else ictRight d visits1 found overflow rr stack sp1 cd
    else if overflow then ok (ControlFlow.cont (stack, sp1, visits1, found, overflow))
    else ictRight d visits1 found overflow rr stack sp1 cd

/-- The extracted step is the pop, then `ictTail` of the popped node's reads. -/
theorem body_split (M : machine.Store S) (s : S) (i d : U64) (stack : Array U64 32#usize) (sp : Usize)
    (visits : U64) (found overflow : Bool) :
    localtimer.in_core_timer_tree_loop.body M s i d stack sp visits found overflow =
      (if sp > 0#usize then
        if visits < localtimer.TREE_VISITS then
          if found then ok (ControlFlow.done found)
          else if overflow then ok (ControlFlow.done found)
          else do
            let visits1 ← visits + 1#u64
            let sp1 ← sp - 1#usize
            let i1 ← Array.index_usize stack sp1
            ictTail i d stack sp1 visits1 found overflow i1 (obj.Tcb.timer_deadline M i1 s)
              (obj.Tcb.timer_left M i1 s) (obj.Tcb.timer_right M i1 s)
        else ok (ControlFlow.done found)
      else ok (ControlFlow.done found)) := rfl

/-- **One step of the search reads only `TreeReads` words**: the guarded step is the real step. -/
theorem ictt_body_eq {s : S} {c target d : U64} {Ks : List U64}
    (hR : ∀ w, TreeReads st s c Ks w → R w)
    (x : Array U64 32#usize × Usize × U64 × Bool × Bool) (hx : StackOK Ks x.1 x.2.1) :
    localtimer.in_core_timer_tree_loop.body (guard st R Wr) s target d x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 =
      localtimer.in_core_timer_tree_loop.body st s target d x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  obtain ⟨stack, sp, visits, found, ov⟩ := x
  rw [body_split, body_split]
  by_cases h1 : sp > 0#usize
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : visits < localtimer.TREE_VISITS
    · rw [if_pos h2, if_pos h2]
      cases found
      · cases ov
        · simp only [Bool.false_eq_true, ite_false]
          refine PathObl.bind_guard_congr rfl fun v1 _ => ?_
          refine PathObl.bind_guard_congr rfl fun sp1 esp1 => ?_
          refine PathObl.bind_guard_congr rfl fun i1 ei1 => ?_
          have hsp1 : sp1.val + 1 = sp.val := by
            obtain ⟨z, ez, hz⟩ := spec_ex_fd (Usize.sub_spec (x := sp) (y := 1#usize) (by scalar_tac))
            rw [ez] at esp1
            have e := ok_inj_ff esp1
            subst e
            scalar_tac
          have hl : sp1.val < stack.length := by
            have : stack.length = 32 := by simp
            have := hx.1
            scalar_tac
          have hi := Array.index_usize_spec stack sp1 hl
          rw [ei1, WP.spec_ok] at hi
          have hi1m : i1 ∈ Ks := by rw [hi]; exact hx.top hsp1 hl
          have rd : R (tdA i1) := hR _ (Or.inr (Or.inr ⟨i1, hi1m, Or.inl rfl⟩))
          have rl : R (tlA i1) := hR _ (Or.inr (Or.inr ⟨i1, hi1m, Or.inr (Or.inl rfl)⟩))
          have rr : R (trA i1) := hR _ (Or.inr (Or.inr ⟨i1, hi1m, Or.inr (Or.inr rfl)⟩))
          rw [tdG (Wr := Wr) (s := s) rd, tlG (Wr := Wr) (s := s) rl, trG (Wr := Wr) (s := s) rr]
        · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, if_pos rfl, if_pos rfl]
      · rw [if_pos rfl, if_pos rfl]
    · rw [if_neg h2, if_neg h2]
  · rw [if_neg h1, if_neg h1]

end

end Fl4Proofs.P2
