/-
WIP (p2lt, not imported): the `in_core_timer_tree` access proof. Elaboration of `ictt_body_step` /
`ictt_body_eq` blew up (19 GiB, no result) on afkprover: to be restructured (smaller per-branch lemmas).
-/
import Fl4Proofs.P2.FootTimerAcc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read)

/-! ## Loops -/

theorem loop_unfold {α β : Type _} (b : α → Result (ControlFlow α β)) (x : α) :
    loop b x = (do
      let r ← b x
      match r with
      | ControlFlow.cont x' => loop b x'
      | ControlFlow.done z => ok z) := by
  conv_lhs => rw [loop]
  congr 1

/-- Two loops agree from a state of the invariant when their bodies agree on it and each step of the
first keeps it with a smaller measure. -/
theorem loop_congr {α β : Type _} (b1 b2 : α → Result (ControlFlow α β)) (Inv : α → Prop) (μ : α → Nat)
    (heq : ∀ x, Inv x → b1 x = b2 x)
    (hstep : ∀ x, Inv x → ∀ x', b1 x = ok (ControlFlow.cont x') → Inv x' ∧ μ x' < μ x) :
    ∀ x, Inv x → loop b1 x = loop b2 x := by
  intro x
  induction hm : μ x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro hx
    rw [loop_unfold b1 x, loop_unfold b2 x, ← heq x hx]
    cases e : b1 x with
    | ok r =>
      cases r with
      | cont x' =>
        simp only [bind_ok]
        obtain ⟨hx', hlt⟩ := hstep x hx x' e
        exact ih (μ x') (hm ▸ hlt) x' rfl hx'
      | done z => rfl
    | fail _ => rfl
    | div => rfl

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
  simp only [Bool.false_eq_true, ↓reduceIte]
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
  simp only [tdG (Wr := Wr) (s := s) rd, tlG (Wr := Wr) (s := s) rl, trG (Wr := Wr) (s := s) rr]

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
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  have hv : visits.val < 64 := by
    have := h2; unfold localtimer.TREE_VISITS at this; scalar_tac
  obtain ⟨v1, ev1, hv1⟩ := spec_ex_fd (U64.add_spec (x := visits) (y := 1#u64) (by scalar_tac))
  obtain ⟨sp1, esp1, hsp1⟩ := spec_ex_fd (Usize.sub_spec (x := sp) (y := 1#usize) (by scalar_tac))
  rw [ev1, esp1] at h
  simp only [bind_ok] at h
  have hsp32 := hx.1
  have hlen : stack.length = 32 := by simp
  have hl : sp1.val < stack.length := by scalar_tac
  have e1 : sp1.val + 1 = sp.val := by scalar_tac
  obtain ⟨i1, ei1, hi1⟩ := spec_ex_fd (Array.index_usize_spec stack sp1 hl)
  rw [ei1] at h
  simp only [bind_ok] at h
  have hi1m : i1 ∈ W.keys := by rw [hi1]; exact hx.top e1 hl
  have hlt : 64 - v1.val < 64 - visits.val := by scalar_tac
  have hpop : StackOK W.keys stack sp1 := hx.pop e1
  have lk := ct.rep.links i1 hi1m
  have lkl : L.mem s (tlA i1) ≠ 0#u64 → L.mem s (tlA i1) ∈ W.keys := fun hne => lk.1.resolve_left hne
  have lkr : L.mem s (trA i1) ≠ 0#u64 → L.mem s (trA i1) ∈ W.keys := fun hne => lk.2.1.resolve_left hne
  rw [eq_of_spec_fd (tcb_eq.blk _ _)] at h
  simp only [bind_ok] at h
  rw [eq_of_spec_fd (obj.Tcb.timer_deadline.val (L := L) s _), eq_of_spec_fd (obj.Tcb.timer_left.val (L := L) s _),
    eq_of_spec_fd (obj.Tcb.timer_right.val (L := L) s _)] at h
  simp only [bind_ok] at h
  have h31 : sp1.val < 32 := by scalar_tac
  obtain ⟨⟨xm, back⟩, em, hxm, hback⟩ := spec_ex_fd (Array.index_mut_usize_spec stack sp1 hl)
  subst hback
  obtain ⟨sp2, esp2, hsp2⟩ := spec_ex_fd (Usize.add_spec (x := sp1) (y := 1#usize) (by scalar_tac))
  have hupd1 : ∀ v, Array.update stack sp1 v = ok (stack.set sp1 v) := fun v =>
    eq_of_spec_fd (Array.update_spec stack sp1 v hl)
  rw [em, esp2] at h
  simp only [bind_ok, hupd1] at h
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
  split_ifs at h with c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 <;>
    first
    | exact fin _ h hpop rfl
    | exact fin _ h (pl sp1 sp2 hpop h31 (by scalar_tac) ‹_›) rfl
    | (have hl2 : sp1.val < stack.length := hl
       exact fin _ h (pr stack sp1 sp2 hpop h31 (by scalar_tac) ‹_›) rfl)
    | (obtain ⟨sp3, esp3, hsp3⟩ := spec_ex_fd (Usize.add_spec (x := sp2) (y := 1#usize) (by scalar_tac))
       have hl2 : sp2.val < (stack.set sp1 (L.mem s (tlA i1))).length := by
         simp only [Array.set_length]; scalar_tac
       rw [eq_of_spec_fd (Array.update_spec _ sp2 (L.mem s (trA i1)) hl2), esp3] at h
       simp only [bind_ok] at h
       exact fin _ h (pr _ sp2 sp3 (pl sp1 sp2 hpop h31 (by scalar_tac) ‹_›) (by scalar_tac) (by scalar_tac) ‹_›) rfl)

/-- **`in_core_timer_tree` reads only `TreeReads`**: core `c`'s root and min words and the deadline and
child links of the keys of `c`'s tree (with the null handle's, never read). -/
theorem in_core_timer_tree_access {s : S} {c target d : U64} {W : TRB.RBT} {b : Bool} (ct : CoreTree st T s c W)
    (hR : ∀ w, TreeReads st s c W.keys w → R w)
    (h : localtimer.in_core_timer_tree st s c target d = ok b) :
    localtimer.in_core_timer_tree (guard st R Wr) s c target d = ok b := by
  rw [← h]
  have init : ∀ (stack1 : Array U64 32#usize) (sp : Usize), StackOK W.keys stack1 sp →
      localtimer.in_core_timer_tree_loop (guard st R Wr) s target d stack1 sp 0#u64 false false =
        localtimer.in_core_timer_tree_loop st s target d stack1 sp 0#u64 false false := by
    intro stack1 sp hok
    unfold localtimer.in_core_timer_tree_loop
    exact loop_congr _ _ (fun x => StackOK W.keys x.1 x.2.1) (fun x => 64 - x.2.2.1.val)
      (fun x hx => ictt_body_eq hR x hx) (fun x hx x' e => ictt_body_step ct x hx x' e) _ hok
  have hroot : L.mem s (L.nodeAt s c layout.node.TIMER_ROOT) = 0#u64 ∨
      L.mem s (L.nodeAt s c layout.node.TIMER_ROOT) ∈ W.keys := ct.rep.root_mem
  unfold localtimer.in_core_timer_tree
  rw [eq_of_spec_fd (obj.Tcb.is_null.spec target)]
  simp only [bind_ok]
  by_cases hn : decide (target = 0#u64) = true
  · rw [if_pos hn, if_pos hn]
  rw [if_neg hn, if_neg hn]
  rw [nodeGetG (Wr := Wr) (hR _ (Or.inl rfl)), nodeGetG (Wr := Wr) (hR _ (Or.inr (Or.inl rfl)))]
  rw [eq_of_spec_fd (obj.node_get.spec (L := L) s c layout.node.TIMER_ROOT),
    eq_of_spec_fd (obj.node_get.spec (L := L) s c layout.node.TIMER_MIN)]
  simp only [bind_ok]
  by_cases c1 : L.mem s (L.nodeAt s c layout.node.TIMER_MIN) = target
  · rw [if_pos c1, if_pos c1]
  rw [if_neg c1, if_neg c1]
  by_cases c2 : L.mem s (L.nodeAt s c layout.node.TIMER_ROOT) = target
  · rw [if_pos c2, if_pos c2]
  rw [if_neg c2, if_neg c2]
  by_cases c3 : (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT) != 0#u64) = true
  · rw [if_pos c3, if_pos c3]
    have hr : L.mem s (L.nodeAt s c layout.node.TIMER_ROOT) ∈ W.keys := hroot.resolve_left (by simpa using c3)
    have hl : (0#usize).val < (Array.repeat 32#usize 0#u64).length := by simp
    rw [eq_of_spec_fd (Array.update_spec _ 0#usize _ hl)]
    simp only [bind_ok]
    refine init _ _ ⟨by simp, fun j hj hj1 => ?_⟩
    have : j = 0 := by simp at hj1; omega
    subst this
    simpa [Array.set_val_eq] using hr
  · rw [if_neg c3, if_neg c3]
    simp only [bind_ok]
    exact init _ _ ⟨by simp, fun j hj hj1 => by simp at hj1⟩
end

end Fl4Proofs.P2
