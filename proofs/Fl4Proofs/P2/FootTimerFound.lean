/-
# P2: `in_core_timer_tree` finds only nodes of the tree

* `in_core_found`: on a state with core `c`'s tree `W` (`CoreTree`), `in_core_timer_tree s c target d = true`
  (any `d`) only for a key `target` of `W`;
* `CoreTree.agree`: a core's tree depends only on its root and min words and the timer fields of its keys.

Used for the decline of `TCB_SetTimer` on a thread of this core armed in another core's tree: whatever the racy
deadline read, the search of this core's tree does not find it.

No named premises.
-/
import Fl4Proofs.P2.FootTimerAccLoop
import Fl4Proofs.P2.GuardGE
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

theorem ictRight_found {d v1 n' cd : U64} {rr : Result U64} {a : Array U64 32#usize} {n : Usize}
    {y : Array U64 32#usize × Usize × U64 × Bool × Bool} {f o : Bool} (hn : n' = v1)
    (h : ictRight d v1 f o rr a n cd = ok (ControlFlow.cont y)) : y.2.2.2.1 = f := by
  unfold ictRight at h
  split at h
  · obtain ⟨r, -, h⟩ := bind_eq_ok h
    split at h
    · split at h
      · rw [← cont_inj h]
      · obtain ⟨a1, -, h⟩ := bind_eq_ok h
        obtain ⟨n1, -, h⟩ := bind_eq_ok h
        rw [← cont_inj h]
    · rw [← cont_inj h]
  · rw [← cont_inj h]

theorem ictTail_found {i d v1 i1 : U64} {rd rl rr : Result U64} {stack : Array U64 32#usize} {sp1 : Usize} {o : Bool}
    {y : Array U64 32#usize × Usize × U64 × Bool × Bool}
    (h : ictTail i d stack sp1 v1 false o i1 rd rl rr = ok (ControlFlow.cont y)) (hf : y.2.2.2.1 = true) : i1 = i := by
  unfold ictTail at h
  rw [eq_of_spec_fd (tcb_eq.blk _ _)] at h
  simp only [bind_ok] at h
  by_cases hb : i1 = i
  · exact hb
  exfalso
  rw [decide_eq_false hb] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨cd, -, h⟩ := bind_eq_ok h
  have k : ∀ {a : Array U64 32#usize} {n : Usize}, ictRight d v1 false o rr a n cd = ok (ControlFlow.cont y) → False :=
    fun h => by rw [ictRight_found rfl h] at hf; exact absurd hf Bool.false_ne_true
  have k' : ∀ {a : Array U64 32#usize} {n : Usize} {b : Bool},
      (ok (ControlFlow.cont (a, n, v1, false, b)) :
        Result (ControlFlow ((Array U64 32#usize) × Usize × U64 × Bool × Bool) Bool)) = ok (ControlFlow.cont y) → False :=
    fun h => by rw [← cont_inj h] at hf; exact absurd hf Bool.false_ne_true
  split at h
  · obtain ⟨l, -, h⟩ := bind_eq_ok h
    split at h
    · split at h
      · exact k' h
      · obtain ⟨p, -, h⟩ := bind_eq_ok h
        obtain ⟨sp2, -, h⟩ := bind_eq_ok h
        split at h
        · exact k' h
        · exact k h
    · split at h
      · exact k' h
      · exact k h
  · split at h
    · exact k' h
    · exact k h

theorem ictRight_not_done {d v1 cd : U64} {rr : Result U64} {a : Array U64 32#usize} {n : Usize} {b f o : Bool}
    (h : ictRight d v1 f o rr a n cd = ok (ControlFlow.done b)) : False := by
  unfold ictRight at h
  split at h
  · obtain ⟨r, -, h⟩ := bind_eq_ok h
    split at h
    · split at h
      · simp at h
      · obtain ⟨a1, -, h⟩ := bind_eq_ok h
        obtain ⟨n1, -, h⟩ := bind_eq_ok h
        simp at h
    · simp at h
  · simp at h

theorem ictTail_not_done {i d v1 i1 : U64} {rd rl rr : Result U64} {stack : Array U64 32#usize} {sp1 : Usize}
    {f o b : Bool} (h : ictTail i d stack sp1 v1 f o i1 rd rl rr = ok (ControlFlow.done b)) : False := by
  unfold ictTail at h
  obtain ⟨e, -, h⟩ := bind_eq_ok h
  split at h
  · simp at h
  obtain ⟨cd, -, h⟩ := bind_eq_ok h
  split at h
  · obtain ⟨l, -, h⟩ := bind_eq_ok h
    split at h
    · split at h
      · simp at h
      · obtain ⟨p, -, h⟩ := bind_eq_ok h
        obtain ⟨sp2, -, h⟩ := bind_eq_ok h
        split at h
        · simp at h
        · exact ictRight_not_done h
    · split at h
      · simp at h
      · exact ictRight_not_done h
  · split at h
    · simp at h
    · exact ictRight_not_done h

theorem ictt_body_found {s : S} {c target d : U64} {W : TRB.RBT} (ct : CoreTree st T s c W)
    (x : Array U64 32#usize × Usize × U64 × Bool × Bool) (hx : StackOK W.keys x.1 x.2.1)
    (hf : x.2.2.2.1 = true → target ∈ W.keys) :
    ∀ r, localtimer.in_core_timer_tree_loop.body st s target d x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 = ok r →
      LoopPost (fun y : Array U64 32#usize × Usize × U64 × Bool × Bool =>
        StackOK W.keys y.1 y.2.1 ∧ (y.2.2.2.1 = true → target ∈ W.keys)) (fun y => 64 - y.2.2.1.val)
        (fun b => b = true → target ∈ W.keys) x r := by
  intro r h
  cases r with
  | cont y =>
    obtain ⟨h1, h2⟩ := ictt_body_step ct x hx y h
    refine ⟨⟨h1, fun hy => ?_⟩, h2⟩
    obtain ⟨stack, sp, visits, found, ov⟩ := x
    rw [body_split] at h
    by_cases g1 : sp > 0#usize
    swap
    · rw [if_neg g1] at h; simp at h
    rw [if_pos g1] at h
    by_cases g2 : visits < localtimer.TREE_VISITS
    swap
    · rw [if_neg g2] at h; simp at h
    rw [if_pos g2] at h
    cases found
    swap
    · simp at h
    cases ov
    swap
    · simp at h
    simp only [Bool.false_eq_true, ite_false] at h
    obtain ⟨v1, -, h⟩ := bind_eq_ok h
    obtain ⟨sp1, esp1, h⟩ := bind_eq_ok h
    obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
    have hi := ictTail_found h hy
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
    have hi1 := Array.index_usize_spec stack sp1 hl
    rw [ei1, WP.spec_ok] at hi1
    rw [← hi, hi1]
    exact hx.top hsp1 hl
  | done b =>
    intro hb
    obtain ⟨stack, sp, visits, found, ov⟩ := x
    refine hf ?_
    rw [body_split] at h
    have dn : ∀ {f : Bool}, (ok (ControlFlow.done f) :
        Result (ControlFlow ((Array U64 32#usize) × Usize × U64 × Bool × Bool) Bool)) = ok (ControlFlow.done b) →
        f = true := fun h => by
      have e := ok_inj_ff h
      simp only [ControlFlow.done.injEq] at e
      rw [e]; exact hb
    split at h
    · split at h
      · cases found
        · cases ov
          · simp only [Bool.false_eq_true, ite_false] at h
            exfalso
            obtain ⟨v1, -, h⟩ := bind_eq_ok h
            obtain ⟨sp1, -, h⟩ := bind_eq_ok h
            obtain ⟨i1, -, h⟩ := bind_eq_ok h
            exact ictTail_not_done h
          · exact dn h
        · rfl
      · exact dn h
    · exact dn h

/-- **`in_core_timer_tree` finds only keys** (module docstring). -/
theorem in_core_found {s : S} {c target d : U64} {W : TRB.RBT} (ct : CoreTree st T s c W)
    (h : localtimer.in_core_timer_tree st s c target d = ok true) : target ∈ W.keys := by
  have init : ∀ (stack1 : Array U64 32#usize) (sp : Usize), StackOK W.keys stack1 sp →
      localtimer.in_core_timer_tree_loop st s target d stack1 sp 0#u64 false false = ok true → target ∈ W.keys := by
    intro stack1 sp hok h
    have g := GE.loop (body := fun x : Array U64 32#usize × Usize × U64 × Bool × Bool =>
        localtimer.in_core_timer_tree_loop.body st s target d x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (body' := fun x : Array U64 32#usize × Usize × U64 × Bool × Bool =>
        localtimer.in_core_timer_tree_loop.body st s target d x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (Q := fun b : Bool => b = true → target ∈ W.keys)
      (fun y : Array U64 32#usize × Usize × U64 × Bool × Bool =>
        StackOK W.keys y.1 y.2.1 ∧ (y.2.2.2.1 = true → target ∈ W.keys)) (fun y => 64 - y.2.2.1.val)
      (fun x hx => ⟨rfl, ictt_body_found ct x hx.1 hx.2⟩) (stack1, sp, 0#u64, false, false)
      ⟨hok, fun h => absurd h Bool.false_ne_true⟩
    refine g.2 true ?_ rfl
    unfold localtimer.in_core_timer_tree_loop at h
    exact h
  have hroot : L.mem s (L.nodeAt s c layout.node.TIMER_ROOT) = 0#u64 ∨
      L.mem s (L.nodeAt s c layout.node.TIMER_ROOT) ∈ W.keys := ct.rep.root_mem
  unfold localtimer.in_core_timer_tree at h
  rw [eq_of_spec_fd (obj.Tcb.is_null.spec target)] at h
  simp only [bind_ok] at h
  by_cases hn : decide (target = 0#u64) = true
  · rw [if_pos hn] at h; simp at h
  rw [if_neg hn] at h
  have hn0 : target ≠ 0#u64 := by simpa using hn
  rw [eq_of_spec_fd (obj.node_get.spec (L := L) s c layout.node.TIMER_ROOT),
    eq_of_spec_fd (obj.node_get.spec (L := L) s c layout.node.TIMER_MIN)] at h
  simp only [bind_ok] at h
  by_cases c1 : L.mem s (L.nodeAt s c layout.node.TIMER_MIN) = target
  · rw [ct.min] at c1
    rw [← c1]; exact W.minKey_mem.resolve_left (by rw [c1]; exact hn0)
  rw [if_neg c1] at h
  by_cases c2 : L.mem s (L.nodeAt s c layout.node.TIMER_ROOT) = target
  · rw [← c2]; exact hroot.resolve_left (by rw [c2]; exact hn0)
  rw [if_neg c2] at h
  by_cases c3 : (L.mem s (L.nodeAt s c layout.node.TIMER_ROOT) != 0#u64) = true
  · rw [if_pos c3] at h
    have hr : L.mem s (L.nodeAt s c layout.node.TIMER_ROOT) ∈ W.keys := hroot.resolve_left (by simpa using c3)
    have hl : (0#usize).val < (Array.repeat 32#usize 0#u64).length := by simp
    rw [eq_of_spec_fd (Array.update_spec _ 0#usize _ hl)] at h
    simp only [bind_ok] at h
    refine init _ _ ⟨by simp, fun j hj hj1 => ?_⟩ h
    have : j = 0 := by simp at hj1; omega
    subst this
    simpa [Array.set_val_eq] using hr
  · rw [if_neg c3] at h
    simp only [bind_ok] at h
    exact init _ _ ⟨by simp, fun j hj hj1 => by simp at hj1⟩ h

/-- **A core's tree depends only on its own words.** -/
theorem CoreTree.agree {s s' : S} {c : U64} {t : TRB.RBT} (h : CoreTree st T s c t)
    (hN : ∀ o, L.nodeAt s' c o = L.nodeAt s c o)
    (h1 : L.mem s' (L.nodeAt s c layout.node.TIMER_ROOT) = L.mem s (L.nodeAt s c layout.node.TIMER_ROOT))
    (h2 : L.mem s' (L.nodeAt s c layout.node.TIMER_MIN) = L.mem s (L.nodeAt s c layout.node.TIMER_MIN))
    (hk : ∀ y ∈ t.keys, L.mem s' (tdA y) = L.mem s (tdA y) ∧ L.mem s' (tlA y) = L.mem s (tlA y) ∧
      L.mem s' (trA y) = L.mem s (trA y) ∧ L.mem s' (tpA y) = L.mem s (tpA y) ∧ L.mem s' (thA y) = L.mem s (thA y)) :
    CoreTree st T s' c t where
  rep := by
    rw [hN, h1]
    exact TRB.Rep.congr h.rep fun y hy => by
      obtain ⟨-, e1, e2, e3, e4⟩ := hk y hy
      exact ⟨e1, e2, e3, by unfold lk; simp only [e4]⟩
  nodup := h.nodup
  inT := h.inT
  armed := fun y hy => by rw [(hk y hy).1]; exact h.armed y hy
  core := fun y hy => by rw [(hk y hy).2.2.2.2]; exact h.core y hy
  sorted := List.Pairwise.imp_of_mem (fun ha hb hab => by rw [(hk _ ha).1, (hk _ hb).1]; exact hab) h.sorted
  bal := h.bal
  black := h.black
  min := by rw [hN, h2]; exact h.min

end

end Fl4Proofs.P2
