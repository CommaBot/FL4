/-
# P2: `in_core_timer_tree` reads only core `c`'s tree (`PathObl.acc` piece)

See `P2/FootTimerAccEq.lean` (the guarded step) and `P2/FootTimerAccStep.lean` (the stack invariant).

No named premises.
-/
import Fl4Proofs.P2.FootTimerAccStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (guard guard_read)

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {R Wr : U64 → Prop}

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
    exact PathObl.loop_guard_congr (fun x => StackOK W.keys x.1 x.2.1) (fun x => 64 - x.2.2.1.val)
      (fun x hx => ⟨ictt_body_eq hR x hx, fun x' e => ictt_body_step ct x hx x' e⟩) _ hok
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
