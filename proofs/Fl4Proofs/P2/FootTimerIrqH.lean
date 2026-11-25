/-
# P2: the timer interrupt local path's state check, budget check and interrupt handler on the guarded store

On any store `gS` that answers `R` reads (and `W` writes) as `st` (`PathObl.GRd` / `PathObl.GWr`: `guard st R W` for
`acc`, `gd st R P` for `move`):

* `interrupt.irq_state.guard`: the IRQ's state word (`ks + IRQ_STATE + 8 irq`) is read;
* `interrupt.handle_interrupt.guard_timer`: for an IRQ in range whose state is `IRQ_TIMER`, the handler reads the
  state word and writes the node's `REPROGRAM` and `ARMED` (the `Arch`'s mask / ack are no store words);
* `sched.check_budget.guard_suf`: when the current SC's budget is sufficient, `check_budget` reads `CUR_SC`,
  `CONSUMED` and the SC's head (`RdHead`), and writes nothing (one domain: `is_cur_domain_expired` reads nothing).

`localtimer.same_plan` takes no store. The insufficient-budget branch of `check_budget` (`charge_budget`, the
round-robin case of the timer interrupt) is not covered here.

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (bind_guard_congr RdHead)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

/-- **The IRQ's state word.** -/
theorem interrupt.irq_state.guard (s : S) (irq : U64) {i : U64} (hi : interrupt.state_off irq = ok i)
    (h : R (core.num.U64.wrapping_add (L.ksb s) i)) :
    interrupt.irq_state gS s irq = interrupt.irq_state st s irq := by
  unfold interrupt.irq_state
  rw [hi]
  simp only [bind_ok]
  exact PathObl.obj.ks_get.guard (gS := gS) s i h

theorem irq_timer_ne_signal : ¬ (interrupt.IRQ_TIMER = interrupt.IRQ_SIGNAL) := by
  intro h
  have := congrArg (fun x : U64 => x.val) h
  simp [interrupt.IRQ_TIMER, interrupt.IRQ_SIGNAL] at this

/-- **The handler of a timer IRQ**: the state read (`hr`, e.g. `interrupt.irq_state.guard`), then `REPROGRAM` and
`ARMED`. -/
theorem interrupt.handle_interrupt.guard_timer {A : Type} (ar : machine.Arch A) (s : S) (a : A) (irq : U64)
    (hst : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER)
    (hr : interrupt.irq_state gS s irq = interrupt.irq_state st s irq)
    (hw1 : W (L.nodeAt s (L.cpu s) layout.node.REPROGRAM))
    (hw2 : ∀ s2, obj.node_set st s (L.cpu s) layout.node.REPROGRAM 1#u64 = ok s2 →
      W (L.nodeAt s2 (L.cpu s) layout.node.ARMED)) :
    interrupt.handle_interrupt gS ar s a irq = interrupt.handle_interrupt st ar s a irq := by
  unfold interrupt.handle_interrupt
  refine bind_guard_congr rfl fun i _ => ?_
  by_cases hi : irq > i
  · rw [if_pos hi, if_pos hi]
  rw [if_neg hi, if_neg hi, hr, hst]
  simp only [bind_ok]
  rw [if_neg irq_timer_ne_signal, if_neg irq_timer_ne_signal]
  simp only [eq_self_iff_true, if_true, ↓reduceIte]
  refine bind_guard_congr ?_ fun _ _ => rfl
  simp only [PathObl.gst_cur_cpu, L.cur_cpu_eq, bind_ok]
  rw [PathObl.obj.node_set.guard (gS := gS) s _ _ _ hw1]
  refine bind_guard_congr rfl fun s2 e2 => ?_
  rw [PathObl.obj.node_set.guard (gS := gS) s2 _ _ _ (hw2 s2 e2)]

/-- **`check_budget` with a sufficient budget** reads `CUR_SC`, `CONSUMED`, the SC's head, and writes nothing. -/
theorem sched.check_budget.guard_suf {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (h1 : R (L.nodeAt s (L.cpu s) layout.node.CUR_SC)) (h2 : R (L.nodeAt s (L.cpu s) layout.node.CONSUMED))
    (h3 : ∀ sc, sched.cur_sc st s = ok sc → RdHead (L := L) R s sc)
    (hsuf : ∀ sc c, sched.cur_sc st s = ok sc → sched.consumed st s = ok c →
      sporadic.sufficient st ar s a sc c = ok true) :
    sched.check_budget gS ar s a = sched.check_budget st ar s a := by
  unfold sched.check_budget
  rw [PathObl.sched.cur_sc.guard (gS := gS) s h1]
  refine bind_guard_congr rfl fun sc esc => ?_
  rw [PathObl.sched.consumed.guard (gS := gS) s h2]
  refine bind_guard_congr rfl fun c ec => ?_
  rw [PathObl.sporadic.sufficient.guard (gS := gS) ar s a sc c (h3 sc esc), hsuf sc c esc ec]
  simp only [bind_ok, if_pos, sched.is_cur_domain_expired, if_neg num_domains_one, if_true]

end

end Fl4Proofs.P2
