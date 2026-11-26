/-
# P2 (line p3mc, gen 22): the timer interrupt at a foreign-`tm` state reduces to its tail with the empty plan

Handoff §26c item 3, the head half. When the earliest thread `tm` of the core's timer tree is not on the core
(`AFFINITY tm ≠ cpu` in the run's memory), `plan_objects` returns the empty plan (`plan_objects_off_tm`), so the run
either declines at `same_plan` writing nothing or goes on with `p.tm = 0` (the existing `same_plan_tm`) into `irqTailF`.

* **`irq_fh_guard`**: on any store answering the IRQ state word, `TIMER_MIN` and `tm`'s `AFFINITY` (only these head
  words: `plan_objects.guard_off`, U20), a run of `localtimer.handle_timer_irq_local` is the same run as on `st`,
  given that the tail with an empty plan is (`htail`; `irqTail_guardT` supplies it at a P1 state).

No named premises; no existing statement changed.
-/
import Fl4Proofs.P2.IrqTailR
import Fl4Proofs.P2.E2EPU20
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (irqTailF bind_guard_congr tr_bind_same tr_ite)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **With the earliest thread off the core, the plan is empty.** -/
theorem plan_objects_off_tm {s : S} {tip : localtimer.TimerIrqPlan}
    (hoff : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      L.mem s (affA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ L.cpu s)
    (e : localtimer.plan_objects st s = ok tip) : tip.tm = 0#u64 := by
  unfold localtimer.plan_objects at e
  obtain ⟨cpu, ecpu, e⟩ := bind_eq_ok e
  rw [L.cur_cpu_eq] at ecpu
  have hc := ok_inj_ff ecpu
  subst hc
  dsimp only at e
  obtain ⟨i, ei, e⟩ := bind_eq_ok e
  rw [node_get_ok] at ei
  have hi := ok_inj_ff ei
  subst hi
  obtain ⟨b, eb, e⟩ := bind_eq_ok e
  rw [is_null_eq eb] at e
  by_cases h0 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) = 0#u64
  · rw [if_pos (decide_eq_true h0)] at e
    rw [← ok_inj_ff e]
  rw [if_neg (by simpa using h0)] at e
  obtain ⟨i1, ei1, e⟩ := bind_eq_ok e
  have ha : (i1 != L.cpu s) = true := by
    rw [aff_ok] at ei1
    rw [← ok_inj_ff ei1]
    simpa using hoff h0
  rw [if_pos ha] at e
  rw [← ok_inj_ff e]

variable {R : U64 → Prop} {gS : machine.Store S} [PathObl.GRd gS st R] {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **The timer interrupt at a foreign-`tm` state, on any store answering the head's reads and the tail**
(module docstring). -/
theorem irq_fh_guard {s : S} {a : A} {irq : U64} {p : localtimer.TimerIrqPlan} {r : Bool × S × A}
    (hi : irq.val < 128 → ∀ i, interrupt.state_off irq = ok i → R (core.num.U64.wrapping_add (L.ksb s) i))
    (h1 : R (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))
    (h2 : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) 3520#u64))
    (hoff : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64 →
      L.mem s (affA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) ≠ L.cpu s)
    (htail : p.tm = 0#u64 → ∀ r', irqTailF st ar s a irq (L.cpu s) p = ok r' →
      irqTailF gS ar s a irq (L.cpu s) p = ok r')
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok r) :
    localtimer.handle_timer_irq_local gS ar s a irq p = ok r := by
  have hpl := plan_objects.guard_off (gS := gS) h1 h2 hoff
  revert h
  rw [irq_splitF st, irq_splitF gS, PathObl.gst_cur_cpu (g := gS), L.cur_cpu_eq]
  simp only [bind_ok, num_domains_ne_one_false, Bool.false_eq_true, ↓reduceIte]
  refine tr_bind_same (fun mx emx => ?_)
  refine tr_ite (fun _ h => h) (fun hle => ?_)
  have hlt : irq.val < 128 := by
    rw [eq_of_spec_fd layout.irq.MAX.spec] at emx
    have e := ok_inj_ff emx
    subst e
    scalar_tac
  have eirq : interrupt.irq_state gS s irq = interrupt.irq_state st s irq := by
    unfold interrupt.irq_state
    exact bind_guard_congr rfl fun i ei => PathObl.obj.ks_get.guard (gS := gS) s i (hi hlt i ei)
  rw [eirq]
  refine tr_bind_same (fun i1 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [hpl]
  refine tr_bind_same (fun tip etip => ?_)
  refine tr_bind_same (fun b eb => ?_)
  refine tr_ite (fun hb => ?_) (fun _ h => h)
  subst hb
  have hp0 : p.tm = 0#u64 := (same_plan_tm eb).1.symm.trans (plan_objects_off_tm hoff etip)
  exact htail hp0 r

end

end Fl4Proofs.P2
