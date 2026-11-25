/-
# P2: the quiet case of an accepted timer interrupt (budget sufficient, no timer due): the tail's first two calls

* `check_budget_suf`: with a sufficient budget `check_budget` returns `(true, s, a)` (one domain: never expired);
* `handle_interrupt_timer`: for an IRQ in range with state `IRQ_TIMER` the handler sets the node's `REPROGRAM` to 1
  and `ARMED` to 0, then acks the IRQ (`Arch`).

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqW
import Fl4Proofs.P2.FootTimerIrqH
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A)

/-- **`check_budget` with a sufficient budget** writes nothing and returns `true`. -/
theorem check_budget_suf {s : S} {a : A} {csc u : U64} (ecsc : sched.cur_sc st s = ok csc)
    (eu : sched.consumed st s = ok u) (hb : sporadic.sufficient st ar s a csc u = ok true) :
    sched.check_budget st ar s a = ok (true, s, a) := by
  unfold sched.check_budget
  rw [ecsc]; simp only [bind_ok]
  rw [eu]; simp only [bind_ok]
  rw [hb]
  simp only [bind_ok, ↓reduceIte, sched.is_cur_domain_expired, if_neg num_domains_one]
  simp only [Bool.false_eq_true, not_false_eq_true, decide_true]

/-- **The handler of a timer IRQ** sets `REPROGRAM` and clears `ARMED` on the current core's node, then acks. -/
theorem handle_interrupt_timer {s s3 : S} {a a3 : A} {irq mx : U64} (emx : layout.irq.MAX = ok mx)
    (hle : ¬ irq > mx) (hst : interrupt.irq_state st s irq = ok interrupt.IRQ_TIMER) [L : LawfulStore st]
    (h : interrupt.handle_interrupt st ar s a irq = ok (s3, a3)) :
    ∃ s2, obj.node_set st s (L.cpu s) layout.node.REPROGRAM 1#u64 = ok s2 ∧
      obj.node_set st s2 (L.cpu s) layout.node.ARMED 0#u64 = ok s3 ∧ ar.ack_irq a irq = ok a3 := by
  unfold interrupt.handle_interrupt at h
  rw [emx] at h; simp only [bind_ok] at h
  rw [if_neg hle, hst] at h; simp only [bind_ok] at h
  rw [if_neg irq_timer_ne_signal] at h
  simp only [eq_self_iff_true, if_true, ↓reduceIte] at h
  obtain ⟨⟨s1, a1⟩, e1, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨a2, e2, h⟩ := bind_eq_ok h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  rw [L.cur_cpu_eq] at e1; simp only [bind_ok] at e1
  obtain ⟨s2, e3, e1⟩ := bind_eq_ok e1
  obtain ⟨s4, e4, e1⟩ := bind_eq_ok e1
  have e' := ok_inj_ff e1
  simp only [Prod.mk.injEq] at e'
  obtain ⟨rfl, rfl⟩ := e'
  exact ⟨s2, e3, e4, e2⟩

end

end Fl4Proofs.P2
