/-
# P2: the shape of an accepted timer-interrupt local path

`irq_accept_walk`: an accepted run of `localtimer.handle_timer_irq_local` (result `true`) passes its checks in
order (the IRQ in range with state `IRQ_TIMER`, the plan, `current_ok`, `sched_quiet`, after `update_timestamp` no
due release) and then runs `check_budget`, `handle_interrupt`, `schedule`, `activate_thread` and `vcpu.check`. The
check before the tail is one of three cases (`IrqCase`):

* `quiet`: the budget is sufficient and no timer is due;
* `fire`: the budget is sufficient, a timer is due and `fire_ok` holds;
* `rr`: the budget is insufficient, no timer is due and `round_robin_ok` holds.

No named premises.
-/
import Fl4Proofs.P1.LocalTimer
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A)

/-- The three ways the check before the tail passes (module docstring). -/
inductive IrqCase (st : machine.Store S) (ar : machine.Arch A) (s1 : S) (a1 : A) (cpu ct csc : U64)
    (p : localtimer.TimerIrqPlan) (now : U64) (b4 due : Bool) : Prop
  | quiet (h4 : b4 = true) (hd : due = false)
  | fire (h4 : b4 = true) (hd : due = true) (hf : localtimer.fire_ok st s1 cpu ct p now = ok true)
  | rr (h4 : b4 = false) (hd : due = false)
      (hr : localtimer.round_robin_ok st ar s1 a1 cpu ct csc now = ok true)

set_option maxHeartbeats 4000000 in
/-- **An accepted timer interrupt beside the gate**, step by step (module docstring). -/
theorem irq_accept_walk {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (true, s', a')) :
    ∃ (cpu mx i1 ct csc now i2 : U64) (tip : localtimer.TimerIrqPlan) (b4 due x : Bool)
      (s1 s2 s3 s4 s5 : S) (a1 a2 a3 a4 a5 : A) (t : U64),
      st.cur_cpu s = ok cpu ∧ layout.irq.MAX = ok mx ∧ ¬ irq > mx ∧
      interrupt.irq_state st s irq = ok i1 ∧ i1 = interrupt.IRQ_TIMER ∧
      localtimer.plan_objects st s = ok tip ∧ localtimer.same_plan tip p = ok true ∧
      sched.cur_thread st s = ok ct ∧ sched.cur_sc st s = ok csc ∧
      localtimer.current_ok st s cpu ct csc = ok true ∧ localtimer.sched_quiet st s cpu = ok true ∧
      sched.update_timestamp st ar s a = ok (s1, a1) ∧ sched.cur_time st s1 = ok now ∧
      localtimer.release_due st s1 cpu = ok false ∧ sched.consumed st s1 = ok i2 ∧
      sporadic.sufficient st ar s1 a1 csc i2 = ok b4 ∧ localtimer.timer_due st s1 cpu now = ok due ∧
      IrqCase st ar s1 a1 cpu ct csc p now b4 due ∧
      sched.check_budget st ar s1 a1 = ok (x, s2, a2) ∧
      interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3) ∧
      sched.schedule st ar s3 a3 = ok (s4, a4) ∧ sched.activate_thread st ar s4 a4 = ok (s5, a5) ∧
      sched.cur_thread st s5 = ok t ∧ vcpu.check st ar s5 a5 t = ok (s', a') := by
  unfold localtimer.handle_timer_irq_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨cpu, ecpu, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨mx, emx, h⟩ := bind_eq_ok h
  by_cases c1 : irq > mx
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
  by_cases c2 : (i1 != interrupt.IRQ_TIMER) = true
  · rw [if_pos c2] at h; simp at h
  rw [if_neg c2] at h
  have hi1 : i1 = interrupt.IRQ_TIMER := by by_contra hne; exact c2 (bne_iff_ne.mpr hne)
  obtain ⟨tip, etip, h⟩ := bind_eq_ok h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨ct, ect, h⟩ := bind_eq_ok h
  obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
  obtain ⟨b1, eb1, h⟩ := bind_eq_ok h
  cases b1
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨b2, eb2, h⟩ := bind_eq_ok h
  cases b2
  · simp at h
  simp only [↓reduceIte] at h
  obtain ⟨⟨s1, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨now, enow, h⟩ := bind_eq_ok h
  obtain ⟨b3, eb3, h⟩ := bind_eq_ok h
  cases b3
  swap
  · simp at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i2, ei2, h⟩ := bind_eq_ok h
  obtain ⟨b4, eb4, h⟩ := bind_eq_ok h
  obtain ⟨due, edue, h⟩ := bind_eq_ok h
  obtain ⟨ok1, eok1, h⟩ := bind_eq_ok h
  cases ok1
  · simp at h
  simp only [↓reduceIte] at h
  have hc : IrqCase st ar s1 a1 cpu ct csc p now b4 due := by
    cases b4 <;> cases due <;> simp at eok1
    · exact .rr rfl rfl eok1
    · exact .quiet rfl rfl
    · exact .fire rfl rfl eok1
  obtain ⟨⟨x, s2, a2⟩, ecb, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  obtain ⟨⟨s3, a3⟩, ehi, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s4, a4⟩, esc, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨⟨s5, a5⟩, eac, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨⟨s6, a6⟩, evc, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  have e := ok_inj_ff h
  simp only [Prod.mk.injEq, true_and] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨cpu, mx, i1, ct, csc, now, i2, tip, b4, due, x, s1, s2, s3, s4, s5, a1, a2, a3, a4, a5, t, ecpu, emx, c1,
    ei1, hi1, etip, eb, ect, ecsc, eb1, eb2, eu, enow, eb3, ei2, eb4, edue, hc, ecb, ehi, esc, eac, et, evc⟩

end

end Fl4Proofs.P2
