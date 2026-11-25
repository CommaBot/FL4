/-
# P2: replaying an accepted timer-interrupt local path on another store

`irq_replay`: if a store `st'` (in practice `PathObl.guard st R W` or `gd st R P`) answers every call of an
accepted run of `localtimer.handle_timer_irq_local` on `st` the same way, at the arguments of that run (the
equations `irq_accept_walk` returns), it ends the same way. `round_robin_ok` is asked only in the `rr` case and
`fire_ok` only in the `fire` case (`IrqCase`), so their answers are premises under those cases.

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqW
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {st st' : machine.Store S} {A : Type _} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **Replay** (module docstring). -/
theorem irq_replay {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    {cpu mx i1 ct csc now i2 : U64} {tip : localtimer.TimerIrqPlan} {b4 due x : Bool}
    {s1 s2 s3 s4 s5 : S} {a1 a2 a3 a4 a5 : A} {t : U64}
    (ecpu : st.cur_cpu s = ok cpu) (gcpu : st'.cur_cpu = st.cur_cpu)
    (emx : layout.irq.MAX = ok mx) (hle : ¬ irq > mx)
    (ei1 : interrupt.irq_state st s irq = ok i1) (gi1 : interrupt.irq_state st' s irq = interrupt.irq_state st s irq)
    (hi1 : i1 = interrupt.IRQ_TIMER)
    (etip : localtimer.plan_objects st s = ok tip) (gtip : localtimer.plan_objects st' s = localtimer.plan_objects st s)
    (eb : localtimer.same_plan tip p = ok true)
    (ect : sched.cur_thread st s = ok ct) (gct : sched.cur_thread st' s = sched.cur_thread st s)
    (ecsc : sched.cur_sc st s = ok csc) (gcsc : sched.cur_sc st' s = sched.cur_sc st s)
    (eb1 : localtimer.current_ok st s cpu ct csc = ok true)
    (gb1 : localtimer.current_ok st' s cpu ct csc = localtimer.current_ok st s cpu ct csc)
    (eb2 : localtimer.sched_quiet st s cpu = ok true)
    (gb2 : localtimer.sched_quiet st' s cpu = localtimer.sched_quiet st s cpu)
    (eu : sched.update_timestamp st ar s a = ok (s1, a1))
    (gu : sched.update_timestamp st' ar s a = sched.update_timestamp st ar s a)
    (enow : sched.cur_time st s1 = ok now) (gnow : sched.cur_time st' s1 = sched.cur_time st s1)
    (eb3 : localtimer.release_due st s1 cpu = ok false)
    (gb3 : localtimer.release_due st' s1 cpu = localtimer.release_due st s1 cpu)
    (ei2 : sched.consumed st s1 = ok i2) (gi2 : sched.consumed st' s1 = sched.consumed st s1)
    (eb4 : sporadic.sufficient st ar s1 a1 csc i2 = ok b4)
    (gb4 : sporadic.sufficient st' ar s1 a1 csc i2 = sporadic.sufficient st ar s1 a1 csc i2)
    (edue : localtimer.timer_due st s1 cpu now = ok due)
    (gdue : localtimer.timer_due st' s1 cpu now = localtimer.timer_due st s1 cpu now)
    (hc : IrqCase st ar s1 a1 cpu ct csc p now b4 due)
    (grr : b4 = false → localtimer.round_robin_ok st' ar s1 a1 cpu ct csc now =
      localtimer.round_robin_ok st ar s1 a1 cpu ct csc now)
    (gfire : due = true → localtimer.fire_ok st' s1 cpu ct p now = localtimer.fire_ok st s1 cpu ct p now)
    (ecb : sched.check_budget st ar s1 a1 = ok (x, s2, a2))
    (gcb : sched.check_budget st' ar s1 a1 = sched.check_budget st ar s1 a1)
    (ehi : interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3))
    (ghi : interrupt.handle_interrupt st' ar s2 a2 irq = interrupt.handle_interrupt st ar s2 a2 irq)
    (esc : sched.schedule st ar s3 a3 = ok (s4, a4))
    (gsc : sched.schedule st' ar s3 a3 = sched.schedule st ar s3 a3)
    (eac : sched.activate_thread st ar s4 a4 = ok (s5, a5))
    (gac : sched.activate_thread st' ar s4 a4 = sched.activate_thread st ar s4 a4)
    (et : sched.cur_thread st s5 = ok t) (gt : sched.cur_thread st' s5 = sched.cur_thread st s5)
    (evc : vcpu.check st ar s5 a5 t = ok (s', a'))
    (gvc : vcpu.check st' ar s5 a5 t = vcpu.check st ar s5 a5 t) :
    localtimer.handle_timer_irq_local st' ar s a irq p = ok (true, s', a') := by
  unfold localtimer.handle_timer_irq_local
  try simp only [lift, bind_ok]
  rw [gcpu, ecpu]
  simp only [bind_ok]
  rw [num_domains_ne_one_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [emx]
  simp only [bind_ok]
  rw [if_neg hle, gi1, ei1, hi1]
  simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [gtip, etip]
  simp only [bind_ok]
  rw [eb]
  simp only [bind_ok, ↓reduceIte]
  rw [gct, ect]
  simp only [bind_ok]
  rw [gcsc, ecsc]
  simp only [bind_ok]
  rw [gb1, eb1]
  simp only [bind_ok, ↓reduceIte]
  rw [gb2, eb2]
  simp only [bind_ok, ↓reduceIte]
  rw [gu, eu]
  simp only [bind_ok, uncurry_apply_pair]
  rw [gnow, enow]
  simp only [bind_ok]
  rw [gb3, eb3]
  simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  rw [gi2, ei2]
  simp only [bind_ok]
  rw [gb4, eb4]
  simp only [bind_ok]
  rw [gdue, edue]
  simp only [bind_ok]
  cases hc with
  | quiet h4 hd =>
    subst h4 hd
    simp only [Bool.false_eq_true, not_false_eq_true, not_true_eq_false, ↓reduceIte, bind_ok]
    rw [gcb, ecb]; simp only [bind_ok, uncurry_apply_pair]
    rw [ghi, ehi]; simp only [bind_ok, uncurry_apply_pair]
    rw [gsc, esc]; simp only [bind_ok, uncurry_apply_pair]
    rw [gac, eac]; simp only [bind_ok, uncurry_apply_pair]
    rw [gt, et]; simp only [bind_ok]
    rw [gvc, evc]; simp only [bind_ok, uncurry_apply_pair]
  | fire h4 hd hf =>
    subst h4 hd
    simp only [Bool.false_eq_true, not_false_eq_true, not_true_eq_false, ↓reduceIte, bind_ok]
    rw [gfire rfl, hf]
    simp only [bind_ok, ↓reduceIte]
    rw [gcb, ecb]; simp only [bind_ok, uncurry_apply_pair]
    rw [ghi, ehi]; simp only [bind_ok, uncurry_apply_pair]
    rw [gsc, esc]; simp only [bind_ok, uncurry_apply_pair]
    rw [gac, eac]; simp only [bind_ok, uncurry_apply_pair]
    rw [gt, et]; simp only [bind_ok]
    rw [gvc, evc]; simp only [bind_ok, uncurry_apply_pair]
  | rr h4 hd hr =>
    subst h4 hd
    simp only [Bool.false_eq_true, not_false_eq_true, not_true_eq_false, ↓reduceIte, bind_ok]
    rw [grr rfl, hr]
    simp only [bind_ok, ↓reduceIte]
    rw [gcb, ecb]; simp only [bind_ok, uncurry_apply_pair]
    rw [ghi, ehi]; simp only [bind_ok, uncurry_apply_pair]
    rw [gsc, esc]; simp only [bind_ok, uncurry_apply_pair]
    rw [gac, eac]; simp only [bind_ok, uncurry_apply_pair]
    rw [gt, et]; simp only [bind_ok]
    rw [gvc, evc]; simp only [bind_ok, uncurry_apply_pair]

end

end Fl4Proofs.P2
