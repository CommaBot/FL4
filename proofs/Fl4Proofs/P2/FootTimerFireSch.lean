/-
# P2 (p2lf): `schedule` after a fired timer, on the guarded store: the shape

`schedSw`: `schedule`'s block for an action other than `RESUME_CURRENT` (the current thread re-queued when
schedulable, then choose-new, or the action thread switched to, appended or enqueued). `schedule_sw_eq`: on any
store, `schedule` is `awaken`, the action, `schedSw` unless it is `RESUME_CURRENT`, then `schedRes`.
`sched.awaken.guard_fire` (`timer::fire` and an `awaken_loop` that releases nothing, guarded) and
`sched.schedule.guard_sw` (the composition, premises at the real intermediate states).

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireQ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (bind_guard_congr)

/-- `schedule`'s block for an action `act` other than `RESUME_CURRENT`, at the state `s2` after `awaken`. -/
def schedSw {S : Type _} {A : Type _} (M : machine.Store S) (ar : machine.Arch A) (s2 : S) (a1 : A) (act : U64) :
    Result (S × A) := do
  let ct ← sched.cur_thread M s2
  let was_runnable ← sched.is_schedulable M s2 ct
  let s4 ←
    if was_runnable
    then sched.enqueue M s2 ct
    else ok s2
  if act = sched.ACTION_CHOOSE_NEW
  then
    sched.schedule_choose_new_thread M ar s4 a1
  else
    let ct1 ← sched.cur_thread M s4
    let t ← sched.idle_thread M s4
    let b ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq ct1 t
    let fastfail ←
      if b
      then ok true
      else
        do
        let i ← obj.Tcb.prio M act s4
        let i1 ← obj.Tcb.prio M ct1 s4
        if i < i1
        then ok true
        else ok false
    if fastfail
    then
      let i ← sched.cur_domain M s4
      let i1 ← obj.Tcb.prio M act s4
      let b1 ← sched.is_highest_prio M s4 i i1
      if b1
      then
        if was_runnable
        then
          let i2 ← obj.Tcb.prio M ct1 s4
          if i1 = i2
          then
            let s5 ← sched.append M s4 act
            let s6 ←
              sched.set_action M s5 sched.ACTION_CHOOSE_NEW
            sched.schedule_choose_new_thread M
              ar s6 a1
          else
            sched.switch_to_thread M ar s4 a1
              act
        else
          sched.switch_to_thread M ar s4 a1 act
      else
        let s5 ← sched.enqueue M s4 act
        let s6 ←
          sched.set_action M s5 sched.ACTION_CHOOSE_NEW
        sched.schedule_choose_new_thread M ar
          s6 a1
    else
      if was_runnable
      then
        let i ← obj.Tcb.prio M act s4
        let i1 ← obj.Tcb.prio M ct1 s4
        if i = i1
        then
          let s5 ← sched.append M s4 act
          let s6 ←
            sched.set_action M s5 sched.ACTION_CHOOSE_NEW
          sched.schedule_choose_new_thread M ar
            s6 a1
        else
          sched.switch_to_thread M ar s4 a1 act
      else
        sched.switch_to_thread M ar s4 a1 act

section eq
variable {S : Type} {A : Type} (M : machine.Store S) (ar : machine.Arch A)

theorem schedule_sw_eq (s : S) (a : A) :
    sched.schedule M ar s a = (do
      let (s1, a1) ← sched.awaken M ar s a
      let act ← sched.action M s1
      let (s3, a2) ← if act != sched.ACTION_RESUME_CURRENT then schedSw M ar s1 a1 act else ok (s1, a1)
      PathObl.LT.schedRes M ar s3 a2) := by
  unfold sched.schedule
  refine bind_guard_congr rfl fun x _ => ?_
  obtain ⟨s1, a1⟩ := x
  simp only [Aeneas.Std.uncurry_apply_pair]
  rw [PathObl.LT.check_domain_time_any]
  simp only [bind_ok]
  rfl

end eq

section gst
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

/-- **`awaken` after a fired timer**: the guarded `timer::fire` (`hf`), then `awaken_loop` releasing nothing at the
state it ends in (as `sched.awaken_loop.guard_nodue`). -/
theorem sched.awaken.guard_fire {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (hf : timer.fire gS ar s a = timer.fire st ar s a)
    (hl : ∀ s1 a1, timer.fire st ar s a = ok (s1, a1) →
      sched.awaken_loop gS s1 layout.WALK_FUEL = sched.awaken_loop st s1 layout.WALK_FUEL) :
    sched.awaken gS ar s a = sched.awaken st ar s a := by
  unfold sched.awaken
  rw [hf]
  refine bind_guard_congr rfl fun x hx => ?_
  obtain ⟨s1, a1⟩ := x
  simp only [Aeneas.Std.uncurry_apply_pair]
  rw [hl s1 a1 hx]

/-- **`schedule` on the guarded store, by its shape** (module docstring). -/
theorem sched.schedule.guard_sw {A : Type} (ar : machine.Arch A) (s : S) (a : A)
    (haw : sched.awaken gS ar s a = sched.awaken st ar s a)
    (hk : ∀ s1 a1, sched.awaken st ar s a = ok (s1, a1) →
      R (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) ∧
      (L.actionW s1 ≠ sched.ACTION_RESUME_CURRENT →
        schedSw gS ar s1 a1 (L.actionW s1) = schedSw st ar s1 a1 (L.actionW s1)) ∧
      ∀ s3 a2, (if L.actionW s1 != sched.ACTION_RESUME_CURRENT then schedSw st ar s1 a1 (L.actionW s1)
          else ok (s1, a1)) = ok (s3, a2) →
        PathObl.LT.schedRes gS ar s3 a2 = PathObl.LT.schedRes st ar s3 a2) :
    sched.schedule gS ar s a = sched.schedule st ar s a := by
  rw [schedule_sw_eq, schedule_sw_eq, haw]
  refine bind_guard_congr rfl fun x hx => ?_
  obtain ⟨s1, a1⟩ := x
  obtain ⟨rA, hsw, hres⟩ := hk s1 a1 hx
  simp only [Aeneas.Std.uncurry_apply_pair]
  rw [PathObl.sched.action.guard (gS := gS) s1 rA, eq_of_spec_fd (sched.action.spec (L := L) s1)]
  simp only [bind_ok]
  refine bind_guard_congr ?_ fun y hy => ?_
  · by_cases h : (L.actionW s1 != sched.ACTION_RESUME_CURRENT) = true
    · rw [if_pos h, if_pos h]; exact hsw (bne_iff_ne.mp h)
    · rw [if_neg h, if_neg h]
  · obtain ⟨s3, a2⟩ := y
    simp only [Aeneas.Std.uncurry_apply_pair]
    exact hres s3 a2 hy

end gst

end Fl4Proofs.P2
