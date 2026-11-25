/-
# P2 (p2lf): `schedule`'s action block for a woken thread, on the guarded store

`schedSwB`: the part of `schedSw` after the current thread `ct` is re-queued (when `was` schedulable) for an action
`act` other than `CHOOSE_NEW`: the fastfail test (`ct` idle, or `act`'s priority below `ct`'s), the bitmap test,
then `append` / `enqueue` of `act` and choose-new, or `switch_to_thread act`. `schedSw_eq`: `schedSw` is the
re-queue, then choose-new or `schedSwB`. `schedSwB.guard` / `schedSw.guard`: the guarded runs are the real ones
given the words read and the three possible tails at the real states.

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireSch
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (bind_guard_congr RdBitmap)

/-- `schedSw` after the re-queue of the current thread, for an action thread `act` (module docstring). -/
def schedSwB {S : Type _} {A : Type _} (M : machine.Store S) (ar : machine.Arch A) (s4 : S) (a1 : A) (act : U64)
    (was_runnable : Bool) : Result (S × A) := do
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

theorem schedSw_eq {S : Type _} {A : Type _} (M : machine.Store S) (ar : machine.Arch A) (s2 : S) (a1 : A)
    (act : U64) :
    schedSw M ar s2 a1 act = (do
      let ct ← sched.cur_thread M s2
      let was_runnable ← sched.is_schedulable M s2 ct
      let s4 ← if was_runnable then sched.enqueue M s2 ct else ok s2
      if act = sched.ACTION_CHOOSE_NEW then sched.schedule_choose_new_thread M ar s4 a1
      else schedSwB M ar s4 a1 act was_runnable) := rfl

section gst
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

set_option maxHeartbeats 4000000 in
/-- **`schedSwB` on the guarded store** (module docstring). -/
theorem schedSwB.guard {A : Type} (ar : machine.Arch A) (s4 : S) (a1 : A) (act : U64) (was : Bool)
    (rC : R (L.nodeAt s4 (L.cpu s4) layout.node.CUR_THREAD))
    (rId : R (L.nodeAt s4 (L.cpu s4) layout.node.IDLE_THREAD))
    (rPa : R (prioA act)) (rPc : R (prioA (L.curW s4)))
    (rCd : R (core.num.U64.wrapping_add (L.ksb s4) layout.ks.CUR_DOMAIN)) (hBm : RdBitmap (L := L) R s4)
    (hA : (do
        let s5 ← sched.append gS s4 act
        let s6 ← sched.set_action gS s5 sched.ACTION_CHOOSE_NEW
        sched.schedule_choose_new_thread gS ar s6 a1) = (do
        let s5 ← sched.append st s4 act
        let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
        sched.schedule_choose_new_thread st ar s6 a1))
    (hE : (do
        let s5 ← sched.enqueue gS s4 act
        let s6 ← sched.set_action gS s5 sched.ACTION_CHOOSE_NEW
        sched.schedule_choose_new_thread gS ar s6 a1) = (do
        let s5 ← sched.enqueue st s4 act
        let s6 ← sched.set_action st s5 sched.ACTION_CHOOSE_NEW
        sched.schedule_choose_new_thread st ar s6 a1))
    (hS : sched.switch_to_thread gS ar s4 a1 act = sched.switch_to_thread st ar s4 a1 act) :
    schedSwB gS ar s4 a1 act was = schedSwB st ar s4 a1 act was := by
  unfold schedSwB
  rw [PathObl.sched.cur_thread.guard (gS := gS) s4 rC, cur_thread_ok]
  simp only [bind_ok]
  rw [PathObl.sched.idle_thread.guard (gS := gS) s4 rId]
  refine bind_guard_congr rfl fun t _ => ?_
  refine bind_guard_congr rfl fun b _ => ?_
  refine bind_guard_congr ?_ fun ff _ => ?_
  · by_cases hb : b = true
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb, PathObl.obj.Tcb.prio.guard (gS := gS) act s4 rPa,
        PathObl.obj.Tcb.prio.guard (gS := gS) _ s4 rPc]
  · by_cases hf : ff = true
    · rw [if_pos hf, if_pos hf, PathObl.sched.cur_domain.guard (gS := gS) s4 rCd]
      refine bind_guard_congr rfl fun d _ => ?_
      rw [PathObl.obj.Tcb.prio.guard (gS := gS) act s4 rPa]
      refine bind_guard_congr rfl fun i1 _ => ?_
      rw [PathObl.sched.is_highest_prio.guard (gS := gS) s4 _ _ hBm]
      refine bind_guard_congr rfl fun b1 _ => ?_
      by_cases h1 : b1 = true
      · rw [if_pos h1, if_pos h1]
        by_cases hw : was = true
        · rw [if_pos hw, if_pos hw, PathObl.obj.Tcb.prio.guard (gS := gS) _ s4 rPc]
          refine bind_guard_congr rfl fun i2 _ => ?_
          by_cases he : i1 = i2
          · rw [if_pos he, if_pos he]; exact hA
          · rw [if_neg he, if_neg he]; exact hS
        · rw [if_neg hw, if_neg hw]; exact hS
      · rw [if_neg h1, if_neg h1]; exact hE
    · rw [if_neg hf, if_neg hf]
      by_cases hw : was = true
      · rw [if_pos hw, if_pos hw, PathObl.obj.Tcb.prio.guard (gS := gS) act s4 rPa,
          PathObl.obj.Tcb.prio.guard (gS := gS) _ s4 rPc]
        refine bind_guard_congr rfl fun i _ => ?_
        refine bind_guard_congr rfl fun i1 _ => ?_
        by_cases he : i = i1
        · rw [if_pos he, if_pos he]; exact hA
        · rw [if_neg he, if_neg he]; exact hS
      · rw [if_neg hw, if_neg hw]; exact hS

/-- **`schedSw` for an action thread on the guarded store**: the current thread's schedulability, its
re-queue (`hq`), then `schedSwB` at the state it ends in (`hB`). -/
theorem schedSw.guard {A : Type} (ar : machine.Arch A) (s2 : S) (a1 : A) (act : U64)
    (hcn : act ≠ sched.ACTION_CHOOSE_NEW)
    (rC : R (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD))
    (rS : R (stA (L.curW s2))) (rSc : R (scA (L.curW s2))) (rM : R (maxA (L.mem s2 (scA (L.curW s2)))))
    (rI : R (inqA (L.curW s2)))
    (hq : sched.is_schedulable st s2 (L.curW s2) = ok true →
      sched.enqueue gS s2 (L.curW s2) = sched.enqueue st s2 (L.curW s2))
    (hB : ∀ was s4, sched.is_schedulable st s2 (L.curW s2) = ok was →
      (if was then sched.enqueue st s2 (L.curW s2) else ok s2) = ok s4 →
      schedSwB gS ar s4 a1 act was = schedSwB st ar s4 a1 act was) :
    schedSw gS ar s2 a1 act = schedSw st ar s2 a1 act := by
  rw [schedSw_eq, schedSw_eq, PathObl.sched.cur_thread.guard (gS := gS) s2 rC, cur_thread_ok]
  simp only [bind_ok]
  rw [PathObl.sched.is_schedulable.guard (gS := gS) s2 _ rS rSc rM rI]
  refine bind_guard_congr rfl fun was hw => ?_
  refine bind_guard_congr ?_ fun s4 h4 => ?_
  · by_cases h : was = true
    · subst h; rw [if_pos rfl, if_pos rfl]; exact hq hw
    · rw [if_neg h, if_neg h]
  · rw [if_neg hcn, if_neg hcn]
    exact hB was s4 hw h4

end gst

end Fl4Proofs.P2
