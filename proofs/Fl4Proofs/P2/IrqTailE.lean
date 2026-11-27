/-
# P2 (line p3mc, gen 21): the timer interrupt's tail tree and its function

Handoff §26c item 1, first half. `irqTailF`: the extracted body of `localtimer.handle_timer_irq_local` after the plan
check (Funs.lean, from `cur_thread` on, text copied), a function of the plan `p` only through `fire_ok`.
**`irqTailS_eq`**: `interp` of `PathObl.irqTailS` (P2/IrqTailS.lean) is `irqTailF` (the generated tree's `_eq`
tactic); **`irqTailS_nz`**: `NoZero`.

No named premises; no existing statement changed.
-/
import Fl4Proofs.P2.IrqTailS
open Aeneas Aeneas.Std Result

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace Fl4Proofs.P2.PathObl
open fl4_core

section
variable {S : Type} {A : Type} (mS : machine.Store S) (mA : machine.Arch A)

/-- The extracted timer-interrupt body after the plan check (module docstring). -/
def irqTailF {S : Type _} {A : Type _} (machineStoreInst : machine.Store S) (machineArchInst : machine.Arch A)
    (s : S) (a : A) (irq cpu : Std.U64) (p : localtimer.TimerIrqPlan) : Result (Bool × S × A) := do
  let ct ← sched.cur_thread machineStoreInst s
  let csc ← sched.cur_sc machineStoreInst s
  let b1 ← localtimer.current_ok machineStoreInst s cpu ct csc
  if b1
  then
    let b2 ← localtimer.sched_quiet machineStoreInst s cpu
    if b2
    then
      let (s1, a1) ←
        sched.update_timestamp machineStoreInst machineArchInst s a
      let now ← sched.cur_time machineStoreInst s1
      let b3 ← localtimer.release_due machineStoreInst s1 cpu
      if b3
      then ok (false, s1, a1)
      else
        let i2 ← sched.consumed machineStoreInst s1
        let b4 ←
          sporadic.sufficient machineStoreInst machineArchInst s1 a1
            csc i2
        let due ← localtimer.timer_due machineStoreInst s1 cpu now
        let ok1 ←
          if ¬ b4
          then
            if due
            then ok false
            else
              if ¬ b4
              then
                localtimer.round_robin_ok machineStoreInst
                  machineArchInst s1 a1 cpu ct csc now
              else
                if due
                then
                  localtimer.fire_ok machineStoreInst s1 cpu ct p now
                else ok true
          else
            if ¬ b4
            then
              localtimer.round_robin_ok machineStoreInst
                machineArchInst s1 a1 cpu ct csc now
            else
              if due
              then localtimer.fire_ok machineStoreInst s1 cpu ct p now
              else ok true
        if ok1
        then
          let (_, s2, a2) ←
            sched.check_budget machineStoreInst machineArchInst s1 a1
          let (s3, a3) ←
            interrupt.handle_interrupt machineStoreInst machineArchInst
              s2 a2 irq
          let (s4, a4) ←
            sched.schedule machineStoreInst machineArchInst s3 a3
          let (s5, a5) ←
            sched.activate_thread machineStoreInst machineArchInst s4
              a4
          let t ← sched.cur_thread machineStoreInst s5
          let (s6, a6) ←
            vcpu.check machineStoreInst machineArchInst s5 a5 t
          ok (true, s6, a6)
        else ok (false, s1, a1)
    else ok (false, s, a)
  else ok (false, s, a)

theorem irqTailS_eq (irq cpu : Std.U64) (p : localtimer.TimerIrqPlan) (sS : S) (aA : A) :
    interp mS mA (irqTailS irq cpu p) sS aA =
      (irqTailF mS mA sS aA irq cpu p >>= fun r => ok (r.1, r.2.1, r.2.2)) := by
  unfold irqTailS
  simp only [reif_simps, irqTailF]
  repeat' (first
    | (with_reducible apply bind_congr_r; intro)
    | (with_reducible refine ite_congr' (fun _ => ?_) (fun _ => ?_))
    | (with_reducible refine ite_bind_congr' (fun _ => ?_) (fun _ => ?_))
    | (simp only [reif_simps])
    | ((with_reducible refine bind_cut mS mA ?sh ?_ (fun _ => ?_)); (case sh => first
      | ((refine (show BlkShape S A 0 _ _ from ?_)); exact (fun r sB aB => (r, sB, aB)))
      ))
    | reif_step)
  all_goals (exfalso; simp only [*, reduceCtorEq] at *)

theorem irqTailS_nz (irq cpu : Std.U64) (p : localtimer.TimerIrqPlan) : NoZero (irqTailS irq cpu p) := by
  unfold irqTailS
  try simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret]
  repeat' (first
    | (with_reducible apply NoZero.sbind)
    | (with_reducible apply NoZero.blk)
    | (with_reducible apply NoZero.ite')
    | (with_reducible exact NoZero.liftR _)
    | (with_reducible exact NoZero.read _)
    | (with_reducible exact NoZero.readPair _)
    | (with_reducible exact NoZero.write _ _)
    | (with_reducible exact NoZero.ksBase)
    | (with_reducible exact NoZero.curCpu)
    | (with_reducible exact NoZero.frameMasks)
    | (intro; try dsimp only)
    | (with_reducible apply R.interrupt.handle_interrupt_nz)
    | (with_reducible apply R.interrupt.irq_state_nz)
    | (with_reducible apply R.localtimer.current_ok_nz)
    | (with_reducible apply R.localtimer.fire_ok_nz)
    | (with_reducible apply R.localtimer.plan_objects_nz)
    | (with_reducible apply R.localtimer.release_due_nz)
    | (with_reducible apply R.localtimer.round_robin_ok_nz)
    | (with_reducible apply R.localtimer.sched_quiet_nz)
    | (with_reducible apply R.localtimer.timer_due_nz)
    | (with_reducible apply R.sched.activate_thread_nz)
    | (with_reducible apply R.sched.check_budget_nz)
    | (with_reducible apply R.sched.consumed_nz)
    | (with_reducible apply R.sched.cur_sc_nz)
    | (with_reducible apply R.sched.cur_thread_nz)
    | (with_reducible apply R.sched.cur_time_nz)
    | (with_reducible apply R.sched.schedule_nz)
    | (with_reducible apply R.sched.update_timestamp_nz)
    | (with_reducible apply R.sporadic.sufficient_nz)
    | (with_reducible apply R.vcpu.check_nz)
    | (simp only [reif_nz])
    | split
    | (exact trivial)
    | (dsimp only))

end

end Fl4Proofs.P2.PathObl
