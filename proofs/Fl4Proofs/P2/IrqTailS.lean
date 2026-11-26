/-
# P2 (line p3mc, gen 21): the timer interrupt's program split at the plan check

Handoff §25d, step 1. `irqTailS irq cpu p`: the generated tree of `localtimer.handle_timer_irq_local` after the plan
check `same_plan (plan_objects s) p` (text of `R.localtimer.handle_timer_irq_local`, `P2/ProgGenTm2.lean`, from its
`cur_thread` on). **`irq_split`**: the tree is its head (`cur_cpu`, the IRQ range and state, `plan_objects`,
`same_plan`) followed by `irqTailS` (by `rfl`). The plan `p` occurs in the tail only in the two `fire_ok` calls.

No named premises; no existing statement changed.
-/
import Fl4Proofs.P2.ProgGenTmTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core

/-- The timer interrupt's tree after the plan check (module docstring). -/
noncomputable def irqTailS (irq cpu : Std.U64) (p : localtimer.TimerIrqPlan) : SProg Bool := do
  let ct ← R.sched.cur_thread
  let csc ← R.sched.cur_sc
  let b1 ← R.localtimer.current_ok cpu ct csc
  if b1 then do
    let b2 ← R.localtimer.sched_quiet cpu
    if b2 then do
      let _ ← R.sched.update_timestamp
      let now ← R.sched.cur_time
      let b3 ← R.localtimer.release_due cpu
      if b3 then do
        pure (false)
      else do
        let i2 ← R.sched.consumed
        let b4 ← R.sporadic.sufficient csc i2
        let due ← R.localtimer.timer_due cpu now
        let ok1 ← SProg.blk 0 (
            if ¬ b4 then do
              if due then do
                pure (false)
              else do
                if ¬ b4 then do
                  R.localtimer.round_robin_ok cpu ct csc now
                else do
                  if due then do
                    R.localtimer.fire_ok cpu ct p now
                  else do
                    pure (true)
            else do
              if ¬ b4 then do
                R.localtimer.round_robin_ok cpu ct csc now
              else do
                if due then do
                  R.localtimer.fire_ok cpu ct p now
                else do
                  pure (true))
        if ok1 then do
          let _ ← R.sched.check_budget
          let _ ← R.interrupt.handle_interrupt irq
          let _ ← R.sched.schedule
          let _ ← R.sched.activate_thread
          let t ← R.sched.cur_thread
          let _ ← R.vcpu.check t
          pure (true)
        else do
          pure (false)
    else do
      pure (false)
  else do
    pure (false)

/-- **The timer interrupt's tree is its head, then `irqTailS`** (module docstring). -/
theorem irq_split (irq : Std.U64) (p : localtimer.TimerIrqPlan) :
    R.localtimer.handle_timer_irq_local irq p = (do
      let cpu ← SProg.curCpu
      if layout.NUM_DOMAINS != 1#u64 then do
        pure (false)
      else do
        let i ← SProg.liftR (layout.irq.MAX)
        if irq > i then do
          pure (false)
        else do
          let i1 ← R.interrupt.irq_state irq
          if i1 != interrupt.IRQ_TIMER then do
            pure (false)
          else do
            let tip ← R.localtimer.plan_objects
            let b ← SProg.liftR (localtimer.same_plan tip p)
            if b then irqTailS irq cpu p
            else do
              pure (false)) := by
  unfold R.localtimer.handle_timer_irq_local irqTailS
  rfl

end Fl4Proofs.P2.PathObl
