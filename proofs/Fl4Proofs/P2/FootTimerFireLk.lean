/-
# P2 (p2lf): the timer interrupt glue's locks (`PlanLk` [P])

fl4-sync's `local_timer_irq` (`crates/fl4-sync/src/lib.rs:632-662`) runs `localtimer::handle_timer_irq_local` with
the objects of the plan `p` locked: `plan_timer_irq` / `plan_objects` (`crates/fl4-core/src/localtimer.rs:333-367`)
name the notification the due timer signals (`p.ntfn`, 64 bytes) and, when that wakes its thread from `Recv`, the
endpoint (`p.ep`, 16 bytes) and reply object (`p.reply`, 32 bytes) that `cancel_ipc` writes; `lock_object` takes
each before `observe` and the run, `unlock_held` after. `PlanLk lk p` says the path's lock set `lk` holds them.

An accepted fire run writes words those locks own (`OwnMap.gOwner`: a queued thread's `EP_NEXT` / `EP_PREV` are
`lock BLOCK_OBJ`'s; an endpoint's and a reply's words are their own lock's), so `PathObl.acc` / `move` of the fire
case need `PlanLk` (p2lf finding: with `lk = ∅` both fail at a `WAITING` notification whose head is the due
thread).

Named premise: `PlanLk` [P] (the glue's locks, as p2vm's `VmGlue`).
-/
import Fl4Proofs.P2.FootTimerIrqObl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core

/-- **The glue holds the plan's locks** [P] (module docstring): at every state of the path, the plan's
notification, endpoint and reply object, when named. -/
def PlanLk {S : Type _} (lk : S → U64 → Prop) (p : localtimer.TimerIrqPlan) : Prop :=
  ∀ s, (p.ntfn ≠ 0#u64 → lk s p.ntfn) ∧ (p.ep ≠ 0#u64 → lk s p.ep) ∧ (p.reply ≠ 0#u64 → lk s p.reply)

end Fl4Proofs.P2
