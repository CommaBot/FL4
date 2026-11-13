/-
P3 (DESIGN.md §9), scheduler: the top module.

* SchedRel.lean: the relation `SchedRel` (single core `c`, one domain):
  P1's scheduler words (`SchedCore`) and their spec counterparts
  (`SchedSpec`: ready queues, release queue, current thread, scheduler
  action, current SC/time, consumed time, reprogram flag, TCB SC and
  priority, SCs' `refill_max`); `SchedRel.stable` (`SchedHyps.stable`).
* SchedTcb.lean: `is_schedulable` ↔ `schedulable`, the action word,
  `schedule_tcb` ↔ `set_thread_state_act` (`SchedHyps.scheduleTcb`).
* SchedQueue.lean, SchedAppend.lean: `enqueue` / `dequeue` / `append` ↔
  `tcb_sched_action tcb_sched_enqueue / dequeue / append`.
* SchedSwitch.lean: `reschedule_required`, `possible_switch_to` (with the
  refill hypothesis `ActReady`).
* SchedNtfn.lean: `set_thread_state` ↔ `set_thread_state`; the
  notification proofs' `SchedHyps` from `WakeHyps` (SC donation and the
  sporadic unblock check) and the IPC hypothesis on `cancel_ipc`.
* SchedChoose.lean: `choose_thread`'s pick ↔ the spec's.
-/
import Fl4Proofs.P3.SchedNtfn
import Fl4Proofs.P3.SchedChoose
