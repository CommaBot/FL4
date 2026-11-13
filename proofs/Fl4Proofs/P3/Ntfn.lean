/-
P3 (DESIGN.md §9), notifications: the top module.

* NtfnRel.lean: the relation `NtfnStateRel` (notifications ↔ l4v
  `notification`, with the waiting queue through P1's `QueueRel`; TCB state,
  badge register and priority), placement `NPlaced`, footprint `NFoot`,
  frame lemmas.
* NtfnSpec.lean: the spec's accessors on related objects.
* NtfnWrite.lean, NtfnQueue.lean: what FL4's writes and queue operations
  leave alone.
* NtfnSend.lean: `send_signal` on an idle (unbound, or bound TCB not
  receiving) or active notification: single spec outcome, no hypotheses on
  other subsystems.
* NtfnSched.lean, NtfnWake.lean: the scheduler/IPC interface `SchedHyps`
  (relation `SR` of the other subsystems, abstract) and `send_signal` on a
  waiting notification and on an idle one whose bound TCB is receiving.
* NtfnRecv.lean, NtfnBlock.lean: `receive_signal` (polling, active,
  blocking) and `complete_signal` (active), with `RecvHyps`.
-/
import Fl4Proofs.P3.NtfnBlock
