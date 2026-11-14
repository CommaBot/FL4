/-
P3 (DESIGN.md §9), endpoints: the top module.

* EpRel.lean: the relation `EpStateRel` (endpoints ↔ l4v `endpoint` with the
  queues through P1's `QueueRel`; TCB state with the `BlockedOnSend` /
  `BlockedOnReceive` / `BlockedOnReply` payloads, all registers, priority,
  fault, bound notification; replies' `reply_tcb`; mapped IPC-buffer words),
  placement `EPlaced`, footprint `EFoot`, frame lemmas.
* EpSpec.lean, EpWrite.lean, EpQueue.lean: spec accessors, relation updates,
  `ep_append` / `ep_dequeue` with frames.
* EpSched.lean: the interface `EpHyps` (`SR` stable, `schedule_tcb`) and
  `set_thread_state`.
* EpAppend.lean, EpBlock.lean: blocking on an endpoint; `send_ipc` on an idle
  endpoint or one with senders (blocking and not).
* EpRegs.lean, EpRecv.lean: register writes; `receive_ipc` on an idle
  endpoint or one with receivers (blocking and polling).
* EpXferSpec.lean, EpXfer.lean: `do_ipc_transfer` without receive buffer
  (`EpBufHyps`).
* EpDeq.lean, EpTail.lean: `ep_dequeue`, `reply_unlink`, the scheduler tails
  `EpTailHyps`.
* EpSend.lean: `send_ipc` to a waiting receiver (non-call).
* EpRecvSend.lean: `receive_ipc` from a waiting sender (non-call).
* EpCall.lean: `reply_push` without donation; `send_ipc` (call) to a waiting
  receiver with a reply object.
-/
import Fl4Proofs.P3.EpCall
