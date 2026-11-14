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
* EpCall2.lean, EpCall3.lean: the other call branches (caller / sender
  `Inactive`; `receive_ipc` from a calling sender with `reply_push`).
* EpBytes.lean, EpBufSpec.lean: X64 `storeWord` / `loadWord` round trip; the
  spec's buffer accessors and `copy_mrs` with both buffers.
* EpXferBuf.lean, EpXferBuf2.lean: buffer words in the relation (`upd_buf`),
  the second `copy_mrs` loop, `do_ipc_transfer` with a receive buffer
  (`EpBufMapHyps`).
* EpSendBuf.lean, EpRecvBuf.lean: send to / receive from a waiting partner
  with a mapped receive buffer.

## Merging the subsystem relations (note for later)

`NtfnStateRel` (NtfnRel.lean, `TcbRel1`) and `EpStateRel` (`TcbRelE`) both
relate TCB fields: the state word (both), the block-object word (both, for
their own blocked states), the badge register RDI (`TcbRel1.badge`; one of
the 24 registers of `TcbRelE.regs`) and the priority (both). Each proof
assumes the *other* relation is in `SR` and stable under its writes
(`SchedHyps.stable`, `EpHyps.stable`), which fails for these shared words, so
the two cannot simply be conjoined. The plan for one TCB relation:

* `TcbRel R m t x` (one structure, owned by neither subsystem): the state
  code `tsCode` (as now), the block object for every blocked state
  (`epBlocked` and `ntfnBlocked`), the IPC payloads of `TcbRelE` (send badge
  and flags, receive / reply reply-object words), all registers, priority,
  fault, bound notification, and the SC word (`tcbSchedContext ↔ scA`, now
  assumed through `SR`); `TcbRel1` and `TcbRelE` become projections of it.
* The object parts stay per subsystem: `NtfnObjRel` + `NtfnRel1`,
  `EpObjRel`, replies, SCs, with the queue-membership facts they need from
  TCBs read through `TcbRel` (state 3/4 with `blockedOnReceive` /
  `blockedOnSend`, 6 with `blockedOnNotification`).
* `StateRel = TcbsRel ∧ NtfnObjsRel ∧ EpObjsRel ∧ …`, with one footprint (the
  union of `NFoot` and `EFoot`; `TF` already covers the notification TCB
  words, the badge register being one of the registers) and one `KView`
  (the union of the two). The update lemmas become `upd_tcb` on the shared
  part plus per-object `upd_ntfn` / `upd_ep` / `upd_reply`, each requiring that
  the TCB stays in no queue of either kind or keeps its state and block word
  (`not_queued` and NtfnBlock's `not_member` both follow from `tsCode`).
* `SR` then only stands for subsystems that do not read TCB IPC fields
  (scheduler queues and action, SCs, CSpace), and its `stable` hypotheses
  are sound for both the notification and the endpoint writes.
-/
import Fl4Proofs.P3.EpRecvBuf
