/-!
P2 (p2j): **the remote-stall model gap** (write-up only; no declarations, no
change to the Arch model).

## What the model says

`smp::remote_tcb_stall` (crates/fl4-core/src/smp.rs:49) calls
`Arch::remote_stall(cpu)` when the thread is `CUR_THREAD` of another core
(and, on AArch64, for the core running a VCPU's `RUN_CALLER`). The extracted
interface (`Fl4Core/Types.lean`, `machine.Arch.remote_stall : A → U64 →
Result A`) returns only an `Arch` value: in the Lean model the stall changes
no store word. INV-PLAN E5/C1 assume `remote_tcb_stall s a q = ok (s, a)`
([P] one core); P1 and P3 inherit that view.

## What the kernel does

`remote_stall(cpu)` is `smp::remote_call(CALL_STALL, …, 1 << cpu)`
(crates/fl4-arch-x86_64/src/arch.rs:178, smp.rs:84; AArch64 alike): it
publishes the call (`CALL.pending`, Release), sends the IPI and spins until
the target acknowledges (`pending` load, Acquire). The target runs
`smp::service`, which for `CALL_STALL` runs, **on the target's own `Store`
view (`cur_cpu` = target `d`)**, `fl4_core::smp::stall` and then
`fl4_core::smp::send_pending` (fl4-kernel/src/entry.rs:249–258,
fl4-kernel-aarch64/src/entry.rs:46–55), and only then clears its pending bit
(AcqRel). `smp::stall` (smp.rs:74–93), when `d`'s current thread `ct` is not
idle, writes:

* `update_timestamp`: `node[d].CUR_TIME`, `CONSUMED`;
* `check_budget`: if `CUR_SC` is short, `charge_budget(…, true)`: the SC's
  refills and `CONSUMED`, `node[d].CONSUMED`, and if `ct` is schedulable
  `end_timeslice`, i.e. one of: **a timeout-fault IPC**
  (`faults::handle_timeout` → `send_fault_ipc(…, can_donate = false)`: the
  timeout endpoint's queue, the handler's state/registers/IPC buffer and
  wakeup, `ct` blocked on a reply object, possibly another core's queues and
  `node[d].IPI_PENDING`), `append` (`d`'s ready queue) or `postpone` (`d`'s
  release queue); then `reschedule_required` and `REPROGRAM`;
* `commit_time`: `CUR_SC`'s refills and `CONSUMED`, `node[d].CONSUMED`;
* `ct.STATE`: `Running` → `Restart`;
* `enqueue(ct)` if schedulable: `d`'s ready queue, bitmap and `ct`'s links
  and `IN_QUEUES` (`ct`'s affinity may already be another core's if the gate
  holder moved it — then that core's queue);
* `switch_to_idle_thread`: `set_kernel_vm_root` (an Arch effect on `d`) and
  `node[d].CUR_THREAD := IDLE_THREAD`;
* `node[d].CUR_SC := IDLE_SC`, `CONSUMED := 0`, `REPROGRAM := 1`,
  `SCHED_ACTION := RESUME_CURRENT`;
* then `send_pending`: `node[d].IPI_PENDING := 0` and reschedule IPIs.

So the effect is not confined to `d`'s node: a stall may run a timeout-fault
IPC on `d`'s behalf. (seL4's `ipiStallCoreCallback` does not charge budget;
FL4 settles `ct`'s time first so the SC can be deleted or donated at once.)

## Which serial entries stall

Every call of `remote_tcb_stall` is inside `handle_invocation` or a
finalisation, i.e. under the gate:

* `tcb::decode` (tcb.rs:405), every TCB invocation's target; CopyRegisters'
  source (tcb.rs:549);
* `schedcontext::decode` (`maybeStallSC`, schedcontext.rs:193), every
  SchedContext invocation with a bound thread; `SchedContext_Bind` of an
  AArch64 guest TCB (schedcontext.rs:220); `unbind_all_tcbs`
  (schedcontext.rs:59: `SchedContext_Unbind`, SC finalisation); `donate`'s
  donor (schedcontext.rs:68: e.g. `reply_remove`/`reply_pop` when the server
  runs elsewhere); `configure_flags` (schedcontext.rs:297,
  `SchedControl_ConfigureFlags`);
* finalisation of a final Thread cap (objects.rs:360);
* `DomainSet_Set` (domain.rs:36);
* VCPU operations (`vcpu::stall`, vcpu.rs:700; VCPU SetTCB, vcpu.rs:840); on
  AArch64 also `kick_guest` (notification.rs:157).

No local path stalls: the only one that reaches `remote_tcb_stall` is
`TCB_SetTimer` (`tcb::decode`), and `localtimer::set_timer_target_ok`
requires `target.affinity == cur_cpu` (and, on AArch64, no bound VCPU), so
`remote_tcb_stall` sends nothing (P1 `LocalTimer`'s `stall_none`).

## Why the stall's effect belongs to the serial entry

1. The issuer holds the gate. `SerialGate::acquire` (fl4-sync/src/lib.rs:142)
   set `closed`, waited for every other core's `active` flag to clear and set
   `closed = 2` before the entry's body runs, so no local path is running on
   any core when `remote_stall` is issued, and none can start:
   `try_enter_local` fails while `closed ≠ 0` (the Dekker handshake of
   DESIGN §7). Other serial entries wait for their ticket.
2. So the target `d` is between entries when the IPI arrives: in user mode
   (the IPI vector enters the kernel and runs `service_remote` before any
   entry, entry.rs:572), idle (entry.rs:486), or spinning in a wait that
   services remote calls before running any entry body: `lock()`'s
   `acquire`, `local_entry`'s wait for a closed gate (which then returns
   `Local::Stalled`: the entry is cancelled), or the VM-exit path
   (entry.rs:748). A local path body runs with interrupts masked and has
   no stall-servicing wait: its only spin, `remote_call`'s `CALL_LOCK` wait
   for a TLB invalidation, runs `service` with a `debug_assert` that no stall
   comes, which item 1 guarantees.
3. Ordering: the issuer's writes before the stall happen-before the
   target's reads (`pending` Release/Acquire, then the IPI); the target's
   writes happen-before the issuer's continuation (`fetch_and` AcqRel, the
   issuer's Acquire spin). `d`'s previous entry ended before (a serial one
   released the gate earlier in ticket order; a local one was drained, with
   `acquire`'s Acquire fence), and its next entry starts only after the
   issuer releases the gate (serial) or the gate opens (local).

Hence every execution equals the serial one in which the issuer's entry, at
the program point of `remote_stall(d)`, runs `smp::stall` and
`smp::send_pending` with `cur_cpu = d` on the same memory, and continues.
This is exactly how the deterministic simulator models it when entries run
one at a time (`fl4-sim`'s `remote_stall`, `conc: None`: a `SimStore` with
`cpu` = target over the same memory, then `stall` and `send_pending`).

## Consequence for the Lean model

The store after a stalling serial entry differs from the model's on `d`'s
`CUR_TIME`, `CONSUMED`, `CUR_THREAD`, `CUR_SC`, `REPROGRAM`, `SCHED_ACTION`,
`IPI_PENDING`, on `ct`'s `STATE` (`Restart`, not `Running`), on `ct`'s SC's
refills and `CONSUMED`, and, if `ct`'s budget had run out with a valid
timeout handler, on everything a timeout-fault IPC writes. The holder's code
after the stall (e.g. `configure_flags`' `dequeue`, `donate`'s
`dequeue`/`release_remove`) brings the queues back in line, but not these
words. For `OwnJ` (`P2/InvAff.lean`), (1) `CurAff` and `CurScOf` at `d` hold
of the machine (`d` is on its idle thread and SC) but not of the model, e.g.
after `configure_flags` moves `d`'s current thread to another core.

Options (for the lead): model `Arch.remote_stall` as the store effect
`stallAt d` = `smp.stall` then `smp.send_pending` on the store viewed at
`cur_cpu = d` (needs a `cur_cpu` override on `LawfulStore`, the simulator's
model); or keep the [P] one-core premise for P1/P3 and state a [W] premise
for P2 that `remote_stall`'s store effect is `stallAt d`.
-/
