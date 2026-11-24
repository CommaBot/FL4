/-!
P2 (p2j5): **design note — replacing the no-op `remote_stall` in the
Store/Arch model** (write-up only; no declarations, nothing rewired).

## Today

`smp::remote_tcb_stall` (crates/fl4-core/src/smp.rs:49) calls
`a.remote_stall(cpu)` at two sites (smp.rs:52, and smp.rs:63 under
`feature = "aarch64"`, not extracted). The extracted interface
(`Fl4Core/Types.lean:163`, `machine.Arch.remote_stall : A → U64 → Result A`;
`Funs.lean:10983`) threads only the `Arch` value, so in the Lean model a
stall changes no store word. The kernel (fl4-kernel `service_remote`) and
the simulator (`fl4-sim` `remote_stall`, `conc: None`) run `smp::stall` then
`smp::send_pending` with `cur_cpu = cpu` on the same memory: exactly
`stallAt st ar cpu` (`P2/StallAt.lean`).

## What relies on "a stall is a no-op" (counts on this branch)

P1 lemmas whose statements say so (uses outside their own definition /
files that mention them):

| lemma | uses | files |
|---|---|---|
| `smp.remote_tcb_stall.spec` (`s' = s` or the issuer's `IPI_PENDING`) | 13 | 14 |
| `smp.remote_tcb_stall.all` (invariants, every TCB and `Ω` word kept) | 14 | 12 |
| `smp.remote_tcb_stall.blk` | 10 | 10 |
| `smp.remote_tcb_stall.bxi` | 7 | 6 |
| `smp.remote_tcb_stall.blkS`, `.cur0` | 2 + 2 | 2 + 2 |
| `smp.remote_tcb_stall.tm`, `Stalled.stall`, `ipi_all` | 0 + 2 + 3 | 1 + 2 + 2 |

That is **9 lemmas, about 53 uses in about 25 P1 files** (QueueIpcFoot,
TimerRBSig, QueueIpc, QueueDecSc, QueueDecDom, QueueDecTcb2, QueueDecVcpu,
QueueSchedCtl, QueueFinSc, QueueFinIo, QueueFinThr, QueueFinCur, QueueFinal,
QueueFootD, QueueReplyKw, QueueReplyPop, QueueReply, QueueDead,
QueueDeadTd, QueueAppend, LocalTimer; P2 FootN4). P3 uses
`remote_tcb_stall_id` (20 uses, 15 files) and `vcpu_stall_id` (3 / 2), both
in the one-core setting (the target is on the current core, so no call is
made), and a handful of `.spec`/`.all`/`.bxi`/`.blk` uses (ScRestP1,
XTopJointSendDon, XTopJointDbgKeep). In all, `smp.remote_tcb_stall` is
named 207 times in 67 files, most of them through unfolding
`remote_tcb_stall_id` in P3, which a faithful model leaves valid.

## Cheapest faithful route

1. **fl4-core** (one signature, one call site; re-extracts): move the call to
   the `Store` trait as `Store::remote_stall(&mut self, cpu: u64)` (no `Arch`
   argument: the `Store` trait has no `Arch`); the kernel's implementation
   is today's `remote_call(CALL_STALL, …)`, the simulator's today's body;
   `Arch::remote_stall` goes. Extraction: `machine.Store.remote_stall :
   S → U64 → Result S`, and `remote_tcb_stall` threads `s` through it.
   (Size: ~10 Rust lines across fl4-core/fl4-kernel/fl4-kernel-aarch64/
   fl4-sim/untyped test double; `Funs.lean`/`Types.lean` regenerate; P0's
   `StoreTotal` gains one field and `P0/Auto` one entry.)
2. **The law** (new class beside `LawfulStore`, its laws untouched; [W]):
   `StallLaw st ar : ∀ s d s', st.remote_stall s d = ok s' → ∃ a a',
   stallAt st ar d s a = ok (s', a')`. The target's own Arch effects
   (`set_kernel_vm_root`, reschedule IPIs) are the target's and are dropped
   from the issuer's `Arch` value, as the real kernel does.
3. **P1** (the bulk): restate the 9 lemmas. `.spec` becomes "`s'` is a
   `stallAt d` result or `s`". The facts the 53 users need after the stall
   are what `stallAt.views` (`P2/StallAll.lean`) now gives: `EntryInv` and
   `IdleSc` at every core's view, `OKeep` (the other cores' node identity
   words, the protected threads' `STATE`/`IN_QUEUES`, every `SC`/`AFFINITY`
   word and SC link), plus, for the issuer, its own clauses at the base
   store (`EntryInv.ofView`, `P2/StallBase.lean`). What the users read and
   `OKeep` does not give: the stalled thread's `STATE` (now `RESTART`, not
   `RUNNING`) and `IN_QUEUES` (now possibly enqueued). The users that
   `dequeue` afterwards (`configure_flags`, `donate`'s donor) already handle
   an enqueued thread in the real kernel; their P1 proofs take the unqueued
   case only (`schedcontext.donate.ipc`'s premise) and need the queued case
   (`dequeue.inv` exists). Estimate: 9 lemma rewrites (~600 lines), ~25
   call-site adjustments (~10–40 lines each, ~700 lines), the two `dequeue`
   paths (~300 lines). P1 premises gained: the transfer and `TmoCap` [P] of
   `stallAt.views` at each stalling call (or carry them in `EntryHyps`).
4. **P3**: unchanged where the one-core premise holds (`remote_tcb_stall_id`,
   `vcpu_stall_id`: no call is made); the three P3 files using `.spec`/
   `.all`/`.bxi`/`.blk` follow P1's new statements (~100 lines).

Cheaper alternative (no fl4-core change): keep `Arch.remote_stall` and state
in P2 only a [W] premise that the issuer's continuation sees `stallAt d`'s
store, i.e. reason about a *modified* program `remote_tcb_stall'` that calls
`stallAt` and prove the P2 results for it, with a refinement lemma
`remote_tcb_stall' = remote_tcb_stall` modulo the store effect. This keeps
P1/P3 intact but leaves the extracted model and the proved model different
programs, which is the gap the rewire is meant to close.

Recommendation: route 1–4, done in a dedicated line after P2's all-cores
invariant (`OwnJ` across serial entries) is in place, since step 3's users
need exactly that invariant at the stalling call.
-/
