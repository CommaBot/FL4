# Kernel entry above handle_invocation at J (ke1 line, branch par/kentry in FL4-rb, base 95ba7a8)

(The old local branch `par/kentry` (efc87ca = pre-merge copy of 2fb6582, already in the base) was renamed
`par/kentry-old-efc87ca`; `par/kentry` is new at 95ba7a8.)

## Phase 1: the call chain on both sides

FL4 = crates/fl4-core/src (Aeneas: proofs/Fl4Core/Funs.lean). Spec = proofs/Fl4Spec.

### Top
| FL4 | spec | status |
|---|---|---|
| `syscall::handle_syscall` syscall.rs:308 (Funs 40359) | `callKernel (.syscallEvent c)` Syscall.lean:297 = `handleE (handleEvent ev) (fun _ => withoutPreemption preemptionPath); schedule; activateThread` | nothing at P3 (P1: `handle_syscall.entry`, QueueEntry) |
| 1. read cur thread, `set_reg FAULT_IP (NEXT_IP - 2)` :310-312 | none in `callKernel`: l4v puts the user context into the TCB in ADT_A `kernel_entry` (`thread_set (tcb_arch := arch_tcb_context_set tc …)`) before `call_kernel` | MISMATCH M1 |
| 2. `flags & TRAP_SYSCALLS` → `unknown_syscall_fault` :314 (l4h 0001) | no spec counterpart (handleEvent has no trap flag) | MISMATCH M2 (out of this line's scope) |
| 3. number out of [SYSCALL_MIN, SYSCALL_MAX] → `handle_unknown_syscall` :318 (debug syscalls, SetTLSBase, `.unknownSyscall`) | `handleEvent (.unknownSyscall n)` :244 | not here (M2) |
| 4. `budget_ok` :32 = `update_timestamp` sched.rs:440; `check_budget_restart` sched.rs:524 | `handleEvent` :221-222 `updateTimeStamp` KHeap.lean:588; `checkBudgetRestart` Ipc.lean:570 | ScEntry `budget_ok_refines` (SchedRel/Inv/CurInv level, NOT J); ScEntryRd `budget_ok_offReady`, `checkBudget_true`, `checkBudgetRestart_true` (spec: true ⇒ action unchanged) |
| 5. `dispatch_syscall` :329 (Funs 40253) | the `match call` of `handleEvent` :223-243 | this line, below |
| 6. `finish` :37 = `sched::schedule` sched.rs:623; `activate_thread` sched.rs:664 | `schedule` Schedule.lean:225; `activateThread` Tcb.lean:74 | ScFireJ `jat_scheduleF` / ScSignalJ `jat_scheduleS`: JAtZ kept across FL4 `schedule` (the spec outcome only via `hTail`'s `SchTailHypsR`, not in the conclusion); `activate_thread` nothing at P3 |

### dispatch_syscall (number → spec `Syscall`)
Reads `t = cur_thread`, `cptr = t.reg CAP`, `reply = t.reg REPLY` up front (spec: `getCapReg cap_register` /
`replyRegister` per case; IpcRecvTop `mem_getCapReg`; the register words related by `IRel`'s `TcbRelE.regs`).
| FL4 (syscall.rs) | spec (Syscall.lean) | status |
|---|---|---|
| SysSend :333 `handle_invocation(false,true,false,false,cptr)` + `after_invocation` | `.sysSend` → `handleSend true` :165 = `getCapReg cap_register >>= handleInvocation false true false false` | `handle_invocation_refinesJ` (XTopJointEntry, against `fl4HandleInvocationR true`, M3); front-end equations are its hypotheses (item 1) |
| SysNBSend :336 (false,false,false,false) | `handleSend false` | same |
| SysCall :339 (true,true,true,false) | `handleCall` :170 | same |
| SysRecv/NBRecv/Wait/NBWait :342-349 `handle_recv(bl, canReply)` syscall.rs:223 | `withoutPreemption (handleRecv bl cr)` :186 | IpcRecvTop `handle_recv_refines` (any `Rel`, given `RecvLeaves`); leaves: IpcLeaves `recvLeaves_of` at IpcRel level (`RecvRest` named). At J: no `receive_ipc` (endpoint.rs:113) / `receive_signal` (notification.rs:117) yet |
| SysReplyRecv :351 `handle_invocation(false,false,true,true,reply)`; if `after_invocation` then `handle_recv(true,true)` | `.sysReplyRecv` :229: `handleInvocation false false true true replyCptr; withoutPreemption (handleRecv true true)` (an error = preemption skips the receive) | invocation at J; recv not at J; JEntryAt facts at the mid state (M6) |
| SysNBSendRecv :357 (dest = `NBSEND_RECV_DEST` reg) | `.sysNBSendRecv` :233 `getCapReg nbsendRecvDest` | same |
| SysNBSendWait :363 | `.sysNBSendWait` :237 | same |
| SysYield :368 `handle_yield` :274 | `withoutPreemption handleYield` :156 | statement-for-statement equal (both read `sc.consumed` and `consumedTime` before `chargeBudget head false`, then store the sum); `charge_budget` only at SchedRel (ScCharge6 `charge_budget_refines`, with `hto`/`hval` premises), not at J |
| no other number (in range, no op) | no other `Syscall` constructor | the range check of step 3 covers it |

### Preemption (`Err Preempted` of handle_invocation)
| FL4 | spec | status |
|---|---|---|
| `after_invocation` :282: Ok → `true`; Err → `mcs_preemption_point` :261, `take_pending_irq`, `check_interrupt` :294 (`interrupt::handle_interrupt` interrupt.rs:106) | `handleE … (fun _ => withoutPreemption preemptionPath)` in `callKernel`; `preemptionPath` :277 = (schedulable ? `checkBudget` : active ? `chargeBudget consumed false` : consumed := 0); `maybeHandleInterrupt true` | handle_invocation_refinesJ gives `JAtPre` after a preemption. Nothing at P3 for `mcs_preemption_point` (as a whole), `handle_interrupt` / `maybeHandleInterrupt` (P1 only: `interrupt.handle_interrupt.bxi`). MISMATCH M4: `take_pending_irq` (arch) vs `maybeHandleInterrupt true` (`getActiveIRQ true` machine op) – a platform [P] correspondence |

### Mismatches / decisions
* **M1 FAULT_IP**: FL4 writes FAULT_IP := NEXT_IP − 2 inside `handle_syscall`; the spec has no such write (l4v: done
  in the user-context `tc` that `kernel_entry` installs). It matters: `activate_thread` restarts a `Restart` thread at
  FAULT_IP (spec `getRestartPC`). Options: (a) state the top theorem against `asUser ct (setRegister FaultIP (nextIP−2))
  >> callKernel ev` (an `Fl4Spec.Ext` "entry" def, PORTING entry), FL4 side unchanged; (b) state it from the FL4 state
  after the write, i.e. the theorem starts at `budget_ok` with the relation at the written state (entry precondition
  "FAULT_IP set"). Recommendation (a): faithful to l4v's `kernel_entry` (the context is part of the event), small
  (one register-write frame lemma at J: a TCB register word, `IRel` regs).
* **M2 trap flag / unknown syscalls**: `TRAP_SYSCALLS` (l4h) and FL4's debug/TLS syscalls have no spec branch; outside
  this line (Send/Call/Recv/Yield). Needs an Ext event def later.
* **M3 spec dispatcher**: `handleEvent`/`handleSend`/`handleCall` call l4v's `handleInvocation`; FL4 refines
  `fl4HandleInvocationR true` (Ext/Invocation + Ext/ReplyError). DECISION: add `Fl4Spec.Ext` `fl4HandleEvent rep`
  (= `handleEvent` with `handleInvocation ↦ fl4HandleInvocationR rep`) and `fl4CallKernel` (PORTING.md "FL4
  differences": the same substitution one level up). Until then, the J theorems here are stated against the inline
  expressions (`getCapReg cap_register >>= fl4HandleInvocationR true …`), which are exactly those branches.
* **M4 interrupt source** (above): [P].
* **M5 activateThread fails** on a non-running/restart/idle current thread (`NonDet.fail`), FL4 does nothing: needs l4v
  `activatable_state` of the current thread after `schedule` ([J], l4v `ct_activatable`); not in JAtZ today.
* **M6 mid-syscall entry facts**: ReplyRecv/NBSendRecv's receive starts at the state after an invocation. The
  [J] facts of `JEntryAt` (`ni`, `ctnq`, `cnf`, `vfh`, `rd0`, …) are entry-only premises; a receive at J that needs
  any of them at the mid state needs them re-proved there (or carried in a separate invariant). Same for the
  Yield/recv after `budget_ok`: `JEntryAt.rd0` comes from `budget_ok_offReady`.
* **M7 schedule at J is preservation-only**: `jat_scheduleS` concludes `∃ σ', JAtZ … σ'` with `σ'` tied to the spec
  `schedule` only through `hTail` (`SchTailHypsR`); the top theorem needs `σ' ∈ (schedule σ1).1`.
* **M8 FL4 TCB timers** (`awaken` = `timer::fire`, l4h): proved at J (`JAtZ.fireJ`), spec side
  `Fires` (`jat_scheduleF`).

## Plan (ordered; sizes = new Lean lines, rough)
1. `JAtZ.frontEx` (front end discharged): from `JAtZ` (+ `ipcBufOK`/`bufCover` at the entry), ∃ info mi buf buffer r2
   er argsU with the seven equations `handle_invocation_refinesJ` takes (`msg_info_spec`, `lookup_buf_full`,
   `lookup_extra_top`/`lookup_extra_rel`, `getMessageInfo_eq`, `lookupIpcBuffer_eq`, `getMrs_eq`). ~120. No decision.
2. `handle_invocation_entryJ`: `handle_invocation_refinesJ` with item 1, the path premise quantified over the
   front-end values. ~40.
3. `dispatch_sendJ` (Send/NBSend/Call): `dispatch_syscall` for the three numbers: the register reads, the cap register
   against `getCapReg cap_register` (`mem_getCapReg`, regs relation), `handle_invocation_entryJ`, `after_invocation`'s
   Ok branch; the preempted branch exposed (FL4's `after_invocation` from a `JAtPre` state, spec `.error ()`), to be
   closed by item 7. ~150. No decision (spec target inline, M3).
4. `handle_recvJ`: `handle_recv_refines` at `Rel := JAt`: registers, `lookup_cap` relation and `CapObjE` from
   `JAtZ`, the bound-TCB leaf and the cap-fault leaf (`faultHypJZ` variant with `in_recv = true`) proved; the
   `receive_ipc` / `receive_signal` leaves at J named [W] (`JRecvIpcHyp`, `JRecvSigHyp`). ~200.
5. `receive_signal` at J (poll / active / block): ~600 (block analogous to `sendBlockJ`).
6. `receive_ipc` at J: block (≈ `sendBlockJ`), from a blocked sender (do_ipc_transfer at J exists; sender wake,
   call-sender reply push and donation ≈ `SendRecvCPD`), fault senders (fault xfer at J exists). ~1500+. Needs M6
   for ReplyRecv.
7. Preemption path at J: `mcs_preemption_point` (checkBudget / chargeBudget at J) + `check_interrupt` at J
   (`handle_interrupt`: notification signal at J exists = `notifLeafJ` route; timer IRQ = budget/`reprogram`) +
   M4 [P]. ~800.
8. `charge_budget` at J (shared by Yield, `budget_ok` false branch, item 7): `end_timeslice` / postpone /
   `handle_timeout` at J (the timeout-fault send at J exists: `JAtZ.runTmoJ`, `runTmoP_recv`). ~600.
9. Yield at J = item 8 + the consumed-word write. ~100 after 8.
10. `budget_ok` at J (true branch: time words only; false: item 8) and the spec `checkBudgetRestart` outcome; gives
    `JEntryAt.ni`/`rd0` at dispatch. ~300.
11. `schedule` refinement at J (M7) + `activate_thread` at J (M5). ~500.
12. `handle_syscall` composition (M1, M2 decisions, M3 Ext defs). ~200.

## Phase 2 progress
(see below)
- DONE (XTopJointDispatch.lean, std axioms): item 1 `JAtZ.frontEx`; item 2 `handle_invocation_entryJ` (path premise
  `JPathAt` at the front end's values); item 3 `dispatch_invokeJ` (Send/NBSend/Call against `DispInv call bl don` =
  `getCapReg cap_register >>= fl4HandleInvocationR true call bl don false`; preempted branch: any `Q` that
  `after_invocation (Err)` reaches from every related `JAtPre` state, premise `hPre`, closed by item 7); item 4
  `handle_recvJ` + `dispatch_recvJ` (registers, lookup, cap objects, bound TCB, cap faults proved; the leaves
  `JRecvIpcHyp`/`JRecvSigHyp` [W] = items 6/5). `handle_recvJ` takes JEntryAt's `ni`/`ctnq`/`vfh` at its own state
  (fine for Recv right after `budget_ok`; for ReplyRecv's mid state see M6).
- NOT DONE: Yield (item 9) needs `charge_budget` at J (item 8: refill/round-robin, `end_timeslice` with
  `can_timeout_fault = false`, `postpone`, `reschedule_required`); only ScCharge6 `charge_budget_refines` at
  SchedRel exists. No decision needed, only size (~600 + 100).

## ke2 (branch par/kentry2 in FL4-rb, base 345538d)
Lead decisions taken: M3 = Ext defs; M1 = option (a); M4 [P]; M2 out of scope; M5/M6/M7 plan items.
- DONE 2c87b44: `Fl4Spec/Ext/Entry.lean` (PORTING.md entry): `fl4HandleSyscall rep` (the `match call` of
  `handle_event` with `fl4HandleInvocationR rep`), `fl4HandleEvent rep` (`fl4HandleEvent_other`: non-syscall events
  are l4v's, `rfl`), `fl4CallKernel rep`, `fl4SyscallFaultIP` / `fl4KernelEntrySyscall rep c` (M1 (a): `FaultIP :=
  NextIP - 2` on the current thread, then `fl4CallKernel`). XTopJointDispatch: `invSysOf`/`recvSysOf`,
  `fl4HandleSyscall_inv` (= `DispInv`, `rfl`), `fl4HandleSyscall_recv` (= `withoutPreemption (handleRecv bl cr)`),
  `dispatch_invokeJE` / `dispatch_recvJE` (the dispatch theorems against `fl4HandleSyscall true c`).
- DONE 3d874fc (XTopJointRecvSig, item 5 part): `JAtZ.recvSigPollJ` (non-blocking, non-active: badge := 0),
  `JAtZ.recvSigActiveJ` (active: badge, ntfn idle via `signal_badge_post`, P1 BlkOK by `receive_signal.ipc`; the
  donation/sporadic check are no-ops because the current thread runs on `curSc`, `CurInv.tcb`), `JAtZ.canBlockCur`
  (P1 `CanBlock` of the resumed current thread), `jRecvSigHyp_of`, `dispatch_recvJS`. `JRecvSigHyp` [W] is replaced
  by `JRecvSigBlockHyp` [W] (blocking receive on an idle/waiting notification only).
- NEXT for item 5: the block = an ntfn analogue of XTopJointSendBlock (`send_ipc_blockF` footprint `CnW`,
  `sendIpcBlock_eq` frame `BFr`, `JAtZ.sendBlockJ`) with `ntfn_append` (IpcNtfnBlock's `receive_signal_blockI` is
  IRel-only and takes `IpcRecvHyps.returnSc` as a premise; no instance exists), then `maybe_return_sched_context`:
  a no-op unless the notification's SC is the thread's (passive server; ScReturnRef has it at SchedRel only).
  A generic "block the current thread on a queue at J" lemma would also give receive_ipc's `wait_for_sender`.
- DONE 8e553d8 (XTopJointRecvIpc, item 6 part): `JAtZ.recvIpcPollJ` (polling receive, no bound notification,
  endpoint idle/receiving, reply cap null or naming an unlinked reply = EpRecv's `ReplyArg`: badge := 0;
  `receive_ipc_poll_eq` via EpRecv's `receive_ipc_pre`, spec via `receiveIpc_noSend`), `jRecvIpcHyp_of`,
  `dispatch_recvJR` (the receiving syscalls at J against `fl4HandleSyscall rep (recvSysOf bl cr)` with premises
  `JRecvIpcRestHyp` [W] = `JRecvIpcHyp` outside `RecvIpcPollCase`, and `JRecvSigBlockHyp` [W] when blocking).
- NEXT for item 6, cheapest first: (a) bound notification active → `complete_signal` (as `recvSigActiveJ`: badge,
  ntfn idle via `signal_badge_post`, the donation a no-op for the current thread on `curSc`; the spec's sporadic
  check needs `scp ≠ curSc`, false); (b) the blocking wait (`wait_for_sender`: shares the block lemma of item 5,
  plus the reply's TCB word); (c) `take_reply`'s `cancel_ipc` of a reply's other thread; (d) a waiting sender
  (`do_ipc_transfer` at J exists; sender wake / reply push / donation ≈ `SendRecvCPD`); (e) bound ntfn +
  blocking → `maybe_return_sched_context` (as item 5's).
- NOT STARTED: items 7, 8 (preemption path, charge_budget at J), M5/M6/M7, `kernel_entryJ`.

## ke3 (branch par/kentry3 in FL4-rb, base 1fae4d6)
- DONE (XTopJointRecvSigBlock, IpcRecvTopH; std axioms): item 5's blocking receive.
  * `receive_signal_blockF` (FL4 on `IRel`, footprint `RBW` = `NWrite` + the action word; `RBW.cnW`,
    `JAtZ.rbw_dbg`), `Sched.maybe_return_noop` / `Ipc.maybeReturnSc_noop` (no-op when the notification's SC is
    not the thread's), spec frame `BFrN` + keeps, `recvSigBlock_eq` (outcome, `IK`), `JAtZ.recvSigBlockJ`
    (JAtZ → JAtZ, the notification leaves the dead set, covered by the held cap).
  * The held cap: IpcRecvTopH = copy of IpcRecvTop's `handle_recv_refines` with an extra property `Hd` of the
    looked-up cap passed to the leaves (IpcRecvTop has ~290 dependents); at J `Hd = JHeld Z.th s` (cap in a
    slot; `lookup_cap_held`). `JRecvIpcHyp`/`JRecvSigHyp`/`JRecvIpcRestHyp` take `th` and the `JHeld` premise.
  * `JRecvSigBlockHyp` [W] removed; narrowed to `JRecvSigRetHyp` [W]: the blocking receive on an idle/waiting
    notification whose SC is the current SC (l4v `maybe_return_sc` unbinds it: a passive server waiting again on
    the notification that lent it its SC; reachable, so a genuine gap). `jRecvSigHyp_of`, `dispatch_recvJS` moved
    to XTopJointRecvSigBlock; XTopJointRecvIpc imports it.
- NEXT for `JRecvSigRetHyp`: the post-block state is a J state (the `recvSigBlockJ` assembly at σ3); then
  `maybe_return_sched_context` (t.sc := 0, sc.tcb := 0, reschedule since t is current) needs the SC-step
  framework XTopJointFinThreadSc's `JAtZ.unbindTcbJ` uses (`nkt_*`, `pres_*`, `skm_*`, `lkm_*`, `unbindTcb_mid`,
  `xtop_sc_step`) for `maybeReturnSc`; FL4: ScReturnRef `maybe_return_refines` (SchedRel), P1
  `maybe_return_sched_context.inv`/`.kw`. Not started.
- Builds: module builds ke3-b7 (`lake build Fl4Proofs.P3.XTopJointRecvIpc`, the whole changed cone: IpcRecvTopH,
  XTopJointDispatch, XTopJointRecvSig, XTopJointRecvSigBlock, XTopJointRecvIpc) OK; ke3-ax1 `#print axioms`
  (scratch/axke3.lean, untracked) std only, incl. `handle_invocation_refinesJ`.
- HANDOFF (ke3 stopped for context; nothing uncommitted). Next, in the brief's order:
  (a-rest) `JRecvSigRetHyp`, see above. The same no-op/return split applies to receive_ipc's
  bound-notification `maybe_return_sched_context` (item 6 (e)).
  (b) receive_ipc, cheapest first. All leaves now get `JHeld Z.th s (.Endpoint …)`, so the endpoint's cover is
  `J.cover_cap (P1.WritesIn.refl s _) hy (by rw [capAt_capV, hcv]) … (range_ep …)` as in `jRecvSigHyp_of`.
  (b1) bound ntfn active → `complete_signal` (FL4 `notification.complete_signal`; at J: copy
  `JAtZ.recvSigActiveJ`; the spec's sporadic check `scp ≠ curSc` is false for the current thread; first
  `take_reply` must be the no-op case `RecvIpcPollCase`-like: reply null or unbound, else (b3)).
  (b2) `wait_for_sender` blocking: like `recvSigBlockJ` but state BLOCKED_ON_RECV + reply word + `reply.set_tcb`
  (spec `blockedOnReceive e (some r) d` and `replyTcb := t`): a new spec frame with the reply change (CallRel,
  RFree, `rrecv` (null PREV/NEXT of the bound reply: from `RFree`/`ReplyArg` unlinked reply), `rp` change);
  FL4 footprint EWrite-based as `send_ipc_blockF` plus the reply's TCB word. ~700 lines.
  (b3) `take_reply`'s `cancel_ipc` of another thread: XTopJointCancel's cancel at J exists.
  (b4) waiting sender: do_ipc_transfer at J exists (XTopJointXfer*), sender wake / reply push / donation as
  SendRecvCPD.
  (c) item 7, (d) item 8, (e) M5/M6/M7: not started (plan items above).

## ke4 (branch par/kentry3 in FL4-rb, rebased onto c8baff2)
- DONE 573c003 (XTopJointRecvSigRet, first half): `JAtZ.maybeReturnJ` = FL4's `maybe_return_sched_context` at J
  for a thread that is not runnable, neither idle nor the switch target, whose SC is the notification's
  (`maybeReturn_shape`/`maybeReturn_mid` as `unbindTcb_shape`/`_mid`; `nkt_/lkm_/skm_/pres_maybeReturnSc`;
  `maybe_return_sfoot`; `maybe_return_refines` for SchedRel, `Inv.ret`, `ActIdle.ret`, P1 `.inv`/`.kw`).
- DONE 9a40106: `JRecvSigRetHyp` [W] removed. The blocking receive is split before `maybe_return`:
  `rsPre` + `receive_signal_split`, `receive_signal_preF`, P1 `ntfn_blockPre`, `recvSigBlockPre_eq`,
  `JAtZ.recvSigBlockPreJ` (copies of `receive_signal_blockF`/`ntfn_block`/`recvSigBlock_eq`/`recvSigBlockJ`
  without the last step: FOLD LATER, the old ones can be derived from the new ones + the no-op);
  `JAtZ.recvSigRetJ`; `jRecvSigHyp_of` and `dispatch_recvJS` moved to XTopJointRecvSigRet, no premise.
  `dispatch_recvJR` lost `hB`.
- item 6 (a) (XTopJointRecvIpcAct): receive_ipc with an active bound notification and a reply cap null or
  naming an unlinked reply: `JAtZ.recvIpcActJ` (`receiveIpc_active`, `completeSignal_cur`,
  `receive_ipc_preA`, `complete_signal_cur_eq`; P1 `BlkOK` from `receive_signal.ipc`, same final state
  `recvActS`). `RecvIpcActCase`; `JRecvIpcRestHyp` [W] now also excludes it; `jRecvIpcHyp_of` takes
  `hAT hcur hni hnq`; `JAtZ.replyArg_of` factored.
- NEXT (item 6, cheapest first): (b) blocking `wait_for_sender` (no bound ntfn or bound idle ntfn and
  `blocking`): a `recvSigBlockPreJ` analogue with BLOCKED_ON_RECV, the reply word and `reply.set_tcb`
  (spec `blockedOnReceive e r`, `replyTcb := t`; new frame with the reply change, `rrecv` for the
  bound reply from `ReplyArg`'s unlinked reply); a bound non-active ntfn when blocking adds
  `maybe_return_sched_context` BEFORE the endpoint part (FL4 and spec: `maybeReturnJ` first, then the
  wait); (c) `take_reply`'s `cancel_ipc` (XTopJointCancel at J); (d) a waiting sender (do_ipc_transfer at
  J, SendRecvCPD). Then items 7, 8, M5-M7.
- Builds: ke4-b5 (`lake build Fl4Proofs.P3.XTopJointRecvIpc`, cone RecvSigBlock/RecvSigRet/RecvIpc) and ke4-b7
  (+ RecvIpcAct) OK; ke4-ax2 `#print axioms` (scratch/axke4.lean, untracked) std only, incl.
  `handle_invocation_refinesJ`, `recvSigRetJ`, `recvIpcActJ`, `jRecvIpcHyp_of`, `dispatch_recvJR`.
- HANDOFF (ke4 stopped for context; nothing uncommitted). Next: item 6 (b) as above. Recipe that worked
  here: write the FL4 prefix as a `def` (cf. `rsPre`) and split the function with `Std.bind_assoc`
  (`receive_signal_split`), so P3/P1/spec prefix lemmas combine by `WP.spec_and` on the prefix and the
  J state after the prefix is a full `JAtZ` (then `maybeReturnJ` or the next J step). For
  `wait_for_sender` the prefix is receive_ipc's `take_reply` + bound-ntfn read + (blocking ∧ bound)
  `maybe_return`; `step` picks P0 lemmas in new modules: use `step with Endp.obj.Tcb.bound_ntfn.spec`,
  `Endp.obj.Reply.tcb.spec`, `P1.obj.Tcb.is_null.spec` explicitly.

## ke5 (branch par/kentry3 in FL4-rb, rebased onto 67e4e8e4)
- DONE f4e7739 (XTopJointRecvIpcBlock, std axioms): item 6 (b), the cheapest part: the blocking
  `wait_for_sender` with a NULL reply cap and no bound notification, on an idle/receiving endpoint.
  * P1 `endpoint.wait_for_sender.foot0` (`Foot`, copy of `send_block.foot`; reply word := 0).
  * `Ipc.wait_for_sender_blockF0` (IRel + `CnW` footprint; copy of `send_ipc_blockF` with EpRecv's
    `block_recv_writes`/restate), `receive_ipc_block0_red` (EpRecv's `receive_ipc_pre` + the state split).
  * Spec: `BFrR` (copy of XTopJointSendBlock's `BFr` with `blockedOnReceive ep none d`; its `khrb` is
    false now: `t` becomes receive-blocked), `recvIpcBlock0_eq`, `RRecv.frameR` (no reply names `t`
    before: `SchedValid.replyTcb`, `t` runnable).
  * `JAtZ.recvIpcBlock0J` (assembly as `recvSigBlockJ`/`sendBlockJ`; P1 `BlkOK` by
    `wait_for_sender.inv`, `kw_dbg` from `foot0`); `RecvIpcBlock0Case`; `JRecvIpcRestHyp` [W] also
    excludes it; `jRecvIpcHyp_of` proves the case (endpoint cover from `JHeld` via `J.cover_cap`,
    `range_ep`).
- NEXT, cheapest first:
  (b2') blocking wait with an UNLINKED reply cap (`ReplyArg`, `rTcbA q = 0`), no bound ntfn. What it needs
  (checked): FL4 side = `wait_for_sender_blockF0` + reply word `q` + `reply.set_tcb q t` (EpRecv
  `receive_ipc_block`'s `reply_link_rel` for EpStateRel; NtfnStateRel across one reply word; `CnW` has
  `rTcbA r` (`b.val = r.val`)). P1 foot: `BlkFoot`'s third disjunct (`r0 ≠ 0`, `rTcbA r0`) -- `blkfoot_foot`
  only takes `r0 = 0`; need its `rTcbA` case in `KW`. Spec: a `BFrR` variant with the reply's
  `replyTcb none → some t` (CallRel/RFree/RPlaced frames fine: `replySc` kept; `RRecv` for `q`: `q` was
  `Free` (EpStateRel.reply: `replyTcb = optRef (rTcbA q)`), so `J.rfree` gives null links, kept by `k4`).
  BLOCKER: `DeadP` (DeadKeep `hRp`) keeps dead replies' `replyTcb`, so `q` must leave `D`
  (`JCovD.undead`), which needs the reply cap HELD: `JRecvIpcHyp` only passes `JHeld` of the endpoint
  cap. Fix: IpcRecvTopH's `handle_recv_refines` passes `Hd` of the reply cap too (`lookup_cap_held`, as
  for the endpoint), `JRecvIpcHyp`/`JRecvIpcRestHyp` take it, then `J.cover_cap` with a `range_reply`.
  IK of `setReplyObjRef replyTcbUpdate` (no `ikm_` lemma yet; cf. ScRestartSpec `ikm_replyUnlinkTcb`).
  (b-ntfn) bound idle/waiting ntfn + blocking: `maybe_return_sched_context` first (no-op when the ntfn's
  SC is not the thread's: `maybe_return_noop`/`maybeReturnSc_noop`; else `JAtZ.maybeReturnJ`), then the
  wait; the spec's `receiveIpc` reads the ntfn (`receiveIpc_noSend` needs bound = none: a variant
  for a bound non-active ntfn). Use ke4's split recipe (prefix `def` + `Std.bind_assoc`).
  (c) `take_reply`'s `cancel_ipc`; (d) waiting sender; then items 7, 8, M5-M7: not started.
- Builds: ke5-b2 (`Fl4Proofs.P3.XTopJointRecvIpcBlock`), ke5-b3 (`Fl4Proofs.P3.XTopJointRecvIpc` +
  scratch/axke5.lean, untracked): OK, std axioms only, incl. `handle_invocation_refinesJ`,
  `JAtZ.recvIpcBlock0J`, `jRecvIpcHyp_of`, `dispatch_recvJR`. Build script: scratch/ke5build.sh
  (untracked; `AX=<file> sh proofs/scratch/ke5build.sh Mod...` from the mirror root).

## ke6 (branch par/kentry3 in FL4-rb, on 67e4e8e4 + ke5)
- DONE 00ac613 (IpcRecvTopH/XTopJointDispatch): `RecvLeavesH.ipc`, `JRecvIpcHyp`, `JRecvIpcRestHyp` take the
  reply cap's held fact `∀ q g', rc = .Reply q g' → JHeld th s rc` (`handle_recv_refinesH` passes `hob1`).
- DONE 6ac0d70 + 018db90 (XTopJointRecvIpcBlock, generalised in place): the blocking wait with a reply cap
  null OR naming an unlinked reply (`ReplyArg`): `JAtZ.recvIpcBlockJ` (was `recvIpcBlock0J`).
  * P1 `blkfoot_footR` (BlkFoot's reply word via `kw_sg`, `ObjsOK.tcbW`), `endpoint.wait_for_sender.footR`
    (foot0 removed).
  * FL4 `wait_for_sender_blockF` (was `..F0`): `tail` after `schedule_tcb`, `reply_link_rel` +
    `ntfn_reply_write` when `rv ≠ 0`, the reply's TCB word in `CnW` (`rTcbA_val`); `receive_ipc_block_red`.
  * Spec: `BChgR`/`BFrR t e r` (third change: the reply `r`'s `replyTcb := some t`; field `rq`),
    `replyF/replyB` now existential (`replyF'`, `replyB'`, `replyB_free` for the kept cases), `BFrR.ik`
    (IK from the frame; no `ikm_` lemma needed), `recvIpcBlock_eq` (any `SpecReplyArg`; the reply step via
    `Endp.setReplyTcb_eq`), `RRecv.frameR` takes the reply's null links (`hrq`).
  * J: `D' := if rv = 0 then D \ {e} else D \ {e} \ {rv}` (the reply leaves the dead set: `JCovD.undead`
    with the reply cap's cover, `hcovR`); `RRecv` for the reply from `RFree` (it was free) + `k4`.
  * The wait now takes the reductions as arguments: `hred` (FL4's `receive_ipc` to the wait) and `hsp`
    (spec `receiveIpc = receiveIpcBlocked true t e (optRef rv)`); no `hbn`.
- DONE b278e79 (XTopJointRecvIpcBound, new leaf): a bound idle/waiting notification whose SC is not the thread's
  (maybe_return no-op): `receiveIpc_boundNA`, `receive_ipc_blockN_red`, `JAtZ.recvIpcBlockNJ`.
- `JRecvIpcRestHyp` [W] now excludes `RecvIpcPollCase`, `RecvIpcActCase`, `RecvIpcBlockCase` (blocking, no
  bound ntfn, no sender, reply null/unlinked), `RecvIpcBoundCase` (blocking, bound ntfn not active and not
  lending the thread's SC, no sender, reply null/unlinked). `jRecvIpcHyp_of` proves all four
  (`JAtZ.recvCov_of`: both caps' covers).
- LEFT in `JRecvIpcRestHyp`, cheapest first:
  (p-ntfn) polling with a bound non-active ntfn: `receiveIpc_boundNA` (blk = false) + a `receive_ipc_preN`
  variant for `blk = false` (no maybe_return) + `recvIpcPollJ` with `hred`/`hsp` arguments (refactor as
  done for `recvIpcBlockJ`). Small.
  (b-ret) blocking with a bound ntfn lending the thread's SC (`xn.ntfnSc = xt.tcbSchedContext ≠ none`,
  reachable: a passive server): `maybe_return_sched_context` on the RUNNING current thread, then the wait.
  The state between is not a `JAtZ` (current thread without SC), so the J assembly must be one step:
  combine `maybeReturn_mid`/`unbindTcb`-style SC frame (XTopJointRecvSigRet `JAtZ.maybeReturnJ`'s lemmas,
  `nkt_/lkm_/skm_/pres_maybeReturnSc`) with `BFrR`; FL4 and spec both run maybe_return before the wait
  (spec reads `ep` first; maybe_return keeps endpoints). Large.
  (c) `take_reply`'s `cancel_ipc` (reply linked to another thread): XTopJointCancel at J, then the rest.
  (d) a waiting sender: do_ipc_transfer at J (XTopJointXfer*), sender wake/reply push/donation (SendRecvCPD).
  Then items 7, 8, M5-M7: not started.
- Builds: ke6-b1 (IpcRecvTopH cone), ke6-b3 (groundwork), ke6-b5 (recvIpcBlockJ), ke6-b9 (+ Bound) all
  `lake build Fl4Proofs.P3.XTopJointRecvIpc` (whole changed cone) OK; ke6-ax1/b9 `#print axioms`
  (scratch/axke6.lean, untracked): std only for `handle_invocation_refinesJ`, `JAtZ.recvIpcBlockJ`,
  `JAtZ.recvIpcBlockNJ`, `Ipc.wait_for_sender_blockF`, `jRecvIpcHyp_of`, `dispatch_recvJR`, `handle_recvJ`.
- HANDOFF (ke6 stopped for context; nothing uncommitted). Next: (p-ntfn), then (b-ret), (c), (d) above.
  Gotchas: in `do` blocks with `let (s2, a2) ← (do let t ← m; ok (t, a))` state the intermediate `have`
  in exactly that tuple form and close with `simpa only [bind_tc_ok, bind_ok, Bind.bind] using key`;
  `rintro x rfl` on `x = s` with `s` a theorem variable eliminates `s` (use `rw`); `by cases e` inside
  `⟨…, …⟩` needs parentheses; `P1.rTcbA` vs `Endp.rTcbA` after `step` (`rw [show P1.rTcbA r = Endp.rTcbA r
  from rfl]`); `optRef_ne` is ambiguous between Sched/Notif (qualify).

## ke7 (branch par/kentry3 in FL4-rb, on 42e06d26)
- DONE 8a10d79 (std axioms, ke7-b3 `lake build Fl4Proofs.P3.XTopJointRecvIpc` 5336 jobs OK; scratch/axke7.lean):
  * (p-ntfn) polling with a bound non-active notification: `JAtZ.recvIpcPollJR` (poll from the reductions
    `hpoll`/`hsp`), `receive_ipc_poll_cont`, `receive_ipc_pollN_pre`, `JAtZ.recvIpcPollNJ`; `RecvIpcPollCase`
    widened (bound none OR bound to a non-active ntfn).
  * (b-ret) blocking with a bound non-active ntfn lending the thread its SC (new XTopJointRecvIpcRet,
    `JAtZ.recvIpcRetJ`). ke6's "the state between is not a JAtZ" was wrong: after maybe_return on the RUNNING
    current thread the state IS a JAtZ (Inv only needs the thread in no queue; the scheduler action becomes
    chooseNewThread). What was needed: `Inv.retQ`, `maybeReturn_shape`/`_mid` take `NotQueued` (shape also
    gives "t in no ready queue after"), `JAtZ.maybeReturnJQ` (spec `NotQueued` + FL4 CanBlock words `hout`;
    post adds the `TFoot` WritesIn), `JAtZ.canBlockCurG` and `JAtZ.recvIpcBlockJG`/`recvIpcBlockNJG`
    (Entered replaced by: cur ≠ idle, not in release queue, runnable, action = resume ∨ (chooseNew ∧ no SC);
    JG is stated for any FL4 program `m` reducing to the wait), `recvIpcBlock_eq` keeps chooseNew. At the
    post-maybe_return state both receives reduce to the wait as a NON-lending bound ntfn (the ntfn's SC is no
    longer the thread's): spec `receiveIpc σ = receiveIpcBlocked σ2 = receiveIpc σ2` (`receiveIpc_boundR`,
    `receiveIpc_boundNA`), FL4 `receive_ipc_blockR_red` + `recvTail_wait`; covers at s' by `recvCov_ofW`.
    `RecvIpcBoundCase` lost its ¬lending conjunct.
  * `JRecvIpcRestHyp` [W] now = a waiting sender, or a reply cap whose reply is linked to a thread.
- NEXT (c) take_reply's cancel_ipc (reply linked to i ≠ ct; i is blockedOnReply or blockedOnReceive _ (some r),
  `J.sv.replyTcb`). Plan: FL4 `receive_ipc s = cancel_ipc s a i >>= receive_ipc` (take_reply at the post state is
  a no-op: rTcbA q = 0), spec `receiveIpc σ = receiveIpc σ'` (when-clause false at σ'); J step by
  `jCancel_reply`/`jCancel_recv` (JCancelAt), then the proved cases at σ'. BLOCKERS found: JCancelAt exposes no
  spec facts of σ' (curThread, Entered, cur's tcb/bound ntfn, ep e's "no sender", cur not queued); and
  `cancelIpc_recv_cfr` only says action = old ∨ chooseNewThread (reply_remove_tcb may reschedule), so
  recvIpcBlockJG's hsa would need a chooseNew-WITH-SC branch (hscA: the cur SC active without CurInv -- needs a
  carried fact). Expect ~400 lines; consider instead proving i ≠ cur ⇒ action unchanged for both cancel kinds.
- (d) waiting sender (receive_from_sender: do_ipc_transfer at J, unblock_sporadic, reply_push(sender → cur) with
  donation of the SENDER's SC, or sender inactive): the roles are the mirror of SendRecvCPD; ~1500. Items 7, 8,
  M5-M7: not started.
- Gotcha: after `if` reductions a leftover `let (s2, a2) := (s, a)` blocks `simpa ... using h`; `exact h` works.

## ke8 (branch par/kentry3 in FL4-rb, on cd423afe)
- DONE 8ca7a775 (new leaf XTopJointRecvIpcLink, imported from Fl4Proofs.lean; ke8-b1 `lake build
  Fl4Proofs.P3.XTopJointRecvIpcLink` 5338 jobs OK; scratch/axke8.lean (untracked): std axioms only for
  `handle_invocation_refinesJ`, `dispatch_recvJL`, `jRecvIpcHypL_of`, `jRecvIpcLink_of`, `JAtZ.cancelLinkJ`,
  `receiveIpc_linked`, `receive_ipc_linked`). Item 6 (c), the linked reply, by ke7's cheaper route:
  * Spec: `Vs.caF t` (cur thread, idle thread, and the action when `t` is not current) kept by `cancelIpc t`
    (generic VsDom `FK` + `caf_*` leaves; `setThreadStateAct t` reschedules only when `t` is current);
    `cancelOther_keep` (with ScRestartSpec `ikm_cancelIpc` for ready queues, TcbReadRegsSpec `pxk_cancelIpc`
    for other TCBs); `PostI`/`postI_replyRemoveTcb` (reply_remove_tcb leaves its thread inactive);
    `cancelOther_reply` (after the cancel the reply is free: SchedValid before/after + IpcStK `st_cancelIpc`);
    `receiveIpc_linked` (spec receive at σ = receive at the post-cancel state).
  * FL4: `take_reply_free`, `take_reply_linked`, `receive_ipc_linked` (cancel_ipc, then receive_ipc after).
  * J: `JAtZ.cancel_slots` (P1 `ipc.cancel_ipc.kw` + `JPlaced.kwOutBlk` + `slotsSame_of_foot`: the caps stay
    held, `jHeld_of_same`), `JAtZ.cancelLinkJ` (cancelReplyJ / cancelRecvJ + slots + the thread inactive;
    no edit of XTopJointCancelReply, whose cone is huge), `jRecvIpcU_of` (copy of jRecvIpcHyp_of for a null or
    free reply), `jRecvIpcLink_of`, `jRecvIpcHypL_of`, `dispatch_recvJL`.
  * `JRecvIpcRestHyp` is superseded by `JRecvSendHyp` [W] (waiting sender only; reply null or free; at every
    JAtZ state of `th`, like JCancelAt, because the linked case reaches it at the post-cancel state). The old
    `JRecvIpcRestHyp`/`jRecvIpcHyp_of`/`dispatch_recvJR` in XTopJointRecvIpc are unused now; delete them
    when (d) lands (nothing downstream imports them).
- NEXT (d) the waiting sender = prove `JRecvSendHyp`. Cases (FL4 endpoint.rs:162 receive_from_sender, spec
  Ipc.lean:314 sendEP branch): (d1) non-call sender without fault: dequeue the head sender, do_ipc_transfer
  sender -> cur (XTopJointXferG `JAtZ.xferStepGJ` is generic in snd/rcv, needs `xs.tcbFault = none`),
  `unblock_sporadic(sender)` BEFORE `Running` (spec `specSporadicAssert`, EpTail.lean:40 =
  ifSporadicCurScAssertRefillUnblockCheck; at J: XTopJointSendRecv `JAtZ.sendUnblockJ`), sender Running +
  `possible_switch_to` (`JAtZ.sendSwitchJ`). Template: XTopJointSendRecv `JAtZ.sendRecvJ0` with the roles
  swapped (sender woken as a cancelled SEND: the KFr/`cancelIpc_send_kfr` frame of XTopJointCancel instead
  of CFr); IRel-level reference: EpRecvSend `receive_ipc_send`. (d2) call/fault without grant or reply:
  sender Inactive. (d3) call with grant + reply: `reply_push sender cur reply donate` (mirror of
  XTopJointSendPushD/PushDon: donation of the SENDER's SC to the cur thread, which then must have none, i.e.
  after maybe_return or a passive server). (d4) fault senders: XTopJointFaultRecv has the fault transfer.
  Prefix: bound non-active ntfn + blocking -> maybe_return first (ke7 `JAtZ.maybeReturnJQ` route), polling
  -> none. Expect ~1500 lines over several files; do (d1) without bound ntfn first, then narrow
  `JRecvSendHyp` case by case (state the proved cases as `RecvSendBasicCase` etc. like RecvIpcPollCase).
- Items 7, 8, M5-M7: not started.

## ke9 (branch par/kentry3 in FL4-rb, on 5a758a10)
- FINDING (why (d) is not a copy of `sendRecvJ0`): no existing spec frame covers a receive from a waiting
  sender. `CFr`/`DWFr` (IpcSignalBoundFr/IpcSignalDonFr) let only the WOKEN thread's registers change and
  need it receive-blocked or inactive (`TCX`/`RbIn`); `KFr` (IpcCancelFr) has no `Running`, no register or SC
  change. Here the woken thread is the send-blocked sender `t`, the registers that change are the CURRENT
  thread `r`'s (the receiver), and the sender's sporadic check (FL4 `unblock_sporadic` BEFORE `Running`, so
  at the hole between the dequeue and the wake, where no `JAtZ` holds: `sendUnblockJ` is not usable) changes
  the sender's SC refills. Reordering FL4 steps is impossible (abstract `LawfulStore`, no state equality).
- DONE (commit "receive from a waiting sender, groundwork"; spec + J groundwork; ke9-b2 module build, ke9-ax2 std axioms only for `handle_invocation_refinesJ`, `dispatch_recvJL`, `JAtZ.rsfrStep`, `JAtZ.deadP_rsfr`, `Inv.scRef`; names RS* because XTopJointFinScReply already has `Sched.RFr`):
  * IpcRecvSendFr (new leaf, spec side): `RSTc` (registers only of `r`, state only of `t`: `KbIn` to
    `Inactive`/`Running`), `RSChg` (TCB by `RSTc`; an SC other than the current one, refills only; an endpoint
    holding `t` to a sub-queue), `RSFr t r` (+ `trans`/`upd`/`sts`/`um`/`reprog`/`stsRun`/`arch`, the per-kind
    lemmas, `curF`/`curB` (current SC kept), and `szKeep`/`ykeep`/`mcpKeep`/`bufKeep`/`prio`/`nsc`/`isorted`/
    `own`/`off`/`idleOK`/`bsa`/`curInv`/`curRunW`/`sched`/`kback`/`ksz`/`ksub`/`callKeep`/`khrb`).
    `Inv.scRef`: `Inv` across one SC's refill change given `unblock_result`'s explicit outcome (copy of
    ScInvU `Inv.unblock`'s body): the way to get `Inv` at the end (below).
  * XTopJointRecvSendStep (new leaf, J side): `JAtZ.deadP_rsfr`, `JAtZ.rsfrStep` (= `kfrStep` for `RSFr`).
- NEXT (d1) `JAtZ.recvSendJ0`: non-call sender without fault, receiver without bound ntfn (then add the
  bound non-active prefixes as ke7 did). Recipe, mirroring `sendRecvJ0` with roles swapped (FL4 order:
  `receive_ipc` -> take_reply no-op -> `receive_from_sender`: head, `ep_dequeue`, badge/flags reads
  (EpRecvSend `receive_ipc_send_gen` has the FL4 stepping and `flags_grant`/`flags_call`), `xferStepGJ`
  (snd = sender, rcv = cur; base `y`/`σy`/`Jy`), `unblock_sporadic sender` AT THE HOLE, fault read,
  `set_thread_state sender RUNNING`, `possible_switch_to sender`):
  1. dequeue: `ep_dequeue_c` (as in sendRecvJ0, `.sendEP`), P1 `ep_dequeue.inv`/`.foot` with the sender's
     state `TS_BLOCKED_ON_SEND`.
  2. transfer: `J.xferStepGJ hZ hk o hR1 hS1 hW1 F1 hsT htT hne hks hkt hfs badge grant ...` then
     `J.bufRebaseX`-style rebase is NOT needed for the frame (the receiver's buffer writes are `RcvBufW`):
     use `JAtZ.bufRebaseX` on `Jy` for `r = cur` exactly as sendRecvJ0 does for its receiver.
  3. unblock at the hole: IRel level `Ipc.unblock_irel` (IpcEpTail; IRel from `IpcRel.ofSRN`), its spec
     outcome `specUnblock` = `specSporadicAssert` (`specSporadicAssert_eq`); P1 `sporadic.unblock_check.all`
     /`.kw` (X-generic, take the hole's `SchedQueuesInvX X`); the FL4 words: `unblock_check_kfoot` (as in
     `JAtZ.unblockRJ`). Spec outcome form: `unblock_result` (σ3 = σ2 or `updSc {σ2 with reprogramTimer :=
     true} p z n`, `p ≠ curSc` from the if-guard), so the frame step is `RSFr.reprog` + `RSFr.upd` (SC case).
  4. `set_thread_state_c`/`sts_all`/`set_thread_state.kw` as in sendRecvJ0 (sender `KbIn` via
     blockedOnSend, `RSFr.stsRun`); the receiver's TCB change by `RSFr.arch` (+ `RSFr.um` for `setUm`).
  5. `Inv` at the end: σ5' := the same state without the SC update; `Inv σ5'` by
     `(Jy.inv.toBut sd).ik hnq IK` (IK as sendRecvJ0: `IK.updOther` for the endpoint and the receiver's
     TCB (same state/SC), `IK.um`, `IK.updSelf` + `IK.sts` for the sender) and the sender's `RelIfBound`
     (`Inv.rd` at σy: blockedOnSend with no fault is `inClassR`; carried by `SKeep`); then σ5 =
     `updSc {σ5' with reprogramTimer := true} p z n` (updK at different keys commute; `stsAct_ne`) and
     `Inv.scRef` (no release-queue member bound to p: only the sender is, by `Inv.back`/`scTcb`, and it is
     blocked).
  6. `JAtZ.rsfrStep` (action unchanged: `stsAct_ne`, sender ≠ cur), then `JAtZ.sendSwitchJ` for
     `possible_switch_to` (sender runnable, not in the release queue, SC active by `BlockedScActive.tcb` at
     σy since it was ipc-queued, not idle, not current).
  7. spec outcome: EpRecvSend `receiveIpc_send_eq` (no bound ntfn) with `possibleSwitchTo` after.
  Then narrow `JRecvSendHyp` by `RecvSendBasicCase` (sendEP, head sender non-call, no fault, no bound
  ntfn) and wire it into `jRecvIpcU_of`. (d2) call/fault without grant: sender `Inactive` (RSTc allows it).
  (d3) reply_push with donation: RSFr needs a donation case (DWFr's `DChg` SC/TCB cases) -- extend RSFr.

## ke10 (branch par/kentry3 in FL4-rb, on edfb68a1)
- Scope change (lead): items 7-10 (charge_budget, Yield, budget_ok, preemption/hPre) moved to kp1 (FL4-tcbj);
  this line: the waiting sender until `JRecvSendHyp` is gone, then M5-M7. Don't edit ScCharge*/budget files.
- DONE c192d6f6 (d1) + the next commit (d2 + bound prefix), new leaf XTopJointRecvSend (imported from
  Fl4Proofs.lean; XTopJointRecvIpcLink imports it):
  * `unblockHole`: FL4 `unblock_sporadic` at the dequeued sender's hole (only `IRel` there, no `JAtZ`):
    IRel after (`sc_step_lift`), `KFoot`, P1 posts for any hole set `X` + P1 `Foot`, the TCB words kept, and
    the spec's outcome `UnblockOut` (unchanged, or `updSc {σ with reprogramTimer} p z n`, `p ≠ curSc`, the
    `unblock_result` facts that `Inv.scRef` takes). Takes `hne` (active SC refills nonempty), which the
    caller gets from `Jy.inv.ne` through `SKeep σy σ2`.
  * `JAtZ.recvSendJ0`: ke9's 7 steps as planned, with: `σy`-based frames as sendRecvJ0 (Fr2/IK2/SK2),
    `Inv` at the end by `InvBut.ik` at `σ5' := updK σ2 sd x5` (no SC refill) + `Inv.scRef` and
    `updSc_updK_comm` (ScBind) for `σ5 = updSc {σ5' with reprogramTimer} p z n`; `hnr'` of scRef from
    `I5'.back` (only the sender is bound to p) + `hnqD`. Branches on `dd.senderIsCall`: false -> Running +
    `sendSwitchJ` (spec `receiveIpc_send_eqB`); true (no grant/grant-reply, or reply cap null) -> Inactive,
    no switch (spec `receiveIpc_sendCall_eq`; P1's sts_all `hq` from `J.curBits` at σ and
    `actionW_ne_of` + `Jy.act.1`/`schedulable_inv`). `RSFr.stsInact`, `RSFr.ofUm`, `flags_grantReply`.
  * Bound-notification prefix (receiver with a bound non-active ntfn, polling or not lending its SC):
    `receive_ipc_preN` (FL4; `maybe_return_noop`), spec lemmas take `hbN` (the `maybeReturnSc_noop` tail as
    in XTopJointRecvIpcBound). Lending + blocking (maybe_return really returns the SC) is NOT covered.
  * `RecvSendBasicCase ct blocking σ p rc` (XTopJointRecvIpcLink): receiver bound none or non-active
    (blocking -> not lending), head sender unfaulted, not calling or calling with neither grant right or
    rc = Null. `JRecvSendHyp` [W] gains `¬ RecvSendBasicCase …`; `jRecvIpcU_of`/`jRecvIpcLink_of`/
    `jRecvIpcHypL_of` take `hZ : XferHZ L AR Z` (dispatch_recvJL has it).
- LEFT in `JRecvSendHyp` (the waiting sender): (d3) calling sender with grant/grant-reply and a reply cap:
  `reply_push sender cur reply can_donate` (sender BlockedOnReply, reply linked; donation of the sender's
  SC when the receiver has none). RSFr cannot hold it (RSTc only Inactive/Running; replies kept): plan as
  XTopJointSendPushD: after the transfer + unblockHole, do the link/block on IRel (`reply_push_iC`'s
  block part with the roles of SendPushD swapped: there the CURRENT thread blocks; here the sender, which
  is already off-queue), reach `JAtZ` at the block's state by a `wake_postGR`-like step (needs a frame
  with the sender to BlockedOnReply + reply's replyTcb := sender; check XTopJointSendPushD's `pushSt`),
  then XTopJointPushDon's `JAtZ.pushDonJ` for the donation (receiver = current thread has no SC: then it
  must be a passive server, `CurInv`/`CurOwnW` need care since the current thread GETS an SC), receiver
  stays current. (d4) faulted senders (fault transfer: XTopJointFaultRecv's `xferFaultStepJ`/fault
  variants instead of `xferStepGJ`; the Inactive/push split as for calls, FL4 reads ftype). (d5) blocking
  receive with a bound ntfn lending its SC (ke7's `maybeReturnJQ` route before the sendEP branch).
  When all are in: delete `JRecvSendHyp`, `JRecvIpcRestHyp`, `jRecvIpcHyp_of`, `dispatch_recvJR`.
- Tooling: scratch/ke10chk.sh (elaborate a file, errors + goals only via ke10f.py), scratch/axke10.lean.
  station_task keys are single-use: a new key per run (same key returns the old result).
## kp1 (branch par/budget in FL4-tcbj, on 8a3919e9; scheduling-budget items 8, 9, 10, 7)
- DONE f55d72b0 (item 8, std axioms): `charge_budget used false` at J.
  * ScChargeG (new leaf, SchedRel level): ScCharge6's `charge_budget_refines` asks `hto` (the timeout-fault send)
    for every `can`; copies without it: `end_timeslice_refinesG` (`hto : can = true → …`),
    `charge_tail_refinesF` / `charge_budget_refinesF` (`can = false`, no `hto`), and FL4's writes in the posts:
    `charge_head_refinesK` (`KFoot`: ring, `budget_check`, the SC's CONSUMED word), `end_timeslice_sfootF`
    (`SFoot`: `append` or `postpone`; `r.2 = a`), the tail's `SFoot` (node words, `reschedule_required`);
    `charge_budget_refinesF` also exposes the mid state (`∃ σ2, HeadKeeps σ σ2 csc ∧ chargeTail false σ2 = …`).
    `rel0_of`: a thread off the spec's release queue has a clear release bit.
  * ScChargeJ (new leaf): P1 `sched.end_timeslice.allF` / `sched.charge_budget.allF` (QueueBudgetG's `.allG` at
    `cto = false` without `TmoKG`); spec `nkt_/pres_/lkm_/fk_chargeBudgetF` (`chargeBudget u false` is an SC
    step: `NKT`, `Pres f`, `LKM W`, `FKA`), `kh_chargeTailF` (the tail keeps the kheap);
    `JAtZ.chargeBudgetJ`: from `JAtZ` + `CurInv σ` + current thread not idle + action not a switch to it,
    `sched.charge_budget used false` refines `chargeBudget used False` and ends at `JAtZ` (same `Z`, `Ac`, `D`;
    `Lst'`), `r.2 = a`. An SC step (`xtop_sc_step`, `ScAll.of_tr`, `JAtZ.sc_frame`, the `sc_*` frames);
    `CurInv`/`CurRunM` after from `HeadKeeps` when no reschedule; `CurOwnW`/`OffOK` vacuous on the consumed-time
    side (`consumedTime = 0`); `BlockedScActive.back` from the kheap shape (only the current SC changes, kept
    active); `hval` from `hval_of_rel` (ScTmo). Only [P] premises: `hmrt`, `hmb` (MAX_RELEASE_TIME/MIN_BUDGET),
    `ArchTotal`. `curSc ≠ idleSc` derived (`Inv.back` + `IdleOK`), which gives `cscW ∈ Ac` for P1.
- DONE f786ae48 (item 9, XTopJointYieldSys, new leaf): `JAtZ.curSc_ne_idle`, `JAtZ.setScConsumedJ` (any value to an SC's
  CONSUMED word at J; `reg_frame` as `updConsumedJ`, IRel by `sc_step_lift`, P1 by `consumedW_all`),
  `JAtZ.handleYieldJ` (FL4 `syscall::handle_yield` refines `handleYield` at J: reads, `chargeBudgetJ` of the
  head's amount, the consumed word), `dispatch_yieldJ` (`dispatch_syscall SysYield` against
  `fl4HandleSyscall rep .sysYield` at `RJ`, from `Entered σ`: `CurInv` by `JAtZ.cur`). There was no Yield
  dispatch at J before (no premise to remove); Yield is now proved with [P] `hmrt`/`hmb` only.
- FINDING (items 10 and 7 are not "item 8 + time words"): FL4's `check_budget` (sched.rs:513) and the spec's
  `checkBudget` (Ipc.lean:555) charge with `can_timeout_fault = true` (`charge_budget(c, true)` /
  `chargeBudget consumed true`), so `budget_ok`'s false branch and the preemption point's schedulable branch run
  `end_timeslice true`: when the current SC is not round-robin and the current thread has a valid timeout
  handler, `handle_timeout` of the CURRENT thread (fault to its timeout endpoint: send/block of the current
  thread, at the hole after the refill charge where only `InvBut` holds). The existing timeout sends at J
  (`JAtZ.runTmoJ`, `runTmoP_recv`, XTopJointFaultTmo) are for a thread other than the current one
  (`htc : t ≠ curThread`) after `Running`/`Restart`. Needed: a current-thread variant of
  `JAtZ.runTmoJ`/`sendTmoRecvIJ` composed with the head (`charge_head_refinesK`, InvBut) — or prove
  `end_timeslice_refinesG`'s `hto` at J in the J setting (`JTmoCurHyp`-shaped: SchedRel-level post plus the
  J-level rest, as `chargeBudgetJ` does for `can = false`).
- Item 10 plan, true branch only (no timeout): `JAtZ.timestampJ` (XTopJointPP; JAtZ after when `OffOK` and
  `CurOwnW` hold after) + ScEntry `budget_ok_refines` (`OffReady σ → OffOK σ'`) + ScEntryRd
  `checkBudgetRestart_true`; the FL4 side of `check_budget` true leaves the state unchanged (P1
  `check_budget.allG`'s `r = true → s' = s`, which asks `TmoKG` — needs a `cto`-free copy like `.allF`, or
  stepping `sufficient` directly). Totality of the false branch still needs the timeout send (`hto`).
- Item 7 (`mcs_preemption_point`): branch 2 (not schedulable, SC active: `charge_budget c false`) is
  `JAtZ.chargeBudgetJ` only under `CurInv` (`JAtPre` gives `chooseNewThread ∨ CurInv`; with a pending reschedule
  the current SC may be unbound, e.g. after the thread deleted its own SC: `chargeBudgetJ` would need a variant
  for an unbound current SC: `hcsc`/`hts` hold vacuously in P1, the spec charges `curSc` without an owner);
  branch 3 (inactive SC: node CONSUMED := 0, spec `consumedTime := 0`) is a node-word step (as
  `update_timestamp`'s CONSUMED write in `JAtZ.timestampJD`); branch 1 (schedulable: `check_budget`) needs the
  timeout send as above; then `check_interrupt` / `maybeHandleInterrupt` with M4 [P]. Not started.
- Builds: kp1-b9 (`lake build Fl4Proofs.P3.ScChargeJ`, cone ScChargeG/ScChargeJ, 5078 jobs) and kp1-b13
  (`Fl4Proofs.P3.XTopJointYieldSys`, 5370 jobs) OK; `#print axioms` (proofs/scratch/axkp1.lean, untracked):
  std only for `JAtZ.chargeBudgetJ`, `JAtZ.handleYieldJ`, `JAtZ.setScConsumedJ`, `dispatch_yieldJ`,
  `Sched.charge_budget_refinesF`, `Sched.end_timeslice_refinesG`, `Sched.kh_chargeTailF`,
  `P1.sched.charge_budget.allF`, `handle_invocation_refinesJ`. Build script: proofs/scratch/kp1build.sh
  (untracked; `AX=<file> sh proofs/scratch/kp1build.sh Mod...` from the mirror root).
- HANDOFF (kp1 stopped after items 8/9; items 10 and 7 need the current thread's timeout-fault send at J, see
  FINDING above). No premise added; `handle_invocation_refinesJ`'s `hPre` still open (item 7).

## ke11 (branch par/kentry3 in FL4-rb, on 65723946)
- (d5) blocking receive from a waiting sender whose bound notification lends the receiver its SC: new leaf
  XTopJointRecvSendRet: spec `receiveIpc_lend_eq` (the receive at σ = the receive at the state after
  `maybe_return_sc`, a no-op there), `JAtZ.recvSendRetJ` (ke7's route: `receive_ipc_blockR_red`,
  `JAtZ.maybeReturnJQ` to `J2`, then the sender cases at `J2` on FL4's `recvTail`). For this
  XTopJointRecvSend's `JAtZ.recvSendJ0` was split into `JAtZ.recvSendJG` (any FL4 program `m` reducing to the
  endpoint-state switch, `hm`) and `JAtZ.recvPreN` (the reduction for a non-lending bound ntfn).
- (d4, cap faults, no reply pushed) new leaf XTopJointRecvSendF: `JAtZ.recvSendFJG` (recvSendJG with
  XTopJointFaultRecv's `xferFaultStepJ` on IRel, frames from σ, `JAtZ.bufRebaseX`, FL4's fault word CapFault
  takes the call-or-fault branch, sender Inactive); spec `receiveIpc_sendCall_eq` generalised to
  `call ∨ fault ≠ none` (after the transfer). `SendOK xs rc` (unfaulted as before, or cap-faulted with
  neither grant right or rc = Null), `JAtZ.recvSendJX` / `recvSendJ0X` dispatch. `RecvSendBasicCase` now:
  bound none or non-active (any lending), head sender `SendOK`.
- Builds: ke11-b6/b7 `XTopJointRecvSendRet XTopJointRecvIpcLink XTopJointEntry` 5390 jobs OK; scratch/axke11.lean:
  std axioms for handle_invocation_refinesJ, dispatch_recvJL, recvSendRetJ, recvSendFJG, recvSendJX,
  receiveIpc_lend_eq. (station_task `dir` sync wedged this run; workaround: upload files with station_file to
  `ke11up/` under a prepared key and `cp` them into `FL4-rb/` in a dir-less task.)
- LEFT in `JRecvSendHyp` [W]: (d3) the head sender pushing a reply (calling or faulted, grant/grant-reply,
  reply cap non-null: `reply_push sender cur reply can_donate`), and (d4') senders with a fault other than a
  cap fault (needs footprint lemmas like XTopJointFaultRecv's `do_ipc_transfer_capF_rg/_rgB` for the other
  fault messages, EpFaultNone/EpFaultMore give the IRel level for all kinds; then `recvSendFJG` generalised).
## kp2 (branch par/budget in FL4-tcbj, on 8c856ee4)
- DONE (new leaf XTopJointBudgetOk, imported from Fl4Proofs.lean; kp2-b4 `lake build Fl4Proofs.P3.XTopJointBudgetOk`
  5058 jobs OK; scratch/axkp2.lean (untracked): std axioms only for `JAtZ.budgetOkJ`, `Sched.check_budget_restartT`,
  `Sched.checkBudgetRestart_suff`, `handle_invocation_refinesJ`). Item 10, the true branch, no premise added:
  * `Sched.check_budgetT` / `Sched.check_budget_restartT` (SchedRel level): FL4 returns `true` only in the
    `sufficient` branch (one domain: `is_cur_domain_expired_eq`), then state and arch unchanged and the spec's
    `getScRefillSufficient curSc consumedTime = {(true, σ)}` plus the head's `refillSufficient`; the charge/restart
    branches by P0 totality only (`P0.sched.charge_budget.p0` etc.), post vacuous (`r.1 = false`).
  * `Sched.checkBudgetRestart_suff` (spec): sufficient current SC ⇒ `checkBudgetRestart σ = {(true, σ)}`.
  * `JAtZ.budgetOkJ`: from `JAtZ` + `CurInv σ` + `OffReady σ` (as `budget_ok_offReady`), [P] `NowAgree`, `hmb`,
    `ARKeep`, `ArchTotal`, `numDomains = 1`: `syscall.budget_ok ⦃ r => r.1 = true → ∃ σ', (updateTimeStamp >>=
    checkBudgetRestart) σ = {(true, σ')} ∧ kheap/curThread/curSc/schedulerAction/idleThread kept ∧ CurInv σ' ∧
    OffReady σ' ∧ ∃ Ac' Lst' D', JAtZ … r.2.1 r.2.2 σ' ⦄` (`JAtZ.timestampJ` in parallel with
    `update_timestamp_refines` for `Inv`/`CurInv` after; `OffOK` = `OffReady.ok` with the sufficient head;
    `CurOwnW` by `curOwn_of_curInv`). So `Entered`, `OffReady.rd0` (JEntryAt.rd0) are available at dispatch.
- NOT DONE (a): the current thread's timeout send inside `charge_budget can=true`. FINDINGS for the next agent:
  * `JAtZ.faultBlockJ` (XTopJointFaultEp, the current thread's cap-fault block) uses `Inv` only at the end
    (`(J.inv.toBut ct).ik hnqT hik` + `J.inv.rd ct` for the RelIfBound of the blocked thread). For a TIMEOUT fault
    the blocked thread is exempt (`inClassR` excludes blockedOnSend with a timeout fault; Inactive / blockedOnReply
    are not in class), so only `InvBut σ ct` is needed -- which is exactly what holds at the hole after the head
    charge. But every other `J.*` lemma it uses needs a full `JAtZ` at the send's start, which does not exist at the
    hole (Inv.rd of ct genuinely fails there: insufficient head ⇒ not `released`). No JAtZ field may change.
  * Route ("frames from the base", as ke10's `recvSendJ0` / XTopJointFaultTmo's `sendTmoRecvIJ`): keep `J0` at the
    pre-charge state σ0 and assemble the end by `J0.cs_frameI` with `W = CnW … s0 σ0` (CnW ⊇ FinW ⊇ KFoot, so the
    SC ring / SC CONSUMED / node words of the head are inside) and a composite spec frame σ0 → σ' = "SC step at
    curSc (HeadKeeps: only refills/consumed, scTcb and refillMax kept) + consumedTime := 0" then `BFrT ct ep`
    (XTopJointSendBlockG). Steps: (1) `charge_head_refinesK` (ScChargeG) for SchedRel/NtfnStateRel/NSC/KFoot at s2,
    IRel at s2 by `sc_step_lift` (as `JAtZ.setScConsumedJ`); (2) P1 at the hole: the head's P1 posts are inline in
    `sched.charge_budget.allF` (ring_bx, node_bx) -- factor them out as a lemma (charge_budget.allG needs TmoKG, a
    ∀-state premise, unusable); `P1.CanBlock` of ct from J0.curBits (queue bits untouched by the head);
    (3) spec: `chargeBudget u true` at a schedulable ct with a valid handler and non-RR SC = chargeHead; consumed := 0;
    handleTimeout ct (.timeout badge); rescheduleRequired; reprogram (`end_timeslice_refinesG`'s `hspec` shape);
    (4) faultBlockJ's body from `set_fault` (timeout words: `set_fault_timeout_eq`, XTopJointSendBlockG) on, with
    every start fact read off J0 + HeadKeeps, `Inv` at the end by `InvBut.ik` from `InvBut σ2 ct` (charge_head's
    post); (5) then `reschedule_required` / `set_reprogram` at J (the tail of `charge_tail_refinesF`). The
    waiting-receiver cases additionally use `xferTmoStepJ` (XTopJointFaultTmo) and `sendFaultIJ`/`sendFaultPJ`
    (can_donate = false: no PDJ). Expect ~800 lines for the block case alone.
- (b) false branch and (c) item 7 wait on (a). Item 7 note: `JAtPre`'s second disjunct is the post of a PREEMPTED
  `sched.preemption_point` from a JAt state (XTopJointCnDel), so `hPre` first needs ppJ-style facts at that post
  (XTopJointPP `JAtZ.ppJD` covers only the non-preempting outcome).
- HANDOFF (kp2 stopped: (a) is several hundred lines beyond this context). Builds via proofs/scratch/kp1build.sh.
## kp3 (branch par/budget in FL4-tcbj, on c6e750ff)
- DONE (new leaf ScChargeN, imported from Fl4Proofs.lean; std axioms): `charge_budget` with `can_timeout_fault = true`
  when the current thread's timeout-handler slot holds no endpoint cap (no timeout fault can be raised).
  * `Sched.endTimeslice_noTmo` (spec) / `Sched.end_timeslice_noTmo` (FL4): the two `end_timeslice`s are equal when
    the handler is not valid (FL4: `if rr then R else R`).
  * `Sched.charge_budget_noTmo` (SchedRel level, `charge_budget_refinesF`'s premises + `hnt`): FL4's
    `charge_budget used true = charge_budget used false` (the mid state through `charge_head_refinesK`'s WP by
    `bind_congr_spec`; the handler at the state after the head by `TmoKeep` + `hval`) and the spec's
    `chargeBudget u true σ = chargeBudget u false σ` (`chargeBudget_noTmo`: `HeadKeeps` keeps the TCB).
  * `JAtZ.chargeBudgetNJ`: `JAtZ.chargeBudgetJ` for `can = true` under `hnt : ∀ xt, σ.kheap σ.curThread =
    some (.tcb xt) → isEpCap xt.tcbTimeoutHandler = false`. So (a) is now only the case "endpoint timeout handler"
    (and non-round-robin SC, thread not RUNNING_VM); with an RR SC it is also `can = false`'s path, not yet
    stated (HeadKeeps does not carry `scPeriod`; add it, or read the period off `charge_head`'s `updSc` shape).
- FINDING for (b) (budget_ok's false branch) and item 7 branch 1: the start of `charge_budget` there is NOT a `JAtZ`
  state either. After `update_timestamp` the consumed time is the new one and `check_budget` charges exactly when the
  head is insufficient for it, so `OffOK` (JAtZ field `off`) fails at that state (`JAtZ.timestampJ` gives `JAtZ` only
  under `OffOK`; `budgetOkJ` gets it from the sufficient head). `chargeBudgetJ`/`chargeBudgetNJ` need `JAtZ` at their
  start, so (b) needs either (i) `chargeBudgetJ` from "JAtZ but `off`" (the charge resets consumed time to 0, so
  `OffOK` after is vacuous; check whether `JAtZ.sc_frame` and the sub-lemmas `chargeBudgetJ` uses read `J.off`; if
  only `cs`/`sc_frame`'s construction needs the old structure, a `JAtZ`-minus-`off` record built from
  `timestampJ`'s hole is the way), or (ii) fusing `update_timestamp` with the charge (frames from the entry
  state). (i) looks cheaper. The same applies to (a): its start is the same hole.
- NOT DONE: (a) the current thread's timeout-fault send (route in kp2 unchanged; its start is the hole above, so it
  must start from J at the entry (pre-timestamp) state or from the (i) record); (b) false branch; (c) item 7.
- Builds: kp3-b4 `lake build Fl4Proofs.P3.ScChargeN` (5080 jobs) OK; scratch/axkp3.lean (untracked): std axioms only for
  `JAtZ.chargeBudgetNJ`, `Sched.charge_budget_noTmo`, `handle_invocation_refinesJ`. No premise added or removed.
- HANDOFF (kp3 stopped for context). Gotcha: `Result` here is ITree-like (`ret`/`vis`), so `cases m` with `ok`/`fail`
  alternatives fails; go through `spec_exists`, and reduce `ok v >>= f` with `simp only [Bind.bind, bind_ok]`.
## kp4 (branch par/budget in FL4-tcbj, on ba3cf690)
- DONE (a0) 0846788c, new leaf ScChargeH (std axioms, no premise added): kp3's option (i) in the form "frames from
  the base". `JHole … s0 a0 σ0 s a σ` (a structure beside `JAtZ`, JAtZ untouched): `JAtZ` at the base
  `(s0,a0,σ0)` (the entry state), the hole's spec state `{σ0 with machineState := ms, curTime, consumedTime}`
  (same memory), FL4's writes in the base's `KFoot` (the core's CUR_TIME/CONSUMED), `XTopAt`, `NSC`, `Inv`,
  `CurInv`-or-reschedule, `ActIdle`, `BlkOK` (same `Ac`) and the node-0 debug word at the hole: everything the
  charge reads except `OffOK`/`CurOwnW`. No `J.*` lemma reads `J.off` (checked: `sc_frame` takes `hoff` of the end
  state; `chargeBudgetJ`'s other `J.*` uses are frames from J's own state), so the end is `J0.sc_frame` with the
  writes composed (ScKFoot's `WritesIn.kfoot_trans`, SzKeepC from the equal kheaps) and the spec steps composed
  (`ScTKw`/`SOK`/`LK`/`FK` `.trans`).
  * `JAtZ.timestampJH`: XTopJointPP's `timestampJD` ending at a `JHole` (no `OffOK`/`CurOwnW` asked after).
  * `JHole.toJ`: `JHole` + `OffOK` + `CurOwnW` at the hole ⇒ `JAtZ` there.
  * `JHole.chargeBudgetJ` (can = false) / `JHole.chargeBudgetNJ` (can = true, no endpoint timeout handler):
    `chargeBudgetJ`/`chargeBudgetNJ` from a `JHole`; posts also give `ScTKw (fun _ => False) σ σ'`.
  * `JHole.checkBudgetF`: FL4 `check_budget` returning `false` at a `JHole` (insufficient head: `sufficient_refines`,
    then `chargeBudgetNJ` of the CONSUMED word) ⇒ spec `checkBudget σ = {(false, σ')}`, arch kept, `JAtZ` after.
- DONE (b) d0cda4ad, new leaf XTopJointBudgetF (std axioms): `JAtZ.budgetOkF`: from `JAtZ` + `Entered` + `CurInv`
  + `hnt` (no endpoint cap as the current thread's timeout handler) + [P] `NowAgree`/`hmrt`/`hmb`/`ARKeep`/
  `ArchTotal`, one domain: `syscall.budget_ok ⦃ r => r.1 = false → ∃ σ', (updateTimeStamp >>= fun _ =>
  checkBudgetRestart) σ = {(false, σ')} ∧ ∃ Ac' Lst' D', JAtZ … r.2.1 r.2.2 σ' ⦄` (timestampJH, checkBudgetF, then
  `set_thread_state Restart` of the still-runnable current thread: `JAtZ.restartRunJ` = XTopJointTcbInstall's
  `restartJ` from a runnable current thread instead of `Entered`, since a reschedule is pending after the charge;
  runnability kept through the charge by `OTK.tcb_false`). With `JAtZ.budgetOkJ` (true branch) item 10 is complete
  for threads without an endpoint timeout handler. No premise added (`hnt` is a case split, not a gap).
- NOT DONE (a) the current thread's own timeout-fault send (endpoint handler, non-RR SC); (c) item 7. Notes:
  * (a): `JHole` is the pattern for its start too: the send starts after `charge_head` inside `charge_budget` at a
    state that is again "the base's spec state + an SC step + consumed := 0"; generalise `JHole.spec` to
    `ScTKw (fun _ => False) σ0 σ ∧ SOK … ∧ LK … ∧ FK …` (what `sfacts` gives; `JHole.toJ`'s proof only uses those +
    curRun/bsa, which then need `CurRunM σ`/`BlockedScActive σ` as fields), and `ws` to the base's `TFoot`. Then the
    send (`faultBlockJ` body from `set_fault` on, kp2's route) is a frame from `J0` with `InvBut σ2 ct` at the hole.
  * RR SC with a valid handler: FL4/spec `end_timeslice true` take the round-robin path (no fault); a
    `chargeBudgetRJ` like `chargeBudgetNJ` needs the SC's `scPeriod`/RR flag kept by the head (HeadKeeps lacks it).
  * (c) unchanged (kp2's note): `JAtPre`'s preempted disjunct needs ppJ-style facts after a preempting
    `preemption_point`; item 7's schedulable branch can now use `JHole.checkBudgetF` once the preemption point's
    `update_timestamp` is given as a `JHole` (XTopJointPP's `ppJD` builds on `timestampJ`; a `ppJH` over
    `timestampJH` is the next step), the active-SC branch `JHole.chargeBudgetJ` (needs `CurInv` at the hole; the
    unbound-current-SC case of kp1 remains).
- Builds: kp4-b3 `ScChargeH` (5096 jobs), kp4-b4 `XTopJointBudgetF` (5102), kp4-b5 `XTopJointEntry` (5368, the mirror
  cone after 77d7a27e's JAtZ change) OK; scratch/axkp4.lean (untracked): std axioms only for timestampJH, JHole.toJ,
  JHole.chargeBudgetJ/NJ, JHole.checkBudgetF, restartRunJ, budgetOkF, handle_invocation_refinesJ.
- HANDOFF (kp4 stopped for context after (a0)/(b)): next is (a) (route above) or the `ppJH` step toward (c).
## ke12 (branch par/kentry3 in FL4-rb, on 077819cd)
- (d4') 89ce2da4, new leaf XTopJointXferF: FL4's footprint of the fault transfer uniform in the fault type
  and the receive buffer (`FW T rw W`; `set_mr_rgW`, `copy_mrs_fault_rgW`, `set_mrs_fault_rgW`,
  `do_ipc_transfer_fault_rgW`; a timeout only with `scA snd = 0`), `makeFaultMsg_pure` (the spec's message
  leaves the state unchanged unless timeout-with-SC), `xferFaultStepGJ` = `xferFaultStepJ` for any fault
  with EpFaultMore's `FaultOK`. `JAtZ.recvSendFJG` / `SendOK` now take any fault with
  `∀ b, f = .timeout b → xs.tcbSchedContext = none` (RelIfBound for a timeout-faulted sender from its
  null SC, not `Inv.rd`).
- (d3, receiver not lending) d36f89fd, new leaf XTopJointRecvSendP: at a resumed entry the receiver has
  the current SC (`CurInv`), so `reply_push` never donates. `JAtZ.recvSendFPJG` (faulted sender) /
  `JAtZ.recvSendPJG` (calling, unfaulted; base `Jy` of `xferStepGJ`): FJG/JG up to the fault-word read,
  then `reply_push_iC` (IRel), P1 `ipc.reply_push.ipc`/`.nd` from the dequeue hole (X = {sender}),
  `JAtZ.rsfr_postGR` (wake_postGR with `RSFr` as first frame; replies kept by RSFr so no reply fact) at
  `pushSt σ5 …` where σ5 = the sender-Inactive state of FJG (Inv there as before, `ps_inv`;
  `updK3_eq` gives pushSt σ3 … = pushSt σ5 …); the reply leaves the dead set first (`JAtZ.undeadC`
  from `recvCov_of`). Spec: `receiveIpc_sendPush_eq`, `replyPush_don_irrel`. `PushOK`,
  `JAtZ.recvSendP0X`; XTopJointRecvIpcLink: `RecvSendPushCase`, excluded from `JRecvSendHyp`.
- Deleted the unused `JRecvIpcRestHyp` / `jRecvIpcHyp_of` / `dispatch_recvJR` (XTopJointRecvIpc).
- LEFT in `JRecvSendHyp` [W] (l4v receive_ipc send_ep branch):
  (R1) blocking receiver whose bound ntfn lends it its SC + a pushing sender: after `maybe_return_sc`
  (XTopJointRecvSendRet's route, J2 has chooseNewThread and the receiver no SC) `reply_push` donates
  the sender's SC to the CURRENT thread (donor not current: no reschedule; `pushDonJ` assumes the donor
  is current and the callee Inactive, so a variant `pushDonRJ` is needed; if the sender has no SC or a
  timeout fault the push does not donate: FPJG/PJG generalised to action = chooseNewThread).
  (R2) senders with a timeout fault and an SC (Inactive or non-donating push): `xferTmoStepJ` changes
  the sender's SC consumed word, which RSFr cannot hold; plan as XTopJointFaultTmo's
  `sendTmoRecvIJ`: a base JAtZ at the state after `update_consumed` (`JAtZ.updConsumedJ`, as
  `JAtZ.tmoBaseJ` without set_fault), footprints rebased (`writesIn_rebase`), RSFr from that base.
- Builds: ke12-b2 (d4' cone), ke12-b3 `XTopJointRecvSendP XTopJointRecvIpcLink XTopJointEntry` 5394 jobs OK;
  scratch/axke12.lean std axioms (handle_invocation_refinesJ, dispatch_recvJL, recvSendFJG, recvSendJX,
  xferFaultStepGJ, recvSendFPJG, recvSendPJG, recvSendP0X, receiveIpc_sendPush_eq).
- Station: the FL4-rb mirror had a sync conflict at proofs/Fl4Proofs.lean (ke11's cp workaround left an
  older copy); fixed by uploading the local file with station_file and cp'ing it into the mirror in a
  dir-less task, after which dir sync worked.

## ke13 (branch par/kentry3 in FL4-rb, on d8ed0bbb = int/r2m ba3cf690 + ke12)
- (0) 5a8294c3: integration fix. `JAtZ.rsfr_postGR` (XTopJointRecvSendP) takes the second frame's
  `hfk1 : IpcFrKeep σa σ'` (gl13's `cs_frameI` argument), `F.ipcFr.trans hfk1` at `cs_frameI`, callers
  pass `ps_ipcFr hkta hkwa hws`. ke13-b1: `XTopJointRecvSendP XTopJointRecvIpcLink XTopJointEntry`
  5406 jobs OK. No other receive module needed a change.
- (R1, sender without an SC) 0ee443a2, new leaf XTopJointRecvSendRP: `JAtZ.recvSendRetPJ` = RecvSendRet's
  route (`maybeReturnJQ`, `receiveIpc_lend_eq`), covers at the state after by `JAtZ.recvCov_ofW` (TFoot
  of maybe_return_sc), then `recvSendPJG` / `recvSendFPJG` at J2. Those two now take
  `hni : σ.curThread ≠ σ.idleThread` and `hAct : action = resumeCurThread ∨ (action = chooseNewThread ∧
  t ∉ releaseQueue ∧ xs.tcbSchedContext = none)` instead of `Entered σ`: no donation from
  `xs.sc = none ∨ xt.sc ≠ none` (FL4: `can_donate` false from the sender's SC word 0, or the receiver's
  SC word ≠ 0; `hPush`/`HH` take `cd = false ∨ scA t ≠ 0`); `hna3` by `actionW_ne_of`; CurInv/CurRunM/ActIdle
  after by cases (`hcur6`, `hrun6`). `replyPush_don_irrel` takes `xt.sc = none ∨ xd.sc ≠ none`.
  XTopJointRecvIpcLink: `RecvSendRetPushCase` (blocking, bound ntfn inactive and lending, PushOK sender
  with no SC), excluded from `JRecvSendHyp`. ke13-b3 `XTopJointRecvSendP XTopJointRecvSendRP
  XTopJointRecvIpcLink XTopJointEntry` 5408 jobs OK; scratch/axke13.lean std axioms
  (handle_invocation_refinesJ, dispatch_recvJL, recvSendRetPJ, recvSendFPJG, recvSendPJG, rsfr_postGR,
  replyPush_don_irrel).
- LEFT in `JRecvSendHyp` [W]:
  (R1b) blocking receiver whose bound ntfn lends it its SC, PushOK sender WITH an SC (so no timeout
  fault): the passive-server call. After maybe_return_sc (J2: action chooseNewThread, receiver current,
  Running, no SC) FL4's `reply_push sd t rv true` donates sd's SC to t. Spec: `schedContextDonate sc t`
  with from = sd ≠ cur: `testReschedule sd` is a no-op (action chooseNewThread, not switchThread), so
  the result is the same `dnSt`/`pdSt` as XTopJointPushDon's `donate_curN_eq` (there `t = cur` sets
  action := chooseNewThread, which J2 already has): generalise `testReschedule_curN`/`donate_curN_eq`
  to `hct ∨ σ.schedulerAction = .chooseNewThread`. J side: a `JAtZ.pushDonJ` variant with the donor
  sd blocked on the reply (not current; `hct`/`hcsc` dropped) and the callee t current Running
  (instead of `Inactive`, `hsd`); check Inv/BlockedScActive/CurRunM for a Running current thread
  gaining an active SC (CurInv not needed: action chooseNewThread). Then a FPJG/PJG variant whose
  `reply_push_iC` `hD` branch calls it (as XTopJointSendPushD:544 / XTopJointFaultRecv:2101), P1 by
  `ipc.push_don.blk` (caller = sd, callee = t; its hypotheses hold: neither queued, actionW ≠ either).
  (R2) senders with a timeout fault and an SC (Inactive, or non-donating push; any receiver ntfn
  case): FL4 order is dequeue, `update_consumed` (SC CONSUMED word) + 2 message registers, then
  `unblock_sporadic sd` (refills of the same SC). Plan unchanged from ke12: base JAtZ after
  `update_consumed` (`JAtZ.updConsumedJ`, needs `hmax`/`htu` = JEntryGlob.maxTU/tu, so
  `jRecvIpcU_of`/`dispatch_recvJL` will take them), FL4 footprints rebased (`writesIn_rebase`),
  spec shadows as XTopJointFaultTmo's `rhoT`, transfer by `xferTmoStepJ`/`doIpcTransfer_tmo_eq`, then
  RSFr from that base as recvSendFJG / recvSendFPJG.
- M5/M6/M7: not started.
