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

## ke14 (branch par/kentry4 in FL4-rb, on 8bea61cb = int/j2)
- (R1b) 90f97473, new leaf XTopJointRecvSendRD (imported from Fl4Proofs.lean): the passive-server call.
  * Spec: `testReschedule_cnN`, `donate_cnN_eq`, `pd_eqN`, `bd_donate_eqN` (donor not current, a reschedule
    already pending: `test_reschedule` of a non-current thread is a no-op and `dnSt`'s
    `schedulerAction := chooseNewThread` is the pending one); `receiveIpc_sendPushD_eq` (the spec's
    `can_donate` true for a sender with an SC and no timeout fault); `runnable_notQ`, `runnable_tsc0`.
  * `JAtZ.pushDonRJ`: pushDonJ with the donor `t` blocked on the reply, not current; the callee `d` any
    thread with `ipcQueuedThreadState = false` (`hdq`), not idle (`hidd`); the donated SC `released`
    (`hrelD`, push_donate_refinesW's `hrel`); the current SC another one (`hcsx`), in `Z.C`, bound to no
    thread (`hk0`, `hcsF`): `CurOwnW` by its second disjunct, `OffOK` by the frame (`pd_ko`/`bd_oth`).
  * `JAtZ.recvSendFPDJ` / `JAtZ.recvSendPDJ` = FPJG / PJG with `hAct` replaced by `hcn` (chooseNewThread),
    `hnrT0`, `hxtn` (receiver no SC), `hpC`/`hxsp` (sender's SC `p`), `hnto` (FPDJ: no timeout fault) and
    the current-SC facts. FL4's `can_donate` = true (`hpw3`, `hftT`); `reply_push_iC (don := true)` with
    `P := σ'' = σD → ∃ V Lst', JAtZ ..` (hP' by `hneq`: the callee's SC differs), its donation step:
    P1 at the block by `set_blocked_on_reply.ipc`/`.kw`, `JAtZ` at `pushSt σ5 ..` by `rsfr_postGR` (as
    before), then `pushDonRJ`. `p` released at σ5 (`IR5`: no unblock -> `hrib`; unblock -> `ready_now` +
    `sufficient_of_refOK (hz1 (I5'.refills ..))`), carried to σ' by `G'.tm`. The stack head (`hhP`) from
    `J.stackHead` at σ (the receiver's reply free, so `Detached`) through `Fr5.callKeep`/`ps_ck`.
  * `JAtZ.recvSendRetPDJ` = RetPJ's route with `hsn : xs.tcbSchedContext ≠ none`; σ.curSc = i by CurInv
    (`hcsI`), `i` unbound after maybe_return_sc (`maybeReturn_shape`'s kheap-i field).
  * XTopJointRecvIpcLink: `RecvSendRetPushCase` lost its `xs.tcbSchedContext = none` conjunct, the branch
    splits on it (RetPJ / RetPDJ). `JRecvSendHyp` [W] now = the timeout-faulted sender with an SC only.
  * ke14-b1: `XTopJointRecvSendRD XTopJointRecvIpcLink XTopJointEntry` 5410 jobs OK; scratch/axke14.lean
    std axioms (handle_invocation_refinesJ, dispatch_recvJL, recvSendRetPDJ, recvSendFPDJ, recvSendPDJ,
    pushDonRJ, donate_cnN_eq, receiveIpc_sendPushD_eq).
  * Note: `lake env lean` of the 1750-line RD file takes ~20-35 s on the studio (ke10chk.sh), so iterate with it.
- (R2) NOT started (context). Plan, refined:
  * Remaining case: head sender with `tcbFault = some (.timeout bb)` and `tcbSchedContext = some sc`
    (FL4: `can_donate` false, so either `Inactive` (no reply pushed: SendOK's shape) or a non-donating push
    (PushOK's shape)), any receiver notification case (non-lending: J0X / P0X routes; lending blocking:
    RetJ / RetPJ routes, after maybe_return_sc).
  * Two core lemmas, copies of XTopJointRecvSendF's `JAtZ.recvSendFJG` (sender Inactive) and
    XTopJointRecvSendP's `JAtZ.recvSendFPJG` (push), say `recvSendFTJ` / `recvSendFPTJ`, taking
    `hmax`/`htu` (JEntryGlob.maxTU/tu; the callers jRecvIpcU_of / jRecvIpcLink_of / jRecvIpcHypL_of /
    dispatch_recvJL must take them; dispatch_recvJL is not used by XTopJointEntry yet, so this is local):
    (1) transfer by XTopJointFaultTmo's `xferTmoStepJ` instead of `xferFaultStepGJ` (outcome
    `updK (tmoSt σ1 sc y n) t x'`, footprint `scW sc 8` + receiver registers, `Agree` with `tmoS`);
    (2) the base `Jb` := `J.updConsumedJ hAT hmax htu hsc ht` at (`tmoS st s sc`, `tmoSt σ sc y n`) as in
    `JAtZ.tmoBaseJ` (without set_fault: the fault is already there), spec equality with
    `update_consumed_irel` as in tmoBaseJ;
    (3) the spec frame `RSFr sd t (tmoSt σ sc y n) σ5` (dequeue/receiver/unblock updates commute with the SC
    update: `rhoT`-style shadows or `updK` commutation, the unblock touches `sc` only via refills — check
    UnblockOut's `p ≠ curSc` and that its `y` is the consumed-cleared one);
    (4) FL4 footprints rebased onto `tmoS s sc` by `writesIn_rebase` (sendTmoRecvIJ does exactly this for
    the send side: read it first, lines 641-1257 of XTopJointFaultTmo.lean);
    (5) `Inv` at σ5' for the Inactive sender with an SC and a timeout fault: RelIfBound not needed if
    `inClassR` excludes it (UPDATE 02:24Z: Inv.rd weakened for timeout-faulted senders); else from Jb.
  * Then cases in XTopJointRecvIpcLink (`RecvSendTmoCase` split by receiver ntfn / push) and delete
    `JRecvSendHyp`, its parameter of jRecvIpcU_of/jRecvIpcLink_of/jRecvIpcHypL_of/dispatch_recvJL.
- M5/M6/M7: not started.
## kp5 (branch par/budget in FL4-tcbj, on 9060ec31)
- DONE 91a38af5 (new leaf ScChargeR, std axioms; (b) round-robin part): `charge_budget used true` for a round-robin
  current SC is `charge_budget used false` on both sides (`end_timeslice`'s timeout branch needs `!rr`).
  `endTimeslice_rr`/`end_timeslice_rr`, `chargeHead_rr` (the spec head of an RR SC is an explicit `updSc` keeping
  `scPeriod`; no `HeadKeeps` change needed), `charge_budget_rr` (FL4's period word after the head read from
  `SchedRel` there + determinism of the head), `NoTmoSend σ` := no endpoint timeout handler ∨ RR current SC,
  `JAtZ.chargeBudgetRJ`/`TJ`, `JHole.chargeBudgetRJ`/`TJ`. `JHole.checkBudgetF` and `JAtZ.budgetOkF` now take
  `hnt : NoTmoSend σ` (was: no endpoint handler); callers: none outside these leaves.
- DONE f737f874 (new leaves ScChargeT, XTopJointBudgetT, std axioms; (a) and the rest of (b) for an idle/sending
  handler endpoint):
  * P1: `sched.charge_head.ring` (the head's writes: ring + SC CONSUMED word, factored out of `charge_budget.allF`),
    `rperiod_of_ring` (the head keeps the period word), `charge_pre_post` (BlkOK and a Foot-closed `G` after the
    head and the node CONSUMED write). Spec: `nkt_/pres_/lkm_/fk_chargeHead`.
  * `ScOnly c σ σ'` (kheap changes only at SC `c`, keeping size/scTcb/refillMax/yieldFrom/replies, ntfn kept or
    cleared) + frame lemmas (szKeep, ykeep, mcpKeep, bufKeep, kback, ksz, ksub, khrb, ipcFr, prio, othF/othB,
    scF/scB, tcbF/tcbB).
  * `JTH … s0 a0 σ0 s a σ` (structure beside JAtZ, kp4's JHole pattern): JAtZ at the base, FL4 writes from it in
    its KFoot, `ScOnly σ0.curSc σ0 σ` + scheduler fields equal + consumedTime 0, and at the hole XTopAt, buffer
    words, NSC, `InvBut σ σ.curThread`, ActIdle, BlockedScActive, CurOwnW, IpcSorted, BlkOK, node-0 debug word.
  * `JTH.tmoBlockJ`: `handle_timeout` of the current thread (Running/Restart, not queued, action
    ResumeCurThread, not idle, active SC) with an endpoint handler on an idle/sending endpoint: runTmoJ's tail
    for the current thread; the end assembled from the BASE JAtZ with composite frame facts (ScOnly then BFrT:
    SzKeep/YKeep/McpKeep/BufKeep/KBack/KSz/KSub/KhRB/IpcFrKeep/call/reply/archObj via the existing `.trans`
    lemmas), Inv by `InvBut.ik` at the hole + `inClassR.notTmoS`; state properties (nsc, own, bsa, isorted,
    act) pushed from the hole through `BFrT`. `JAtZ (Z.mv Z.G V)` after with the action chooseNewThread.
  * `JTH.endTimesliceTmoJ` (both sides take the timeout branch), `JHole.chargeBudgetTmoJ` (whole
    `charge_budget used true` from a JHole, ends with `JAtZ.reschedJ` + `JAtZ.reprogramJ`; post: membership
    `∃ z ∈ (chargeBudget …).1, ∃ V Ac' Lst' D', JAtZ (Z.mv Z.G V) …`), `JHole.checkBudgetT`, `JAtZ.budgetOkT`
    (budget_ok false branch: `∃ z ∈ ((updateTimeStamp >>= checkBudgetRestart) σ).1, z.1 = false ∧ JAtZ …`;
    restart branch generic via `restartRunJ`).
  * No premise added or removed. Case restrictions (not invariant gaps): `hcb` (handler endpoint idle or
    sending), `hrr` (current thread Running/Restart), `hnq` (= JEntryAt.ctnq at entry), `hres` (Entered).
- Item 10 coverage now: NoTmoSend (budgetOkF) + endpoint handler, non-RR, idle/sending endpoint (budgetOkT).
  LEFT: (i) handler endpoint with waiting receivers: the current thread's timeout-fault transfer to a receiver
  = XTopJointFaultTmo `sendTmoRecvIJ`/`sendTmoRecvPJ` analogue started from a `JTH` (those build their base with
  `JAtZ.tmoBaseJ`, which needs JAtZ at the send's start: at a JTH the base is the entry state, so the frames go
  ScOnly-then-CFr as in tmoBlockJ; expect ~1200 lines, two cases (Inactive / reply push)); (ii) a RUNNING_VM
  current thread with an endpoint handler: `valid = false`, so add a third disjunct `xt.tcbState = .runningVM`
  to `NoTmoSend` (copy `endTimeslice_noTmo`/`end_timeslice_noTmo` with the VM guard; ~60 lines).
- NOT DONE (c) item 7 / `hPre`: `JAtPre`'s second disjunct is the post of a PREEMPTING `sched.preemption_point`
  from a `JAt` state (XTopJointCnDel); `hPre` (XTopJointDispatch `dispatch_invokeJ`) needs `after_invocation
  (Err)` = `mcs_preemption_point` + `take_pending_irq` + `check_interrupt` from such states. Steps: (1) ppJ-style
  facts after a preempting `preemption_point` (XTopJointPP `JAtZ.ppJD` covers only the non-preempting outcome;
  the preempting one should end at a JHole-like state: it runs `update_timestamp`, so `JAtZ.timestampJH`);
  (2) `mcs_preemption_point` branches: schedulable → `check_budget` (`JHole.checkBudgetF`/`T`; note the action
  there may be chooseNewThread or a switch, so `checkBudgetT`'s `hres` must be generalised: with a switch target
  pending the current thread's block leaves `cur` unprovable — CurInv fails and the action is not
  chooseNewThread — l4v's preemption point has the same shape, so it needs the action-after facts from the
  invocation (switch targets are set only by possible_switch_to, check whether `JAtPre`'s state can have one)),
  active SC → `JHole.chargeBudgetJ` (needs CurInv; unbound current SC case of kp1 remains), inactive SC → node
  CONSUMED := 0; (3) `check_interrupt` at J with M4 [P]. Not started.
- Builds: kp5-b2 (`ScChargeR ScChargeH XTopJointBudgetF`), kp5-b12/b13 (`ScChargeT XTopJointBudgetT`, 5168/5176
  jobs), kp5-ax1 (`XTopJointEntry`, 5368 jobs, + scratch/axkp5.lean, untracked): std axioms only for
  charge_budget_rr, JAtZ/JHole.chargeBudgetTJ, checkBudgetF, budgetOkF, JTH.tmoBlockJ, JTH.endTimesliceTmoJ,
  JHole.chargeBudgetTmoJ, JHole.checkBudgetT, JAtZ.budgetOkT, handle_invocation_refinesJ. Build script
  proofs/scratch/kp5build.sh (kp1build.sh with longer error output; untracked).
- HANDOFF (kp5 stopped for context after (a)/(b) idle/sending case). Next: (ii) above (cheap), then (i) or (c).

## ke15 (branch par/kentry5 in FL4-rb, on d0509548 = int/j2)
- (R2) 4093653e, new leaf XTopJointRecvSendT (imported from Fl4Proofs.lean): the head sender with a timeout
  fault and an SC.
  * `JAtZ.tmoRecvBaseJ`: base `Jb` at (`tmoS st s sc`, `tmoSt σ sc y n`) by `JAtZ.updConsumedJ` +
    `update_consumed_irel` (tmoBaseJ without set_fault).
  * `JAtZ.recvSendFTJ` / `JAtZ.recvSendFPTJ` = recvSendFJG / recvSendFPJG with `hft : tcbFault = some (.timeout bb)`,
    `hsn : tcbSchedContext ≠ none`, `hAT hmax htu`: transfer `xferTmoStepJ` (no receive-buffer write, so no
    `bufRebaseX`); spec states rewritten from the base by `updSc_updK_comm` (dequeue commutes with the SC
    update), `RSFr`/`IK`/`SKeep` from `σb`; `Inv` from `Jb.inv` (`InvBut.inv`'s premise vacuous: the sender
    ends Inactive, not `inClassR`); FL4 footprints from `s` rebased (`writesIn_rebase`, the SC word in
    `CnW` via `sw_hdr`, in `KW` via `scW8_inSC`), then `Jb.rsfrStep` / `Jb.rsfr_postGR`. Push: FL4's
    `can_donate` false (`hcdF`: fault word 5 = Timeout), spec `receiveIpc_sendPushT_eq` (spec can_donate
    false); `hAct` lost the `xs.sc = none` conjunct.
  * `TmoOK`, `sendOK_split` (SendOK ∨ PushOK ∨ TmoOK for a blocked sender), `noPush_of`, `JAtZ.head_sendT`,
    wrappers `JAtZ.recvSendT0X` (recvPreN) / `JAtZ.recvSendRetTJ` (RP's maybe_return route).
- da8d8f6b: `JRecvSendHyp` [W] DELETED. jRecvIpcU_of's last branch proves exhaustiveness (bound ntfn exists by
  `J.sv.tcbNtfn`, active -> RecvIpcActCase; no sender -> Poll/Block/Bound; head sender by head_sendT +
  sendOK_split -> Basic / Push / RetPush / the tmo wrappers). jRecvIpcU_of / jRecvIpcLink_of /
  jRecvIpcHypL_of / dispatch_recvJL take `hmax` / `htu` (JEntryGlob.maxTU / tu) instead of `hS`;
  dispatch_recvJL is still not used by XTopJointEntry.
- Builds: ke15-b1 `XTopJointRecvSendT XTopJointRecvIpcLink XTopJointEntry` 5416 jobs OK; scratch/axke15.lean std
  axioms (handle_invocation_refinesJ, dispatch_recvJL, jRecvIpcU_of, recvSendFTJ, recvSendFPTJ, recvSendT0X,
  recvSendRetTJ, tmoRecvBaseJ, receiveIpc_sendPushT_eq, sendOK_split).
- Stale docstring mentions of `JRecvSendHyp` remain in RecvSend/RecvSendF/P/RP/RD/Ret/Step, XferF, IpcRecvSendFr
  (not touched to avoid rebuilding their cones).

## sch1 (branch par/sched1 in FL4-sc, on d0509548 = int/j2; items M5-M7 / 11)
New leaf XTopJointSchedR (imported from Fl4Proofs.lean; std axioms). No premise added to existing theorems, none
removed; JAtZ untouched.
- DONE fccc456d (a) M7: `jat_scheduleFR` / `jat_scheduleSR`: ScFireJ's `jat_scheduleF` (same premises, proof copied)
  with the spec outcome in the post: `∃ σ1 σ', Fires σ σ1 ∧ Fl4Spec.schedule σ1 = ({((), σ')}, False) ∧ RJ r σ' ∧
  (∃ V' Ac' Lst' D', JAtZ (Z.mv Z.G V') … r σ') ∧ CurInv σ' ∧ CurRunW σ'` (`CurRunW σ'` is `RunW.scAndTimer`, which
  the old proof already built for `sch_tail`). The old `jat_scheduleF/S` are left alone (FOLD LATER: derive them).
  * The spec relation is `Fires` then `schedule`: FL4's TCB timers (`timer::fire`, l4h 0003, M8) have no spec
    counterpart in `fl4CallKernel`. DECISION for the top statement (lead): either an Ext step (e.g.
    `fl4Awaken := NonDet.select {σ1 | Fires σ σ1}` before `schedule`; `Fires` is defined in P3 ScAwaken over the
    spec's `sendSignal`, so it would move to Fl4Spec/Ext) or a relational top theorem `∃ σ1, Fires σ σ1 ∧ …`.
  * FINDING (`hd : σ.domainTime ≠ 0`, kept from `jat_scheduleF`, needed by `schedule_refinesWP`'s `SchedPreW`):
    FALSE in reachable states right after DomainScheduleSetStart (spec `domainSetStart` sets `domainTime := 0`;
    with `numDomains = 1` nothing else writes it; the next `schedule` takes `scheduleChooseNewThread`'s
    `nextDomain` branch, FL4 `switch_to_thread`'s `next_domain`). It is a case hypothesis of these theorems, not a
    global premise, but `kernel_entryJ` needs the other case: `schedule_refinesWP`/`cn_refines` (ScScheduleTop)
    with `domainTime = 0` (FL4 `next_domain` ks words vs spec `nextDomain`: domainIndex/curDomain/domainTime/
    reprogramTimer/workUnits; `archPrepareNextDomain` = FPU release? check). Not started.
- DONE 06434837 (b) M5: `JAtZ.activateJ`: FL4's `sched::activate_thread` refines `activateThread` at `J` from `JAtZ` +
  `CurRunW σ` (what `jat_scheduleFR` gives) + `hvm` [W]: `∀ x, σ.kheap σ.curThread = some (.tcb x) → x.tcbState ≠
  .runningVM`. Yield completion by `JAtZ.completeYieldJa` (FL4 re-reads `yield_to`; the spec's `completeYieldTo`
  keeps every thread state, cur and idle: `completeYieldTo_sframe`, the SC from `YieldRel.toSc`), then
  `JAtZ.actRestJ` (Restart: NEXT_IP := FAULT_IP via `reg_wr_irel` + `JAtZ.regWrJ`, then `JAtZ.runJ`; spec
  `getRestartPC`/`setNextPC`/`setThreadState running`; Running/idle: no-op, spec `return ()`/
  `archActivateIdleThread = return ()`). The spec's `NonDet.fail` branch is unreachable from `CurRunW` (`runnable`
  = running/restart/runningVM; idle by `IdleOK`) except `RunningVM`. `hvm` justification: VT-x is outside the
  native scope (IpcLeaves' `NativeScope`, DESIGN §9). SPEC FINDING: the ported `activateThread` has no `RunningVM`
  branch (seL4 C `activateThread` has `case ThreadState_RunningVM:` under CONFIG_VTX, a no-op); adding
  `| .runningVM => return ()` to Fl4Spec (a PORTING "FL4 differences" entry) would remove `hvm` here (FL4's
  `activate_thread` does nothing for TS_RUNNING_VM). Premise is false in reachable states only when a VM runs.
  `jat_finishJ`: FL4's `syscall::finish` = schedule ; activate_thread against `Fires` then
  `schedule >>= activateThread` (one outcome), `RJ`/`JAtZ` after; `hvm` there is ∀ `JAt` states (same [W]);
  `htu` [P] at every arch state.
- NOT DONE (c) M6, FINDING: the receive after ReplyRecv / NBSendRecv / NBSendWait's invocation cannot get
  JEntryAt's `ni : Entered σmid` – it is FALSE in reachable mid states: the invocation may leave
  `switchThread t` (a reply/send waking a higher-priority thread: `possibleSwitchTo`) or `chooseNewThread`
  (a blocking or self-suspending invocation; with `chooseNewThread` the current thread may be Inactive, e.g.
  NBSendRecv on its own TCB cap's Suspend). Uses of `hni` in the receive at J (grep `hni` in XTopJointRecv*):
  (1) `J.curInv (hni.2 ▸ …)` – needs only `action ≠ chooseNewThread`; (2) `J.curRun.run hni` – the current thread
  runnable; (3) `Or.inl hni.2` – an `action = resume ∨ …` disjunct of the block lemmas (`recvIpcBlock*`,
  `recvIpcBound*`: check whether `switchThread t` with `t ≠ ct` is admissible there, as for `cnN` in ke13);
  (4) `hni.1` – not idle (kept: the invocation keeps `curThread`, `hPK`, and idleness). Route: replace `hni` in
  `handle_recvJ` / `dispatch_recvJ*` / the leaves by `JMid σ := σ.curThread ≠ σ.idleThread ∧ σ.schedulerAction ≠
  .chooseNewThread ∧ CurRun σ ∧ (∀ t, σ.schedulerAction = .switchThread t → t ≠ σ.curThread)` (l4v:
  `ct_active`, `scheduler_act_sane`), and separately prove the chooseNewThread / non-runnable mid case (the
  spec's receive from an inactive or blocked current thread; l4v proves `handle_recv` from `ct_active` only, so
  check what l4v's `handle_event` ReplyRecv proof assumes after `handle_invocation` before naming anything).
  `ctnq` (no ready queue holds ct: `possibleSwitchTo` enqueues only other threads) and `vfh` (only TCB installs
  write the fault handler, after `valid_fault_handler`) are true at the mid state but need a post fact of
  `handle_invocation_refinesJ` (per decode path) or a separate invariant beside `JAtZ`; `cnf` likewise (a lookup
  fault in the invocation leaves ct faulted and blocked: then (2) fails too). Nothing proved for (c).
- kernel_entryJ statement plan (no proof): for `c` a native syscall (Send/NBSend/Call/Recv*/Yield/ReplyRecv/
  NBSendRecv/NBSendWait, M2 excluded),
  `syscall.handle_syscall st arI s a n ⦃ r => ∃ σ1 σ2 σ', (fl4SyscallFaultIP-then-handleE part) σ = … σ1 ∧
  Fires σ1 σ2 ∧ (schedule >>= activateThread) σ2 = {σ'} ∧ RJ r σ' ⦄` from `JAtZ` + `Entered` + `CurInv` +
  `OffReady` + `σ.domainTime ≠ 0` (until the next_domain case is proved), against
  `fl4KernelEntrySyscall true c` (M1 (a)) once the `Fires` decision above is taken (then literally
  `(fl4KernelEntrySyscall true c σ).1 ∋ ((), σ')` with the Ext timer step). Pieces: M1 FAULT_IP write at J
  (`JAtZ.regWrJ` + `reg_wr_irel`, as in `actRestJ`); `budgetOkJ`/`budgetOkF` (kp2/kp4; endpoint timeout handler
  open); `dispatch_invokeJE`/`dispatch_recvJL`/`dispatch_yieldJ`; preemption (`hPre`, item 7, open);
  ReplyRecv's receive at the mid state (M6, open); `jat_finishJ` from any `RJ` post: needs `CurRunW`-free
  inputs: `jat_scheduleFR` takes only `JAtZ` + `hd` (+ globals), so the RJ of each branch suffices.
- Builds: sch1-b1 (5380 jobs) / sch1-b5 / sch1-b7 `lake build Fl4Proofs.P3.XTopJointSchedR` OK; axioms
  (axsch1.sh/axsch1.lean, untracked): std only for jat_scheduleFR/SR, JAtZ.activateJ, JAtZ.actRestJ,
  activateThread_eq, jat_finishJ, handle_invocation_refinesJ.
## kp6 (branch par/budget2 in FL4-tcbj, on cccbf9a3 = int/j2 + kp5)
- Base check: kp6-b1 `ScChargeT XTopJointBudgetT XTopJointEntry` (5172/5180/5372 jobs) built at cccbf9a3 with no
  change: the XferHZ removal (gl15/gl16) needed no fix in kp5's modules.
- DONE a605fcf9 (new leaf XTopJointPPH, std axioms): item 7 step 1.
  * `pp_err_eq` (spec): every `error` outcome of `preemption_point` is the state after its time update and IRQ
    check (`NAll` of SpecFreeRet; `nall_getsThe`). `JAtZ.ppJH`: a PREEMPTING `sched.preemption_point` from `JAtZ`
    (no `PPR0` needed) ends at a `JHole` whose base is the state after the two WORK_UNITS writes, for every spec
    `error` outcome (ppJD with `timestampJH`). `JAtZ.toHole` (a JAtZ is a JHole over itself), `jAtPre_hole`: every
    `JAtPre` state is a `JHole`.
- DONE 892af980 + 64cc669d + (this commit) (new leaf XTopJointPreempt, std axioms): item 7 at J.
  * Spec: `mem_pp_sched`/`mem_pp_charge`, `fail_pp_sched`/`fail_pp_charge` (outcomes/failure of `preemption_path`
    from those of its budget part and `maybe_handle_interrupt true`; NB the spec's `preemption_path` elaborates with
    a join point `__do_jp`, so it is not `ppIf >>= maybe…` by `rfl`), `checkBudget_suff`, `mem_maybeHandle_none/_some`,
    `fail_maybeHandle_some`.
  * `JHole.msAr` (another machine state with the same memory and an arch keeping AR), `JHoleAt` (∃ JHole ending at
    the state).
  * `JHole.mcsPPJ`: `mcs_preemption_point` from a JHole under `PPCov` (CurInv, current thread not idle, no switch to
    it pending, `NoTmoSend`) or `PPCovT` (checkBudgetT's case: endpoint handler on an idle/sending endpoint, non-RR
    SC, Running/Restart, unqueued, ResumeCurThread): schedulable → check_budget (true: unchanged, `check_budgetT` +
    `checkBudget_suff`; false: `JHole.checkBudgetF`/`checkBudgetT`); not schedulable → `JHole.chargeBudgetJ` (SC
    active by CurInv.active + `curSc_ne_idleSc_of`); the inactive-SC branch is unreachable under either.
  * `JHole.afterInvJ`: `after_invocation (Err _)` = mcs + `take_pending_irq` + `check_interrupt` refines
    `preemption_path` (`PPQ σ r` := spec fails ∨ ∃ outcome z, `JHoleAt r z` ∨ ∃ Z', XTopAt r z): no pending line
    → `JHoleAt` (msAr); pending line → `JIrqHyp`.
  * `hPre_of`: `invoke_afterJ`'s `hPre` for `Q := PPQ`; `dispatch_invokeJP` / `dispatch_invokeJEP` =
    `dispatch_invokeJ`/`JE` without `hPre`.
- PREMISES (hPre, a ∀ over JAtPre states with an arbitrary Q, is replaced in dispatch_invokeJP/JEP by):
  * `IrqPlat arI AR` [P] (M4; l4v: `getActiveIRQ` is the machine's IRQ oracle): `take_pending_irq a ⦃ r => ∃ irq ms,
    doMachineOp (getActiveIRQ true) σ = {(irq, {σ with machineState := ms})} ∧ (r.1 = NO_IRQ ↔ irq = none) ∧
    (∀ i, irq = some i → r.1.val = i.toNat ∧ ms.irqMasks i = false) ∧ ms.underlyingMemory = σ.….underlyingMemory ⦄`,
    and `take_pending_irq` keeps AR.
  * `JIrqHyp` [W] (l4v `handle_interrupt_corres`): for a `JHoleAt` state σ, `w.val = i.toNat`,
    `σ.machineState.irqMasks i = false`: `handle_interrupt s a w ⦃ r => (handleInterrupt i σ).2 ∨ ∃ z ∈
    (handleInterrupt i σ).1, ∃ Z', XTopAt AR Z' r.1 r.2 z.2 ⦄`. Post XTopAt, not JHoleAt (a JHole's spec state differs
    from its base only in machine state/time words; the timer branch sets reprogramTimer, a signal changes the heap).
    The spec-failure disjunct covers an inactive line (spec `fail`, FL4 masks it; l4v excludes it by
    `valid_irq_masks`, not carried by JHoleAt). Known deviations to check when proving it: IPI lines (FL4 IRQ_IPI /
    `smp::handle_ipi` vs spec irqReserved / `handleReservedIrq`), the ARMED node word in the timer branch.
  * `JPreemptRestHyp` [W]: `after_invocation (Err Preempted) ⦃ PPQ ⦄` at `JHoleAt` states with
    `¬ (PPCov σ ∨ PPCovT σ)`: a reschedule pending without CurInv (e.g. the thread deleted its own SC: kp1's
    unbound-current-SC case), the idle thread current, a switch to the current thread pending, the endpoint-handler
    case with waiting receivers / reschedule pending / queued or RUNNING_VM thread, the handler case with an RR SC is
    in PPCov via NoTmoSend. PPQ's weak disjuncts (spec failure, XTopAt only) keep it from being false.
  * plus `ARKeep`, `ArchTotal`, `numDomains = 1`, `PPPlat` [P], `∀ a, max_release_time …` [P] (as elsewhere).
- NOT DONE: (a) of the brief (current-thread timeout send to a waiting receiver from a JTH; RUNNING_VM third
  disjunct of NoTmoSend) — untouched; the latter would also shrink JPreemptRestHyp. `JIrqHyp` (handle_interrupt at
  J: the signal case is the notifLeafJ / send_signal route at J; the timer case is two node words). The chooseNewThread
  case of the preemption path (CurInv missing: `chargeBudgetJ` variant for an unbound current SC). PPQ's `JHoleAt`
  is not `JAtZ` (OffOK may fail after a time update; schedule at J (M7) would need a JHole start or PPR0-style facts).
- Builds: kp6-c* (`lake env lean` checks, scratch/kp6chk.sh), kp6-b2..b5 (`XTopJointPPH XTopJointPreempt`, 5110/5404
  jobs) OK; scratch/axkp6.lean (untracked): std axioms only for pp_err_eq, JAtZ.ppJH, jAtPre_hole, JHole.msAr,
  JHole.mcsPPJ, JHole.afterInvJ, hPre_of, dispatch_invokeJP, dispatch_invokeJEP, handle_invocation_refinesJ.

## sch2 (branch par/sched2 in FL4-sc, on 073c67e5 = int/j2 incl. sch1)
- DONE 87f9493f (a) D1: new `Fl4Spec/Ext/Timer.lean` (generic `Z`): `fl4TimerSignal` (one `send_signal` outcome),
  `fl4TimerFire` (none or one signal, then `reprogram_timer := true`), `fl4TimerFires` (ReflTransGen),
  `fl4Awaken σ := ({p | fl4TimerFires σ p.2}, False)` (never fails), `mem_fl4Awaken`. Ext/Entry's `fl4CallKernel`
  runs `fl4Awaken` between the event and `schedule`; PORTING.md "FL4 differences" entry `Ext/Timer` + the
  `Ext/Entry` line. P3's `Fires` (ScAwaken) is NOT moved (ScAwaken's cone is 446 modules = a full build):
  `fires_iff : Fires σ σ1 ↔ Fl4Spec.fl4TimerFires σ σ1 := Iff.rfl` (XTopJointSchedR; the definitions are the
  same). FOLD LATER (at a lead full build): `def Fires := Fl4Spec.fl4TimerFires (Z := Unit)` etc. in ScAwaken.
  `jat_finishJ` restated: `∃ σ1 σ', ((), σ1) ∈ (fl4Awaken σ).1 ∧ (schedule >>= fun _ => activateThread) σ1 =
  {((), σ')} ∧ ((), σ') ∈ ((fl4Awaken >>= fun _ => schedule >>= fun _ => activateThread) σ).1 ∧ RJ ∧ JAtZ`
  (membership: `fl4Awaken` is nondeterministic, so "one outcome" is per chosen `σ1`). D2: `hvm` tagged [S]
  (scope, NativeScope) in JAtZ.activateJ / jat_finishJ docstrings; Fl4Spec's activateThread unchanged.
  Build sch2-b1 (Ext.Entry's cone: XTopJointSchedR + the 13 XTopJointRecv*/YieldSys modules) 5428 jobs OK.
- PARTIAL (b) domainTime = 0, new leaf ScNextDom (imported from Fl4Proofs.lean): the pieces both sides compute.
  * `DomListOK σ` [J]: l4v `valid_domain_list` (DetSchedDomainTime_AI, `rt`: `1 < length`, time 0 only in the end
    marker, `start < length`, `dlist ! start ≠ (0,0)`, last entry `(0,0)`, `index < length - 1`) + every entry's
    domain 0 (FL4 `numDomains = 1`; l4v's own note on `valid_domain_list_2`: "domains ... should also be ≤
    maxDomain"). Not carried by any invariant yet (l4v keeps it by `next_domain_valid_domain_list`,
    `domain_set_start_valid_domain_list_inv`, `domain_schedule_configure_valid_domain_list_inv`; spec init
    `[(0,-1),(0,0)]` satisfies it). With DomRel's length 2: `DomListOK.idx0` (index 0), `start0` (start 0),
    `last1` (entry 1 = end marker).
  * `nextDomain_eq`: spec `nextDomain σ = {((), ndSt σ (ucast 64 d))}` (`ndSt` = index 0, domain 0, domain time
    `d`, `reprogram_timer`; work units = extended op, none at `Z = Unit`).
  * `next_domain_eq`: FL4 `next_domain s = ok (ndS s dur0)` (IDX := 0, REPROGRAM := 1, WORK_UNITS := 0,
    CUR_DOMAIN := 0, DOMAIN_TIME := entry 0's duration word), from IDX = START = 0, entry 1 duration 0, entry 0
    domain 0; `next_domain_words` gives those from `DomRel` + `DomListOK` + `hidx : (m (ksW kb 24)).val =
    σ.domainIndex` ([J] too: FL4's DOM_SCHED_IDX word is in no relation; true: boot 0/0, ScheduleSetStart
    writes 0 vs `length - 2` = 0, next_domain writes START vs `domain_start_index`), and `ucast 64 d =` the word.
  * NOT DONE (route, all new code in leaves; ScScheduleTop's cone is 445 modules, do not edit it):
    (1) spec `archPrepareNextDomain` = `switchLocalFpuOwner none` (FPU save into the owner's TCB, owner := none,
    FPU disabled; FL4: nothing, its FPU switching is behind `machine.Arch`): same nature as `ArchSw`'s
    `archSwitchToThread` (which also runs `lazyFpuRestore`/`switchLocalFpuOwner (some t)` yet is assumed with
    `ArchKeeps`, i.e. `kheap` unchanged): add an `ArchSw`-style arch hypothesis for it (∃ one outcome, SchedRel/
    NtfnStateRel kept, `ArchKeeps` + domain fields kept), or prove it from an FPU invariant (saved image of the
    owner = machine FPU) that does not exist; NOTE `ArchSw` itself relies on that unstated invariant.
    (2) `schedule_choose_new_thread_refines0` (dt = 0) at SchedRel: FL4 `next_domain` (ndS) then
    `choose_thread_refines` at (ndS s, ndSt σ'); SchedRel across the ks writes: copy `Sched.SchedRel.domW`
    (DomDecode) with the footprint {kb+16, kb+24, kb+40} (all in [kb+16, kb+216], so its `hm` argument applies)
    and the CUR_DOMAIN write of the same value 0 (`hcd`), `SchedRel.set_reprogram` (ScFrame) for REPROGRAM;
    NtfnStateRel by `.frame` (FootEq: ks/node words are no ntfn/TCB word), Inv/NSC unchanged fields (record
    update: likely defeq). Its post differs from the dt ≠ 0 lemma: `TK` (domainTime kept) fails, footprint
    `SFoot ∪ {ks 8,16,24,40}`, `reprogramTimer` set.
    (3) copies of `cn_refines`/`cn_enq`/`cn_app`/`switch_branch_refines`/`schedule_refinesWP` with
    `hdt : σ.domainTime ≠ 0 ∨ (DomRel ∧ DomListOK ∧ hidx ∧ arch hyp)` (≈700 lines, mechanical except the TK/
    footprint posts: `hd4`-style transfers become "domain time kept or ndSt").
    (4) jat_scheduleFR's JAtZ reconstruction: KFoot ∌ ks words, so either widen the footprint used there or
    pass the ks writes through `JAtZ.ksW_*` frame lemmas (XTopJointDbgKeep `KsW`, DeadKeep `JAtZ.ksW_scKeep`;
    preemption_point's WORK_UNITS write at J is handled in XTopJointPP — reuse), `SchStep` (ScXSched) keeps
    domainList/domainStartIndex (fine), DomRel after (`DomRel.of_same`, entries untouched).
    Then jat_scheduleFR/SR/jat_finishJ take `hd : σ.domainTime ≠ 0 ∨ (DomRel .. ∧ DomListOK σ ∧ hidx)`;
    l4v also has `domain_time s = 0 → scheduler_action s = choose_new_thread` (DetSchedDomainTime_AI, for
    `1 < numDomains`; with one domain it is not needed: the resume branch never reads the domain time).
- NOT DONE (c) M6. FINDING from l4v (`rt`, Syscall_AI): `he_invs` for SysReplyRecv/NBSendRecv/NBSendWait gets the
  receive's precondition `invs and ct_active` (`hw_invs`) from
  `handle_invocation_not_blocking_not_calling_first_phase_ct_active`: from `invs ∧ ct_active ∧
  scheduler_action = resume_cur_thread ∧ ct_schedulable`, `handle_invocation False False can_donate True cptr`
  ends in `ct_active`, because `decode_invocation True …` (first phase) rejects Thread/Domain/SchedContext/
  SchedControl/CNode caps (`InvalidCapability 0`, `decode_invocation_safe_invocation`: `safe_invocation`) and a
  safe non-blocking non-calling `perform_invocation` keeps `ct_active`
  (`perform_invocation_not_blocking_not_calling_ct_active`, needs `fault_tcb_at None ct`). Both Fl4Spec's
  `fl4DecodeInvocation firstPhase` (Ext/Invocation) and FL4's `decode_invocation(first_phase)` (syscall.rs:119-147)
  have the same rejection, so sch1's example (NBSendRecv on the own TCB cap's Suspend) cannot occur.
  l4v requires NOTHING about the scheduler action at the receive (`hw_invs` = `invs and ct_active`); the mid
  action may be `switch_thread t` (reply/send waking a thread: `possible_switch_to`) or `choose_new_thread`
  (`reschedule_required` inside `possible_switch_to` when an action is already pending, timeout paths, …).
  So sch1's `JMid` (with `action ≠ chooseNewThread`) is FALSE in reachable mid states; the right mid
  precondition is l4v's: `CurRun σ` (ct_active: running/restart; `Restart` is set by handle_invocation and reset
  to `Running` on success) + not idle + whatever JAtZ already has, with the receive leaves generalised over the
  action (uses (1) `J.curInv (hni.2 ▸ …)` and (3) `Or.inl hni.2` of sch1's list must handle `chooseNewThread`
  and `switchThread t`, t ≠ ct, not only resume). Route: (i) a post fact of `handle_invocation_refinesJ` for
  `firstPhase = true, blocking = calling = false`: `CurRun` at the Ok outcome (decode-path by decode path, as
  l4v: the first phase leaves only Endpoint/Notification/Reply/Untyped/IRQ/arch caps); (ii) the receive at J
  from `CurRun ∧ ¬idle` with any action: check `JRecvIpcHyp`'s leaves (`recvIpcBlock*`, `recvIpcBound*`) —
  ke13 already handled `cnN` (chooseNewThread) for the passive server; where `CurInv` is used, replace it by
  the `CurInv`-free facts (CurInv is only needed under `resumeCurThread`). The receive-file signature change
  was NOT made: replacing `hni` by sch1's JMid would bake in a premise that is false in reachable states.
- Builds: sch2-b1 (D1, 5428 jobs), sch2-b2 `ScNextDom XTopJointSchedR` 5384 jobs OK; axioms (sch2ax.sh/axsch2.lean,
  untracked): std only for jat_finishJ, jat_scheduleFR/SR, handle_invocation_refinesJ, fires_iff,
  mem_fl4Awaken_of, nextDomain_eq, next_domain_eq, next_domain_words, DomListOK.start0.
## kp7 (branch par/budget3 in FL4-tcbj, on ca33ecc3 = int/j2)
- DONE 41f1a808 (new leaves SchedArmed, XTopJointIrq, imported from Fl4Proofs.lean; std axioms): scope (a),
  `JIrqHyp` [W] is now a theorem (`jIrqHyp_of`) up to a narrow signal premise.
  * Correspondence decided (XTopJointIrq docstring): line > FL4 `irq::MAX` (127) = spec `irq > maxIRQ` (mask + ack on
    both sides, arch vs machine ops); state word 0 = spec `irqInactive` (spec fails: JIrqHyp's failure disjunct); 2 =
    timer (FL4 `REPROGRAM := 1`, `ARMED := 0`; spec `reprogram_timer := True`, `ackDeadlineIRQ` no-op); 3 (`IRQ_IPI`)
    and every other word = spec `irqReserved` (`handle_reserved_irq` no-op; FL4 `handle_ipi` is a no-op off
    `RESCHEDULE_IPI`); 1 = signal (IRQ node slot cap via `IrqRel.node` + `IntLayout.node` + StateRel, notification cap
    with send right: `send_signal` both sides, then the mask). DECISION IPI: the IPI lines 126/127 never reach
    `handle_interrupt` -- new field `IrqPlat.noIpi` [P] (one core; l4v is uniprocessor, seL4 C raises IPIs only under
    `ENABLE_SMP_SUPPORT`). Without it JIrqHyp is false at line 127 (FL4 `reschedule_required`, spec masks the line).
  * XTopJointPreempt edits: `IrqPlat` += `noIpi`, `ackAR` [P] (`ack_irq` keeps `AR`); `JIrqHyp` takes
    `w.val ≠ 126 → w.val ≠ 127 →`; `afterInvJ` passes them from `noIpi`.
  * `Sched.SchedRel.set_armed` (SchedArmed): writing node offset 80 keeps `SchedRel` with the spec unchanged
    (`SAgree`/`CAgree` ask offset 80 to agree, so the agreement proofs are redone with 80 exempt). Timer branch:
    `xtop_sc_step` from the hole (node words are `TFoot`), `NtfnStateRel.frame`.
  * `XTopAt.msAR` (machine state with the same memory + an `AR` arch state); spec membership lemmas
    `mem_hi_big/_reserved/_timer/_signal`, `fail_hi_inactive` (NB: `handleInterrupt`'s arms carry the final
    `ackInterrupt` inside, right-nested binds).
  * Signal at `J`: from a hole with `OffOK ∧ CurOwnW`, `JHole.toJ` + ScSignalJ's `signalJHyp_of`; its
    `SignalRestJHyp` (bound thread RunningVM) discharged by `hNS` [S].
- PREMISES now (jIrqHyp_of / hPre_ofI / dispatch_invokeJPI / dispatch_invokeJEPI; JIrqHyp gone from the latter three):
  * `hNS : ∀ s a σ, JHoleAt arI AR s a σ → NativeScope σ` [S] (VT-x outside the native scope; sch1's `hvm`).
  * `JIrqSigHyp arI AR` [W]: `∀ Z H Cs Ac Lst D s0 a0 σ0 s a σ w n badge r, JHole … s0 a0 σ0 s a σ →
    ¬ (OffOK σ ∧ CurOwnW Z.T Z.C σ) → w.val < 128 → capAt (L.mem s) (nodeA (L.ksb s) w) = ok (.Notification n badge
    true r) → send_signal s a n badge ⦃ r' => ∃ z ∈ (sendSignal n.bv badge.bv σ).1, ∃ Z', XTopAt AR Z' r'.1 r'.2 z.2 ⦄`.
    A proof gap, not an invariant: only the sufficient-head branch of `mcs_preemption_point` reaches
    `check_interrupt` at a non-`JAtZ` hole (all charge branches end at `JAtZ`); there `OffOK` needs l4v
    `cur_sc_offset_ready` (`OffReady`) at the hole, which `JHole` does not carry. Ways out: carry `OffReady` through
    the invocation (JEntryAt.rd0 holds at entry; `update_timestamp` keeps it, modulo time wrap) into `JHole`, then
    `OffReady.ok` + sufficiency give `OffOK`, `curOwn_of_curInv` gives `CurOwnW` (PPCov/PPCovT carry CurInv) — that
    also gives schedule-at-J (M7) a `JAtZ` start after the preemption path; or a frames-from-the-base signal
    (ScChargeH/T style, ~6 branches: large).
  * `JPreemptRestHypN arI AR` [W] = `JPreemptRestHyp` with an extra `NativeScope σ →` (a RUNNING_VM current thread is
    `hNS` [S]); `jPreemptRestHyp_of` gives the old one.
  * unchanged: `IrqPlat` (now with noIpi/ackAR) [P], `PPPlat` [P], `ARIface` (was `ARKeep`; the mask), `ArchTotal`,
    `numDomains = 1`, `max_release_time` [P].
- NOT DONE (b) beyond the RUNNING_VM case. Findings for the remaining `JPreemptRestHypN` cases:
  * switch to the current thread pending: excluded in l4v by `scheduler_act_sane`; not carried by `JAtZ`/`JHole`
    (Inv/ActIdle/CurRunM do not say it). A ∀-JHoleAt premise would be false at unreachable JHoleAt states; it has to
    be carried as a post of the invocation (like sch1's M6 `JMid`) or added beside JAtZ.
  * idle current: the invoker is never idle (Entered at entry, invocations keep curThread), same carrying problem.
  * reschedule pending without CurInv (kp1's unbound current SC): needs a `chargeBudgetJ` variant for an unbound /
    no-owner current SC (P1 `hcsc`/`hts` vacuous) and the inactive-SC branch (node CONSUMED := 0).
  * endpoint handler with waiting receivers (kp5 (i)): current-thread `sendTmoRecvIJ/PJ` from a `JTH` (~1200 lines).
- Builds: kp7-c1..c4 (`lake env lean` checks, scratch/kp7chk.sh), kp7-b1 (`SchedArmed XTopJointPreempt XTopJointIrq`,
  3704/5404/5408 jobs), kp7-b2 (+ `XTopJointEntry`); scratch/axkp7.lean (untracked): std axioms only for
  SchedRel.set_armed, jIrqHyp_of, hPre_ofI, dispatch_invokeJPI, dispatch_invokeJEPI, hPre_of, JHole.afterInvJ,
  handle_invocation_refinesJ.

## kp8 (branch par/budget4 in FL4-tcbj, on 21c0a352 = int/j2 incl. kp7, sch2)
- DONE c155f952 (new leaf XTopJointPreemptZ; XTopJointIrq edited; std axioms): scope (1), `JIrqSigHyp` [W] DELETED
  (not needed by the new top theorems; still defined, used only by the old `jIrqHyp_of`/`hPre_ofI`/`*PI`).
  * No OffReady carried through the invocation was needed: the hole's time words are the base's shifted by one
    `update_time_stamp` (`TShift σ0 σ` := `σ0.curTime ≤ σ.curTime ∧ σ.consumedTime = σ0.consumedTime + (σ.curTime -
    σ0.curTime)`), and the base is `JAtZ`. `jAtPre_holeT`: every `JAtPre` state is a `JHole` with `TShift` (first
    disjunct: `TShift.refl`; second: `pp_err_eq` + `updateTimeStamp_eq'` + `PPPlat.now`/`.irq`, spec only, no
    change to `JHole`, `ppJH` or `JAtPre`).
  * `JHole.offOK_suff`: shifted hole + `CurInv` + non-idle schedulable current thread + sufficient head ⇒ `OffOK`
    (positive consumed time at the base: `J0.off`; zero: `J0.inv.rd` of the runnable, bound, unreleased current
    thread = released head; then `rdy_shift`). This is l4v's `cur_sc_offset_ready` for the sufficient branch.
  * `JHole.mcsPPJZ` (= `mcsPPJ` with `JAt` after in every branch), `JAtZ.msArJ`, `JIrqHypZ`/`jIrqHypZ_of`
    (`handle_interrupt` from `JAt`: `JHole.handleIrqJ` over `J.toHole`, signal premise refuted by `J.off`/`J.own`;
    `JHole.handleIrqJ` is kp7's `jIrqHyp_of` body with a per-hole signal premise, `jIrqHyp_of` now a wrapper),
    `JHole.afterInvJZ` (post `PPQZ`: spec fails ∨ outcome with `JAt` (no line pending: the post-budget-check
    state IS `JAtZ`, for M7) ∨ `XTopAt` (handled line); `PPQZ.toPPQ`), `hPre_ofZ`, `dispatch_invokeJPZ/JEPZ`.
- DONE b7ec37e6 (new leaf XTopJointPreemptI, std axioms): (b), the inactive-SC branch (the reachable shape of
  "reschedule pending without CurInv" after the thread finalised its own SC: l4v unbinds and zeroes refill_max,
  cur_sc stays). `PPCovI σ` := `schedulable σ.curThread σ = false ∧ ∀ x n, σ.kheap σ.curSc = some (.schedContext
  x n) → scActive x = false`. `JHole.mcsPPJI`: from ANY `JHole` (no CurInv), FL4's node `CONSUMED := 0` vs spec
  `consumed_time := 0` (`SchedRel.set_node_consumed`, `consumed0_bxi`, `xtop_sc_step` from the base, KFoot
  node word), `JAt` after (`toJ`: OffOK vacuous at 0, CurOwnW = the base's). `afterInv_of_mcs` (afterInvJZ
  generic in the budget part), `hPre_ofZI`, `dispatch_invokeJPZI` / `dispatch_invokeJEPZI`.
- PREMISES of `dispatch_invokeJEPZI` (the new top): `ARIface`, `ArchTotal`, `numDomains = 1`, `PPPlat` [P],
  `max_release_time` [P], `IrqPlat` [P], `hNS` [S] (unchanged), and
  `JPreemptRestHypI arI AR` [W] := `∀ s a σ, JHoleAt arI AR s a σ → NativeScope σ → ¬ (PPCov σ ∨ PPCovT σ ∨
  PPCovI σ) → after_invocation s a (.Err .Preempted) ⦃ r => PPQ arI AR σ (r.2.1, r.2.2) ⦄`
  (= kp7's `JPreemptRestHypN` minus the inactive-SC case; `jPreemptRestHypI_of : JPreemptRestHypN →
  JPreemptRestHypI`). `JIrqSigHyp` gone. Nothing added.
- LEFT in `JPreemptRestHypI` (findings):
  * (a) switch to the current thread pending / idle current thread. NoSwitch is ALREADY carried by the deletion
    loop: `WJ` (XTopJointDelR) has `Vs.NoSwitch σ` (no switch at all), and `WJP`'s base is a `WJ` state, but
    `JAtPre`'s second disjunct (built at XTopJointCnDel:187, XTopJointWJLRestart:150, XTopJointTcbInstall:1114
    from WJP, and UtResetZ `JAtZ.jAtPre_pp` from the reset loop UtResetLoopJ:325) drops it. Route: second
    disjunct `∃ s0 a0 σ0, (JAt s0 a0 σ0 ∧ NoSwitch σ0 ∧ σ0.curThread ≠ σ0.idleThread) ∧ pp ∧ mem`; NoSwitch from
    WJ at the three WJP sites; the reset loop carries no NoSwitch (UtResetLoopJ/UtResetTopJ: none) — add it to
    its loop invariant (the reset never touches the action: `Entered` at the decode gives resumeCurThread).
    ct ≠ idle is carried by neither loop: add `σ.curThread ≠ σ.idleThread` beside PPR0 in WJR/WJL and the reset
    loop (kept by every spec step there: curThread/idleThread are unchanged by finalise/reset frames; from
    `Entered` at the invocation start). The first disjunct of JAtPre (Or.inl via hXP for non-preempting caps) is
    only formal for preempted outcomes; it would need the facts too unless those statements are narrowed. Then
    `ppJH` keeps both (action/curThread/idleThread unchanged), and `PPCov`'s `hni`/`hnsw` follow for JAtPre
    states, which shrinks `JPreemptRestHypI` to the CurInv-less active-SC and kp5 (i) cases. Size: JAtPre edit +
    ~6 construction sites + 3 loop invariants; several module rebuilds (XTopJointTcbInstall, TcbSsp, CnDel,
    WJLRestart, UtReset*, XTopJointEntry cone).
  * (b') reschedule pending, current SC ACTIVE but not the current thread's (e.g. SchedContext Unbind of the
    own SC, or a pending reschedule with the SC re-bound): `charge_budget c false` of an unowned active SC.
    `chargeBudgetJ` uses CurInv only through `CurInv.facts` (`htw` SC TCB word = cur thread, `hts` thread SC
    word = cur SC, `hnr`, `hnb`) fed to ScChargeG `charge_budget_refinesF` and P1 `charge_budget.allF`
    (`hcsc1` vacuous if the thread's SC word is 0) — needs a `charge_budget_refinesF` copy without htw/hts
    (the spec head/tail do not read the owner; `reschedule_required` already pending) and `CurOwnW`'s second
    disjunct after. Not started.
  * (c) kp5 (i) (endpoint timeout handler with waiting receivers) untouched.
- Builds: kp8-b1 (`XTopJointIrq` 5410 jobs; PreemptZ failed on one rw), kp8-b2 (`XTopJointPreemptZ` 5412),
  kp8-ax1 (+ `XTopJointEntry` 5372, scratch/axkp8.lean), kp8-c1/c2 (`lake env lean` checks, kp7chk.sh), kp8-b4
  (`XTopJointPreemptI` 5414, scratch/axkp8b.lean; both untracked): std axioms only (propext, Classical.choice,
  Quot.sound) for jAtPre_holeT, JHole.offOK_suff, JHole.mcsPPJZ, jIrqHypZ_of, JHole.afterInvJZ, hPre_ofZ,
  dispatch_invokeJPZ, dispatch_invokeJEPZ, JHole.mcsPPJI, afterInv_of_mcs, jPreemptRestHypI_of, hPre_ofZI,
  dispatch_invokeJPZI, dispatch_invokeJEPZI, jIrqHyp_of, dispatch_invokeJEPI, handle_invocation_refinesJ.
## sch3 (branch par/sched3 in FL4-sc, on d6bc987c = int/j2 incl. sch2)
- (b) domainTime = 0, schedule level. New leaves ScNextDomB, ScNextDomC (imported from Fl4Proofs.lean; ScScheduleTop
  untouched). No existing theorem changed; JAtZ untouched.
  * ScNextDomB: `DI m` (outcomes keep `domain_index`; combinators + `di_awaken`: the spec's `awaken` keeps it —
    SchStep/SOK keep the domain list/start but not the index, which `next_domain` writes); `TK0` (= `TK` without
    the domain time); `NdW` (ks DOMAIN_TIME/DOM_SCHED_IDX/WORK_UNITS), `SFootN = SFoot ∪ NdW`, `KFootN = KFoot ∪ NdW`
    (+ `sfootN_trans`, `kfootN_trans`); `NdOK s σ := DomRel ∧ DomListOK σ ∧ IDX word = domain_index` (the two [J]
    facts of sch2, unchanged; hidx NOT folded into DomRel/SchedRel: SchedRel's cone is the 445-module one, and a
    DomRel field would have to be re-proved by every DomRel producer); `NdOK.keep/sfoot/sfoot'` (kept by SFoot
    writes); `ndS_writes` (footprint of FL4's next_domain: NdW + node REPROGRAM; CUR_DOMAIN rewritten with its
    value 0), `schedRel_ndS` (SchedRel at `ndS s t`, `ndSt σ t.bv`), `ntfnRel_ndS` (needs `hNk`: notifications
    off the ks block, = JAtZ.nk), `ks_not_sfoot`; `ArchNd` [P] (below); `scnt_refines0`:
    `schedule_choose_new_thread` for `σ.domainTime ≠ 0 ∨ NdOK s σ` (0 case: next_domain_eq + nextDomain_eq after
    archPrepareNextDomain, then `choose_thread_refines` at `ndS s t`/`ndSt σa t.bv`), post with `TK0`, `SFootN`.
  * ScNextDomC: `SchedPreW0` (SchedPreW minus the domain time), `awaken_refinesW0`, `cn_refines0`,
    `cn_enq0`/`cn_app0`, `switch_branch_refines0`, `schedule_refinesWP0` (copies; hfire's post carries
    `SchedPreW0 ∧ ((dt ≠ 0 ∨ NdOK r.1 σ1) ∧ hNk at r.1 ∧ Pf)`, extra `hAN : ArchNd`; post footprint `KFootN`; the
    NdOK transfer across awaken uses `schs_awaken` (dl/dsi) + `di_awaken`, across the ct enqueue `schs_when`/
    `di_when`).
  * `ArchNd st N T C c` [P] (l4v `arch_prepare_next_domain` = X64 `switch_local_fpu_owner None`; FL4: nothing):
    `∀ s σ, SchedRel s σ → NtfnStateRel s σ → ∃ σ1, archPrepareNextDomain σ = {((), σ1)} ∧ SchedRel s σ1 ∧
    NtfnStateRel s σ1 ∧ ArchKeeps σ σ1 ∧ domainList/domainIndex/domainStartIndex kept`. CHECKED: NOT TRUE in
    every reachable state. The spec's owner is set by `lazyFpuRestore` in every `archSwitchToThread` to a thread
    without `fpuDisabled`; then `switchLocalFpuOwner none` saves the machine FPU image into the owner's `tcbArch`
    (`asUser … setFPUState`) and clears its `tcbCurFpu` (`setX64CurrentFpuOwner`), so `kheap` changes (only inside
    that TCB's `tcbArch`, registers kept: the shape of XTopFpuRel's `fpuRelease_outF`). FL4's lazy FPU (arch
    backend, `machine.Arch`) does keep the owner live across `next_domain`: there is no FPU-boundary at a domain
    switch in FL4 — harmless with `numDomains = 1` (the release exists in l4v for domain separation of FPU state),
    but the spec states differ in `tcbArch`/owner. Same defect as `ArchSw`'s `archSwitchToThread` (sch2 finding).
    Fix route for both: replace `ArchKeeps`'s `kheap` equality by "equal up to TCB `tcbArch` with registers kept"
    (`fpuRelease_outF` normal form) through choose_thread/switch_to_thread posts and `SchStep` (its `OTK` already
    tolerates it: `schs_switchLocalFpuOwner`), J side via `JAtZ.tcbArchJ`.
  * NOT DONE (J side, `jat_scheduleFR2` and `jat_finishJ` without `hd`). Route (checked against the code):
    from J1 (after fire, at rf/σ1) build J0 at a *fake pre-state* `s0 := rf.1` with ks16/ks24/ks40 set to their
    values in the final `r.1`, spec `σ0 := {σ1 with domainTime := σ'.domainTime, domainIndex := σ'.domainIndex}`:
    ks40 by `JAtZ.workUnitsJD` (XTopJointPP), ks16/ks24 by a SchedStep copy of DomDecode's `schedStep_start`
    (domW + blkKeep_domKW) through `stepClosed_jat`'s sched case (XTopAt.schedStep + jowes_sched + cs_frame,
    keeps Z.G/Z.vs). Then `WritesIn s0 r.1 (KFoot s0 σ0)` is immediate from WP0's `KFootN` post, and every
    spec fact transfers by defeq (`SchStep`, `LK`, `SOK`, IK, `RunM` read no domain time/index), so the rest of
    `jat_scheduleFR` runs from J0 with a `sch_tail` copy taking `SchS σ0 σ'`, the IK facts and `bsa` directly
    (instead of `schedule σ0 = {σ'}`, false for σ0). hTail's footprint argument becomes `KFootN`. Missing
    piece for the entry: NdOK at the post-fire state from NdOK at entry — needs `Fires` to keep
    domain_index/list/start (DI for `sendSignal`: cancelIpc subtree, not done; dl/dsi from a Pres lemma) and
    FL4's `timer.fire` to keep ks24 (P1 `FootD`/`KW`: check `Sg` excludes ks24).
- (c), (d): not started (context). (d)'s statement is the ArchNd/ArchSw finding above: the FPU invariant that
  would make `ArchKeeps` true does not exist in the spec (no reachable invariant makes the owner's saved image
  equal the machine's: user code runs in between); the right fix is the frame weakening, not an invariant.

## kp9 (branch par/budget5 in FL4-tcbj, on 2f97adc4 = int/j2 incl. kp8)
- FINDING (blocks kp8's route (a) as written): `JAtPre`'s FIRST disjunct (`JAt` itself) is not "only formal" in a
  way the proofs can ignore. It is produced by `hPre := fun _ _ _ h => Or.inl h` / `hXP` at ~35 sites
  (XTopJointEntry `decOK_J`: every cap but CNode/Thread/Untyped; XTopJointWJLRestart: CNode Copy/Mint/Move/Mutate/
  Rotate, illegal labels, CancelBadgedSends; XTopJointTcb:2804: the Thread cap's other labels; XTopJointTcbSsp /
  XTopJointTcbInstall: the decode-error outcomes of the five installing labels), and `hPre_of*` must then run the
  preemption path from an arbitrary `JAt` state (ct may be idle, a switch to ct may be pending). So adding
  `NoSwitch σ0 ∧ ct ≠ idle` to the SECOND disjunct alone shrinks nothing: `JPreemptRestHypI` is still needed at
  every `JAt` state. Neither fact can be put on the first disjunct either (after an invocation `NoSwitch` is false
  in general; `ct ≠ idle`/`scheduler_act_sane` would have to be threaded through every invocation).
- ROUTE (decided): DELETE the first disjunct. A preempted outcome only comes out of a preemption point, so at every
  `Or.inl` site the outcome `Preempted` is impossible:
  * error branch of `TopPostDMX`: `ErrRel .Preempted e'` is false (`ErrRel.not_preempted`);
  * invocation branch: the spec's `fl4PerformInvocation` returns `.error ()` only for `PreInv` invocations
    (Untyped, CNode Revoke/Delete, TCB ThreadControlCaps, ThreadControlSched with a fault handler), and the decode
    of the site's cap/label yields none of them.
- DONE (new leaf SpecNoPre, spec side only, checked with `lake env lean`, std axioms only):
  `NoPre.NoErrE`/`OkP` (+ `liftE`/`pure`/bind/`liftME` lemmas), `NoPre.PreInv`, `NoPre.perform_noErr` (every
  non-`PreInv` invocation never returns `.error ()`), `NoPre.dec_noPre`/`decOut_noPre` (a cap other than
  CNode/Untyped/Thread decodes to no `PreInv`), `NoPre.dec_cnode_noPre` (CNode decode at a label ≠ Revoke/Delete),
  `NoPre.dec_tcb_noPre`/`dec_thread_noPre` (TCB decode at a label not among Configure/SetSchedParams/
  SetTimeoutEndpoint/SetIPCBuffer/SetSpace; SetPriority/SetMCPriority decode to ThreadControlSched with no fault
  handler), `ErrRel.not_preempted`, `TopPostDMX.not_preempted` (a `TopPostDMX` outcome whose decoded invocations
  are all non-`PreInv` is not `Preempted`).
- NEXT (the many-module part, in this order; one cone build at the end):
  1. XTopJointCnDel: import SpecNoPre; `JAtPre := ∃ s0 a0 σ0, (JAt s0 a0 σ0 ∧ Vs.NoSwitch σ0 ∧ σ0.curThread ≠
     σ0.idleThread) ∧ pp ∧ mem` (first disjunct gone); `TopPostDMX.toPN (h) (hnp : ∀ inv, DecOut m σ inv →
     ¬ PreInv inv) : TopPostDMXP X XP` (any XP: `TopPostDMX.not_preempted` + `if_neg`), `XCap.toPN` likewise,
     `TopPostDMX.errP` for an explicit error outcome (`ErrRel.not_preempted`, no hnp).
  2. Replace every `Or.inl` `hPre`/`hXP` (list above) by `toPN` with `decOut_noPre` (via `DecOut.liftME`-style
     inversion: `dec_noPre … σ _ h.1 inv rfl`), `dec_cnode_noPre` (WJLRestart; labels from `hlbl` +
     `cnodeLabelOf`), `dec_thread_noPre` (Tcb:2804; labels from `hlbl`/`tcbLabelOf`), `errP` (TcbSsp/TcbInstall:
     all are `TopPostDMX.toP (Or.inl ⟨…⟩) hXP`, mechanical). TcbSsp:921 is an `.Ok` outcome (`ifP_ok`).
  3. Facts at the preemption point's base: the deletion loop has `Vs.NoSwitch` in `WJ`, but `ct ≠ idle` in no loop.
     Cheapest: put `σ.curThread ≠ σ.idleThread` into `WJP`'s base (`WJ … ∧ σ0.curThread ≠ σ0.idleThread`) and into
     `WJR` beside `PPR0` (kept: finalise/insert frames keep curThread/idleThread — add a `curThread`/`idleThread`
     equality to the step posts where missing), from `Entered` at the decode (`hni`, already passed to
     `decode_invocation_cnode_*JL`, `thread_control_capsJ`). The reset loop (UtResetLoopJ/UtResetTopJ) needs both
     facts in its invariant, from `Entered` at the Untyped decode (`JAtZ.utResetJ` callers have `hni`).
     `JAtZ.jAtPre_pp` takes `NoSwitch σ` and `ct ≠ idle`.
  4. Consumers: `jAtPre_hole`/`jAtPre_holeT`/`hPre_of*` lose the first case; from the second, `pp_err_eq` (σ is σ0
     with the time updated) moves both facts to the hole, giving `PPCov`'s `ct ≠ idle` and `action ≠ switchThread
     ct`. New premise `JPreemptRestHypJ` = `JPreemptRestHypI` with `σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ →`
     added (remaining cases: ¬CurInv with an active current SC = (2b), kp5 (i) = (2c)); `jPreemptRestHypJ_of`.
  Builds: XTopJointCnDel's dependents are the whole J cone (TcbInstall, TcbSsp, Tcb, WJL*, Ut*, Entry, Dispatch,
  Preempt*); expect one long cone build.
- (2b), (2c): not started.
- Builds: kp9-c1..c10 (`lake env lean` checks of SpecNoPre, kp7chk.sh), kp9-b1 (`SpecNoPre` 4206 jobs,
  scratch/axkp9.lean untracked): std axioms only (`ErrRel.not_preempted`: propext only) for perform_noErr, dec_noPre,
  decOut_noPre, dec_cnode_noPre, dec_tcb_noPre, dec_thread_noPre, ErrRel.not_preempted, TopPostDMX.not_preempted.
  Nothing in the existing cone was edited, so `handle_invocation_refinesJ` / `dispatch_invokeJEPZI` and their
  premises are unchanged from kp8 (JPreemptRestHypI [W] still present). Lean note: `unfold`/`simp only [f]` of the
  spec's big label matches (`decodeTcbInvocation`, the TCB sub-decoders) times out at 200000 heartbeats while
  generating equation lemmas regardless of `set_option … in`; use `delta f` + `generalize`/`cases` + `dsimp only`,
  and `with_reducible` for the syntax-directed `OkP` steps.
## sch4 (branch par/sched4 in FL4-sc, on 382b094a = int/j2 incl. sch3)
- (A) DONE: the arch premises up to the FPU. New leaves ScArchF, ScScheduleF, XTopJointSchedRF, ScNextDomF
  (imported from Fl4Proofs.lean; nothing in the 445-module cone changed; JAtZ untouched).
  * Check (1): no relation reads the spec's saved FPU image (`userFpuState`) or `tcbCurFpu` (only `userRegs`;
    XTopFpuRel/XTopJointFpu say the same, ScTK's TKObj already tolerates them) ⇒ frame weakening, not an
    invariant. `TcbFpuEq y x` (= but for `tcbArch`, `userRegs` kept), `HeapEqUpToFpu σ σ'` (heaps equal but
    for TcbFpuEq TCBs) + refl/trans/of_eq/eq_trans/trans_eq/tcb/tcb_back/ntcb/sc; frames `Inv.fpu`
    (via Inv.tcbView), `NSC.fpu`, `SzKeep.fpu`, `schedulable_fpu`, `OffOK.fpu`, `IdleOK.fpu`,
    `RunW.of_new2F`, `newcur_ofF`, `newcur_of2F`.
  * New [S] side condition `FpuOwnOK σ` (owner is none or a TCB; l4v X64 `valid_cur_fpu`): without it the
    spec's save `as_user owner …` FAILS for a dangling owner, so even the FPU-weakened premise would be false
    at (unreachable) SchedRel states. `OW m` (owner kept; copy of ScNextDomB's DI framework): `ow_awaken`,
    `ow_tcbSchedAction`, `ow_when`; `FpuOwnOK.of`.
  * `ArchKeepsF` (ArchKeeps with HeapEqUpToFpu; `ArchKeeps.toF`); `ArchSwF` [P]: thread part
    `∀ s a σ, SchedRel → NtfnStateRel → FpuOwnOK σ → ∀ t ∈ T, set_vm_root ⦃ ∃ σ1, archSwitchToThread t σ =
    {σ1} ∧ SchedRel ∧ NtfnStateRel ∧ ArchKeepsF σ σ1 ⦄`, idle part unchanged (`set_vm_root idle`: no FPU
    step, ArchKeeps true); `ArchSw.toF`. `ArchNdF` [P] (ScNextDomF): ArchNd with `FpuOwnOK σ →`, ArchKeepsF,
    and `σ1.archState.x64CurrentFpuOwner = none`. Remaining platform reading in both (as every arch premise):
    one outcome needs the opaque machine ops (enableFpuImpl, writeFpuStateImpl, readFpuStateVal, CR3 write)
    deterministic.
  * Chain copies (posts: `HeapEqUpToFpu σ σ'` for `σ'.kheap = σ.kheap`): `switch_to_thread_refinesF`,
    `choose_thread_refinesF` (ScArchF); `schedule_choose_new_thread_refinesF`, `sw_refinesF`, `cn_refinesF`/
    `cn_enqF`/`cn_appF`, `switch_branch_refinesF` (take `hfo : FpuOwnOK σ`), `schedule_refinesWPF` (extra
    `hPo : ∀ r σ1, Pf r σ1 → FpuOwnOK σ1`; FpuOwnOK carried σ1→σ2 by ow_awaken + Calm, →σ4 by
    ow_when/ow_tcbSchedAction + QChange, →σ6 in cn) (ScScheduleF); `scnt_refines0F` (ScNextDomF; the 0
    branch's switch state has no owner after ArchNdF).
  * J level (XTopJointSchedRF): `jat_scheduleFRF`, `jat_scheduleSRF`, `jat_finishJF` = the old proofs with
    `ArchSwF` and new premise `hFO : ∀ σ1, Fires σ σ1 → FpuOwnOK σ1` [S] (valid_cur_fpu after the timer
    signals; removal route: a DK-style "owner kept + TCBs kept" framework for `sendSignal` (AllDom's dk_auto
    pattern) plus FpuOwnOK carried as an entry invariant). These SUPERSEDE jat_scheduleFR/SR/finishJ; the
    lead's top chain should use jat_finishJF.
- (B), (C): not started (context). Next step for (B): copy ScNextDomC (awaken_refinesW0, cn_refines0,
  cn_enq0/app0, switch_branch_refines0, schedule_refinesWP0) as ScNextDomCF with the same perl renames used
  for ScScheduleF (σ'.kheap = σ.kheap → HeapEqUpToFpu σ σ', ArchSw → ArchSwF, ArchNd → ArchNdF, hfo
  threading, `hPo`), then sch3's jat_scheduleFR2 route on top of `schedule_refinesWP0F`.

## sch5 (branch par/sched5 in FL4-sc, on 4465e559 = int/j2 incl. sch4)
- (A) DONE da41487c (+ fires_dom in the (B) commit): `hFO` gone. `FpuOwnOK` re-tagged [J] (l4v X64 `valid_cur_fpu`,
  a reachable-state invariant; docstrings of ScArchF/ScScheduleF/ScNextDomF/XTopJointSchedRF). New leaf ScFpuOwnK:
  `OWK := FK owF` (VsDom's generic FK; `owF σ = (x64CurrentFpuOwner, domainIndex)`), leaves = SpecGlobFK's GK
  lemmas re-proved for `owF` over send_signal's cone (cancel_ipc, set_thread_state, maybe_donate_sc/
  sched_context_resume/postpone, possible_switch_to, refill checks, update_waiting_ntfn), `owk_sendSignal`,
  `owF_firesP`/`owF_fires` (Fires keeps owner and index), `fires_dom` (with AllDom's `dk_sendSignal'`: list, index,
  start). The "TCBs not deleted" half is NOT a spec framework: `fpuOwnOK_fires` (XTopJointSchedRF) takes the owner
  (a spec TCB at entry) into `Z.T` by `JAtZ.obj.tcb` (ObjCover) and back to a spec TCB after the timers by
  `NtfnStateRel.tcb` of the post-fire J. `jat_scheduleFRF`/`jat_scheduleSRF`/`jat_finishJF` now take
  `hFO : FpuOwnOK σ` [J] at the entry state only (was `∀ σ1, Fires σ σ1 → FpuOwnOK σ1` [S]).
- (B) PARTIAL.
  * DONE: ScNextDomCF (scripted copy of ScNextDomC with ScScheduleF's changes: `ArchSwF`/`ArchNdF`, `hfo` threaded,
    `HeapEqUpToFpu` posts): `cn_refines0F`, `cn_enq0F`/`cn_app0F`, `switch_branch_refines0F`,
    `schedule_refinesWP0F` (`hPo : ∀ r σ1, Pf r σ1 → FpuOwnOK σ1`, no hfo); supersedes `schedule_refinesWP0`.
  * DONE: XTopJointSchedRF2: `JAtZ.ndOK_fire` (NdOK entry → after FL4's timers: `fires_dom` spec side; FL4 side
    `timer.fire.kw`'s FootD misses ks words < 256: `kwApartJ` for KW, `JKern.hks`/node layout for DbgW);
    `jat_scheduleWP0F`: FL4 `schedule` from `JAtZ` with `hd : σ.domainTime ≠ 0 ∨ NdOK s σ`, `FpuOwnOK σ` [J],
    `ArchSwF`/`ArchNdF` [P], post at SchedRel level: `Fires σ σ1`, `schedule σ1 = {σ'}`, SchedRel/NtfnStateRel/
    NSC/Inv/CurInv/ActIdle at σ', `JAtZ` after the timers at `rf`, `WritesIn rf.1 r.1 (KFootN rf.1 σ1)`, the OffOK/
    RunW witness σ3. NdOK's two [J] facts (`DomListOK`, IDX word = domain_index; sch2) now needed only at entry.
  * NOT DONE: `jat_scheduleFR2` (JAtZ/RJ at σ' without `hd`) and `jat_finishJ2`. Route unchanged from sch3,
    starting from `jat_scheduleWP0F`'s post (exactly what `jat_scheduleFRF`'s proof destructures after
    `schedule_refinesWPF`, except KFootN for KFoot and no `hd`): build J0 at the fake pre-state
    s0 := rf.1 with ks16/ks24/ks40 set to their r.1 values and σ0 := {σ1 with domainTime := σ'.domainTime,
    domainIndex := σ'.domainIndex}: ks40 by `JAtZ.workUnitsJD` (XTopJointPP; spec unchanged), ks16/ks24 by a
    SchedStep (StepSem) like DomDecode's `schedStep_start` (domW + blkKeep_domKW; note `startS` also writes ks32,
    so a 2-word variant is needed) through `XTopAt.schedStep`/`stepClosed_jat`'s sched case. Then
    `WritesIn s0 r.1 (KFoot s0 σ0)` from KFootN (NdW words agree by construction), `SchStep σ0 σ'`/LK/SOK by defeq
    from σ1's (they read no domain time/index), and the rest of `jat_scheduleFRF`'s proof from J0 (sch_tail with
    `schedule σ1 = {σ'}` replaced by `SchS σ0 σ'` + IK + `bsa`: `JAtZ.sch_tail` reads `schedule σ = {σ'}` only
    through `schs_schedule`/`lkm_schedule`/`bsa_schedule`; copy it taking those three facts). hTail's footprint
    argument becomes KFootN.
- (C) M6: not started.
- Builds (tokyo, b.sh, module builds): sch5-b2 `ScFpuOwnK ScNextDomF XTopJointSchedRF` OK (5396 jobs; ScArchF/
  ScScheduleF rebuilt), sch5-b3 `ScNextDomCF` OK, sch5-b4 `ScFpuOwnK XTopJointSchedRF2` OK (5402 jobs), sch5-b5
  `XTopJointSchedRF2` OK. Axioms: axsch5.sh/axsch5.lean (untracked).

## kp10 (branch par/budget6 in FL4-tcbj, on 95724d05 = int/j2 incl. kp9 SpecNoPre)
- DONE (2a) = kp9 steps 1-4 (`JAtPre`'s first disjunct deleted). Deviation from kp9 step 3 (cheaper, same
  effect): the two base facts ride in `PPR0` instead of new conjuncts beside it.
  * ScPPR: `PPR0 σ := (σ.curThread ≠ σ.idleThread ∧ ∀ u, σ.schedulerAction ≠ .switchThread u) ∧ (old PPR0)`;
    `PPK` gains `ct`/`idle` equalities and `ns` (no switch kept); `of_cnK` (abs0), `of_ksStep`, `restart`
    (`stsAct` keeps the threads, sets at most `chooseNewThread`), `of_schedK` (now takes the post's NoSwitch;
    both callers have `hact5`), `updTcbSc`, UtResetTopJ's `delSt` frame. SpecPPR `PPR0.of_tr`/`ppr0_finaliseCap`
    take `hct hid hns`, supplied in XTopJointDelR `jFinPPHyp` from `dk_finaliseCap.ct`, `gk_finaliseCap.idle`,
    `ak_finaliseCap_ns`. XTopJointPP `ppJD` (post-time-update state: `rw [hσ2, hσ1]`), `ppr0_start` (from
    `Entered`), UtRetResetJ's restart split. So both loops (deletion WJR/WJL, Untyped reset) carry the facts
    with no new invariant conjunct.
  * XTopJointDelR: `WJP`'s base is `WJR` (was `WJ`); producers `jPreemptHyp_of`, `jPreemptHypL` pass `hp0`.
  * XTopJointCnDel: imports SpecNoPre; `JAtPre := ∃ s0 a0 σ0, (JAt s0 a0 σ0 ∧ Vs.NoSwitch σ0 ∧ σ0.curThread ≠
    σ0.idleThread) ∧ pp ∧ mem`; `TopPostDMX.toPne`/`toPN`/`errP`, `XCap.toPN`, `specDec_noPre`/`NoPreKind`/
    `specDec_noPreK` (any cap but CNode/Untyped/Thread, `(by trivial)`), `specDec_cnode_noPre`,
    `specDec_thread_noPre`. Constructions of the second disjunct: cn_del_topJ, WJLRestart cn_del_topJL,
    TcbSsp:856, TcbInstall:1116 (from WJR's NoSwitch + `PPR0.1.1`), UtResetZ `jAtPre_pp` (takes `PPR0 σ`).
  * The `Or.inl` sites: XTopJointEntry `decOK_J` (25 sites, `specDec_noPreK (by trivial)`), WJLRestart
    (`cnode_noPre_of`: copy/illegal/cancel labels ≠ 25, 26), Tcb `thread_noPre_of` (labels ≠ 5, 8, 9, 10, 11;
    no `split_ifs` on `tcbLabelOf` — it hits simp's step limit — but a by_cases chain), TcbSsp/TcbInstall
    (19 decode errors: `errP`; TcbSsp's Ok outcome: `toPne`), XTopJointUt's decode error (`errP`).
  * Consumers: PPH `jAtPre_hole`, PreemptZ `jAtPre_holeT` (one case); new `jAtPre_holeTN` (the hole has
    `ct ≠ idle` and NoSwitch: `pp_err_eq` makes it the base with the time updated).
  * PreemptI: `JPreemptRestHypJ arI AR` [W] := `∀ s a σ, JHoleAt arI AR s a σ → NativeScope σ →
    σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) → after_invocation s a
    (.Err .Preempted) ⦃ r => PPQ arI AR σ (r.2.1, r.2.2) ⦄` (`jPreemptRestHypJ_of : JPreemptRestHypI →
    JPreemptRestHypJ`), `hPre_ofZJ`, `dispatch_invokeJPZJ`, `dispatch_invokeJEPZJ` (new top; premises as
    `dispatch_invokeJEPZI` with `JPreemptRestHypJ` for `JPreemptRestHypI`). What is left in it (by PPCov's
    conjuncts): (i) no `CurInv` while the thread is schedulable or the current SC active (= (2b)); (ii)
    `CurInv`, ¬`NoTmoSend`, ¬`PPCovT` (kp5 (i) = (2c)). Idle current thread and pending switch are gone.
- (2b) NOT STARTED, finding (sizing): a `charge_budget_refinesF` copy "without htw/hts" is not a local copy. The
  owner facts reach three layers: `charge_head_refinesK` (htw → `hown : x.scTcb = some ct`, fed to
  `Inv.refillUpd`/`budget_check_refines_inv` as `Or.inl hown`, whose `InvBut σ' u0` is parametric in the SC's
  OWNER `u0` and needs `u0 ∉ releaseQueue`), `charge_tail_refinesF` (`hxs` ct's SC = cur SC, `hown`), and
  ScCharge's `rap_refines` (htw, hts). Route: re-parametrise the head/tail/rap chain by the SC's owner
  `o : Option ObjRef` (`x.scTcb = o`, `∀ u, o = some u → u ∉ releaseQueue`) instead of ct; the owner's
  release-queue fact is a NEW spec fact at the hole (l4v: `charge_budget` from `valid_sched`'s
  `active_sc_valid_refills`/`released_sc` of a bound active SC, not `ct_not_in_release_q`); for an owner in
  the release queue the spec's `charge_budget` still runs (l4v `refill_budget_check` on a released SC) — check
  first whether FL4's `charge_budget` writes differ there. Then `JHole.mcsPPJU` (¬CurInv, active SC) with
  `CurOwnW`'s second disjunct after, and `JPreemptRestHypK` = `JPreemptRestHypJ` with `CurInv σ ∨ ¬active`.
- (2c) not started (kp5 (i), unchanged).
- Builds: kp10-b1..b4 (module builds via scratch/kp5build.sh: ScPPR, SpecPPR, XTopJointDelR, XTopJointPP,
  XTopJointCnDel, WJLPP, WJLRestart, UtResetZ/LoopJ/TopJ, UtRetResetJ, TcbInsL, TcbInstall, TcbSsp, Tcb, Ut, PPH,
  PreemptZ, PreemptI, Entry, and the four sinks of ScPPR's reverse cone: XTopJointPreemptI, XTopJointRecvIpcLink,
  XTopJointSchedR, XTopJointYieldSys; all green). scratch/axkp10.lean (untracked): std axioms only for
  PPR0.of_ppk (Classical.choice), jFinPPHyp, jPreemptHyp_of, TopPostDMX.toPN/errP, XCap.toPN, specDec_noPreK,
  specDec_cnode_noPre, specDec_thread_noPre, cn_del_topJ, cnode_noPre_of, thread_noPre_of,
  decode_invocation_cnodeJ_stepsL, decode_invocation_threadJ_step, decOK_J, jAtPre_hole, jAtPre_holeTN,
  jPreemptRestHypJ_of, hPre_ofZJ, dispatch_invokeJPZJ, dispatch_invokeJEPZJ, dispatch_invokeJEPZI,
  handle_invocation_refinesJ.
## sch6 (branch par/sched6 in FL4-sc, on 01d8df6d = int/j2 incl. sch5)
- (B) DONE e90fd451: new leaf XTopJointSchedRF3 (imported from Fl4Proofs.lean; nothing existing edited, JAtZ untouched,
  no premise added). sch3/sch5's fake pre-state route, as planned:
  * `ndF2 s kb v16 v24` / `ndF s kb v16 v24 v40` (FL4: rf.1 with ks16/ks24 [/ks40] written), `ndFSt σ dt di`
    (spec: σ1 with domainTime/domainIndex replaced). `schedStep_dom2`: the two-word write is a `SchedStep`
    (DomDecode's `schedStep_start` without the start word: `SchedRel.domW`, DomRelW kept since entries/start
    are untouched, `blkKeep_domKW`). `JAtZ.ndFJ`: `JAtZ.schedJ` (XTopJointCopyRegs) + `JAtZ.workUnitsJD`
    (XTopJointPP) give `JAtZ` at `ndF rf.1 (ksb rf.1) v16 v24 v40`/`ndFSt σ1 v16.bv di` for ANY values.
  * `ndF_writes`: with v16/v24/v40 := the final state's words, `WritesIn rf.1 r.1 (KFootN rf.1 σ1)` gives
    `WritesIn s0 r.1 (KFoot s0 σ0)` (NdW words equal by construction; the rest via `ndF_mem_ne`).
  * Spec facts transfer: `SchS.ndF` (SchStep/SOK are structures, so rebuilt field by field: defeq per field);
    `LK` and the idle fields by defeq. `JAtZ.sch_tailS` = `JAtZ.sch_tail` taking `SchS σ σ'` + the idle
    equalities instead of `schedule σ = {σ'}`.
  * `jat_scheduleFR2` (from `jat_scheduleWP0F` + P1 kw/tinv + hTail, then the J0 tail), `jat_scheduleSR2`
    (`signalJHyp_of`), `jat_finishJ2` (+ `JAtZ.activateJ`). Conclusions identical to `jat_scheduleFRF`/
    `jat_scheduleSRF`/`jat_finishJF`; premises: `hd : σ.domainTime ≠ 0` REPLACED by `hd : σ.domainTime ≠ 0 ∨
    NdOK s σ` (NdOK = DomRel ∧ DomListOK [J] ∧ DOM_SCHED_IDX word = domain_index [J], sch2/sch3, entry only),
    new `hAN : ArchNdF st Z.N Z.T Z.C Z.c` [P] (ScNextDomF, sch4), `hTail`'s footprint `KFoot` -> `KFootN`
    (hTail only yields `SchTailHypsR.ar`, the CR3 [P] fact). Everything else unchanged (FpuOwnOK σ [J],
    ArchSwF [P], hvm [S], htu/hmax [P]). SUPERSEDE the F versions; no top-chain theorem consumes
    `jat_finishJ*` yet (grep: only XTopJointSchedR/RF/RF3), so the top chain (kernel_entryJ, not written)
    should use `jat_finishJ2`.
- (C) M6 NOT STARTED (scope, not context alone). sch2's route needs (i) a `CurRun` post fact of
  `handle_invocation_refinesJ` for first-phase non-blocking non-calling invocations — inside XTopJointEntry,
  which this line must not touch (kp10 is restructuring JAtPre there) — and (ii) the receive leaves without
  `Entered σ`. Inventory for (ii) (`hni` CONSUMED, not just passed, ~45 sites in 14 files): `J.curInv (hni.2 ▸ …)`
  (CurInv from resumeCurThread: RecvIpcAct:198, RecvIpcRet:220, RecvIpcBound:223, RecvIpcBlock:1084,
  RecvSendRD:1650, RecvSendRP:55, RecvSendT:1256, RecvSig:144/218, RecvSendRet:110, RecvSigRet:829/984,
  RecvSigBlock:746); `J.curRun.run hni` (CurRun: same files + RecvIpcLink:484/502/581/626); `Or.inl hni.2` (the
  action disjunct of recvIpcBlockJG/recvIpcBlockNJG/recvSendPJG/recvSendFPJG/recvSendFPTJ/canBlockCurG);
  `fun u hu => by rw [hni.2] at hu` (no pending switch, RecvIpcRet:250, RecvSendRD:1697, RecvSendRP:93,
  RecvSendT:1294, RecvSendRet:148); `hni.1` (not idle: kept by the invocation). The CurInv uses are the hard
  part: under `switchThread t`/`chooseNewThread` CurInv is not available, so each leaf needs a CurInv-free
  variant (what it reads from CurInv: mostly `.notRel` for the blocking ones). Suggested order once
  XTopJointEntry is free: (i) first (decode-path post `CurRun ∧ ¬idle` at Ok), then a `JMidR σ := ct ≠ idle ∧
  CurRun σ` replacement leaf by leaf, starting with the blocking leaves (only `.notRel` + action disjunct).
- Builds (tokyo, b.sh): sch6-b1 (3 elaboration errors, fixed), sch6-b2 `XTopJointSchedRF3` OK (5404 jobs; only
  `if_neg` deprecation warnings). Axioms (axsch6.sh/axsch6.lean, untracked): propext, Classical.choice,
  Quot.sound only for handle_invocation_refinesJ, jat_finishJ2, jat_scheduleFR2, jat_scheduleSR2,
  JAtZ.sch_tailS, JAtZ.ndFJ, ndF_writes, schedStep_dom2, jat_finishJF; SchS.ndF: propext.

## kp11 (branch par/budget7 in FL4-tcbj, on d06a15fe = int/j2 incl. kp10)
- DONE (2b) step 1, the release-queue hole fact, no [J]: new leaf XTopJointPreemptO. `CurScFree σ := ∀ u xt,
  σ.kheap u = some (.tcb xt) → xt.tcbSchedContext = some σ.curSc → u ∉ σ.releaseQueue`; `curScFree_of : Inv σ →
  CurOwnW T C σ → PPR0 σ → CurScFree σ` (consumed > 0: `CurOwn`'s clause, the owner the only bound thread by
  `Inv.back`; unowned: no bound thread; consumed = 0: `PPR0`'s second clause); `jAtPre_holeO` = `jAtPre_holeTN`
  + `CurScFree` at the hole. For it `JAtPre`'s base conjunct is now `JAt ∧ Vs.NoSwitch σ0 ∧ PPR0 σ0` (was `… ∧
  ct ≠ idle`, = `PPR0.1.1`): the five constructors (CnDel cn_del_topJ, WJLRestart, TcbInstall:1116, TcbSsp:855,
  UtResetZ jAtPre_pp) pass their `PPR0` whole; jAtPre_holeTN reads `hp00.1.1`. l4v counterpart:
  `cur_sc_not_in_release_q` / `cur_sc_in_release_q_imp_zero_consumed` at the preemption point. Note the
  unconditional "owner of an active SC ∉ release queue" is false (every queued thread), and so is the form at
  every `JAtZ` state (the entry's `check_budget_restart` postpones ct at consumed 0): the fact is a hole fact.
- (2b) rest NOT done; findings (what a `¬CurInv` hole still lacks; `JHole.cur` gives `chooseNewThread` there):
  (a) ct schedulable, `¬CurInv`: then ct's SC `p ≠ curSc` (p = curSc would give CurInv: tcb/NotIpcBlk from
      runnable, active and notRel from schedulable). Spec `check_budget` → `end_timeslice` then appends ct or
      POSTPONES curSc, i.e. release-enqueues curSc's owner (≠ ct, maybe none): Inv.rel can break. Not provable
      from JAtZ; must be excluded by a carried fact `CtLink σ := ∀ xt, σ.kheap σ.curThread = some (.tcb xt) →
      xt.tcbSchedContext = some σ.curSc ∨ xt.tcbSchedContext = none` (true from `Entered`/CurInv; deletion only
      unbinds). Carry it in `PPR0` (first conjunct): `PPK` keeps it (`tcb` keeps every link, `ct`, `csc`);
      SpecPPR's `TR` needs a new field "ct's link after is the one before or none" proved at the TK leaves
      (`tk_threadSet`: keeps/clears ✓; `sched_context_donate`/`reply_remove` donee: blocked on the reply, so
      ≠ ct needs "ct not BlockedOnReply" at the leaf — from `Inv`'s rd/rel? no: add to TR's start condition
      `ct runnable-or-restart`, kept by deletion); also `PPR0.setCn`, `PPK.updTcbSc` (TcbInstall), UtResetTopJ's
      `delSt`. With it (a) is vacuous.
  (b) ct not schedulable, curSc active, `¬CurInv`: charge through the owner. Spec side copy of
      `charge_head_refinesK` with `u0` for ct: replace `htw`/`hnr` by `(∀ x n, kheap curSc = sc x n → x.scTcb =
      some u0 ∨ x.scTcb = none)` and `u0 ∉ RQ` (= `CurScFree`; for the unowned case pick any `u0` and note
      `Inv.refillUpd`'s `hnr` is unused when `scTcb = none` — make a variant without it), drop `TmoKeep`
      (no timeout at can = false). Tail: ct not schedulable after the head (HeadKeeps keeps ct's TCB, its SC's
      refill max, the queue), so only `set_consumed 0`; `InvBut σ' u0 → Inv σ'` needs `RelIfBound σ' u0` when
      u0 is `inClassR`. For u0 = ct: ct not schedulable gives it only with NotIpcBlk of ct (not in JAtZ without
      CurInv). For u0 ≠ ct: GENUINELY MISSING = l4v `cur_sc_chargeable` (a thread bound to cur_sc is the
      current thread or not in an `inClassR` state). Proposal: carry `Chg σ := ∀ u xt, kheap u = tcb xt →
      xt.tcbSchedContext = some curSc → u = curThread ∨ ¬ inClassR xt.tcbState xt.tcbFault` plus ct's
      NotIpcBlk in `PPR0` (same TR leaves as (a): donate's donee is blocked on reply, so `¬inClassR` ✓).
      FL4/P1 side: `P1.sched.charge_budget.allF` asks `hcsc1` (ct's SC word ≠ 0 → it is CUR_SC) — with CtLink
      it holds (link = curSc or none). Then `JHole.mcsPPJU` (copy of JHole.chargeBudgetJ: `hcur'` = Or.inl
      (action kept), `hown'` = the base's CurOwnW with consumed 0 (clause vacuous) / unowned, `hoff` vacuous)
      and `JPreemptRestHypK` = `JPreemptRestHypJ` with `CurInv σ ∨ schedulable ct ∨ ¬active` (or delete it once
      (a) is in).
- (2c) not started (kp5 (i), unchanged).
- Builds: kp11-b1 (XTopJointCnDel, UtResetZ, XTopJointWJLRestart, XTopJointTcbInstall, XTopJointTcbSsp, UtRetResetJ
  green; PreemptO failed on a defeq `exact`, fixed), kp11-b2 (XTopJointPreemptO with its cone PreemptZ/PreemptI/PPH,
  XTopJointTcb, XTopJointUt, XTopJointEntry: green). scratch/axkp11.lean (untracked): std axioms only for
  curScFree_of, jAtPre_holeO, jAtPre_holeTN, JAtZ.jAtPre_pp, dispatch_invokeJEPZJ, handle_invocation_refinesJ.
- Premises: none added, none removed (`JPreemptRestHypJ` [W] unchanged; its (2b) part now needs only the carried
  `CtLink`/`Chg` facts above, not a release-queue fact).
## sch7 (branch par/sched7 in FL4-sc, on 1412d306 = int/j2 incl. sch6, kp10)
New leaves XTopJointMidRun, XTopJointKEntry (imported from Fl4Proofs.lean). Nothing existing edited, JAtZ untouched;
no premise added to or removed from any existing theorem.
- (C) step 1 DONE d1c2866f (XTopJointMidRun): `JMidRunHyp rep don cptr σ` [W] = l4v
  `handle_invocation_not_blocking_not_calling_first_phase_ct_active`, at the invocation's entry state on the spec:
  `∀ y ∈ ((fl4HandleInvocationR rep false false don true cptr).run σ).1, y.1 = .ok () → CurRun y.2`.
  NOT derivable from existing facts: `HIPostMXP`'s `JAt` carries only `CurRunM` (the mid action may be
  `switchThread t`/`chooseNewThread`) and the decode paths' `DecOut` facts stay inside `decOK_J`; no spec frame
  keeps the current thread's state across a perform. Removal route: an FK-style "current thread stays runnable"
  frame (VsDom's `dk_auto` pattern) over the first-phase perform cone (sendIpc non-blocking, sendSignal,
  doReplyTransfer, IRQ, untyped retype, arch) with "the woken/receiving thread ≠ ct" from `CurRun` (blocked threads
  are not runnable), plus read-only lookups/decodes; then the `syscall` shell (fault branch is a no-op for
  `blocking = false`, error branch a no-op for `calling = false`, the restart→running tail).
  Derived: `curRun_ne_idle` (CurRun + IdleOK ⇒ ct ≠ idle), `JMid` (= RelTopM ∧ JAt ∧ CurRun ∧ ct ≠ idle, l4v
  `invs and ct_active`, no condition on the scheduler action), `HIPostMXP.mid`, `handle_invocation_midJ`
  (`handle_invocation_refinesJ` for first_phase/non-blocking/non-calling with `JMid` at Ok, `JAtPre` at Preempted).
- (C) step 2 NOT DONE (scope): the receive leaves from `JMid` instead of `Entered` (sch6's ~45-site list in 14
  XTopJointRecv* files; the CurInv uses need CurInv-free variants). In kernel_entryJ it is the `KDispHyps.mid` [W].
- (D) DONE 7bb09948 (XTopJointKEntry): `kernel_entryJ`:
  `syscall.handle_syscall st arI s a n ⦃ r => (fl4KernelEntrySyscall true c σ).2 ∨ ∃ σ', ((), σ') ∈
  (fl4KernelEntrySyscall true c σ).1 ∧ RJ arI AR r.1 r.2 σ' ⦄` for `NativeSys n c` (Send/NBSend/Call, Recv/NBRecv/
  Wait/NBWait, Yield, ReplyRecv/NBSendRecv/NBSendWait). Proved pieces: FAULT_IP write at J (`reg_wr_irel` +
  `JAtZ.regWrJ`; spec `fl4SyscallFaultIP_eq`, `faultIPSt`), `NativeSys.range`, budget split `budgetOkJ` with
  `budgetOkF` or `budgetOkT`, `dispatch_allJ` (dispatch_invokeJEPZJ / dispatch_recvJL / dispatch_yieldJ), `jat_finishJ2`
  after the dispatch and after a stopping budget check, spec composition (`specFront`, `mem_kentry`,
  `fail_kentry`: a failing preemption path fails the entry; `mem_handleE_ok/err`, `mem_fl4HandleEvent`).
  Premises (all at the entry or at spec-reachable intermediate states, never ∀ JAt states except those inherited):
  * `J : JAtZ … s a σ`, `hni : Entered σ` [J] (l4v ct_running, resume_cur_thread).
  * `hflag` [S] (M2, l4h trap mode out of scope): `∀ ct v, cur_thread s = ok ct → obj.Tcb.flags st ct
    (L.wr s (regA ct FAULT_IP) v) ⦃ f => f &&& TRAP_SYSCALLS = 0 ⦄`.
  * `hB : ∀ x, σ.kheap σ.curThread = some (.tcb x) → KBudget arI a (faultIPSt σ σ.curThread x)`:
    `now` NowAgree [P]; `cur` CurInv, `off` OffReady [J] (budget_ok_offReady; FOLD LATER: transfer from σ, the
    write changes one register); `tmo` NoTmoSend ∨ budgetOkT's premises (ct_not_in_q [J], ct running/restart,
    endpoint timeout handler can block [J], non-round-robin SC).
  * `hK : ∀ σb, BudgetAt σ σb true → ∀ ghosts s' a', JAtZ … s' a' σb → KDispHyps …`: `inv` JEntryGlob/JEntryAt/
    JPathAt (dispatch_invokeJEPZJ's, fields tagged there), `recv` ct_not_in_q / valid_fault_handler [J], `mid`
    [W] = the whole ReplyRecv/NBSendRecv/NBSendWait dispatch to `DispPost (PPQ) (fl4HandleSyscall true c)` (M6:
    to be replaced by `handle_invocation_midJ` + `JMidRunHyp` + the receive from `JMid`, (C) step 2).
  * `hFin : ∀ x ∈ (specFront c σ).1, ∀ ghosts s' a', JAtZ … s' a' x.2 → KFinAt …` (jat_finishJ2's state/ghost
    premises: hd (domainTime ≠ 0 ∨ NdOK) [J], hVt [J], hW SignalRestJHyp [W], ArchSwF/ArchNdF [P], FpuOwnOK [J],
    SniHyp/SendHyp [P], hTail (CR3 [P])). Removal: carry FpuOwnOK/NdOK through the dispatch (spec frames) instead
    of assuming them before `finish`.
  * `hPF : KPreFinHyp arI AR c σ` [W]: after a preempted invocation (`PreemptedAt`), from `PPQ σ1 r` (JHoleAt/
    XTopAt or spec failure), `finish` refines `fl4Awaken; schedule; activateThread` from an outcome of
    `preemption_path σ1` (l4v he_invs/schedule_invs). Missing: `JAt` after the uncovered preemption path.
  * globals: hARI hA hnd hPP hmrt hmb hIP [P], hNS [S], hRest JPreemptRestHypJ [W] (kp line), hT hmax htu [P],
    hvm [S].
- Builds (tokyo, b.sh): sch7-b1 `XTopJointMidRun` OK (5376 jobs); sch7-b2..b4 elaboration fixes; sch7-b5
  `XTopJointKEntry` OK (5484 jobs). Axioms (axsch7.sh/axsch7.lean, untracked): propext, Classical.choice,
  Quot.sound only for kernel_entryJ, dispatch_allJ, handle_invocation_midJ, HIPostMXP.mid, mem_kentry, fail_kentry,
  fl4SyscallFaultIP_eq, NativeSys.range, handle_invocation_refinesJ, jat_finishJ2; curRun_ne_idle: propext.
## kp12 (branch par/budget8 in FL4-tcbj, on b3b69063 = int/j2 incl. kp11)
- DONE (2b) case (a), no [J]: a schedulable current thread at a preemption hole has `CurInv`.
  * ScPPR: `NotBlk ts` (not blocked on a reply, an endpoint or a notification), `CtOK σ` (ct's TCB linked to
    `curSc` or to none, and `NotBlk`); `PPR0`'s first conjunct is now `ct ≠ idle ∧ NoSwitch ∧ CtOK` (`.1.2` →
    `.1.2.1` for NoSwitch). `PPK.tcb` also says `NotBlk x → NotBlk y`; `PPK.restart` takes `NotBlk ts`
    (autoParam), XTopJointTcbInstall `PPK.updTcbSc` takes `NotBlk x → NotBlk y` (autoParam: `id`, or a constant).
    `JAtZ.ppr0_start` gives `CtOK` from `CurInv.tcb` (link = curSc) and `CurRunM.run` (runnable → NotBlk).
  * SpecPPR: `TR.tst` (every TCB after: in `E`, or before with `NotBlk x → NotBlk y ∧ (link kept ∨ cleared)`),
    transitive; leaves: `tk_threadSet` takes `hb` (state kept/param/constant, macro `tk_nobor`),
    `tk_setThreadState'` takes `NotBlk ts` (every deletion `set_thread_state` is Restart/Inactive),
    `tr_setTcb`/`tka_setObject(_bind)` take `hb` (autoParam `id`). `TKN E c t := TK (E ∨ · = t) c` (the donee
    exempt), `TR.mono`, `TR.unE` (drop `t` again from a start where it is outside the release queue and not
    `NotBlk`: `tks_replyBody`'s caller is `BlockedOnReply`). `PPR0.of_tr` derives `CtOK` after.
  * New leaf XTopJointPreemptK: `curInv_of_sched` (CtOK + schedulable ct → CurInv), `ct_not_inClassR` ((b) with
    ct as owner: an unschedulable ct bound to the active curSc, with CtOK/CurScFree, is not `inClassR`),
    `jAtPre_holeK` (= jAtPre_holeO + CtOK at the hole), `JPreemptRestHypK` [W] (below), `jPreemptRestHypK_of`,
    `hPre_ofZK`, `dispatch_invokeJPZK`, `dispatch_invokeJEPZK` (new top; premises as dispatch_invokeJEPZJ with
    `JPreemptRestHypK` for `JPreemptRestHypJ`).
- Premise change: `JPreemptRestHypJ` [W] replaced at the top by `JPreemptRestHypK arI AR` [W] := `∀ s a σ,
  JHoleAt arI AR s a σ → NativeScope σ → σ.curThread ≠ σ.idleThread → Vs.NoSwitch σ → CurScFree σ → CtOK σ →
  (CurInv σ ∨ schedulable σ.curThread σ = false) → ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) → after_invocation s a
  (.Err .Preempted) ⦃ r => PPQ arI AR σ (r.2.1, r.2.2) ⦄`. Left in it: (b) ¬CurInv, ct not schedulable, curSc
  active; (2c) CurInv, ¬NoTmoSend, ¬PPCovT.
- (b) NOT done; finding (why the kp11 route stops at cur_sc_chargeable): `ct_not_inClassR` settles the owner =
  ct case; for an owner u ≠ ct (reachable only as `reply_remove`'s donee of curSc, which `replyUnlinkTcb`
  then makes Inactive) `Chg σ := ∀ u xt, kheap u = tcb xt → link = some curSc → u = ct ∨ ¬ inClassR` must be
  carried. It is NOT a TR-leaf fact like `tst`: `restart_thread_if_no_fault` (in `cancel_all_ipc`/
  `cancel_all_signals`/`cancel_badged_sends` loops) sets `Restart` on a queue member with no fault, and only
  the queue invariant (l4v `valid_ep_q`/`valid_ntfn_q`: queued threads are blocked on that object, so
  `inClassR` before, or faulted senders → Inactive) excludes restarting an Inactive/BlockedOnReply thread
  bound to curSc. SpecPPR works from `Inv` only (no queue facts). Route: prove `Chg` preservation at J per
  finalisation kind from the J-level frames that already know the queues (IpcFinEpInv's `EFr`/`TChgE`:
  "a TCB's state kept, or a thread blocked on e made Restart/Inactive"; the ntfn/badged/reply/TCB/SC
  analogues used by `JAtZ.finEpJ` etc.), i.e. a `JFinPPHyp`-level lemma "finalise_cap from a JAtZ state keeps
  Chg" fed into WJR's PPR0 (add Chg as a PPR0 conjunct; `ppr0_start`: Chg from CurInv + Inv.back). Then the
  charge: owner-parametrised copy of `charge_head_refinesK` (u0 for ct; `CurScFree` for `u0 ∉ RQ`; unowned
  variant of `Inv.refillUpd` without `hnr`), tail = only `set_consumed 0` (ct stays unschedulable:
  HeadKeeps), `InvBut σ' u0 → Inv σ'` by `ct_not_inClassR`/Chg; FL4 side `charge_budget.allF`'s `hcsc1` from
  CtOK; `JHole.mcsPPJU` and `JPreemptRestHypL` = K with `CurInv σ` only. curSc = idleSc in (b): the spec skips
  the charge (check FL4's branch; ActIdle may make it PPCovI).
- (2c) not started (kp5 (i), unchanged).
- Builds: kp12-b1 (ScPPR, SpecPPR), kp12-b2..b6 (module builds via scratch/kp5build.sh: SpecPPR, XTopJointCnDel,
  UtResetZ, UtResetTopJ, XTopJointTcbInsL, XTopJointTcbInstall, UtRetResetJ, XTopJointPP, XTopJointPreemptK,
  XTopJointTcb, XTopJointUt, XTopJointEntry, XTopJointWJLEmpty, XTopJointWJLSwap, XTopJointPost, and the sinks
  XTopJointRecvIpcLink, XTopJointSchedR, XTopJointYieldSys: all green after fixes at CnDel:93 and UtRetResetJ:431).
  scratch/axkp12.lean (untracked): std axioms only (propext/Classical.choice/Quot.sound) for ppr0_finaliseCap,
  TR.unE, PPR0.of_ppk, JAtZ.ppr0_start, curInv_of_sched, ct_not_inClassR, jAtPre_holeK, hPre_ofZK,
  dispatch_invokeJPZK, dispatch_invokeJEPZK, dispatch_invokeJEPZJ, handle_invocation_refinesJ.

## sch8 (branch par/sched8 in FL4-sc, on 6b4a8493 = int/j2 incl. sch7, kp12)
New leaves XTopJointKEntry2, XTopJointRecvMid (imported from Fl4Proofs.lean). Nothing existing edited, JAtZ untouched.
- (1) DONE (XTopJointKEntry2): `SignalRestJHyp` [W] and `hvm` [S] are VT-x cases that `hNS` [S] (NativeScope at every
  `JHoleAt` state; a `JAtZ` state is a `JHole` over itself, `JAtZ.toHole`) refutes: `signalRestJHyp_of_ns`,
  `hvm_of_ns`. `KFinAt2` = `KFinAt` without `w`; `KFinAt2.toK hNS`. `dispatch_allK` = `dispatch_allJ` over kp12's
  `dispatch_invokeJEPZK`. `kernel_entryJ2` = `kernel_entryJ` with `hFin : … → KFinAt2`, no `hvm`, and
  `hRest : JPreemptRestHypK` (kp12, narrower than JPreemptRestHypJ). REMOVED: `KFinAt.w` (SignalRestJHyp [W]),
  `hvm` [S]. ADDED: none. The lead's top chain should use `kernel_entryJ2`.
- (2) BLOCKED by a FINDING (a design decision on JAtZ is needed; this line must not edit JAtZ):
  `KDispHyps.mid` [W] is FALSE in reachable states, and no mid-receive leaf can end in `RJ`/`JAt` in that case.
  Run: NBSendRecv (or NBSendWait) whose non-blocking send meets a waiting receiver `u` with an SC (or a
  notification signal waking one), then no sender for the receive. The send's `possibleSwitchTo u`
  (Fl4Spec KHeap.lean:484, MCS: no priority test; with numDomains = 1 and action resume it sets
  `switchThread u` unconditionally), the receive blocks ct (`BlockedOnReceive`/`BlockedOnNotification`), and
  `scheduleTcb`/`setThreadStateAct` reschedule only from `resumeCurThread` (KHeap.lean:500), so the outcome has
  `schedulerAction = switchThread u` with ct IPC-blocked. `JAtZ.cur : chooseNewThread ∨ CurInv σ` fails there
  (`CurInv.tcb` needs `NotIpcBlk` of ct), hence `JAt` fails, while `KDispHyps.mid`'s `DispPost` demands `JAt` at
  the (deterministic) outcome. The spec follows l4v here (not a spec bug); cf. StepSem's `CurRunM`, which already allows exactly this.
  Fix options (lead): (a) weaken `JAtZ.cur` to `σ.schedulerAction = .chooseNewThread ∨ (∃ u, σ.schedulerAction
  = .switchThread u ∧ ¬ runnable ct) ∨ CurInv σ` (every `J.curInv` user under a switch then needs ct runnable,
  e.g. from `CurRun`; grep `J.curInv`/`JAtZ.cur` users), or (b) state the mid receive's post as `JAtZ` OR a
  `JAtZS` (= JAtZ with that disjunct) and give `jat_finishJ2` a `JAtZS` variant (the schedule switch branch with ct
  blocked: no enqueue of ct, switch to u; not checked whether ScScheduleTop's switch branch covers a non-runnable ct
  at SchedRel). Either is a JAtZ-level change; (b) keeps the 445
  cone intact.
  Done meanwhile (XTopJointRecvMid, valid under either option for the non-blocking leaves, whose post keeps ct
  running so CurInv holds): `MidE σ` (ct ≠ idle ∧ CurRun ∧ (resume ∨ switchThread u with u ≠ ct)), `MidE.ncn/run/sa`,
  `JAtZ.midE` (Entered → MidE), `JAtZ.curScAc` (under CurInv: ct's SC word = CUR_SC ∈ Ac, via SCsOK.act and the
  idle SC being the idle thread's), `JAtZ.canBlockCurM` (canBlockCurG with the switch case; `CanBlock.ac` from
  curScAc, since ct is not `Sch` then), `JAtZ.recvSigActiveJM` (recvSigActiveJ from MidE).
  Also needed for MidE at the mid state: `u ≠ ct` for a pending switch (l4v `scheduler_act_sane`) is NOT in JAtZ
  (ActSched only says u schedulable); `possibleSwitchTo` targets a woken (previously blocked) thread, so it is a
  post fact of the first-phase invocation (with JMidRunHyp's route) or a new [J] invariant. The chooseNewThread mid
  case (e.g. own-SC unbind/reply-SC return) is separate: leaves with `hsa`'s second disjunct need ct SC-less.
- (3) NOT STARTED (JMidRunHyp: FK frame "ct stays runnable" over the first-phase perform cone; see sch7 (C) step 1).
- (4) NOT STARTED (needs (2),(3)).
- Builds (tokyo, b.sh): sch8-b1 `XTopJointKEntry2` OK (5486 jobs, on 2c8ea9c8), sch8-b2 `XTopJointRecvMid` OK, sch8-b3
  `XTopJointKEntry2 XTopJointRecvMid` OK on 6b4a8493 (5492 jobs). Axioms (axsch8.sh/axsch8.lean, untracked):
  propext, Classical.choice, Quot.sound only for kernel_entryJ2, dispatch_allK, signalRestJHyp_of_ns, hvm_of_ns,
  KFinAt2.toK, kernel_entryJ, JAtZ.curScAc, JAtZ.canBlockCurM, JAtZ.recvSigActiveJM, JAtZ.midE; MidE.ncn/sa: none.
  No sorry/admit/native_decide/bv_decide.
- (2) after the lead's decision (option (b), JAtZ not edited), on d8d4fc22:
  * DONE (XTopJointJAtZS): `SwBlk σ` := ct ≠ idle ∧ ct not runnable ∧ ∃ u, action = switchThread u ∧ u ≠ ct (the
    target ≠ ct, l4v `scheduler_act_sane`, carried inside). `JAtZS` = JAtZ's fields with `cur : chooseNewThread ∨
    CurInv ∨ SwBlk` (scripted copy of JointAt's field list); `JAtZ.toS`, `JAtZS.toJ` (given JAtZ.cur),
    `JAtZS.toJ_or`, `JAtS`, `JAt.toS`, `JAtS.toJ_or`.
  * DONE (XTopJointKEntry3), step (iii): `DispPostS` (DispPost with `JAtS` at an ok outcome), `DispPost.toS`,
    `KDispHypsS` (= KDispHyps with `mid : MidSys n c → dispatch ⦃ DispPostS … ⦄`), `KDispHyps.toS`, `dispatch_allS`,
    `kernel_entryJ3` = kernel_entryJ2 with `hK : … → KDispHypsS` and new `hSw : KFinSwHyp arI AR c σ` [W]:
    `∀ x ∈ (specFront c σ).1, x.1 = .ok () → ∀ ghosts s' a', JAtZS … s' a' x.2 → SwBlk x.2 → syscall.finish st arI
    s' a' ⦃ r => ∃ σ', ((), σ') ∈ ((fl4Awaken >>= fun _ => schedule >>= fun _ => activateThread) x.2).1 ∧ RJ r.1 r.2
    σ' ⦄` (l4v schedule_invs with scheduler_act_sane; true in reachable states: after schedule the action is
    resume and the chosen thread's CurInv holds). A JAtZ outcome still goes to jat_finishJ2. REPLACED: KDispHyps.mid
    [W] (false in reachable states) by KDispHypsS.mid [W] (true there) + KFinSwHyp [W].
  * (i) ANALYSIS for KFinSwHyp's proof (step (ii), not done): `CurInv` is consumed by the SchedRel-level schedule
    only through `SchedPreW0`'s `cur` (ScNextDomC:26) at `newcur_of`/`newcur_ofF` (ScArchF:185) in the resume
    branch (ScScheduleF:505 / ScNextDomCF:474; not reached under SwBlk: action is a switch) and in the switch branch
    (ScScheduleF:593 / ScNextDomCF:566, `hC2w.resolve_left` with the switch action). In the switch branch the spec
    enqueues ct only `when schedulable ct` (`hwhen`, ScNextDomCF:559: a no-op for a non-runnable ct) and the new
    current thread is the candidate u ≠ ct, a thread chosen from the ready queues (schedulable), or the idle thread;
    `newcur_ofF`'s third disjunct (`σ'.curThread = σ.curThread`, the only one needing the old CurInv) is excluded
    by SwBlk (u ≠ ct; ct, not schedulable, is in no queue). So a `newcur_ofF'` without `hC` for
    `idle ∨ schedulable` and copies `switch_branch_refines0F`/`schedule_refinesWP0F`/`…WPF` (ScNextDomCF/
    ScScheduleF) with `SchedPreW0` weakened to `chooseNewThread ∨ CurInv ∨ SwBlk` suffice at SchedRel. The cost is
    at J BEFORE schedule: FL4's `schedule` first runs `timer.fire` (`JAtZ.fireJ`, ScFireJ:462, over `SignalJHyp`
    = the whole send_signal cone at J: ScSignalJ/ScSignalBoundJ/ScSignalDonJ, `signalJHyp_of`), all stated for
    JAtZ; their J.cur use is only the frame `J.cur.imp … F.curInv` (ScFireJ:303, ScSignalJ:136, + 1–2 per leaf),
    but every leaf takes and builds `JAtZ`, so they need JAtZS copies (a timer signal that wakes a thread under
    `switchThread u` gives `rescheduleRequired`, i.e. chooseNewThread, so the JAtZS post becomes a JAtZ post there;
    waking ct itself likewise). Then `jat_scheduleWP0F`/`jat_scheduleFR2` (XTopJointSchedRF2/RF3) from JAtZS, and
    `sch_tailS` as is (it builds JAtZ after schedule). Suggested leaf XTopJointSchedRF4.
  * Re-check of the other [W]s for the same defect (a post demanding JAt where only JAtZS holds): KFinAt2's
    fields are premises at JAtZ outcomes only (applied after `toJ_or`); KPreFinHyp's post is RJ after schedule
    (resume action, fine) from PPQ (JHoleAt/XTopAt, not JAt); KBudget/KDispHyps.inv/recv are pre facts;
    JPreemptRestHypK's post is PPQ (JHoleAt/XTopAt). kp12's PPQZ (JAt after the preemption path) is outside this
    line: a preempted invocation leaves ct running (restart), so JAtZ.cur's CurInv is not obviously broken there,
    but a preemption after a wake (switch pending) with ct not schedulable should be checked by kp12. The proved
    Send/NBSend/Call/Recv/Yield dispatches are theorems (their JAt posts are proved). No other false premise found.
- (3), (4): NOT STARTED.
- Builds: sch8-b4 `XTopJointJAtZS XTopJointKEntry3` OK (5494 jobs). Axioms (sch8-ax2): std only for kernel_entryJ3,
  dispatch_allS, DispPost.toS, KDispHyps.toS, JAtZ.toS, JAtZS.toJ, JAtZS.toJ_or, JAtS.toJ_or, JAt.toS (+ the earlier
  list). No sorry/admit/native_decide/bv_decide.
## kp13 (branch par/budget9 in FL4-tcbj, on 6b4a8493 = int/j2 incl. kp12, sch7)
- DONE (2b) case (b) part 1, no [J]: l4v `cur_sc_chargeable` carried to the preemption hole, spec side, without
  per-kind J frames for the finalisations that restart no thread.
  * ScPPR: `Chg σ := ∀ u xt, kheap u = tcb xt → link = some curSc → u = curThread ∨ xt.tcbState = .inactive`;
    `PPR0`'s first conjunct is `ct ≠ idle ∧ NoSwitch ∧ CtOK ∧ Chg` (`.1.2.2` → `.1.2.2.1` for CtOK,
    `.1.2.2.2` = Chg). `PPK.ina` (an inactive TCB stays inactive, but for the current thread): `PPK.restart`
    takes `t = curThread ∨ x.tcbState ≠ .inactive` (callers: `Or.inl hcur.symm`), XTopJointTcbInstall's
    `PPK.updTcbSc` takes `hi` (autoParam `Or.inl`; UtRetResetJ passes the current thread), UtResetTopJ's
    `delSt` record. `JAtZ.ppr0_start`: `Chg` from `CurInv` + `Inv.back` (the current SC's only thread).
  * SpecPPR: `TR E W` (new Prop parameter `W`), field `chg : W → (bound to curSc and not inactive after →
    E u ∨ so before)`. Leaves: `tk_threadSet` takes `hi : W → inactive ↦ inactive` (tk_leaf: state kept or
    constant `inactive`), `tk_setThreadState'` takes `hi : W → ts = .inactive` (macro `tk_inact`),
    `tr_setTcb`/`tka_setObject(_bind)` take `hi` (autoParam). The restart leaves (`restart_thread_if_no_fault`,
    `remove_and_restart_*_queued_thread`, `cancel_all_ipc`, `cancel_all_signals`) and so `tks_fastFinalise`,
    `tks_capDeleteOne`, `tks_deletingIrqHandler`, `tks_finaliseCap` are at `W = False`; `TR.unE` takes
    "`t` inactive at the end" (`endIn_replyRemove`: `reply_remove` ends with `reply_unlink_tcb`'s `Inactive`);
    `NoRestartCap`, `tks_finaliseCapW` (`W` any, not ep/ntfn/IRQ handler), `Chg.of_tr`, `chg_finaliseCapW`.
    `PPR0.of_tr` / `ppr0_finaliseCap` take `Chg` after.
  * New leaf SpecPPRC: `Chg.of_efr` (IpcFinEpInv `EFr`: only threads blocked on the endpoint change state),
    `Chg.of_nfr` (`NFr`), `EpQB` (queued threads blocked on their endpoint + `EpPre`), `chg_cancelAllIpc`
    (`inv_cancelAllIpc`), `chg_ntfnBody` (`finNtfn_spec`), `chg_fastFinalise`, `chg_deletingIrqHandler`,
    `chg_finaliseCap`. XTopJointDelR: `JAtZ.epQB` (`J.obj.ep`, `J.epFinPre`, `ep_queue_blocked`),
    `jFinPPHyp` passes `chg_finaliseCap … J.sv J.epQB`.
  * New leaf XTopJointPreemptL: `owner_not_inClassR` (CtOK + CurScFree + Chg + unschedulable ct: every thread
    bound to the active current SC is not `inClassR`), `jAtPre_holeL` (`jAtPre_holeK` + `Chg`),
    `JPreemptRestHypL` [W] (= `JPreemptRestHypK` with `Chg σ →`), `jPreemptRestHypL_of`, `hPre_ofZL`,
    `dispatch_invokeJPZL`, `dispatch_invokeJEPZL` (new top).
- Premise change: `JPreemptRestHypK` [W] replaced at the top by `JPreemptRestHypL arI AR` [W] := as K with an
  extra `Chg σ →` (narrower). Left in it: (b) and (2c) as in kp12.
- (b) part 2 NOT done (handoff, all facts now at the hole): `JHole.mcsPPJU` for FL4's `mcs_preemption_point`
  branch "ct not schedulable, curSc active" = `charge_budget consumed false` vs spec `preemptionPath`'s
  `chargeBudget consumed false`. Ingredients: (i) SchedRel-level copy of ScChargeG's
  `charge_budget_refinesF` (:429) / `charge_head_refinesK` (:190) with the owner `u0` (`hown : scTcb = some u0 ∨
  none` from `Inv.back`/scTcb, `u0 ∉ RQ` from `CurScFree`) instead of `htw` (the SC's TCB word is ct), `hts`
  (ct's SC word is CUR_SC: false in (b) when ct is unbound, `CtOK` allows `none`), `hnr`, `hnb`, an unowned variant of
  `Inv.refillUpd` without `hnr`, no `TmoKeep` (`can_timeout_fault = false`); (ii) the tail: ct stays not
  schedulable (HeadKeeps: ct's TCB, its SC's refill max, the queue kept), so `endTimeslice` is skipped,
  `set_consumed 0`; `InvBut σ' u0 → Inv σ'` because `u0` is not `inClassR` (`owner_not_inClassR`, its `rd`
  vacuous); (iii) FL4 side `P1.sched.charge_budget.allF`'s `hcsc1` (ct's SC word ≠ 0 → it is CUR_SC) from
  `CtOK`; `hna` (action ≠ ct) from the hole's `cur` (no CurInv ⇒ chooseNewThread); (iv) `JHole.toJ` with
  `OffOK` vacuous (consumed 0) and `CurOwnW` the base's; `afterInv_of_mcs` then gives PPQ. Then
  `JPreemptRestHypM` = L with `CurInv σ` instead of the disjunction. Also check FL4's branch when
  curSc = idleSc in (b) (ActIdle may make it PPCovI).
- (2c) not started (kp5 (i)).
- Lead question (switch pending + blocked ct after the preemption path, sch8's JAtZS/SwBlk): not reachable in
  the spec at PPQ. A hole has no switch pending (`JAtPre`: `NoSwitch`); the only `switchThread` source in the
  preemption path is `possibleSwitchTo` in the IRQ's signal (Fl4Spec KHeap:484), which sets `switchThread`
  only when the action is `resumeCurThread`; at a hole that means `CurInv` (`JHole.cur`), ct runnable
  (`CurRunM`), and every step of the charge that stops ct (end_timeslice's reschedule, handle_timeout's fault
  send/block via `set_thread_state`'s `stsAct`) first sets `chooseNewThread`. So PPQ's `JAt` needs no JAtS.
- Builds: kp13-b2 (ScPPR, SpecPPR), kp13-b4 (SpecPPRC, XTopJointCnDel, UtResetZ, UtResetTopJ, XTopJointTcbInsL,
  XTopJointTcbInstall, UtRetResetJ, XTopJointWJLRestart, XTopJointDelR, XTopJointPP, XTopJointPreemptK/L,
  XTopJointTcb, XTopJointUt, XTopJointEntry, XTopJointWJLEmpty, XTopJointWJLSwap, XTopJointPost,
  XTopJointRecvIpcLink, XTopJointSchedR, XTopJointYieldSys: green), kp13-b5 (the other ScPPR dependents
  XTopJointSchedRF/2/3, XTopJointMidRun, XTopJointKEntry). scratch/axkp13.lean (untracked): std axioms only for
  chg_finaliseCap, ppr0_finaliseCap, chg_finaliseCapW, endIn_replyRemove, jFinPPHyp, JAtZ.ppr0_start,
  owner_not_inClassR, jAtPre_holeL, hPre_ofZL, dispatch_invokeJEPZL, dispatch_invokeJEPZK,
  handle_invocation_refinesJ.
## sch9 (branch par/sched9 in FL4-sc, on dfbc145a = int/j2 incl. sch8)
New leaves XTopJointJAtZR, XTopJointJAtZRS, ScNextDomCFR, XTopJointJAtZRA, XTopJointJAtZRB, XTopJointKEntry4 (imported
from Fl4Proofs.lean). Nothing existing edited; JAtZ, JAtZS and ScPPR/PP*/Preempt*/Tcb*/CnDel/WJL* untouched.
- (1) DONE 2da09ef2: `KFinSwHyp` [W] removed (`kernel_entryJ4`).
  * FINDING (why not sch8's JAtZS route): `JAtZS.cur`'s `SwBlk` (ct not runnable) is NOT kept by FL4's timers: a timer
    signal may wake ct (e.g. ct blocked receiving with a bound notification) while a switch to u is pending;
    `possibleSwitchTo ct` then gives `chooseNewThread` only if ct has an SC outside the release queue. Instead:
  * `CurInvR σ := schedulerAction = resumeCurThread → CurInv σ` (XTopJointJAtZR); `JAtZR` = JAtZ with `cur : CurInvR`;
    `JAtZ.toR`, `JAtZS.toR`, `JAtZR.toJ` (given JAtZ.cur), `JRestR`/`JRest.toR`. Kept by every signal/timer step
    (no step sets `resumeCurThread`, and `CurInv` frames unconditionally: `NFr/CFr/DWFr.curInv`), and enough for the
    spec `schedule`: resume branch reads `CurInv` (from CurInvR), switch/choose branches end at idle or a schedulable
    thread (`newcur_of2F`), so the old current thread's CurInv is never needed under a switch.
  * ScNextDomCFR: `SchedPreW0R`, `awaken_refinesW0R` (awaken's `hnr`), `schedule_refinesWP0FR` (switch branch via
    newcur_of2F instead of newcur_ofF). XTopJointJAtZRS: `wake_specBR`, `wake_tailDR`, `wake_specGR` (spec wakes with
    CurInvR in/out).
  * XTopJointJAtZRA/B: SCRIPTED COPIES (sch9gen/gen.py + split.py in the worktree root, untracked): the transitive
    closure of JAtZ-taking lemmas used by `JAtZ.fireJ`, `signalJHyp_of`, `jat_scheduleWP0F/FR2/SR2`, `JAtZ.ndFJ/
    ndOK_fire/sch_tailS`, `jowes_sched`, `kwApartJ`, `recvReplyHyp_holds` (~80 decls, ~3800 lines), `JAtZ`->`JAtZR`,
    `JRest`->`JRestR`, other names suffixed `ZR`; hand changes (in split.py) only at the 9 `cur` frame sites. FOLD
    LATER: if JAtZ.cur is ever weakened to CurInvR in JointAt, all of A/B collapse onto the originals.
  * XTopJointKEntry4: `jat_finishJR` (jat_finishJ2 from JAtZR; JAtZ again after schedule via `toJ` + CurInv σ'),
    `KFinAtR` (= KFinAt2 with `vt` [J] quantified over JAtZR states; same statement, not read from `cur`),
    `signalRestJHypZR_of_ns`, `kernel_entryJ4` = kernel_entryJ3 with `hFin : ∀ x ∈ specFront, ∀ ghosts, JAtZR … x.2 →
    KFinAtR …` (was JAtZ → KFinAt2), new `hNSR : ∀ Z H Cs Ac Lst D s a σ, JAtZR … s a σ → NativeScope σ` [S] (VT-x out
    of the native scope, as `hNS`), no `hSw`. REMOVED: KFinSwHyp [W]. ADDED: hNSR [S].
- (3) DONE 820efe30: `KPreFinRestHyp` [W] = KPreFinHyp restricted to PPQ states with
  `¬ ∃ z ∈ (preemptionPath σ1).1, JAt r.1 r.2 z.2`; `kPreFinHyp_of` proves KPreFinHyp from it (JAt case: jat_finishJR
  with kernel_entryJ4's hFin at the front outcome `(ok z.1, z.2)`); `kernel_entryJ5` = kernel_entryJ4 with
  `hPR : KPreFinRestHyp` for `hPF`. What is left in KPreFinRestHyp: (a) JHoleAt-not-JAt (kp's PPQZ gives JAt where
  covered; the dispatch still produces PPQ until JPreemptRestHypK/afterInv produce PPQZ — kp line), (b) the IRQ case
  (bare `XTopAt` from `JIrqHyp`): needs `JIrqHyp`'s post strengthened to `JAt`/`JAtZR` (l4v handle_interrupt_invs), then
  `jat_finishJR` closes it exactly as above, (c) a failing spec preemption path (FL4 finish must still return).
- (2) NOT STARTED (JMidRunHyp): route unchanged from sch7 (C) step 1 (an FK-style "ct stays runnable" frame over the
  first-phase perform cone + the syscall shell). Note for whoever does it: KDispHypsS.mid's post could now be relaxed
  from JAtS to JAtZR (kernel_entryJ4 only uses `.toR` of it).
- Builds (tokyo, b.sh): sch9-b1..b4 (A/S/CFR/B; 3 rounds of cur-site fixes), sch9-b5 `XTopJointKEntry4` OK (5506 jobs),
  sch9-b6/b7 (kPreFinHyp_of, kernel_entryJ5) OK. Axioms (axsch9.sh, untracked): propext, Classical.choice, Quot.sound
  only for kernel_entryJ5, kPreFinHyp_of, kernel_entryJ4, jat_finishJR, signalRestJHypZR_of_ns, jat_scheduleSR2ZR,
  jat_scheduleFR2ZR, jat_scheduleWP0FZR, JAtZR.fireJ, signalJHyp_ofZR, JAtZR.sch_tailS, JAtZR.toJ, JAtZ.toR, JAtZS.toR,
  Sched.schedule_refinesWP0FR, Sched.awaken_refinesW0R, Sched.wake_specBR/GR, Sched.wake_tailDR, kernel_entryJ3.
  No sorry/admit/native_decide/bv_decide.

## kp14 (branch par/budget10 in FL4-tcbj, on 3be72de5 = int/j2 incl. kp13, sch8)
- DONE (2b) case (b) second half, no premise added: the preemption path's charge of the current SC at a hole
  without `CurInv` (current thread not schedulable, current SC active; l4v `preemption_path`'s
  `charge_budget consumed False` under `cur_sc_chargeable`).
  * New leaf ScChargeU (SchedRel level): `charge_head_refinesU` (= ScChargeG's `charge_head_refinesK` with the
    owner `u0` as a parameter: `hown : scTcb = some u0 ∨ none`, `hnr : u0 ∉ RQ`; `InvBut σ2 u0` after;
    `Inv.refillUpd` and `budget_check_refines_inv` were already owner-parametrised; no `TmoKeep`),
    `schedulable_headKeeps` (an unschedulable thread stays so across a `HeadKeeps` step: the SC's TCB/refill
    max kept), `charge_budget_refinesU` (whole `charge_budget used false` for an unschedulable current thread:
    FL4's `is_schedulable` after the head is false, so the tail is only `set_consumed 0` on both sides;
    `Inv` after from `InvBut σ' u0` + `hnin` (u0 in no `inClassR` state)).
  * New leaf XTopJointPreemptM: `JHole.curSc_in`; `JHole.chargeBudgetUJ` (ScChargeH's `chargeBudgetJ` without
    `CurInv`: `u0` from the BASE's `CurOwnW` — bound: the SC's TCB, `∉ RQ` by `CurScFree`, not `inClassR` by
    `owner_not_inClassR`; unbound: `u0 := curSc`, no TCB, not in RQ by `Inv.rel`; P1 `charge_budget.allF` with
    `hcsc1` from `CtOK` (link = curSc or none), `hna` from the hole's `chooseNewThread`, `hcA` with
    CUR_SC ≠ 0 from `JAtZ.cover.sc0`; after: `CurOwnW` from the base's (SC's TCB kept), `OffOK` vacuous,
    `CurRunM` by `act_cn_nr`); `JHole.mcsPPJU` (FL4's branch, `JAt` after; `mem_pp_charge`/`fail_pp_charge`).
    curSc = idleSc is covered (the head is skipped on both sides; the tail is the same).
  * `JPreemptRestHypM arI AR` [W] := `JPreemptRestHypL` with `CurInv σ →` in place of
    `CurInv σ ∨ schedulable σ.curThread σ = false →` (narrower; `jPreemptRestHypM_of`), `hPre_ofZM`
    (¬CurInv ⇒ ct not schedulable by `curInv_of_sched`; inactive SC ⇒ PPCovI; else `mcsPPJU`),
    `dispatch_invokeJPZM`, `dispatch_invokeJEPZM` (new top). JPreemptRestHypL has no user left besides
    `jPreemptRestHypM_of`. XTopJointKEntry2/3 (sch line) still take `JPreemptRestHypK`; switching them to
    `JPreemptRestHypM` + `dispatch_invokeJEPZM` is a mechanical change there (not done: out of scope).
- DONE (2c) parts, no premise added (both commits after ab7bec1a):
  * New leaf XTopJointPreemptS: `JHole.mcsPPJC` — with `CurInv` and an UNSCHEDULABLE current thread the
    preemption path charges with `can_timeout_fault = false` on both sides, so `NoTmoSend` is not needed
    (XTopJointPreempt's `mcsPPJ` asked `PPCov` for both branches; its charge branch only uses CurInv, non-idle,
    no switch to ct): ScChargeH `JHole.chargeBudgetJ`, `JAt` after. `JPreemptRestHypS` [W] := M with an extra
    `Fl4Spec.schedulable σ.curThread σ = true →` (`jPreemptRestHypS_of`), `hPre_ofZS`, `dispatch_invokeJPZS/JEPZS`.
  * New leaf XTopJointPreemptE: `check_budget_suffT` (FL4's `check_budget` returns true at a sufficient head:
    `sufficient_refines` + `getScRefillSufficient_eq` exclude the other branch), `JHole.mcsPPJS` (schedulable,
    `CurInv`, non-idle, sufficient head: no charge on either side, whatever the timeout handler; `JAt` by
    `offOK_suff` (needs the hole's `TShift`) + `toJ`). `JPreemptRestHypE arI AR` [W] := S with an extra
    `¬ (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → Fl4Spec.refillSufficient σ.consumedTime
    (Fl4Spec.refillHd y) = true) →` (`jPreemptRestHypE_of`), `hPre_ofZE`, `dispatch_invokeJPZE`,
    `dispatch_invokeJEPZE` (NEW TOP; premises as dispatch_invokeJEPZL with `JPreemptRestHypE` for
    `JPreemptRestHypL`).
- Premise at the top now: `JPreemptRestHypE` [W] = `∀ s a σ, JHoleAt arI AR s a σ → NativeScope σ → ct ≠ idle →
  Vs.NoSwitch σ → CurScFree σ → CtOK σ → Chg σ → CurInv σ → schedulable ct σ = true → ¬ (head sufficient) →
  ¬ (PPCov σ ∨ PPCovT σ ∨ PPCovI σ) → after_invocation s a (.Err .Preempted) ⦃ PPQ ⦄`. JPreemptRestHypL /
  M / S are its weaker predecessors (only used through the `_of` lemmas). This is exactly kp5 (i): FL4
  `check_budget` → `charge_budget consumed true` → `end_timeslice` with `can_timeout_fault` → `handle_timeout`
  at an endpoint handler (`¬NoTmoSend`: handler is an endpoint cap, current SC not RR), with `¬PPCovT`, i.e.
  (schedulable ⇒ Running/Restart, NativeScope excludes RunningVM, NoSwitch excludes a switch) one of:
  (A) the action is `chooseNewThread` (reschedule pending), (B) ct is in a ready queue, (C) the handler
  endpoint has waiting receivers (`¬ CanBlock false`), (D) the handler cap's endpoint is no endpoint
  object (check: `isValidTimeoutHandler` should then be false/impossible by the cap invariant).
- HANDOFF for the rest (not started, context): (C) is kp5's `sendTmoRecvIJ`/`PJ` analogue from a `JTH`
  (XTopJointFaultTmo; base by ScChargeT's `JTH` frames ScOnly-then-CFr as in `JTH.tmoBlockJ`; two cases
  Inactive / reply push; ~1200 lines). (A)/(B): `JTH.tmoBlockJ` asks `hres` (resumeCurThread) and `hnq` (not
  queued); l4v's `handle_timeout` → `send_fault_ipc` → `block` path is the same with chooseNewThread (the
  `set_thread_state` keeps it) and with a queued ct (`tcb_sched_dequeue` inside `set_thread_state`'s
  reschedule? check FL4 `block_on_send`/`set_thread_state` dequeue vs spec `setThreadState` → `scheduleTcb`;
  generalising `tmoBlockJ`/`checkBudgetT`'s `hres`/`hnq` is the likely cheap part, then `PPCovT` loses those
  conjuncts). Kernel-entry wiring: XTopJointKEntry2/3 (sch line's files) still take `JPreemptRestHypK`;
  switching them to `JPreemptRestHypE` + `dispatch_invokeJEPZE` is mechanical (`jPreemptRestHypE_of ∘ … ∘
  jPreemptRestHypM_of ∘ jPreemptRestHypL_of` gives E from K).
- Builds: kp14-b1..b6, kp14-ax1 (scratch/kp5build.sh: ScChargeU, XTopJointPreemptM, XTopJointEntry,
  XTopJointPreemptS, XTopJointPreemptE green; the new leaves have no dependents but Fl4Proofs.lean).
  scratch/axkp14.lean (untracked): std axioms only for schedulable_headKeeps, charge_head_refinesU,
  charge_budget_refinesU, JHole.curSc_in, JHole.chargeBudgetUJ, JHole.mcsPPJU, jPreemptRestHypM_of,
  hPre_ofZM, dispatch_invokeJPZM, dispatch_invokeJEPZM, JHole.mcsPPJC, jPreemptRestHypS_of, hPre_ofZS,
  dispatch_invokeJPZS, dispatch_invokeJEPZS, check_budget_suffT, JHole.mcsPPJS, jPreemptRestHypE_of,
  hPre_ofZE, dispatch_invokeJPZE, dispatch_invokeJEPZE, handle_invocation_refinesJ.
## sch10 (branch par/sched10 in FL4-sc, on b629a541 = int/j2 incl. sch9, kp14)
New leaves XTopJointIrqZR, XTopJointKEntry6 (imported from Fl4Proofs.lean). Nothing existing edited; JAtZ, XTopJointIrq,
XTopJointPreempt*, ScPPR/SpecPPR*/CnDel/WJL*/Tcb*/UtReset*/PP*/ScCharge*/Entry untouched.
- (2) DONE: the IRQ case of `KPreFinRestHyp` [W] closed for every covered preemption hole.
  * XTopJointIrqZR: `armed_schedStep` (FL4's node `ARMED` write with the spec unchanged is a `SchedStep`:
    `SchedRel.set_armed`, offset 80 ∈ `SFootI` so `domSame_of_sfootI` keeps DomRelW, P1 `nodew_bxc` for BlkOK),
    `JAtZ.armedJ` (by `JAtZ.schedJ`); `JAtZ.handleIrqJJ` = XTopJointIrq's `JHole.handleIrqJ` from a `JAtZ` state
    with `JAt` after in every branch (big line / signal mask by `JAtZ.msArJ`; signal by `signalJHyp_of`, already
    `JAtZ`; timer by `JAtZ.reprogramJ` + `armedJ`; reserved: unchanged; inactive: spec fails), l4v
    `handle_interrupt_invs`. `JIrqHypJ` / `jIrqHypJ_of` (same premises as `jIrqHypZ_of`: ARIface, ArchTotal,
    IrqPlat, MIN_BUDGET [P], hNS [S]). `PPQJ` (spec failure or `JAt` after the path), `JHole.afterInvJZJ` /
    `afterInv_of_mcsJ` (copies of afterInvJZ / afterInv_of_mcs with `JIrqHypJ`, post `PPQJ`), `RestE σ` (the holes
    JPreemptRestHypE covers: ¬(PPCov ∨ PPCovT ∨ PPCovI) ∧ CurInv ∧ ct schedulable ∧ head insufficient), `PPQC :=
    PPQJ ∨ (RestE σ1 ∧ PPQ)`, `hPre_ofZEC` (kp14's hPre_ofZE with every covered branch through afterInvJZJ /
    afterInv_of_mcsJ), `dispatch_invokeJEPZEC`.
  * XTopJointKEntry6: `DispPostR` (DispPost with `JAtZR` at ok), `KDispHypsR` (= KDispHypsS with `mid` [W] ending in
    `DispPostR … PPQC`: ok outcome relaxed from JAtS to JAtZR (sch9's note), preempted outcome PPQC, which every
    invocation + after_invocation gives through `hPre_ofZEC`), `dispatch_allR`, `KPreFinRestHypC` [W] (=
    KPreFinRestHyp over PPQC states), `kPreFinHypC_of`, `kernel_entryJ6` = kernel_entryJ5 with `hK : … →
    KDispHypsR`, `hPR : KPreFinRestHypC`, `hRest : JPreemptRestHypE` (kp14, via dispatch_invokeJEPZEC).
  * What is left in `KPreFinRestHypC` (PPQC states without JAt after the path): (a) a `RestE` hole, i.e. exactly
    JPreemptRestHypE's output `PPQ` (JHoleAt-not-JAt or the IRQ's bare XTopAt; closes when kp's line gives that
    branch a PPQJ/JAt post — then KPreFinRestHypC's (a) disappears with no change here but a PPQC variant without
    the RestE disjunct), (b) a failing spec preemption path (spec checkBudget/chargeBudget failure inside
    mcsPP*'s `hmf`, or an inactive IRQ line: `fail_hi_inactive`).
  * For (3), (b) route (not started): an inactive line cannot be pending if inactive lines are masked (l4v
    `valid_irq_masks`, a [J] invariant over `interruptStates`/`irqMasks`) — but IrqPlat.take returns a fresh
    machine state `ms`, so the invariant must be stated about it (an IrqPlat field "the pending line is not
    inactive" [P] would be the cheaper form); the spec charge failures need the asserts of checkBudget/chargeBudget
    shown unreachable from JHole (ScCharge* posts carry the success case only). Neither proved.
- (1) NOT DONE (scope): JMidRunHyp needs a conditional frame, not an FK/DK frame: ct's state is set to Restart and
  back, and every `setThreadState t` in the first-phase cone must be shown to have t ≠ ct dynamically (t blocked on
  an endpoint/notification/reply, ct Restart), which needs the queue-state invariants that live only in the J
  relation (NtfnStateRel/EpRel), and untyped retype/reset need ct's TCB outside the region (JCovD). Plan: (i) state
  `JMidRunHyp` from `CurRun σ` (as stated it is false for a non-runnable entry ct: the fault/error branches leave
  the state); (ii) shell lemma: lookups/decode are `RO` (ScCancelFrame's RO) and first-phase decode yields only
  Endpoint/Notification/Reply/IRQ/Untyped/Arch invocations, so JMidRunHyp ⇐ `JPerfRunHyp` (per perform case, from
  ct Restart: ct ends Restart or runnable); (iii) per case, better at J than in the spec: each perform's J leaf
  already knows the woken thread's queue (sendIpc to receiver, sendSignal, doReplyTransfer), so adding a "ct's
  TCB state kept" conjunct to those posts (with t ≠ ct from `NotIpcBlk`-style facts) is local; arch / IRQ /
  untyped performs touch no TCB state (DK-style frame over `tcbState` at ct with ct ∉ retype region from JCovD).
  KDispHypsR.mid's proof also still needs (C) step 2 (the receive from JMid, sch6's ~45-site list).
- Builds (tokyo, b.sh): sch10-b2 `XTopJointIrqZR XTopJointKEntry6` OK (5522 jobs, on b629a541). Axioms (axsch10.sh,
  untracked; sch10-ax1): propext, Classical.choice, Quot.sound only for kernel_entryJ6, kPreFinHypC_of, dispatch_allR,
  DispPost.toR, JAt.toRE, dispatch_invokeJEPZEC, hPre_ofZEC, afterInv_of_mcsJ, JHole.afterInvJZJ, jIrqHypJ_of,
  JAtZ.handleIrqJJ, JAtZ.armedJ, armed_schedStep, PPQC.toPPQ, PPQJ.toPPQ, kernel_entryJ5, handle_invocation_refinesJ.

## kp15 (branch par/budget11 in FL4-tcbj, on b629a541 = int/j2 incl. kp14, sch9)
- DONE 2fd2dad0 (A)/(B), new leaves ScChargeTA, XTopJointPreemptA (nothing existing edited):
  * ScChargeTA: scripted copies (suffix `A`) of ScChargeT's `JTH.tmoBlockJ`, `JTH.endTimesliceTmoJ`,
    `JHole.chargeBudgetTmoJ` and XTopJointBudgetT's `JHole.checkBudgetT` with `hres : action = ResumeCurThread ∨
    action = ChooseNewThread`. Hand changes at the 3 `hres` sites only: P1 `CanBlock`'s "no switch to t"
    (`actionW_ne_of`), `hact3` (ChooseNewThread after the block: `sendIpcBlock_eq`'s `hact''` for resume, its
    action disjunction for a pending ChooseNewThread), `hres3` (the action kept by the head charge). FOLD LATER:
    the originals are the `Or.inl` instances.
  * XTopJointPreemptA: `JHole.mcsPPJA` (CurInv, non-idle, schedulable, Running/Restart, unqueued, resume or
    choose, insufficient head, non-RR SC, endpoint handler on an idle/sending endpoint: `checkBudgetTA`; FL4's
    `true` outcome excluded by `check_budgetT`'s sufficiency; `JAt` after).
  * FINDING (B): a queued current thread cannot be handled: the timeout fault blocks it and neither side
    dequeues it (spec `endTimeslice` → `handleTimeout`; FL4 `end_timeslice` → `handle_timeout`), so `Inv.rq`
    fails after. It is unreachable at a hole: hence the [J] premise below (case (D), handler cap naming no
    endpoint object, is vacuous: `hcb` quantifies over the endpoint object, `tmoBlockJA` gets it from the cap).
  * `JHoleCtNQHyp arI AR` [J] (l4v `ct_not_queued`, precondition of MCS `check_budget`/`charge_budget … True`
    in `preemption_point`) := `∀ s a σ, JHoleAt arI AR s a σ → CurInv σ → schedulable σ.curThread σ = true →
    ∀ d p, σ.curThread ∉ σ.readyQueues d p`. Why true: `JEntryAt.ctnq` at the invocation; the spec's enqueues
    of the current thread (`set_priority`/`set_domain`/`yield_to`/`sched_context_bind_tcb` on it,
    `end_timeslice`'s append) are in no preemptible invocation; the others (`possible_switch_to`,
    `reschedule_required`'s switch target) name woken/switched-to threads. Removing it needs a hole-level
    carried fact (e.g. JAtPre/JHole carrying ctnq through the preemptible invocations: CNode delete/revoke,
    untyped reset, cancel badged sends).
  * `JPreemptRestHypC arI AR` [W] := `JPreemptRestHypE`'s hypotheses + `∀ d p, ct ∉ RQ d p` + `∀ x n, kheap
    curSc = sc x n → x.scPeriod ≠ 0` + `∀ xt p bd r q, kheap ct = tcb xt → (Running ∨ Restart) →
    xt.tcbTimeoutHandler = .endpointCap p bd r → kheap p = some (.endpoint (.recvEP q)) → after_invocation …
    (Err Preempted) ⦃ PPQ ⦄`. Exactly kp5 (i) (C).
  * `jPreemptRestHypE_ofC hARI hA hP hmrt hIP hNS hNQ hRC : JPreemptRestHypE` (¬PPCov ⇒ ¬NoTmoSend ⇒ endpoint
    handler + non-RR; NativeScope ⇒ Running/Restart; NoSwitch ⇒ resume ∨ choose; idle/sending endpoint ⇒
    `mcsPPJA` + `afterInv_of_mcs`; receiving ⇒ C). `dispatch_invokeJPZA`, `dispatch_invokeJEPZA` (NEW TOP:
    dispatch_invokeJEPZE's premises with `hNQ : JHoleCtNQHyp` [J] and `hRC : JPreemptRestHypC` [W] for
    `hRest : JPreemptRestHypE`).
- Premise change at the top: `JPreemptRestHypE` [W] REMOVED from the top, replaced by `JHoleCtNQHyp` [J] (new)
  and `JPreemptRestHypC` [W] (narrower than E: receiving handler endpoint only).
- (C) NOT DONE (handoff). The timeout fault of the CURRENT thread to a receiver waiting on its handler's
  endpoint, inside `charge_budget` (a `JTH` state, then as `endTimesliceTmoJA`/`chargeBudgetTmoJA` with the
  `reschedJ`/`reprogramJ` tail; spec `sendIpc`'s `recvEP (dest :: _)` branch: dequeue, `doIpcTransfer` (fault
  transfer: `update_consumed` of ct's SC, `tmoSt`), reply unlink, then `replyPush ct dest reply false` if
  (grant ∨ grantReply) ∧ reply, else `setThreadState ct Inactive`; dest Running, refill unblock check,
  `possibleSwitchTo dest`). XTopJointFaultTmo's `sendTmoRecvIJ` (:653, ~620 lines) / `sendTmoRecvPJ` (:1270,
  ~750) do this for t ≠ ct from a REAL `JAtZ` base where t is Inactive (`tmoBaseJ`: t with the fault, its SC's
  consumed cleared), reading the frame base→end on shadows `rhoT` (t's TCB and SC as at the base) and closing
  with `JAtZ.wake_postD` + `sendTailJ`. The ct-specific uses: `hcr`/`hdc` (receiver ≠ ct; for t = ct it is
  `htd`), `htc` at `hc3` (:1123, `stsAct_ne` for `setThreadState t Inactive`; for t = ct it sets
  ChooseNewThread when the action is resume, a no-op otherwise), `htc5` (:1242). Two routes:
  (a) tmoBlockJA-style: run the FL4 steps on `IRel` from the `JTH` state (copy the FL4/IRel half of
  sendTmoRecvIJ: `ep_dequeue_c`, `xferTmoStepJ`, reply unlink, `set_thread_state` / `reply_push`, wake), and
  assemble `JAtZ` from `Hj.j0` with the composite frame `ScOnly` then the send's frame, with the shadow taken
  at the hole base (ct's TCB and SC as at `σ0`), `Inv` after from `InvBut ct` (Inactive and BlockedOnReply
  are not `inClassR`) as `tmoBlockJ`'s `hIt.ik`; the receiver's `rd` from `InvBut` (dest ≠ ct).
  (b) a virtual base: a `JAtZ` at the state "ct Inactive with the fault, its SC charged with consumed 0,
  ChooseNewThread" built from `JTH` (FL4: ct's state word and the node action word written), then
  sendTmoRecvIJ/PJ generalised to t = ct under ChooseNewThread. Obstacle for a resume action: the real s7
  has the resume action word, so FL4's `set_thread_state ct INACTIVE` writes the action word, which the
  virtual base does not see — (a) avoids this. Expect ~1200–1500 lines either way; builds here are fast
  (ScChargeTA 10 s), so the cost is context, not CPU. Platform facts needed: `hmax`/`htu` (as
  runTmoP_recv), so `JPreemptRestHypC`'s replacement theorem takes them.
- Kernel-entry wiring (sch line's XTopJointKEntry2/3, out of scope here): replace `JPreemptRestHypK` by
  `JHoleCtNQHyp` + `JPreemptRestHypC` via `jPreemptRestHypE_ofC` and `dispatch_invokeJEPZA` (E from K:
  `jPreemptRestHypE_of ∘ jPreemptRestHypS_of ∘ jPreemptRestHypM_of ∘ jPreemptRestHypL_of`).
- Builds: kp15-b1 (ScChargeTA green; XTopJointPreemptA one error), kp15-b2 (XTopJointPreemptA green, 5436
  jobs), kp15-ax1 (XTopJointEntry up to date). scratch/axkp15.lean (untracked): propext, Classical.choice,
  Quot.sound only for JTH.tmoBlockJA, JTH.endTimesliceTmoJA, JHole.chargeBudgetTmoJA, JHole.checkBudgetTA,
  JHole.mcsPPJA, jPreemptRestHypE_ofC, dispatch_invokeJPZA, dispatch_invokeJEPZA, handle_invocation_refinesJ.
  No sorry/admit/native_decide/bv_decide.

## sch11 (branch par/sched11 in FL4-sc, on 4c7388c7 = int/j2 incl. sch10)
New leaves XTopJointMidRunK, XTopJointMidRunP (spec only, imported from Fl4Proofs.lean); XTopJointMidRun edited (its
only theorem users are in the file itself). JAtZ, ScPPR/SpecPPR*/CnDel/WJL*/Tcb*/UtReset*/PP*/Preempt*/ScCharge*/Entry
untouched.
- (1) restatement DONE a1e93add (lead decision): `JMidRunHyp rep don cptr σ` [W] := `MidEntry σ → ∀ y ∈
  (fl4HandleInvocationR rep false false don true cptr).run σ, y.1 = .ok () → CurRun y.2`, `MidEntry σ` = `run : CurRun σ`
  (l4v ct_active), `nf : ct's tcbFault = none` (l4v fault_tcbs_valid_states: a faulted thread is blocked/inactive),
  `nq : ct ∉ any waiting notification queue` (l4v valid_ntfn). `HIPostMXP.mid` / `handle_invocation_midJ` take
  `(hM : JMidRunHyp …) (hE : MidEntry σ)`. All three fields are true at a syscall entry; deriving them from
  `JAtZ`+`Entered` at the KDispHypsR.mid site is NOT done (run: `J.curRun.run hni`; nf: look for JEntryAt.vfh /
  NoFault-at-J facts; nq: NtfnStateRel puts only BlockedOnNotification threads in queues, ct is running).
- (1) frames DONE ebd9a47a (no premise added anywhere):
  * XTopJointMidRunK: `ctV ct σ` = (curThread, state and fault of the TCB at ct); `KF ct m` := `FK (ctV ct) m`
    (VsDom's projection frame, so dk_step0 is reused). Hand leaves: `kf_setObject_nt` (set_object's aType assertion:
    a TCB is never replaced by another kind), `kf_threadSet` (f keeps state+fault), `kf_threadSet_ne`/
    `kf_setThreadState` (t ≠ ct), `kf_archThreadSet`, `kf_asUser`, `kf_setCap` (`kf_get_set`/`kf_getObject_bind`),
    `kf_setSimpleKo` (simple type ⇒ not a TCB), `kf_setMrs'`, `kfe_bind_returnOk'`, machine/ext ops. ~200 per-function
    lemmas GENERATED from VsDomOps/DomRecDel/TcbDom/AllDom's DK lemmas (sch11gen/gen.py + head.lean + skip.txt/
    hyp.txt, untracked; `bash sch11gen/mk.sh` regenerates after fixing the paths in it), with `(h_ne : t ≠ ct)` for
    replyUnlinkTcb/cancelIpc/replyRemove/replyPush/sendIpcBlocked. Covered: all lookups (kf_lookupCapAndSlot',
    kf_lookupExtraCaps', kf_lookupIpcBuffer', kf_getMrs', kf_getMessageInfo'), doIpcTransfer/transferCaps,
    possibleSwitchTo/reschedule, donation, postpone, IRQ control (kfe_invokeFl4IrqControl'), every arch perform but
    ASID control (kf_performPage*/PageTable/PageDirectory/Pdpt/AsidPool/IoPort/IoportControl/DeriveSubframe/
    TestAndClearAccessed/Pml4Flush). SKIPPED (false unconditionally or need dynamic facts): retypeRegion/deleteObjects/
    reset/invokeUntyped, ASID control, fastFinalise/capDeleteOne/finaliseCap/cancelAllIpc/cancelAllSignals (queue
    members set Restart), sendIpc/sendSignal/doReplyTransfer/updateWaitingNtfn/handleTimeout/sendFaultIpc (→ P).
  * XTopJointMidRunP: `CtRs ct σ` := curThread = ct ∧ ct's TCB (if any) runnable with no fault; `PR ct m` (CtRs kept);
    `pr_of_kf`, `pr_bind`, read-binds `pr_threadGet_bind`/`pr_gts_bind` (a thread whose state is read as blocked is
    ≠ ct). PROVED: `pr_sendIpc` (sender ≠ ct, or block = call = false: the receiver is read BlockedOnReceive; ct's
    fault is read none so the call/fault branch is not taken), `pr_sendFaultIpc`, `pr_handleTimeout` (thread ≠ ct),
    `pr_doReplyTransfer` (receiver read BlockedOnReply; the timeout tail via pr_handleTimeout), `pr_sendSignal`
    (bound TCB read receive_blocked; the waiting-queue head ≠ ct from `NQ ct σ`).
- (1) NOT DONE — the shell `MidEntry σ → JMidRunHyp` (handoff, ~300 lines):
  (a) decomposition of `fl4HandleInvocationR … true` (syscall: fault / error / perform; with blocking = calling = false
      the fault and error handlers are `when false` = pure). Suggested: `HTE P Q m` (every outcome of `run m` from P is
      Q) with a value-aware bind (`hte_bind'`, ExceptT bind = NonDet.bind run m (bindCont f)); draft in
      sch11gen/XTopJointMidRunS.wip.lean (untracked).
  (b) the decode frame: `KFE ct (fl4DecodeInvocation true …)`; no DK lemmas exist for decoders (DomFrame used DecOut).
      The WIP's auto-unfolding `ro_unfold` (unfold the head spec constant) + `dk_step0` hit maxRecDepth at
      lookupCapAndSlot (raise maxRecDepth or go one lemma per decoder); its `hkV` (curThread, kheap) projection is
      WRONG for this cone: `asUser t getRegister` rewrites the TCB object (use ctV, i.e. KF, which kf_asUser covers).
  (c) `NQ` at the perform's start: not in ctV. Needs "the lookups/decode and setThreadState ct Restart keep
      notification objects" (they write only TCBs via asUser/setThreadState, which by aType cannot hit a
      notification): a second frame (projection: the notification view of kheap) or fold NQ into a KF variant.
  (d) okAll for the first-phase decode: decoded invocation ∈ {Endpoint, Notification, Reply, IRQControl,
      IRQHandler, Untyped, Arch} (pattern: AllDom okAll_decode_notDom).
  (e) `setThreadState ct Restart` / `ct Running` keep CtRs (runnable states; one setObject_out lemma).
  (f) remaining perform cases, to name as [W] AT THE TRAJECTORY (not ∀σ: for an arbitrary CtRs state an untyped retype
      can create a TCB at ct): Untyped (retype region disjoint from ct's TCB, l4v invoke_untyped/valid_untyped_inv),
      ASID control (deleteObjects+retype of a free region), IRQ handler set/clear (cap_delete_one of a notification cap:
      cancel_all_signals restarts only BlockedOnNotification threads, ≠ ct by valid_ntfn). Everything else is proved
      above (Endpoint = pr_sendIpc with block = call = false, Notification = pr_sendSignal, Reply = pr_doReplyTransfer,
      IRQ control and non-ASID arch by KF).
- (2) NOT STARTED (receive leaves from JMid / MidE, ReplyRecv/NBSendRecv/NBSendWait dispatch → KDispHypsR.mid).
- (3) NOT STARTED: KPreFinRestHypC (b). Note for the IrqPlat field: `IrqPlat` lives in XTopJointPreempt (out of this
  line's scope), so the [P] field must go into a new structure (e.g. `IrqPlatA := IrqPlat ∧ inactive-line field`) taken
  by kernel_entryJ7; stated over the spec state the existing `take` field quantifies (`getActiveIRQ` returns `some i`
  with `σ.interruptStates i ≠ .irqInactive`), justified by l4v valid_irq_masks (inactive lines masked) + the platform
  never raising a masked line. kernel_entryJ7 not written; the newest top theorem is still kernel_entryJ6.
- Builds (tokyo, b.sh): sch11-b1 XTopJointMidRun OK; b2–b8 MidRunK/MidRunP iterations (generator fixes); b9 the
  S draft (failed, moved out of the tree); sch11-b10 `XTopJointMidRunP XTopJointKEntry6` OK (5526 jobs, incl. the
  KEntry chain over the edited XTopJointMidRun). Axioms (axsch11.sh, untracked, in sch11-b10): propext, Classical.choice,
  Quot.sound only for handle_invocation_midJ, HIPostMXP.mid, kernel_entryJ6, pr_sendIpc/sendSignal/doReplyTransfer/
  handleTimeout/sendFaultIpc, kf_setThreadState/setCap/asUser/setMrs'/doIpcTransfer'/possibleSwitchTo'/replyRemove'/
  cancelIpc'/lookupCapAndSlot'/sendIpcBlocked'/performPageInvocation, kfe_invokeFl4IrqControl'; propext only:
  curRun_ne_idle, kfe_bind_returnOk', CtRs.of_ctV. No sorry/admit/native_decide/bv_decide.
## kp16 (branch par/budget12 in FL4-tcbj, on 10f2b48e = int/j2 incl. kp15, sch10)
- Lead decision done, route (ii): `JHoleCtNQHyp` [J] (kp15) DELETED. The current thread's absence from the
  ready queues is carried to the hole in `PPR0`, no [J] added.
  * ScPPR: `CtNQ σ := ∀ d p, σ.curThread ∉ σ.readyQueues d p`; `PPR0`'s first conjunct is now
    `ct ≠ idle ∧ NoSwitch ∧ CtOK ∧ Chg ∧ CtNQ` (`.1.2.2.2` → `.1.2.2.2.1` for Chg, `.1.2.2.2.2` = CtNQ).
    `PPK.nq : CtNQ σ → CtNQ σ'` (of_cnK, of_ksStep: queues kept; restart: `stsAct` keeps them);
    XTopJointTcbInstall `PPK.of_schedK` takes `hq : σ'.readyQueues = σ.readyQueues` (both callers: the tail's
    `reschedule_required` under `NoSwitch`, `rq_of_resched`), `PPK.updTcbSc` (queues kept).
  * `JAtZ.ppr0_start` takes `hnq` (JEntryAt's `ctnq`); so do `decode_invocation_threadJ_step`,
    `decode_invocation_cnodeJ_stepsL`, `JAtZ.utResetJ`, `JAtZ.jUtRetHypR_of` (XTopJointEntry passes `hE.ctnq`;
    `decOK_J`'s signature unchanged).
  * SpecPPR: `PPR0.of_tr` / `ppr0_finaliseCap` take `CtNQ` after (as kp13's `Chg`).
  * New leaf SpecPPRQ (spec side, namespace `PPNQ`): `NQ c σ` (c in no ready queue, no switch to c pending), `QK c m` + combinators
    + `qk_auto` (copy of SpecNoSwitch's AK machinery); leaves: `qk_tcbSchedAction` (f never adds c), dequeue,
    enqueue/`possible_switch_to`/switch of t ≠ c, `qk_rescheduleRequired'` (target ≠ c by NQ); the restarts
    `qk_restartThreadIfNoFault` / `qk_removeAndRestart{Ep,Ntfn}QueuedThread` for t ≠ c; `qk_cancelAllIpc` /
    `qk_cancelAllSignals` from a state where c is not in that queue (`qk_mapMx_mem`), `nq_ntfnBody` (the queue
    kept by the unbinds: IpcFinNtfnInv `msu_nfr`/`umn_nfr`), `nq_fastFinalise`, `nq_deletingIrqHandler`,
    `nq_finaliseCap` (from `NoQ c`: c queued on no endpoint/notification), `noQ_of` (EpQB + SchedValid.ntfnQ +
    CtOK's NotBlk), `ctnq_finaliseCap` (PPR0 σ → CtNQ after). XTopJointDelR `jFinPPHyp` passes it.
  * XTopJointPreemptA: `JHoleCtNQHyp`, `jPreemptRestHypE_ofC`, the old `dispatch_invokeJPZA/JEPZA` removed
    (JHole.mcsPPJA and `JPreemptRestHypC` kept).
  * New leaf XTopJointPreemptQ: `jAtPre_holeQ` (jAtPre_holeL + CtNQ at the hole: the preemption point keeps the
    queues), `JPreemptRestHypEQ` [W] (= JPreemptRestHypE with `CtNQ σ →`, narrower; `jPreemptRestHypEQ_of`),
    `jPreemptRestHypEQ_ofC hARI hA hP hmrt hIP hNS hRC` (no hNQ), `hPre_ofZQ`, `dispatch_invokeJPZA`,
    `dispatch_invokeJEPZA` (NEW TOP, same names as kp15's: premises as dispatch_invokeJEPZE with
    `hRC : JPreemptRestHypC` [W] for `hRest`; `hNQ` gone).
- Premise change at the top: `JHoleCtNQHyp` [J] REMOVED. Left: `JPreemptRestHypC` [W] (unchanged statement).
- Kernel-entry wiring (sch line's XTopJointKEntry2/3): `dispatch_invokeJEPZA` now takes `hRC` only.
- (C) `JPreemptRestHypC` [W]: NOT started (context spent on the lead decision; kp15's route (a) stands). Shape of
  the work, all new leaves, nothing existing edited:
  1. `JTH.tmoRecvJ` (the core, ~1000–1200 lines, model: XTopJointFaultTmo's `JAtZ.sendTmoRecvIJ` :653 for the
     `Inactive` tail and `sendTmoRecvPJ` :1270 for the reply push, and ScChargeTA's `JTH.tmoBlockJA` for the
     JTH plumbing): `faults.handle_timeout` from a `JTH` state with t = ct (Running/Restart), handler endpoint
     `recvEP (d :: q)`, resume or choose action, ct unqueued (`NotQueued`, now available at the hole from
     `CtNQ`), ⦃ ∃ z ∈ handleTimeout, ∃ V D', JAtZ (Z.mv Z.G V) … ⦄. FL4 half on `IRel` from the JTH state
     (`set_fault`, `ep_dequeue_c`, `xferTmoStepJ`, reply unlink, `set_thread_state ct INACTIVE` (sets
     ChooseNewThread when the action is resume: `stsAct`) or `reply_push`, receiver Running + `possible_switch_to`);
     JAtZ assembled from `Hj.j0` with the composite frame `ScOnly` (the head) then the send's frame (`CFr` as in
     sendTmoRecvIJ, but the shadow taken at the hole base σ0: ct's TCB and SC as there); `Inv` after from
     `InvBut ct` (Hj.inv) since Inactive/BlockedOnReply are not `inClassR` (as tmoBlockJA's `hIt.ik`), the
     receiver's `rd` from `InvBut` (dest ≠ ct: dest is blocked on receive, ct runnable). Platform facts
     `hmax`/`htu` (as runTmoP_recv) become premises of the replacement theorem.
  2. Scripted copies (suffix `R`) of ScChargeTA's `JTH.endTimesliceTmoJA` (:417; the `tmoBlockJA` call at :486
     replaced by `tmoRecvJ`, `hcb` by `hke : kheap p = recvEP (d :: q)`), `JHole.chargeBudgetTmoJA` (:501),
     `JHole.checkBudgetTA` (:732), XTopJointPreemptA's `JHole.mcsPPJA` → `mcsPPJR`.
  3. `jPreemptRestHypC_of hmax htu … : JPreemptRestHypC` (afterInv_of_mcs (mcsPPJR …)); then
     `dispatch_invokeJEPZR` without `hRC` (taking hmax/htu [P]) — no [W] left on the preemption path.
- Builds: kp16-b1/b2 (ScPPR, SpecPPR, SpecPPRQ), kp16-b3 (XTopJointCnDel, XTopJointTcbInstall, XTopJointTcbInsL,
  UtResetTopJ, UtRetResetJ, XTopJointPP, XTopJointWJLRestart, XTopJointDelR, XTopJointTcb, XTopJointEntry,
  XTopJointPreemptQ: green), kp16-b4 (the remaining sinks of the changed modules' cone, XTopJointRecvMid and
  XTopJointKEntry6), kp16-b5 (after renaming the namespace to `PPNQ`: XTopJointPreemptQ, XTopJointRecvMid, XTopJointKEntry6 green). scratch/axkp16.lean (untracked): propext, Classical.choice, Quot.sound only for nq_finaliseCap, ctnq_finaliseCap, qk_rescheduleRequired', qk_cancelAllIpc, nq_ntfnBody, ppr0_finaliseCap, PPR0.of_ppk, jFinPPHyp, JAtZ.ppr0_start, jAtPre_holeQ, jPreemptRestHypEQ_ofC, hPre_ofZQ, dispatch_invokeJPZA, dispatch_invokeJEPZA, handle_invocation_refinesJ. No sorry/admit/native_decide/bv_decide.

## sch12 (branch par/sched12 in FL4-sc, on e8573970 = int/j2 incl. sch11, kp15)
New leaves XTopJointMidRunS, XTopJointIrqZI, XTopJointKEntry7 (imported from Fl4Proofs.lean). Nothing existing edited;
JAtZ, ScPPR/SpecPPR*/CnDel/WJL*/Tcb*/UtReset*/PP*/Preempt*/ScCharge*/Entry untouched.
- (1) DONE 450f99aa (XTopJointMidRunS, spec side + two J lemmas): `JMidRunHyp` [W] is no longer needed as a premise:
  `MidRun.jMidRunHyp_of : JMidPerfHyp don cptr σ → JMidRunHyp rep don cptr σ`. sch11's (a)–(f):
  (a) `syscall_post` (pointwise shell for Syscall_A.syscall: invariant across fault/error phases, final phase from
  the states it starts in on a run from σ) + `post_bindE`/`post_liftE`; `midF`/`midE` = the fault and decode phases of
  `fl4HandleInvocationR` (defeq, used as `mF`/`mE`). (b)+(c) one frame `fV ct σ := (ctV ct σ, nV σ)` (`nV` = every
  notification's `ntfnObj`), `FV`/`FVE` = VsDom's `FK` at `fV`; leaves `fv_asUser` (kf_asUser + `nv_setObject_tcb`: a
  TCB write keeps notifications by set_object's aType assertion), machine/ext ops, `fv_getCap`, `fve_rab`; the rest by
  `fv_auto` (auto-unfold of the head spec constant + dk_step0; `maxRecDepth 20000`, the arch sub-decoders one lemma each
  at 2M heartbeats): getMessageInfo, lookupCapAndSlot, lookupIpcBuffer, lookupExtraCaps, getMrs, decodeFl4IrqControl,
  decodeIrqHandlerInvocation, fl4DecodeUntypedInvocation, the arch decoders (pdpt/pd/pt/page/port/ioportControl/pml4Flush/
  testAndClear/deriveSubframe, archDecodeInvocation, fl4ArchDecodeInvocation), `fve_decodeFirst` (first phase: the
  TCB/Domain/SC/SchedControl/CNode branches throw). So `CtRs ∧ NQ` holds at the perform's start
  (`pr_setThreadState_run`, `nv_setThreadState` for `ct := Restart`). (d) `okAll_decodeFirst`: `FirstInv` (no
  TCB/FL4TCB/Domain/SC/SchedControl/CNode invocation). (e) `pr_setThreadState_run` (any runnable state, also at ct).
  (f) `perf_first`: Endpoint (`pr_sendIpc`, block = call = false), Notification (`pr_sendSignal` with NQ), Reply
  (`pr_doReplyTransfer`), IRQ control, IRQ ack, every arch invocation but ASID control (KF) keep `CtRs`; the rest is
  ADDED `MidRun.JMidPerfHyp don cptr σ` [W] := `∀ inv σ1, MidPerfAt cptr σ inv σ1 → PerfW inv → ∀ y ∈
  ((fl4PerformInvocation false false don inv).run σ1).1, CtRs σ.curThread y.2`, `PerfW` = invokeUntyped,
  IRQHandler setIRQHandler/clearIRQHandler, arch `.spec (.invokeASIDControl _)`; `MidPerfAt cptr σ inv σ1` = σ1 is
  where that perform starts on a run of the invocation from σ (getMessageInfo outcome, `midF` ok outcome, `midE` ok
  outcome `inv`, `setThreadState ct Restart` outcome) — the path from the entry state, never ∀σ (lead decision). l4v:
  `perform_invocation_not_blocking_not_calling_ct_active` (invoke_untyped: the retyped region is free,
  valid_untyped_inv; invoke_irq_handler: cap_delete_one's cancel_all_signals restarts only BlockedOnNotification
  threads; ASID control: delete_objects + retype of a free region). True in reachable states (ct is Restart, its
  TCB outside the free region).
  MidEntry at the site: `JAtZ.midEntry J hni hnf : MidEntry σ` (run = `J.curRun.run hni`; nq from
  `J.xtop.fin.1.1.2.2.1` (NtfnStateRel) + `J.obj` (ObjCover) + `not_in_ntfnQueue` (ScCharge7); `nf` NOT derivable from
  JAtZ: it is JEntryAt.cnf's [J] (l4v fault_tcbs_valid_states), passed in — at the KDispHypsR.mid site JEntryAt is
  only in `inv` (InvSys), so the mid dispatch must take a `cnf` fact for MidSys too). `handle_invocation_midJP` =
  `handle_invocation_midJ` from `JMidPerfHyp` + `Entered` + that `cnf` fact.
- (2) NOT STARTED (scope/context): KDispHypsR.mid [W] is untouched; `kernel_entryJ7` still takes it (as
  `KDispHypsRI.mid`, see (3)). What its proof needs, in order: (i) the mid state after `handle_invocation_midJP`
  (`HIPostMid`: `JMid` = RelTopM ∧ JAt ∧ CurRun ∧ ct ≠ idle at Ok) is not `Entered` (action may be switchThread u /
  chooseNewThread, sch2/sch8); the receive at J (`dispatch_recvJL` → `dispatch_recvJS`, `jRecvIpcHypL_of`, the
  receive_signal leaves) takes `hni : Entered σ`, `hnq : ct ∉ readyQueues` and `hvfh` at its own state: hnq/hvfh at
  the mid state need post facts of the invocation (possibleSwitchTo enqueues only other threads; only TCB installs
  write the fault handler) — a frame like (1)'s over `readyQueues ∋ ct` and ct's fault-handler field is the cheapest
  route (FK on `(ctV, ct ∈ readyQueues, tcbFaultHandler at ct)`: possibleSwitchTo/tcbSchedEnqueue need "t ≠ ct", which
  the woken thread is by the same state-read argument as `pr_sendIpc`); (ii) sch6's ~45 `hni` sites in 14
  XTopJointRecv* files with CurInv-free variants under switch/choose actions (`JAtZ.recvSigActiveJM`,
  `JAtZ.canBlockCurM` exist in XTopJointRecvMid); (iii) the post is `JAtZR` (sch9: KDispHypsR's DispPostR), so a
  receive that blocks ct under a pending switch ends in `JAtZR` not `JAtZ` (sch8's finding) — the block leaves need
  JAtZR copies; (iv) the ReplyRecv/NBSendRecv/NBSendWait dispatch shell (syscall.rs:351-363 vs Syscall.lean:229-237:
  invocation, `after_invocation`, then `handle_recv` only on Ok), preempted outcome `PPQCI` via
  `dispatch_invokeJEPZECI`'s `hPre_ofZECI`.
- (3) DONE (XTopJointIrqZI, XTopJointKEntry7): KPreFinRestHypC (b) closed for the covered preemption holes.
  * ADDED `IrqPlatI arI AR` [P] (new structure, IrqPlat untouched): `base : IrqPlat arI AR` and `act : ∀ s a σ, JAt s a
    σ → arI.take_pending_irq a ⦃ r => ∀ irq ms, doMachineOp (getActiveIRQ true) σ = ({(irq, {σ with machineState :=
    ms})}, False) → ∀ i, irq = some i → σ.interruptStates i ≠ .irqInactive ⦄`. Stated at JAt states only: sch11's
    suggested unrestricted ∀σ form would be UNSATISFIABLE (a spec state with every line inactive and a pending line
    makes it false whenever the platform reports any line) and so vacuous. l4v `valid_irq_masks` (an inactive line is
    masked) + the platform never raising a masked line (IrqPlat.take already gives `irqMasks i = false` for it).
    Removal route: a [J] FL4 invariant "irq state word 0 → line masked in the arch state" (not in JAtZ) plus a [P]
    on `take_pending_irq` never returning a masked line; the arch interface has `mask_irq` but no mask query yet.
  * `JAtZ.handleIrqJI` (scripted copy of handleIrqJJ: post `inactive ∨ JAt`), `JHole.afterInvJZI`,
    `afterInv_of_mcsI` (post `PPQJI` := ∃ z ∈ preemptionPath σ1, JAt after: NO spec-failure disjunct), `PPQCI :=
    PPQJI ∨ (RestE ∧ PPQ)`, `hPre_ofZECI`, `dispatch_invokeJEPZECI`. Finding: on the covered holes the only spec
    failure was the inactive line (the mcsPP*J paths always succeed), so the charge-failure asserts are not reachable
    there; they remain only inside RestE holes (kp15's JPreemptRestHypE).
  * XTopJointKEntry7: `KDispHypsRI` (= KDispHypsR with mid [W] ending in `PPQCI`, slightly stronger post, true as the
    invoking dispatches now prove it), `dispatch_allRI`, REPLACED `KPreFinRestHypC` [W] by `KPreFinRestHypI` [W] :=
    `∀ σ1, PreemptedAt c σ σ1 → RestE σ1 → ∀ r, PPQ σ1 r → (¬ ∃ z ∈ (preemptionPath σ1).1, JAt r.1 r.2 z.2) → finish
    ⦃ same post ⦄` (only RestE holes: KPreFinRestHypC's (a); (b) is gone), `kPreFinHypCI_of`, `kernel_entryJ7` =
    kernel_entryJ6 with `hIP : IrqPlatI` (was IrqPlat), `hK : … → KDispHypsRI`, `hPR : KPreFinRestHypI`.
- Builds (tokyo, b.sh): sch12-b1..b3 `XTopJointMidRunS` (b3 OK, 5384 jobs); sch12-b4/b5 `XTopJointIrqZI
  XTopJointKEntry7` (b5 OK, 5526 jobs). Axioms (axsch12.sh, untracked; sch12-ax1/ax2): propext, Classical.choice,
  Quot.sound only for kernel_entryJ7, kPreFinHypCI_of, dispatch_allRI, dispatch_invokeJEPZECI, hPre_ofZECI,
  afterInv_of_mcsI, JHole.afterInvJZI, JAtZ.handleIrqJI, PPQCI.toC, kernel_entryJ6, MidRun.jMidRunHyp_of/midRun_shell/
  perf_first/okAll_decodeFirst/fve_decodeFirst/fve_midF, JAtZ.midEntry, handle_invocation_midJP; syscall_post: propext.
  No sorry/admit/native_decide/bv_decide.
## kp17 (branch par/budget13 in FL4-tcbj, on 17b1b692 = int/j2 incl. kp16, sch11)
- DONE: `JPreemptRestHypC` [W] (kp15) PROVED; no premise added (the platform facts `hmax`/`htu` [P] come from
  `JEntryGlob.maxTU`/`tu` at the top). kp16's (C) plan, route (b) "virtual base" (kp15's obstacle there, the
  resume action word, is not one: `writesIn_rebase` only needs the base's writes inside the end's footprint, and
  the base includes the thread's own `set_thread_state`). New leaves, nothing existing edited:
  * ScTmoCtBase (da70455f): `JTH.tmoBaseCtJ` — `JAtZ (Z.mv Z.G V) … D sB a (tmoCtSt σ t sc x y n b)` at a VIRTUAL
    state from a `JTH` hole: FL4 `set_fault` (4 words) + `set_thread_state t INACTIVE` (state + action word) +
    the SC's CONSUMED word; spec `tmoCtSt` = `tmoSt (stsAct (updK (updK σ t xF) t xT) t)` (ChooseNewThread). JAtZ
    assembled as tmoBlockJA from the hole's base with the composite frame ScOnly (head) → BFrT (t to a fake
    blockedOnSend + fault) → KFr (to Inactive, stsAct) → ScOnly/QKY (the SC step; `ScOnly.updC`); Inv by
    `InvBut.ik` (Inactive is not `inClassR`). Also exports `WritesIn s sB (CnW s σ)` / `(KW s ∨ False)`.
  * ScTmoCtRecvI / ScTmoCtRecvP (41feed63): `JAtZ.sendTmoRecvCtIJ` / `sendTmoRecvCtPJ` — scripted copies
    (scratch/kp17/genI.py, genP.py, untracked) of XTopJointFaultTmo's `sendTmoRecvIJ`/`PJ` for t = curThread:
    the base `J0` a parameter linked to the pre-state by `hk0`/`hk0t`/`hk0s`/`hsk0 : Sk σ σ0`/`hrq0`; shadow
    frames start from `Fr0`/`IK0`/`SK0` (rhoT σf has σ0's kheap, the action may differ); receiver ≠ ct by
    t ≠ d; the end read on the shadow up to the action (`cfr_congrK`/`ik_congrK`/`skeep_congrK`); after the
    sender's `set_thread_state`/`reply_push` the action is ChooseNewThread (`stsAct_cur`), giving ActIdle,
    CurRunM, cur. Post `∃ V Lst', JAtZ (Z.mv Z.G V) H Cs Ac Lst' D …` (not just `JAt`). `ipcBufCapOK_tr`,
    `bufCover_tr` (buffer facts from the base).
  * ScTmoCtRecv (b3e31191): `JTH.tmoRecvJ` — `handle_timeout` of ct at a JTH state, handler endpoint
    `∃ l, recvEP l`: tmoBlockJA's head (handler cap, set_fault), `tmoBaseCtJ`, then CtPJ/CtIJ as
    `runTmoRecvJ`. `tmoCtSt_kh/kt/ksc/sk/rq`.
  * ScChargeTR (1e8ca8c0): scripted copies (scratch/kp17/genC.py) `JTH.endTimesliceTmoJR`,
    `JHole.chargeBudgetTmoJR`, `JHole.checkBudgetTR`, `JHole.mcsPPJR` (`hkl : ∃ l, kheap p = recvEP l` for
    `hcb`, `hmax`/`htu` added).
  * XTopJointPreemptR (this commit): `jPreemptRestHypC_of hARI hA hP hmrt hIP hNS hmax htu : JPreemptRestHypC` (resume/choose
    from NoSwitch, `mcsPPJR`, `afterInv_of_mcs`); `dispatch_invokeJPZR`, `dispatch_invokeJEPZR` (NEW TOP: premises
    of dispatch_invokeJEPZA without `hRC`; `jPreemptRestHypC_of … hG.maxTU hG.tu`).
- Premise change at the top: `JPreemptRestHypC` [W] REMOVED. The preemption path (`hPre`) has no named premise
  left; what remains there are the platform/arch facts it already took (hARI, hA, hnd, hPP, hmrt, hIP) and `hNS`.
- FOLD LATER: ScChargeTA's A-lemmas and ScChargeTR's R-lemmas differ only in the send; XTopJointFaultTmo's
  sendTmoRecvIJ/PJ are the t ≠ ct instances of a common core (the base as parameter, as here).
- Kernel-entry wiring (sch line's XTopJointKEntry2/3/4, out of scope): they still take `JPreemptRestHypK`;
  switching to `dispatch_invokeJEPZR` drops it (no replacement premise).
- Builds: kp17-c1..c10 (single-file checks, scratch/kp17err.sh), kp17-ax1 (ScTmoCtBase, ScTmoCtRecvI,
  ScTmoCtRecvP, ScTmoCtRecv, ScChargeTR, XTopJointPreemptR, XTopJointEntry; scratch/axkp17.lean untracked).
- Axioms (kp17-ax1): propext, Classical.choice, Quot.sound only (ScOnly.updC: propext; ipcBufCapOK_tr: propext,
  Quot.sound) for ScOnly.updC, JTH.tmoBaseCtJ, ipcBufCapOK_tr, bufCover_tr, JAtZ.sendTmoRecvCtIJ/CtPJ,
  JTH.tmoRecvJ, JTH.endTimesliceTmoJR, JHole.chargeBudgetTmoJR, JHole.checkBudgetTR, JHole.mcsPPJR,
  jPreemptRestHypC_of, dispatch_invokeJPZR, dispatch_invokeJEPZR, handle_invocation_refinesJ. No
  sorry/admit/native_decide/bv_decide.

## sch13 (branch par/sched13 in FL4-sc, on b2c1ab2d = int/j2 incl. sch12, kp17)
New leaves XTopJointIrqPlat, XTopJointIrqZJ, XTopJointKEntry8 (imported from Fl4Proofs.lean). Nothing existing edited;
JAtZ, ScPPR/SpecPPR*/CnDel/WJL*/Tcb*/UtReset*/PP*/Preempt*/ScCharge*/ScTmoCt*/Entry untouched.
- (0) lead check of sch12's `IrqPlatI.act` [P] (XTopJointIrqPlat):
  * `JAt` does NOT imply l4v `valid_irq_masks`: `JAtZ.msArJ` gives `JAt` at `{σ with machineState := ms}` for ANY
    `ms` with the same memory, so the spec's `irqMasks` are unconstrained by `JAt`.
  * But `act` is IMPLIED by `IrqPlat` (`irqPlatI_of : IrqPlat arI AR → IrqPlatI arI AR`), for a worse reason:
    `IrqPlat.take` (XTopJointPreempt, kp line) is `∀ a σ, take_pending_irq a ⦃ r => ∃ irq ms, doMachineOp
    (getActiveIRQ true) σ = ({(irq, …)}, False) ∧ (r.1 = NO_IRQ ↔ irq = none) ∧ … ⦄`, quantified over EVERY spec
    state while `take_pending_irq a` does not depend on σ. At the all-masked copy of any state the spec reports
    `none` (`getActiveIRQ_masked`/`_eq`), so `IrqPlat.noIrq : IrqPlat arI AR → ∀ σ a, take_pending_irq a ⦃ r =>
    r.1 = NO_IRQ ⦄`. FINDING (lead decision; `IrqPlat` is in XTopJointPreempt, out of this line's scope): `IrqPlat`
    is satisfiable only by a platform that never reports an interrupt, so every theorem taking it covers only the
    `NO_IRQ` branch of `check_interrupt`; the `handle_interrupt` work under it (handleIrqJI etc.) is dead there.
    Fix shape: tie the spec machine state to the platform (l4v shares `machine_state` between the levels): a
    platform relation `MR a σ.machineState` carried in the joint relation from the entry (arch ops keep it with
    their machine-op counterparts; `JAtZ.msArJ`'s arbitrary `ms` would then be constrained), `take` stated under
    `MR a σ.machineState` (+ `MR` after). Then `act` needs `valid_irq_masks` [J] (∀ i, interruptStates i =
    IRQInactive → irqMasks i) at the hole state on the path, carried from the entry through the invocation and the
    preemption point (spec `setIRQState` masks iff inactive, DelPost/IntRel already show the update), and the
    platform half "no masked line reported" is `take`'s existing `irqMasks i = false` conjunct.
  * No theorem below takes `IrqPlatI` any more (kernel_entryJ8 takes `IrqPlat`; `act` is derived).
- (lead note, kp17) `KPreFinRestHypI` [W] DELETED; `JPreemptRestHypE` gone from the top (XTopJointIrqZJ): kp17's
  `RestE` holes are `JHole.mcsPPJA` (blocking handler endpoint) and `JHole.mcsPPJR` (receiving), both of
  `afterInv_of_mcsI`'s form, so `jPreemptRestHypEQ_ofI` ends in `r.1 = false ∧ PPQJI` (JAt after the path, no spec
  failure); `hPre_ofZQI` (hPre_ofZQ ending in `r.1 = false ∧ PPQJI` at every hole of a related `JAtPre` state),
  `dispatch_invokeJAll` (dispatch_invokeJEPZR ending in `PPQJI`).
- (2)(iv) DONE: the ReplyRecv / NBSendRecv / NBSendWait dispatch shell (XTopJointKEntry8). `KDispHypsRI.mid` [W]
  (the whole mid dispatch) is replaced by:
  * the entry facts for the mid invocation, as `inv` has them: `JEntryGlob`, `JEntryAt` (incl. `cnf`, used for
    `MidEntry` at the dispatch state = the entry's own [J] fact, `J.midEntry hni hE.cnf`), `JPathAt … ct false false
    true true (L.mem s (regA ct rg))` (rg = REPLY or NBSEND_RECV_DEST);
  * `MidRun.JMidPerfHyp true cptr σ` [W] (sch12, unchanged);
  * ADDED `JMidRecvHyp arI AR cptr cr σ` [W] := `∀ y ∈ ((fl4HandleInvocationR true false false true true cptr).run
    σ).1, y.1 = .ok () → ∀ s1 a1, JMid s1 a1 y.2 → handle_recv s1 a1 true cr ⦃ r => ∃ z ∈ (handleRecv true cr
    y.2).1, RelTopM r.1 z.2 ∧ ∃ Z H Cs Ac Lst D, JAtZR … r.1 r.2 z.2 ⦄` — only the receive, only at `.ok` outcomes
    of the first phase from the dispatch state (path, not ∀σ). l4v `handle_recv_corres` after
    `handle_invocation_corres` in `handleReplyRecv`. True in reachable states (it is the receive refinement at the
    mid state, which sch12 (2) (i)–(iii) will prove).
  * `MidSysR n c rg sr cr`, `midSysR_of`, `MidSysR.reg` (`regIdx sr = rg`), `regIdx_nbsendRecvDest`, `DispMid`,
    `fl4HandleSyscall_mid` (rfl per case), `mid_invRecvJ` (handle_invocation_entryJ + `HIPostMXP.mid` with
    `jMidRunHyp_of`; Ok → `JMidRecvHyp`; Err .Preempted → `hPre_ofZQI`, `r.1 = false` skips the receive),
    `dispatch_midJ` (FL4's number chain; NBSendRecv's extra register read).
  * `KDispHyps8` (`inv`, `recv` as KDispHypsRI; `mid` as above), `dispatch_all8` (every native dispatch ends in
    `DispPostR` with `PPQJI`), `KPreFinHypJI`/`kPreFinHypJI_of` (kPreFinHypCI_of's JAt case only), NEW TOP
    `kernel_entryJ8` = kernel_entryJ7 with `hIP : IrqPlat` (was IrqPlatI), no `hRest` (JPreemptRestHypE), no `hPR`
    (KPreFinRestHypI), `hK : … → KDispHyps8`.
- Premise changes at the top (kernel_entryJ8 vs J7): REMOVED `KPreFinRestHypI` [W], `JPreemptRestHypE` [W]
  (kp17), `IrqPlatI.act` [P] (derived; see the IrqPlat finding); `KDispHypsRI.mid` [W] NARROWED to `KDispHyps8.mid`
  = entry facts ([J], as `inv`) + `JMidPerfHyp` [W] (existing) + `JMidRecvHyp` [W] (new, receive only).
- NEXT (handoff) for `JMidRecvHyp`, sch12 (2)'s order:
  (i) hnq/hvfh at `y.2`: `ct ∉ readyQueues` and ct's `tcbFaultHandler` valid, from the entry's `ctnq`/`vfh` across
      the first phase. Route: a second projection frame next to MidRunS's `fV` (`(ctV, nV)`): add `qV ct σ := (∀ d p,
      ct ∉ readyQueues d p)` is not a projection (enqueues of other threads change the queues) — use a PR-style
      predicate as MidRunP's `CtRs` (`QR ct m`: kept by every leaf; `tcbSchedEnqueue t`/`possibleSwitchTo t` need
      `t ≠ ct`, given by the same state reads as `pr_sendIpc`: the woken thread is read BlockedOn*, ct is runnable);
      the fault handler: extend `ctV` with `tcbFaultHandler` (regenerate sch11gen with the extra field; threadSet
      leaves keep it except TCB installs, which are not first-phase: FirstInv). The PerfW cases need `JMidPerfHyp`
      widened to these two facts (same [W], same l4v lemma family).
  (ii) the receive leaves from `MidE` (resume or `switchThread u`, u ≠ ct) instead of `Entered`: under `MidE`,
      `CurInv` is available (`J.curInv hni.ncn`, as `JAtZ.recvSigActiveJM`), so most of sch6's ~45 `hni` sites are
      `hni.2 ▸` → `hni.ncn`, `Or.inl hni.2` → `hni.sa`, `hni.1` → `hni.1`; no-pending-switch-to-ct from `MidE`'s
      `u ≠ ct`. A `chooseNewThread` mid state (possible: a reply/send's `rescheduleRequired`) needs its own case
      (CurInv absent; the blocking leaves' `hsa` allows `chooseNewThread ∧ sc = none` only).
  (iii) the blocking leaves ending in `JAtZR` under a pending switch (`JAtZ.cur` fails: ct blocked, action
      `switchThread u`): R copies of the block lemmas with `cur := curInvR` (CurInvR holds: action ≠ resume).
  (iv) `JMid` → `MidE`: the action facts at the mid state (sch8) are a post of the invocation; also needed.
- Builds (tokyo, b.sh): sch13-b1..b4 (elaboration fixes: getActiveIRQ_masked membership, a name clash with PreemptI's dispatch_invokeJEPZI), sch13-b5 `XTopJointIrqPlat XTopJointIrqZJ XTopJointKEntry8` OK (5558 jobs, on b2c1ab2d). Axioms (axsch13.sh, untracked; sch13-ax1): propext, Classical.choice, Quot.sound only for kernel_entryJ8, dispatch_all8, kPreFinHypJI_of, dispatch_midJ, mid_invRecvJ, fl4HandleSyscall_mid, midSysR_of, dispatch_invokeJAll, hPre_ofZQI, jPreemptRestHypEQ_ofI, irqPlatI_of, IrqPlat.noIrq, getActiveIRQ_masked/_eq, handle_invocation_refinesJ. No sorry/admit/native_decide/bv_decide.

## budtr (branch par/budtr in FL4-rb, on 3febf556 = int/j2 incl. sch13)
New leaves XTopJointBudgetTR, XTopJointKEntry8B (imported from Fl4Proofs.lean). Nothing existing edited.
- Problem (INV-PLAN §1.2 B4): `KBudget.tmo` = `NoTmoSend σ0 ∨ (ct ∉ RQ ∧ ct Running/Restart ∧ endpoint handler p ∧
  non-RR SC ∧ ∀ xe, kheap p = ep xe → CanBlock false xe)` is FALSE in reachable states when a receiver waits on the
  handler endpoint (recvEP) and the SC is not round-robin.
- DONE `JAtZ.budgetOkTR` (XTopJointBudgetTR): scripted copy of `JAtZ.budgetOkT` with `hkl : ∃ l, kheap p =
  recvEP l` for `hcb` and kp17's `JHole.checkBudgetTR` (action `Or.inl resumeCurThread`) for `checkBudgetT`; extra
  [P] `hmax`/`htu` (already top premises of kernel_entryJ8).
- DONE XTopJointKEntry8B:
  * `KBudgetB arI a σ0` = KBudget with `tmo : NoTmoSend σ0 ∨ ∀ d p, σ0.curThread ∉ σ0.readyQueues d p` [J]
    (l4v `ct_not_in_q`: not queued while `scheduler_action = resume_cur_thread`, given by `Entered`; the same fact
    as `JEntryAt.ctnq` at σb). `KBudget.toB : KBudget → KBudgetB` (strictly weaker premise).
  * `JAtZ.budgetOkB`: kernel_entryJ8's `hBud` under KBudgetB, every case: NoTmoSend → budgetOkJ+F; else
    `¬NoTmoSend` gives the endpoint handler (`isEpCap`) and a non-RR SC (`hper` by kheap determinism);
    Running/Restart from `JAtZ.curRun` (`CurRunM.run` under `Entered`) + `NativeScope` (not RunningVM); then the
    endpoint state: recvEP → `budgetOkTR`, idle/sendEP/non-endpoint → `budgetOkT` (`CanBlock false`).
  * NEW TOP `kernel_entryJ8B` = kernel_entryJ8 with `hB : ∀ x, kheap ct = tcb x → KBudgetB arI a (faultIPSt σ ct
    x)`; `NativeScope` at the entry from the existing [S] `hNSR` applied to `J0.toR`. No other premise changed.
- Premise change at the top (J8B vs J8): `KBudget.tmo` [J, false in reachable states] REPLACED by `KBudgetB.tmo` =
  `NoTmoSend σ0 ∨ ct ∉ readyQueues` [J] (true in reachable states). No premise added elsewhere.
- Removing `KBudgetB.tmo` entirely needs `ct_not_in_q` carried at the entry state (a JAtZ field or a carried
  bundle beside it; JEntryAt.ctnq is the same fact one step later at σb).
- Builds (tokyo): budtr-b2 (mirror warmed from FL4-audit's .lake; XTopJointBudgetTR built, KEntry8B one rewrite
  error: σ0 instantiated unfolded, fixed by `(σ0 := faultIPSt …)`), budtr-b3 `XTopJointBudgetTR XTopJointKEntry8B`
  OK (5562 jobs). Axioms (scratch/axbudtr.lean, untracked): propext, Classical.choice, Quot.sound only for
  JAtZ.budgetOkTR, JAtZ.budgetOkB, KBudget.toB, kernel_entryJ8B. No sorry/admit/native_decide/bv_decide.
## irq1 (branch par/irq1 in FL4-tcbj, on 3febf556 = int/j2 incl. sch13)
New leaf XTopJointMachRel (imported from Fl4Proofs.lean). Nothing existing edited.
- FINDING (formal, `PPPlat.false : PPPlat arI AR → A → False`; inv1's `nowAgree_all_false`): `PPPlat.now : ∀ a σ,
  NowAgree arI a σ` is FALSE for every platform (at `curTime = allOnes` the spec clock is capped at
  `-(getCurrentTimeBuffer+1)` < allOnes, `getCurrentTime_buffer_pos`). So every theorem with `hPP : PPPlat` (or
  `JEntryGlob`, whose `pp` is a PPPlat) and an arch state is vacuous: the preemption path, budget, `dispatch_all*`,
  `kernel_entryJ*` up to J8. `IrqPlat.take` / `PPPlat.irq` are satisfiable only with "no line ever" (sch13 noIrq).
- ∀σ platform premises on kernel_entryJ8 (grep of its premises and the bundles they carry):
  `hPP.now` (false), `hPP.irq` (degenerate), `hIP.take` (degenerate), `JEntryGlob.pp` (= PPPlat, false),
  `JEntryGlob.portIn` = `PortInVal` (∀ σ ∃ ms, the spec `in8/16/32` at σ returns FL4's value: consistent only via the
  opaque `inNImpl`, the same shape; needs the device/port part of MR). Arch-only ∀a facts (`irqAR`, `takeAR`,
  `noIpi`, `ackAR`, `minBudget`, `hmrt/hmb`, `TimeAgree`, `htu`, `ArchIrqRel.map/mapr/mask`) are fine.
  `KBudget.now` is per-state (derivable: `MachPlat.nowAgree` from MR + `ValidMachineTime` at the entry).
  ∀-predicates that are not platform reads (`hNS`, `hNSR`, `JEntryGlob.sigRest`, `delParts.vt/thr.obj`) are out of
  this line.
- DONE (XTopJointMachRel): `getCurrentTime_eq` / `getActiveIRQ_eq` (the spec reads are deterministic functions
  `gctVal/gctState`, `gaiLine/gaiState` of the machine state); `MachPlat arI MR` [P] (statement in the module):
  `now : MR a ms → now a ⦃ r.1.bv = gctVal ms ∧ MR r.2 (gctState ms) ⦄`, `irqPending : MR a ms → irq_pending a ⦃
  (r.1 ↔ gaiLine true ms ≠ none) ∧ MR r.2 (gaiState ms) ⦄`, `take : MR a ms → take_pending_irq a ⦃ (r.1 = NO_IRQ ↔
  gaiLine true ms = none) ∧ (∀ i, gaiLine true ms = some i → r.1.val = i.toNat) ∧ MR r.2 (gaiState ms) ⦄`, `mask :
  MR a ms → w < 256 → mask_irq a w m ⦃ MR a' {ms with irqMasks := update … (w.setWidth 8) m} ⦄`, `ack : MR a ms →
  ack_irq a w ⦃ MR a' ms ⦄`, `frame` (MR reads only masks, irqState, timeState, lastMachineTime);
  `ValidMachineTime σ` [J] (l4v valid_machine_time: curTime ≤ lastMachineTime ≤ cap); `MachPlat.nowAgree` (old
  per-state NowAgree from MR + VMT), `MachPlat.nowAt` (+ MR and VMT after), `MachPlat.irqAt`, `MachPlat.takeAt`
  (old per-state shapes + MR after); non-vacuity: `modelArch` (arch state = spec machine state, reads run the spec
  ops) with `modelArch_machPlat`, `modelArch_take_some` (reports the spec's line), `modelArch_noIrq_iff` (never
  NO_IRQ-only unless the spec oracle never fires), `MachPlat.noIrq_imp`.
- FINDING 2 (blocks threading MR through the preemption point; code reading): FL4 `sched.preemption_point`
  (Funs.lean, `if ok1 … irq_pending a1 … else ok (Err Preempted, s3, a1)`) does NOT read the pending line when the
  budget is insufficient (nor when the domain expired; numDomains = 1), while the spec `preemptionPoint`
  (Fl4Spec/KHeap.lean:601) samples `getActiveIRQ true` unconditionally. With the oracle position shared (MR), the
  spec is one IRQ sample ahead after that branch: `after_invocation`'s `take_pending_irq` answers position p+1, the
  spec's `maybeHandleInterrupt` reads p+2, so the handled lines can differ and the refinement is FALSE for
  `modelArch` there (the existing proofs hide it: `JHole.msAr` lets the spec machine state be anything). No
  satisfiable MR can absorb the skip (MR a ms ∧ MR a (gaiState ms) forces the oracle constant). C seL4 (c98d70ad
  src/model/preemption.c, MCS) reads first: `if (isIRQPending() || isCurDomainExpired() || !(sc_active(ksCurSC) &&
  refill_sufficient(…)))`, i.e. it samples unconditionally like the spec; FL4 reordered the test. Fix (owner
  approval, kernel change + re-extraction): FL4 `preemption_point` calls `irq_pending` right after
  `update_timestamp`, before the budget/domain tests (C's order). A spec deviation is the wrong direction (spec = C).
- NEXT (handoff), after FINDING 2 is decided:
  (1) MR transport lemmas, each = an FL4 arch trace + a spec trace, combined with the existing J lemmas by
      `WP.spec_and` (no copies of the big proofs): `update_timestamp ⦃ ∃ v, arI.now a = ok (v, r.2) ⦄`;
      `preemption_point ⦃ Err → ∃ v a1, now a = ok (v,a1) ∧ irq_pending a1 = ok (true, r.2.2) ⦄` (after the fix);
      spec: `preemptionPoint`'s error outcome has `ms = gaiState (gctState σ.ms)` and VMT (from `pp_err_eq`);
      `mcs_preemption_point` keeps the arch state / `checkBudget`/`chargeBudget` keep the MR fields; then
      `JAtZ.ppJHM` (ppJH + MR + VMT at the hole) and `JHole.afterInvJZJM` (take via `MachPlat.takeAt`).
  (2) carry `MR a σ.ms ∧ VMT σ` from the entry ([J], l4v shared machine_state + valid_machine_time) through
      budget_ok (nowAt) and through every invocation up to its preemption points and `after_invocation`: needs each
      invocation's post to keep MR (FL4 arch ops other than now/irq/take/mask/ack keep MR [P], ARKeep-style; spec
      machine ops other than getCurrentTime/getActiveIRQ/maskInterrupt keep the four MR fields: a spec-only
      `MK`-style lemma family as UtResetSpecJ's `MK`). This is the L-size part (inv1 G0, ~25 use sites).
  (3) kernel_entryJ9 = J8 with `MachPlat` + `MR a σ.ms` + `ValidMachineTime σ` at the entry for `hPP.now/irq` and
      `hIP.take`; NOT started (needs (1)–(2); a J9 with PPPlat would still be vacuous).
- Builds (tokyo, scratch/irq1chk.sh, kp1build.sh): irq1-c1..c4 (elaboration), irq1-b1 `XTopJointMachRel` OK (5528
  jobs, on 3febf556). Axioms (scratch/axirq1.lean, untracked): propext, Classical.choice, Quot.sound (or fewer) for
  PPPlat.false, MachPlat.nowAgree/nowAt/irqAt/takeAt/noIrq_imp, modelArch_machPlat, modelArch_take_some,
  modelArch_noIrq_iff, getCurrentTime_eq, getActiveIRQ_eq, validMachineTime_gct. No sorry/admit/native_decide.
## sch14 (branch par/sched14 in FL4-sc, on 3febf556 = int/j2 incl. sch13, kp17)
New leaves XTopJointMidRunQ, XTopJointKEntry9M (imported from Fl4Proofs.lean). Nothing existing edited;
JAtZ, ScPPR/SpecPPR*/CnDel/WJL*/Tcb*/UtReset*/PP*/Preempt*/ScCharge*/ScTmoCt*/Entry/Irq* untouched.
- (i) DONE for hnq + "no switch to ct" (XTopJointMidRunQ, spec side): `qV σ := (readyQueues, schedulerAction)`,
  `QV := FK qV` (VsDom frame; leaves scripted from SpecGlobFK's GK lemmas (arch performs, cap ops), AllDom's DK
  lemmas (lookups, IPC transfer, refills, IRQ control) and XTopJointMidRunS's decode lemmas, `qv_auto2` = auto-unfold
  as `fv_auto`); `CQ ct σ := CtRs ct σ ∧ PPNQ.NQ ct σ` (SpecPPRQ's NQ: ct in no ready queue, no switch to ct
  pending), `PQ ct m` (KF + QK together, `pq_of`); `pq_sendIpc` / `pq_sendSignal` / `pq_doReplyTransfer`
  (+ `pq_handleTimeout`, `pq_sendFaultIpc`): copies of MidRunP's `pr_` lemmas, the woken thread `≠ ct` by the same
  state reads, so `possible_switch_to` keeps NQ (`qk_possibleSwitchTo`); QK leaves `qk_postponeQ`,
  `qk_schedContextResumeQ`, `qk_maybeDonateScQ`, `qk_replyPushQ`, `qk_sendIpcBlockedQ`; `perf_firstQ`; ADDED
  `MidRun.JMidPerfHypQ don cptr σ` [W] := `∀ inv σ1, MidPerfAt cptr σ inv σ1 → PerfW inv → ∀ y ∈
  ((fl4PerformInvocation false false don inv).run σ1).1, CQ σ.curThread y.2` (sch12's JMidPerfHyp with CQ for
  CtRs; same path restriction and l4v family: perform_invocation_not_blocking_not_calling_ct_active +
  ct_not_in_q/scheduler_act_sane for invoke_untyped / invoke_irq_handler set,clear / ASID control),
  `JMidPerfHypQ.toP`; `midRunQ_shell`: from `CQ ∧ NQ` at the entry every outcome of the first phase is `CQ`.
  hvfh is NOT a frame (see JMidVfhHyp below).
- (iv) partly: from `CQ` the mid state has no switch to ct; the resumed case is an `Entered` state.
- XTopJointKEntry9M:
  * ADDED `JMidVfhHyp cptr σ` [J] := `∀ y ∈ ((fl4HandleInvocationR true false false true true cptr).run σ).1,
    y.1 = .ok () → ∀ x, y.2.kheap y.2.curThread = some (.tcb x) → validFaultHandler x.tcbFaultHandler` (l4v
    valid_objs/valid_tcb `valid_fault_handler`, kept by handle_invocation (hinv_invs); JEntryAt.vfh [J] at the
    mid state). Why not a frame: the first phase's cap writes (granted-cap cte_insert, IRQ control's handler cap,
    the arch cap updates) go to slots found by a CSpace lookup; that such a slot is not ct's TCB fault-handler
    slot (`setCap` on a TCB slot index 3 writes `tcbFaultHandler`) holds only by `valid_cap` (a CNode cap names a
    CNode). True in reachable states.
  * ADDED `JMidRecvHypS arI AR cptr cr σ` [W] = JMidRecvHyp restricted to `.ok` outcomes with
    `y.2.schedulerAction ≠ .resumeCurThread`, and with `∀ d p, y.2.curThread ∉ y.2.readyQueues d p`,
    `y.2.schedulerAction ≠ .switchThread y.2.curThread` and ct's valid fault handler as premises (l4v
    handle_recv_corres at a mid state with a pending switch/reschedule). True in reachable states (it is a
    special case of sch13's JMidRecvHyp).
  * `jMidRecvHyp_of`: JMidRecvHyp from JMidPerfHypQ + JMidVfhHyp + JMidRecvHypS + `CQ ∧ NQ` at the dispatch
    state; the resumed case by `handle_recvJ` + `jRecvIpcHypL_of` + `jRecvSigHyp_of` (all proved), `.toR`.
    `JAtZ.midCQ` (CQ ∧ NQ from Entered + JEntryAt.cnf/ctnq). `KDispHyps9M` (mid: JEntryGlob/JEntryAt/JPathAt,
    JMidPerfHypQ, JMidVfhHyp, JMidRecvHypS), `dispatch_all9M`, NEW TOP `kernel_entryJ9M` = kernel_entryJ8 with
    KDispHyps9M for KDispHyps8.
- Premise changes at the top (kernel_entryJ9M vs J8): `JMidRecvHyp` [W] NARROWED to `JMidRecvHypS` [W] (only the
  non-resumed mid states) + `JMidVfhHyp` [J]; `JMidPerfHyp` [W] WIDENED to `JMidPerfHypQ` [W] (same three
  performs, + the ready-queue/action fact).
- NEXT (handoff) for JMidRecvHypS, unchanged from sch13 (ii)/(iii) but now only for action ≠ resume:
  (a) switch case (`switchThread u`, u ≠ ct, given by the premise): MidE holds (`⟨ni, CurRun, Or.inr ⟨u, e, hu⟩⟩`,
      CurRun from JMid); sch6's hni sites → MidE (`J.curInv hni.ncn`, `hni.sa`); blocking leaves need JAtZR
      copies (ct blocked under a switch: CurInvR holds as the action is not resume).
  (b) chooseNewThread case: CurInv absent (JAtZ.cur's first disjunct); the leaves' `hsa` second disjunct needs ct
      SC-less, which is false in general (a reply that rescheduled), so a CurInv-free route is needed.
- Builds (tokyo, b.sh): sch14-b1..b3 (elaboration: auto-unfold loops on transferCapsLoop, missing QK/QV leaves,
  setReplyObjRef's type), sch14-b4 `XTopJointMidRunQ XTopJointKEntry9M` OK (5562 jobs, on 3febf556). Axioms
  (axsch14.sh, untracked; sch14-ax1): propext, Classical.choice, Quot.sound only for kernel_entryJ9M,
  dispatch_all9M, jMidRecvHyp_of, JAtZ.midCQ, MidRun.midRunQ_shell/perf_firstQ/pq_sendIpc/pq_sendSignal/
  pq_doReplyTransfer/qve_decodeFirst/qve_fl4ArchPerformInvocation/JMidPerfHypQ.toP, kernel_entryJ8. No
  sorry/admit/native_decide/bv_decide.

## sch15 (branch par/sched15 in FL4-sc, on 866bc7ed = int/j2 incl. sch14, irq1 MachPlat, budtr)
New leaves XTopJointRecvSigM, XTopJointKEntry10M (imported from Fl4Proofs.lean). Nothing existing edited;
JAtZ, ScPPR/SpecPPR*/CnDel/WJL*/Tcb*/UtReset*/PP*/Preempt*/ScCharge*/ScTmoCt*/Entry/Irq*/XTopJointRecv* untouched.
- (1) DONE: `JMidRecvHypS` [W] (the whole `handle_recv` at a non-resumed mid state) is no longer a premise.
  * `handle_recvJR` (XTopJointKEntry10M): `handle_recvJ`'s proof with `Rel := RJR` (`RelTopM ∧ ∃ ghosts, JAtZR`) and
    WITHOUT `hni`/`hnq`/`hvfh`: the registers, `lookup_cap_refines`/`lookup_cap_held`, the caps' objects and
    `recv_bound_leaf` read only `JAtZ` (only the fault leaf `faultHypJZ` read `hni`). Leaves: `JRecvLeavesR`
    (ipc / sig / flt of `RecvLeavesH`, blocking = true, post `RJR`, held caps `JHeld`).
  * ADDED `JMidLeavesHyp arI AR cptr σ` [W] := `∀ y ∈ ((fl4HandleInvocationR true false false true true cptr).run
    σ).1, y.1 = .ok () → y.2.schedulerAction ≠ .resumeCurThread → (∀ d p, ct ∉ readyQueues d p) →
    y.2.schedulerAction ≠ .switchThread ct → (ct's fault handler valid) → ∀ s1 a1, RelTopM s1 y.2 → CurRun y.2 →
    ct ≠ idle → ∀ Z H Cs Ac Lst D, JAtZ … s1 a1 y.2 → ∀ ct', sched.cur_thread st s1 = ok ct' → JRecvLeavesRN …
    Z.th ct' s1 a1 y.2` (ct := y.2.curThread). `JRecvLeavesRN` = `JRecvLeavesR` with `sig` asked only under
    `SigOpen y.2 p` := `chooseNewThread ∨ ∃ x, kheap p = notification x ∧ x not active ∧ x.ntfnSc = some curSc`.
    l4v: receive_ipc_corres / receive_signal_corres / handle_fault_corres inside handle_recv_corres under
    scheduler_act_sane. True in reachable states (each leaf is a part of JMidRecvHypS's receive, which sch13/14
    argued true; the leaves are exactly what handle_recv_refinesH asks besides the proved lookups).
  * `JRecvLeavesRN.full` (the switch mid state's notification receives outside SigOpen by `jRecvSigHypM_of`;
    MidE built from CurRun, ct ≠ idle, action = switchThread u with u ≠ ct), `jMidRecvHypS_of`, `KDispHyps10M`
    (mid with JMidLeavesHyp for JMidRecvHypS), `KDispHyps10M.to9M`, NEW TOP `kernel_entryJ10M` = kernel_entryJ9M
    with KDispHyps10M (proof: kernel_entryJ9M through `.to9M`).
- (2) DONE (XTopJointRecvSigM), the first blocking receive leaf under a pending switch (template for the rest):
  * `Sched.recvSigBlock_act`: the spec's blocking notification receive keeps a non-resume action.
  * `JAtZ.recvSigBlockJM`: `JAtZ.recvSigBlockJ` from `MidE` + action ≠ resume, ending in `RJR`. Changes from the
    resumed copy: CurInv by `J.curInv hni.ncn`; CanBlock by `canBlockCurM`; `ActIdle` after by
    `ActIdle.keepE (E := {ct})` (TKeepE from BFrN.tcbF/scF; the switch target ≠ ct by MidE); `CurInvR` after
    vacuous (action stays switchThread u), `CurRunM` by its first disjunct; `JRestR` + `J.toR.cs_frameI`.
  * `jRecvSigHypM_of`: receive_signal (blocking) at a switch mid state for every notification except the SC
    return (non-active, ntfnSc = curSc): active by `recvSigActiveJM` (sch8) + `.toR`, idle/waiting by
    `recvSigBlockJM`.
- (3) JMidVfhHyp [J]: NOT derived (not cheap: needs l4v valid_cap for the first phase's CSpace-found slots, sch14's
  reason); kept path-restricted as in sch14.
- Premise changes at the top (kernel_entryJ10M vs J9M): `JMidRecvHypS` [W] REPLACED by `JMidLeavesHyp` [W]
  (receive leaves only; the switch-state notification receive except the SC return proved).
- NEXT (handoff) to remove JMidLeavesHyp, leaf by leaf, as recvSigBlockJM:
  (a) switch case (MidE + action ≠ resume, CurInv available via J.curInv hni.ncn):
      - sig SC return (`recvSigRetJ`): after the block (action stays switch u) `maybeReturnSc` unbinds ct's SC
        and, ct being current, `rescheduleRequired` enqueues u and sets chooseNewThread; needs JAtZR (not JAtZ)
        copies of `recvSigBlockPreJ`/`maybeReturnJ(Q)` plus the J-level rescheduleRequired-with-enqueue step
        (the timer cone's signal leaves under a switch do this; see sch9 ZRA/ZRB `wake_specBR`).
      - ipc blocking leaves (`recvIpcBlockJG`/`recvIpcBlockNJG`/`recvSendPJG`/`recvSendFPJG`/`recvSendFPTJ`):
        add the switch disjunct to `hsa`, then exactly recvSigBlockJM's changes (an `recvIpcBlock_eq` action
        lemma like recvSigBlock_act).
      - ipc non-blocking leaves that wake a sender (`recvSendRetJ`, `recvSendP0X`, `recvSendRet(P|PD|T)J`,
        `recvSendT0X`): `possibleSwitchTo sender` under a switch is `rescheduleRequired; tcbSchedEnqueue sender`
        (Fl4Spec KHeap.lean:494), not `setSchedulerAction`: new J proofs of that tail (u and the sender enqueued).
      - flt (`faultHypJZ`'s noFaultJ / faultRecvJ / faultBlockJ): MidE copies ending in JAtZR.
  (b) chooseNewThread case: CurInv may be absent (reply SC return leaves ct SC-less); the leaves' `hsa` second
      disjunct already covers `chooseNewThread ∧ sc = none`; with an SC (e.g. cancelAllSignals' reschedule) CurInv
      may hold but is not in JAtZ (JAtZ.cur's first disjunct). Route: a mid-state post fact "chooseNewThread →
      CurInv ∨ ct SC-less" from the first phase, then the two sub-cases.
- Builds (tokyo, b.sh): sch15-b1 `XTopJointKEntry10M` OK (5564 jobs; first form, 4e6987e9), sch15-b2 (RecvSigM: missing
  XTopJointRecvMid import), sch15-b3/b4 `XTopJointRecvSigM XTopJointKEntry10M` OK (5568 jobs, on 866bc7ed). Axioms
  (axsch15.sh, untracked; sch15-ax1): propext, Classical.choice, Quot.sound only for kernel_entryJ10M,
  KDispHyps10M.to9M, jMidRecvHypS_of, JRecvLeavesRN.full, handle_recvJR, JAtZ.recvSigBlockJM, jRecvSigHypM_of,
  Sched.recvSigBlock_act, kernel_entryJ9M. No sorry/admit/native_decide/bv_decide.

## sch16 (branch par/sched16 in FL4-sc, on f6b23fa2 = int/j2 incl. sch15)
New leaves XTopJointRecvIpcBlockM, XTopJointKEntry11M, XTopJointFaultM, XTopJointKEntry12M (imported from
Fl4Proofs.lean). Nothing existing edited; JAtZ, ScPPR/SpecPPR*/CnDel/WJL*/Tcb*/UtReset*/PP*/Preempt*/ScCharge*/
ScTmoCt*/Entry/Irq*/XTopJointRecv* untouched.
- Item 1 DONE (8a1f2013, XTopJointRecvIpcBlockM): the blocking endpoint receive at a switch mid state (`MidE`, action
  ≠ resume) ending in `JAtZR`: `Sched.recvIpcBlock_eqM` (recvIpcBlock_eq + "action ≠ resume → action kept"),
  `JAtZ.recvIpcBlockJGM` (recvIpcBlockJG with recvSigBlockJM's changes: CurInv by `J.curInv hni.ncn`,
  `canBlockCurM`, `ActIdle.keepE (E := {ct})`, CurInvR vacuous, CurRunM first disjunct, JRestR,
  `J.toR.cs_frameI`), `recvIpcBlockJM` (no bound notification), `recvIpcBlockNJGM` (bound idle/waiting
  notification whose SC is not ct's).
- Also DONE (4336f55f, XTopJointKEntry11M): `JAtZ.recvIpcActJM` (active bound notification from MidE, post JAtZ →
  `.toR`), the basic head sender (`RecvSendBasicCase`, no SC return: `recvSendJ0X` reads no action);
  `IpcDoneM` (Act ∨ Block ∨ Bound∧NoRetM ∨ unlinked∧Basic∧NoRetM), `jRecvIpcDoneM`. `IpcOpen ct s σ p rc :=
  chooseNewThread ∨ ¬ IpcDoneM`; `JRecvLeavesRN2` (ipc only under IpcOpen), `.toRN`, `JMidLeavesHyp2` [W],
  `jMidLeavesHyp_of2`, `KDispHyps11M.to10M`, TOP `kernel_entryJ11M`.
- Item 4 PARTLY DONE (32b916b2, XTopJointFaultM + XTopJointKEntry12M): the cap-fault leaf at a switch mid state for a
  null handler and an endpoint handler with no waiting receiver: `Sched.sendIpcBlock_eqM`, `JAtZ.sc_frameR`
  (ScJointFrame's sc_frame with `CurInvR` after, concluding JAtZR; JAtZR has JAtZ's fields in order),
  `JAtZ.stsCurJM`/`noFaultJM` (ct Inactive, action stays switch u), `JAtZ.faultBlockJM` (faultBlockJ: CanBlock by
  canBlockCurM instead of the `actionW = 0` derivation, sendIpcBlock_eqM, JRestR), `JAtZ.faultHypJZM` outside
  `FltOpen σ := chooseNewThread ∨ ct's fault handler is an endpoint cap whose endpoint is recvEP`.
  `JRecvLeavesRN3` (flt only under FltOpen), `.toRN2` (uses ct's valid fault handler, already a JMidLeavesHyp
  premise), `JMidLeavesHyp3` [W], `jMidLeavesHyp_of3`, `KDispHyps12M.to11M`, NEW TOP `kernel_entryJ12M`.
- Premise change at the top (kernel_entryJ12M vs J10M): `JMidLeavesHyp` [W] NARROWED to `JMidLeavesHyp3` [W] :=
  JMidLeavesHyp's premises (ok outcome of the first phase, action ≠ resume, ct in no ready queue, no switch to ct,
  ct's valid fault handler, RelTopM, CurRun, ct ≠ idle, every JAtZ witness, FL4 cur_thread) concluding
  `JRecvLeavesRN3`: `receive_ipc` only under `IpcOpen`, `receive_signal` only under `SigOpen` (sch15), the cap
  fault's `handle_fault` only under `FltOpen`. Same l4v counterpart and truth argument as sch15 (each remaining
  case is a case of JMidLeavesHyp). Nothing added.
- NOT DONE (handoff), what IpcOpen/SigOpen/FltOpen still contain:
  (a) chooseNewThread mid states (item 5): every leaf (CurInv absent from JAtZ there). Route as sch15 (b).
  (b) switch, SC return (item 3): `recvSigRetJ` (SigOpen's second disjunct), `recvIpcRetJ` (RecvIpcBoundCase ∧ ¬
      NoRetM), `recvSendRetJ` (Basic ∧ ¬NoRetM), `recvSendRetPJ`/`RetPDJ`/`RetTJ`: after the block/transfer,
      `maybeReturnSc` unbinds ct's SC and ct being current, `rescheduleRequired` enqueues u, action := choose.
      Needs JAtZR copies of maybeReturnJ(Q) + a J-level rescheduleRequired-with-enqueue of u.
  (c) switch, sender-waking (item 2): `recvSendP0X` (PushCase), the T cases (`recvSendT0X`), and faultRecvJ
      (FltOpen's second disjunct; the fault send to a waiting receiver): `possibleSwitchTo w` under a switch is
      `rescheduleRequired; tcbSchedEnqueue w` (KHeap.lean:494).
  (d) linked replies (any switch case with rc = Reply q, rTcb q ≠ 0): `jRecvIpcLink_of` with MidE is cheap once
      the unlinked cases are complete (cancelOther_keep keeps action/curThread/queues, so MidE survives the
      cancel), but the residue after the cancel is evaluated at the post-cancel state; do it as a final step.
- Builds (tokyo, b.sh): sch16-b1 `XTopJointRecvIpcBlockM` OK (5568 jobs), sch16-b2 `XTopJointKEntry11M` OK (5572),
  sch16-b3 `XTopJointFaultM` OK (5574), sch16-b4 `XTopJointKEntry12M` OK (5576), all on f6b23fa2, no sorry.
  Axioms (axsch16.sh, untracked; sch16-ax1): propext, Classical.choice, Quot.sound only for kernel_entryJ12M,
  kernel_entryJ11M, KDispHyps12M.to11M, KDispHyps11M.to10M, jMidLeavesHyp_of3/of2, JRecvLeavesRN3.toRN2,
  JRecvLeavesRN2.toRN, jRecvIpcDoneM, JAtZ.recvIpcActJM/recvIpcBlockJGM/recvIpcBlockJM/recvIpcBlockNJGM,
  Sched.recvIpcBlock_eqM/sendIpcBlock_eqM, JAtZ.sc_frameR/stsCurJM/noFaultJM/faultBlockJM/faultHypJZM,
  kernel_entryJ10M. No sorry/admit/native_decide/bv_decide.

## kfix1 (branch par/kfix1 in FL4-rb, on a2a4e3a6 = int/j2 incl. irq1): the preemption point reads the IRQ first
Kernel fix for irq1's FINDING 2 (lead decision; aligns FL4 with C seL4 and the l4v spec).
- KERNEL: `sched::preemption_point` reads `a.irq_pending()` right after `update_timestamp` and before the budget and
  domain tests, then `if irq || is_cur_domain_expired(s) || !ok { Err(Preempted) }` (C c98d70ad
  src/model/preemption.c: `isIRQPending() || isCurDomainExpired() || !(sc_active && refill_sufficient)`; spec
  `preemptionPoint`, Fl4Spec/KHeap.lean ~601, always calls `getActiveIRQ`). Outcome unchanged; the line is now read on
  every expired work count, and `sufficient` reads the arch state after the IRQ read (only `min_budget`).
  Regression test `preemption_point_reads_the_irq_line_even_without_budget` (fl4-core tests/audit_core.rs).
- EXTRACTION (Aeneas 0d21a9e): only `sched.preemption_point` changes in Fl4Core/Funs.lean: `let (irq, a2) ←
  irq_pending a1` after the timestamp, `sufficient … s3 a2 …`, then `if irq … else (expired? … else if ok1 Ok else
  Err)`; EVERY preempted outcome now returns `a2` (the arch state after the IRQ read; before, the budget/domain
  outcomes returned `a1`). P0 regenerated: Consts/Auto/status unchanged, 1064/1064.
- PROOFS: the four FL4-side lemmas that unfold `preemption_point` re-done for the new order, statements unchanged:
  P1 `sched.preemption_point.pp` (QueueKeeps), P3 `pp_writes` (PPWrites), `JAtZ.ppJD` (XTopJointPP: the FL4 IRQ read
  is matched with the spec's `getActiveIRQ` sample before the SC reads; every error outcome now ends at the
  post-IRQ arch state `a2`, so `XTopAt` uses `hX2'` (`ARKeep` with `hP.irqAR`) on all error branches),
  `JAtZ.ppJH` (XTopJointPPH: every error outcome is the `JHole` at `(s3, a2)`, `σ2`). Every other user goes through
  these lemmas.
- Kernel checks (pvg-office-2, Linux x86_64, scratch/kfix1test.sh): `cargo test -p fl4-core` 3+14+3+21 passed (incl.
  the new test), `--features aarch64` 10+0+3+0 passed (audit_core is x86-only), `cargo test -p fl4-sim` 8 passed,
  `cargo xtask kernel --release` OK, `cargo build --release -p fl4-kernel-aarch64 --target
  aarch64-unknown-none-softfloat --features=release-profile` OK.
- Builds (tokyo, scratch/kfix1build.sh): kfix1-x1 re-extract + gen_p0 (P0 1064/1064, 3604 jobs); kfix1-b2 QueueKeeps,
  PPWrites, XTopJointPP, XTopJointPPH (5118 jobs) OK first time; kfix1-b3 XTopJointEntry, XTopJointKEntry8B,
  UtResetLoopJ, CnodeRevoke, QueueDecDel, QueueReset (5562 jobs) OK; kfix1-b4 root Fl4Proofs OK (5609 jobs, no sorry warning). Axioms
  (scratch/axkfix1.lean, untracked): propext, Classical.choice, Quot.sound for handle_invocation_refinesJ,
  kernel_entryJ8B, JAtZ.ppJD/ppJ/ppJH, jPreemptHyp_of, pp_writes, P1 sched.preemption_point.pp.
- NEXT: irq1's handoff (1)–(3) is now unblocked: `preemption_point ⦃ Err → ∃ v a1, now a = ok (v,a1) ∧ irq_pending a1 =
  ok (true, r.2.2) ⦄` no longer holds (the error can come from the budget or domain test), but every outcome past
  the work limit has read the line exactly once, like the spec, so MR can be threaded with one `gaiState` step.
## mr1 (branch par/mr1 in FL4-tcbj, on 4ca9647e = int/j2 incl. kfix1, sch16)
New leaves XTopJointMRPP, MachFieldKeep, XTopJointMRMcs (imported from Fl4Proofs.lean). Nothing existing edited.
Goal (irq1 NEXT (1)-(3) with kfix1's correction): move the top off `PPPlat`/`IrqPlat` onto `MachPlat`. Done: (1)
for the preemption point, the hole and the IRQ take, and the non-schedulable preemption-path branch; NOT done: the
MR-keeping of the schedulable branch (`checkBudget` → `chargeBudget _ true`), (2), (3).
- DONE (XTopJointMRPP):
  * `PPPlatA arI AR` [P] (`irqAR`, `minBudget`) / `IrqPlatA arI AR` [P] (`takeAR`, `noIpi`, `ackAR`): the arch-only
    (∀a, no spec state) parts of PPPlat / IrqPlat; `PPPlat.toA`, `IrqPlat.toA`.
  * `update_timestamp_mr : MR a ms → update_timestamp ⦃ MR r.2 (gctState ms) ⦄` (one clock read).
  * `MachPlat.irqAtE`: `irq_pending` at a related state = the spec's `getActiveIRQ true` sample, MR after, memory
    and last machine time kept.
  * `pp_err_ms` (spec): every `error` outcome σ' of `preemptionPoint` σ has `σ'.ms = gaiState (gctState σ.ms)` and
    `ValidMachineTime σ'`.
  * `JAtZ.ppJDM` / `JAtZ.ppJHM`: ppJD / ppJH with `(hM : MachPlat arI MR) (hPA : PPPlatA arI AR) (hR : MR a σ.ms)
    (hV : ValidMachineTime σ)` for `hP : PPPlat`, and `MR r.2.2 σ'.ms ∧ ValidMachineTime σ'` added to every
    outcome (below the work limit σ' = σ, a kept; past it every outcome, incl. the budget/domain error with the line
    false, is at the post-IRQ `(a2, σ2)`, one gctState + one gaiState step: kfix1's order). These are adapted
    COPIES, not spec_and combinations: the originals take the false `PPPlat`, so they cannot be instantiated; the
    copies differ only at the two read points (`hM.nowAgree hR hV`, `hM.irqAtE` at the post-timestamp MR).
  * `afterInv_of_mcsJM`: afterInv_of_mcsJ with `MR r.2 σ'.ms` in the mcs hypothesis, `MachPlat.takeAt` for
    `IrqPlat.take`, `IrqPlatA` for the rest. `JIrqHypJ` stays a hypothesis (as before).
- DONE (MachFieldKeep): `Sched.MF σ σ'` (the four fields MR reads: irqMasks, irqState, timeState,
  lastMachineTime), `MFA`, the full FK-style combinator/leaf/tactic clone of ScFieldKeep (`mf_step`, `mf_unf`,
  `mf_auto`), `mf_chargeBudgetF : MFA (chargeBudget u false)`, `MachPlat.mfKeep` (MR along an MF step).
- DONE (XTopJointMRMcs): `JHole.mcsPPJZM_ns` (mcsPPJZ for a non-schedulable ct: `charge_budget c false`, FL4 keeps
  `a` (`chargeBudgetJ`), spec `mf_chargeBudgetF`, so `MR r.2 σ'.ms` after); `JHole.afterInvJZJM_ns` (the whole
  `after_invocation (Err)` from such a covered hole under MachPlat + MR, ending in PPQJ, no IrqPlat.take);
  `JAtPreM AR MR s a σ` (= JAtPre with `MR a0 σ0.ms ∧ ValidMachineTime σ0` at the pp's pre-state), `JAtPreM.toPre`,
  `jAtPreM_hole` (JHole ∧ MR a σ.ms ∧ VMT σ, by ppJHM).
- No new premise anywhere: MachPlat [P] and ValidMachineTime [J] are irq1's; PPPlatA/IrqPlatA are field subsets of
  the existing [P] PPPlat/IrqPlat (arch-only ∀a facts, satisfiable: no spec state in them).
- NEXT (handoff):
  (a) schedulable branch of the preemption path: `mf_chargeBudget u true` (reaches `handleTimeout` → the fault IPC;
      the clone needs an `mf_doMachineOp` leaf for loadWord/storeWord (memory-only machine ops) plus the fault-path
      unfolds) and copies of mcsPPJZ's checkBudgetF/checkBudgetT branches exposing `a' = a` (both lemmas prove it
      but hide it) or, FL4-side, an `MRKeep` [P] for `fpu_flush`/`fpu_release`/`remote_stall` (the only state-
      returning arch ops reachable from `mcs_preemption_point`, scripted call-graph check) with an ARKeep-style walk.
      Then `JHole.afterInvJZJM` (all covered cases) and the PPCovI / RestE / PreemptK,Q,L,O branches (each uses
      `hP.now a0 σ0` / `hP.irq` only to name the spec outcome: replace by `pp_err_ms`).
  (b) `jIrqHypJ_of`, `JAtZ.handleIrqJJ`, `JHole.handleIrqJ`, `jIrqHypZ_of` take `IrqPlat` but use only `ackAR`:
      generalise them to `IrqPlatA` (edit in place, callers pass `hIP.toA`; cone = IrqZR and below) or copy.
  (c) (2) the invocations: `JPreemptHyp` (∀ WJR states, from `jPreemptHyp_of hP`) must become MR-relative: WJR (or a
      bundle carried beside it, never in JAtZ) needs `MR a σ.ms ∧ VMT σ`, `jPreemptHyp_ofM` from ppJDM, and every
      invocation's post must produce `JAtPreM` (not JAtPre) at its preempting outcome, plus MR at its non-preempted
      outcome: ~25 use sites (inv1 G0: `grep -n 'hP.now\|hPP.now\|\.irq a\|hIP.take\|hIP.base.take'`, and every
      `JEntryGlob.pp` consumer: UtResetLoopJ/UtResetTopJ/UtRetResetJ, XTopJointTcb/TcbInsL, WJLPP/WJLDel/WJLRestart).
      Spec side: `mf_*` for each invocation's spec (memory-only machine ops; getActiveIRQ/getCurrentTime only inside
      preemptionPoint, maskInterrupt in IRQ control: there MR moves by `MachPlat.mask`).
  (d) (3) kernel_entryJ13P: needs (a)–(c) through kernel_entryJ9M's body (`dispatch_all9M`, `dispatch_invokeJAll`,
      `mid_invRecvJ`/`hPre_ofZQI`): at the entry `MR a σ.ms ∧ VMT σ` [J]; budget_ok by `MachPlat.nowAt` (KBudget.now
      is per-state already); a J13P that still takes PPPlat anywhere would be vacuous, so it was not stated.
  `JEntryGlob.portIn` (PortInVal, ∀σ) is untouched: it is the remaining ∀σ platform premise (MR has no device part
      yet; `modelArch.port_in` returns 0, so a per-state PortInVal needs a device field in MR).
- Builds (tokyo, scratch/mr1build.sh, mirror seeded from FL4-rb's .lake): mr1-b1 (warm, MachRel/PPH/IrqZR/KEntry12M
  OK), mr1-b2/b3 (name errors, then pp_err_ms rewrite), mr1-b4 XTopJointMRPP OK (5530 jobs; MachFieldKeep one name
  error), mr1-b5 XTopJointMRPP + MachFieldKeep OK, mr1-b6 XTopJointMRMcs OK (5534), mr1-b7 (term-mode `let` pattern with `-`), mr1-b8 MRMcs + JAtPreM OK
  (5534 jobs; root Fl4Proofs.lean not rebuilt: only three leaf imports added). Axioms
  (scratch/axmr1.lean, untracked): propext, Classical.choice, Quot.sound only for ppJDM, ppJHM, afterInv_of_mcsJM,
  update_timestamp_mr, MachPlat.irqAtE, pp_err_ms, PPPlat.toA, IrqPlat.toA, Sched.mf_chargeBudgetF,
  MachPlat.mfKeep, JHole.mcsPPJZM_ns, JHole.afterInvJZJM_ns, jAtPreM_hole, and the newest top kernel_entryJ12M
  (unchanged). No sorry/admit/native_decide/bv_decide.
## sch17 (branch par/sched17 in FL4-sc, on 4b069906 = int/j2 incl. sch16)
New leaves XTopJointRecvSendPM, XTopJointKEntry13M, XTopJointRecvRetM, XTopJointKEntry14M, XTopJointKEntry15M (imported
from Fl4Proofs.lean). Nothing existing edited; JAtZ, ScPPR/SpecPPR*/CnDel/WJL*/Tcb*/UtReset*/PP*/Preempt*/ScCharge*/
ScTmoCt*/Entry/Irq*/XTopJointRecv* untouched.
- Item 2, reply-pushing senders, DONE (f832d92a, XTopJointRecvSendPM + KEntry13M). Finding: the push cases do NOT go
  through `possibleSwitchTo` (the sender blocks on the reply); only `hAct` excluded a switch. Copies
  `JAtZ.recvSendFPJGM` / `recvSendPJGM` / `recvSendFPTJM` with `hAct : ∃ u, action = switchThread u ∧ u ≠ ct`:
  CurInv by `J.curInv` (no donation, receiver not released), P1's "action word names neither thread" from u ≠ ct and
  u ≠ sender (`hswT`: the switch target is schedulable, the sender blocked on send), `ActIdle` after by `RSFr.sched`
  + `ps_schedM` (u is neither the sender nor the reply), CurRunM first disjunct; post `JAtZ`. Wrappers
  `recvSendP0XM` (PushOK), `recvSendT0XM` (TmoOK; no push: `recvSendFTJ` reads no action). `IpcDoneM2` / `IpcOpen2`,
  `JRecvLeavesRN4.toRN3`, `JMidLeavesHyp4` [W], `KDispHyps13M.to12M` (needs hmax/htu, threaded from the top),
  `kernel_entryJ13M`.
- Item 3, SC return before an endpoint receive, DONE (26b72856, XTopJointRecvRetM + KEntry14M). Finding:
  `maybeReturnJQ` already handles a pending switch (spec `maybeReturn_shape`/`whenResched_fields` and FL4's
  `maybe_return_refines` are generic in the action; it asks only switch target ≠ t), and after it the action is
  `chooseNewThread`, which the resumed tails already cover. Copies `recvIpcRetJM`, `recvSendRetJM`, `recvSendRetPJM`,
  `recvSendRetPDJM`, `recvSendRetTJM` with `hni : MidE` (CurInv `J.curInv hni.ncn`, `hni.run`, `canBlockCurM`,
  `MidE.swNe`). `LendM`, `IpcRetM`, `IpcDoneM3`/`IpcOpen3`, `JRecvLeavesRN5.toRN4`, `JMidLeavesHyp5` [W],
  `KDispHyps14M.to13M`, `kernel_entryJ14M`.
- Linked replies + exhaustiveness DONE (a1c16c18, KEntry15M): `ipcDoneM3_of` (every blocking receive with a null or
  free reply is in IpcDoneM3: jRecvIpcU_of's case split), `jRecvIpcUM`, `jRecvIpcLinkM` (jRecvIpcLink_of at MidE:
  cancelOther_keep keeps action/ct/queues/other TCBs, so MidE and CurRun hold after the cancel). `JRecvLeavesRN6`
  asks `receive_ipc` ONLY under `chooseNewThread`; `.toRN5`, `JMidLeavesHyp6` [W], `KDispHyps15M.to14M`, NEW TOP
  `kernel_entryJ15M`.
- Premise change at the top (kernel_entryJ15M vs J12M): `JMidLeavesHyp3` [W] NARROWED to `JMidLeavesHyp6` [W] :=
  JMidLeavesHyp3's premises (ok outcome of the first phase, action ≠ resume, ct in no ready queue, no switch to ct,
  ct's valid fault handler, RelTopM, CurRun, ct ≠ idle, every JAtZ witness, FL4 cur_thread) concluding
  `JRecvLeavesRN6`: `receive_ipc` only under `chooseNewThread`, `receive_signal` only under `SigOpen` (choose, or the
  sig SC return), the cap fault's `handle_fault` only under `FltOpen` (choose, or an endpoint handler with a waiting
  receiver). l4v as sch15/16 (receive_ipc_corres / receive_signal_corres / handle_fault_corres inside
  handle_recv_corres under scheduler_act_sane); each case is a case of sch15's JMidLeavesHyp, true in reachable
  states. Nothing added. kernel_entryJ15M has the same other premises as J12M.
- NOT DONE (handoff), what JMidLeavesHyp6 still contains:
  (a) switch, sig SC return (`recvSigRetJ`, SigOpen's second disjunct): the block comes first, so after
      `recvSigBlockPreJ` ct is blocked with `switchThread u` pending: CurInv fails, `JAtZ` does not hold (`JAtZS`
      with `SwBlk`, or `JAtZR`, does). Needs a JAtZR (or JAtZS) copy of `recvSigBlockPreJ` (as recvSigBlockJM did
      for recvSigBlockJ) and of `maybeReturnJQ`'s closure (sc_frame, sc_buf, sc_apart, sc_jpl, sc_kern, sc_utc,
      deadP_sc_step, words_of_spec; JAtZR.sc_jcov/idleW_keep/kw_dbg/tcbs_eq exist): sch9gen/gen.py with root
      JAtZ.maybeReturnJQ. maybeReturn_mid's `hcur` is unused when t = ct (result chooseNewThread), so after the
      return the post is JAtZ again (Or.inl).
  (b) switch, fault send to a waiting receiver (`faultRecvJ`, FltOpen's second disjunct): sendFaultPJ/PDJ/IJ take
      `hres : action = resume`; there `possibleSwitchTo w` = `setSchedulerAction (switchThread w)`, under a switch
      it is `rescheduleRequired; tcbSchedEnqueue w` (KHeap.lean:494): a new J step (FL4's possible_switch_to with
      a non-resume action: enqueue u then w, action := choose). This is the only remaining sender-waking case.
  (c) chooseNewThread mid states (item 5): every leaf. Route unchanged (sch15 (b)): a first-phase post fact
      "chooseNewThread → CurInv ∨ ct SC-less"; with it the resumed leaves' `hsa` second disjunct (choose ∧ sc none)
      or the CurInv copies (as here) apply.
- Builds (tokyo, b.sh): sch17-b1 `XTopJointRecvSendPM` OK (5422 jobs), sch17-b2 `+ XTopJointKEntry13M` OK (5580),
  sch17-b3 `XTopJointRecvRetM` OK (5568), sch17-b4 `+ XTopJointKEntry14M` OK (5584), sch17-b5/b6 KEntry15M (an
  eq_of_bv direction, a `cases` eliminating a name), sch17-b7 `XTopJointKEntry15M` OK (5586), all on 4b069906.
  Axioms (axsch17.sh, untracked; sch17-ax1): propext, Classical.choice, Quot.sound only for kernel_entryJ15M/14M/13M,
  KDispHyps15M.to14M/14M.to13M/13M.to12M, jMidLeavesHyp_of6/5/4, JRecvLeavesRN6.toRN5/RN5.toRN4/RN4.toRN3,
  ipcDoneM3_of, jRecvIpcUM, jRecvIpcLinkM, jRecvIpcDoneM3/M2, JAtZ.recvSendFPJGM/PJGM/FPTJM/P0XM/T0XM, ps_schedM,
  JAtZ.recvIpcRetJM/recvSendRetJM/RetPJM/RetPDJM/RetTJM, LendM.at (propext); MidE.swNe none. No sorry/admit/
  native_decide/bv_decide.
## mr2 (branch par/mr2 in FL4-tcbj, on 368f39df = int/j2 incl. mr1)
New leaves MachKeep, XTopJointMRPath, MachFieldFam, XTopJointMRPath2/3/4 (imported from Fl4Proofs.lean). Nothing
existing edited. Goal: mr1 NEXT (a)/(b): every MCS branch of the preemption path and the IRQ take/handler under
`MachPlat` with no `PPPlat`/`IrqPlat`/`IrqPlatI`. DONE for the MCS part, the take and the handler; NOT done: the
hole facts (`jAtPre_holeQ` chain) under MachPlat, hence no `hPre_ofZQIM` yet; (2), (3).
- DONE (MachKeep): `MRKeep arI AR` [P] = ArchKeep's `ARKeep` WITHOUT `now` (set_deadline, send_reschedule,
  remote_stall, fpu_flush/release/sanitise/reload, vcpu_barrier keep `AR` at every 2nd argument; used at `AR :=
  MR`, i.e. those arch ops change no IRQ mask/pending line/clock; arch-only ∀a; l4v: `machine_op_lift`s outside
  irq_masks/irq_state/time_state/last_machine_time). `mk_call`/`mk_walk` (ak_call clone) and `MK.*` = every `AK.*`
  walk + `MK.sched_end_timeslice`, `MK.sched_charge_budget`, `MK.sched_check_budget`,
  `MK.syscall_mcs_preemption_point` (`MR a ms → mcs_preemption_point ⦃ MR r.2 ms ⦄`: the walk type-checks, so no
  `now` is reachable). Must not import P1-level step lemmas (XTopJointMachRel's import made `step` pick LawfulStore
  specs): MachKeep imports ArchKeep only.
- DONE (XTopJointMRPath): `modelArch_mrKeep` (non-vacuity); `ValidIrqMasks σ` [J] := `∀ i, interruptStates i =
  irqInactive → ms.irqMasks i = true` (l4v `valid_irq_masks`); `gai_active` (the spec line at a VIM state is not
  inactive); `JAtZ.handleIrqJIA`/`JAtZ.handleIrqJJA`/`jIrqHypJ_ofA` (scripted copies with `IrqPlatA`, only `ackAR`
  used: mr1 NEXT (b)); `afterInv_of_mcsIM` (afterInv_of_mcsI: hmcs post + `MR r.2 σ'.ms ∧ ValidIrqMasks σ'`,
  `MachPlat.takeAt`, `IrqPlatA`; the inactive-line case closed by `gai_active` instead of sch12's `IrqPlatI.act`,
  which is derivable only from the degenerate `IrqPlat.take`).
- DONE (MachFieldFam, generated by scratch/mr2/mfgen.py + head/tail.lean + skip.txt, `sh scratch/mr2/mk.sh`):
  `msF σ` = (irqMasks, irqState, timeState, lastMachineTime, interruptStates), `MFK m := FK msF m`; machine leaves
  `MKF` for loadWord/storeWord/machineOpLift (`mfk_doMachineOp`); 202 `mfk_*`/`mfke_*` lemmas = the DK family
  (VsDomOps/DomRecDel/TcbDom/AllDom up to dke_fl4Perform) renamed, minus 60 dropped: skip.txt (portIn, setIrqState,
  preemptionPoint, VSpace TLB flushes unmapPage/flushTable/flushAll/invalidatePageStructureCacheAsid/
  hwAsidInvalidate, FPU save/load/switchLocalFpuOwner, invokeSchedContext) and, by the spec call graph, every
  function reaching getActiveIRQ/getCurrentTime/maskInterrupt/ackInterrupt/portOut/setDeadline/ackDeadlineIRQ/
  clearMemory/freeMemory (dropped.txt). The TLB/FPU ones only lack an `MKF` leaf for their machine op (likely
  machine_op_lift-like; add leaves to widen). Plus `mfk_chargeBudget u b`, `mfk_checkBudget` (incl. the timeout
  fault IPC: handleTimeout → sendFaultIpc → sendIpc → doIpcTransfer).
- DONE (XTopJointMRPath2): `msF_mr`/`msF_vim`; `JHole.mcsPPJZMF` (mcsPPJZ + `msF σ' = msF σ`, both branches incl.
  the schedulable one: mr1 NEXT (a)); `JHole.mcsPPJZM` (+ `MR r.2 σ'.ms ∧ ValidIrqMasks σ'` from `MRKeep` +
  `MK.syscall_mcs_preemption_point` by WP.spec_and); `JHole.afterInvJZIM` (covered holes → PPQJI under MachPlat +
  MRKeep + IrqPlatA, MR and VIM at the hole). XTopJointMRPath3: `mcsPPJSM`, `mcsPPJCM`, `mcsPPJUM`; XTopJointMRPath4:
  `mcsPPJIM` (extra hAT), `mcsPPJAM`, `mcsPPJRM` (scratch/mr2/mcscopy.py: original proof as `have key` with the
  msF conjunct at its endpoint, then spec_and with the MK walk). So every `mcs*` branch hPre_ofZQI uses now has an
  MR+VIM version.
- New premises: `MRKeep` [P] (arch-only, satisfied by modelArch), `ValidIrqMasks` [J] (per state, at the hole).
  Neither is used by a top yet. Nothing removed (no top changed; kernel_entryJ12M unchanged).
- NEXT (handoff):
  (a) `hPre_ofZQIM`: hPre_ofZQI with `JAtPreM` (extend JAtPreM, or a JAtPreMV, by `ValidIrqMasks σ0`: the
      preemption point keeps irqMasks and interruptStates, `pp_err_ms` + a preemptionPoint interruptStates frame) for
      `JAtPre`, MachPlat+MRKeep+PPPlatA+IrqPlatA for PPPlat/IrqPlat. Needs a MachPlat copy of `jAtPre_holeQ` (its
      chain jAtPre_holeT/TN/K/L/O uses `hP.now a0 σ0` / `hP.irq` only to name the spec pp outcome: replace by
      `pp_err_ms`/`MachPlat.irqAtE` as mr1's ppJHM did) and `jPreemptRestHypEQ_ofI`'s two cases with
      mcsPPJAM/mcsPPJRM; then every branch: afterInvJZIM / afterInv_of_mcsIM ∘ mcsPPJ{I,S,C,U,A,R}M.
  (b) = mr1 NEXT (c) unchanged: JPreemptHyp MR-relative (WJR + MR + VMT + VIM beside it), invocation posts keep MR:
      spec side now mostly available (MachFieldFam covers every non-time/IRQ spec function of the DK list; the
      preempting loops move MR by pp_err_ms at each preemption point; IRQ handler deletion's maskInterrupt moves it
      by `MachPlat.mask`), FL4 side = MK walks (extend MachKeep's list per invocation; `mask_irq` needs an
      MR-moving field, not MRKeep).
  (c) = mr1 NEXT (d): kernel_entryJ13P after (a)–(b). `JEntryGlob.portIn` (PortInVal ∀σ) stays the remaining ∀σ
      platform premise (MR has no device part; modelArch.port_in returns 0).
- Builds (tokyo, scratch/mr2build.sh, warm mirror): mr2-b1 warm (MRMcs, KEntry12M OK), mr2-b2 (MachKeep: P1 step
  lemmas via the MachRel import), mr2-b3 MachKeep OK (3610 jobs), mr2-b4 XTopJointMRPath OK (5558), mr2-b5
  (MachFieldFam: TLB/FPU/SchedContext leaves, missing imports), mr2-b6 MachFieldFam (4592) + XTopJointMRPath2 (5562)
  OK, mr2-b7 XTopJointMRPath3 OK (5564), mr2-b8 (mcsPPJI has no hAT), mr2-b9 XTopJointMRPath4 OK (5566). Root
  Fl4Proofs.lean not rebuilt (six leaf imports added). Axioms (scratch/axmr2.lean, untracked; mr2-b9): propext,
  Classical.choice, Quot.sound only for MK.syscall_mcs_preemption_point, MK.sched_check_budget,
  MachF.mfk_checkBudget/mfk_chargeBudget, modelArch_mrKeep, gai_active, JAtZ.handleIrqJIA/JJA, jIrqHypJ_ofA,
  afterInv_of_mcsIM, JHole.mcsPPJZM/afterInvJZIM/mcsPPJSM/CM/UM/IM/AM/RM, and the newest top kernel_entryJ12M
  (unchanged). No sorry/admit/native_decide/bv_decide.
## mr3 (branch par/mr3 in FL4-tcbj, on fbf9f232 = int/j2 incl. mr2, sch17)
New leaves XTopJointMRHole, XTopJointMRHole2 (imported from Fl4Proofs.lean). Nothing existing edited. Goal: mr2 NEXT
(a) `hPre_ofZQIM`, then (b) MR through the invocations, (c) kernel_entryJ13P. DONE: (a) fully, plus the loop-side
interface of (b) (`ppJDMV`). NOT done: (b) per invocation family, (c).
- DONE (XTopJointMRHole, 14c9b429):
  * `JAtPreMV AR MR s a σ` = mr1's `JAtPreM` + `ValidIrqMasks σ0` [J] (l4v `valid_irq_masks`) at the preempting
    preemption point's pre-state; `.toM`, `.toPre`.
  * `jAtPreMV_holeQ`: the whole jAtPre_holeT/TN/O/K/L/Q chain under `MachPlat` + `PPPlatA` (no PPPlat): hole by
    `ppJHM`; the spec pp outcome named by `getCurrentTime_eq`/`getActiveIRQ_eq`/`pp_err_eq` (deterministic, no
    platform needed); TShift's `σ0.curTime ≤ σ.curTime` from `vmt_le_gct` (VMT at the base); `ValidIrqMasks` at the
    hole by defeq (gctState/gaiState touch only oracle positions/last time). Output adds `MR a σ.ms ∧ VMT σ ∧ VIM σ`.
  * `jPreemptRestHypEQ_ofIM` (mcsPPJAM/RM + afterInv_of_mcsIM), `hPre_ofZQIM`: every hole of a related `JAtPreMV`
    state → `r.1 = false ∧ PPQJI` under `MachPlat` [P], `MRKeep` [P], `PPPlatA` [P], `IrqPlatA` [P] (+ the existing
    hmrt/hmax/htu [P] and hNS [S]). No PPPlat/IrqPlat/IrqPlatI anywhere in its cone.
- DONE (XTopJointMRHole2, 64b64812):
  * `irqVF` (masks, interrupt table), `ivk_preemptionPoint : FKE irqVF preemptionPoint` (VsDom's generic FK +
    dk_step0, leaves ivk_doMachineOp/ivk_gct/ivk_gai/ivk_doExtendedOp), `vim_pp` (every pp outcome keeps VIM).
  * `JAtZ.ppJDMV`: the preemption point at `JAtZ` + `MR a σ.ms ∧ VMT σ ∧ VIM σ ∧ NoSwitch σ ∧ PPR0 σ`: `∃ r, pp =
    ok r ∧ ∃ σ', (Ok ∧ spec ok ∧ JAtZ' ∧ PPR0 σ' ∧ NoSwitch σ' ∨ Preempted ∧ spec error ∧ JAtPreMV r σ') ∧ XTopAt ∧
    MR r.2.2 σ'.ms ∧ VMT σ' ∧ VIM σ'`. This is the drop-in for `J.ppJD arI hAK hA hnd hP hp0` (PPPlat) in the loops:
    a loop whose invariant carries `MR a σ.ms ∧ VMT σ ∧ VIM σ` beside JAtZ ends in `JAtPreMV` (what hPre_ofZQIM eats).
- No new premise. JAtPreMV's VIM is a carried per-state fact (not a hypothesis of a top yet).
- NEXT (handoff):
  (b) the invocation families still produce `JAtPre` via `ppJD`/`jPreemptHyp_of`/`jPreemptHypL` with `hG.pp`
      (PPPlat): CnodeRevoke, DelRound, UntypedResetRefine, XTopJointDelR, XTopJointEntry, XTopJointWJLPP/WJLDel/
      WJLRestart (grep `hG\.pp\|\.ppJD arI\|jPreemptHyp_of\|jPreemptHypL`), and UtResetLoopJ/UtRetResetJ/XTopJointTcb*
      through them. Per family: extend the loop invariant (e.g. UtResetLoopJ's `loop.spec_decr_nat` inv, WJL's
      `WJL`/`WJP`) by `MR a σk.ms ∧ VMT σk ∧ VIM σk`; replace the pp step by `ppJDMV`; the non-pp steps keep it:
      FL4 side store-only steps keep `a` (MR untouched), arch calls by `MK.*` walks (MachKeep, `MRKeep`), `mask_irq`
      (IRQ handler deletion) by `MachPlat.mask` (and VIM needs the spec's `setIrqState irqInactive` paired with the
      mask: l4v deleting_irq_handler_valid_irq_masks); spec side `MachF.mfk_*` (MFK keeps msF ⊇ MR fields and
      interruptStates). Missing spec leaves: clearMemory (UtReset's chunk clear; memory-only, add an `MKF` leaf),
      maskInterrupt/setIrqState (move msF; need a dedicated pair lemma). Smallest family to start: UtResetLoopJ
      (clear + pp per chunk). Then a `dispatch_invokeJAllM` needs `invoke_afterJ` with `JAtPreMV` for `JAtPre`
      (its hPre is applied only at the Preempted outcome's `hX : JAtPre`, so the copy needs TopPostDMXP at XP :=
      JAtPreMV from `handle_invocation_entryJ` → every decode/perform lemma's XP: that is the bulk).
  (c) kernel_entryJ13P after (b): MR+VMT+VIM at the entry [J] (l4v shared machine_state, valid_machine_time,
      valid_irq_masks); budget_ok via `MachPlat.nowAt` (KBudget.now is already per-state); dispatch_all9M's
      `dispatch_invokeJAll`/`dispatch_midJ` with hPre_ofZQIM; JEntryGlob.pp must be dropped (it is a PPPlat, so any
      top keeping JEntryGlob stays vacuous). JEntryGlob.portIn (PortInVal ∀σ) stays the remaining ∀σ platform premise
      (MR has no device part). Non-vacuity of the platform premises: modelArch_machPlat, modelArch_mrKeep,
      modelArch_take_some (MachRel/MRPath); PPPlatA/IrqPlatA are arch-only.
- Builds (tokyo, scratch/mr3build.sh, warm mirror): mr3-b1 XTopJointMRHole OK first time (5568 jobs); mr3-b2
  MRHole2 one error (ivk_doMachineOp: un-beta-reduced `have e`), mr3-b3 XTopJointMRHole2 OK (5570) + XTopJointKEntry15M
  OK (5586). Root Fl4Proofs.lean not rebuilt (two leaf imports). Axioms (scratch/axmr3.lean, untracked; mr3-b3):
  propext, Classical.choice, Quot.sound only for jAtPreMV_holeQ, jPreemptRestHypEQ_ofIM, hPre_ofZQIM, JAtPreMV.toPre,
  ivk_preemptionPoint, vim_pp, JAtZ.ppJDMV, and the newest top kernel_entryJ15M (unchanged). No sorry/admit/
  native_decide/bv_decide.

## sch18 (branch par/sched18 in FL4-sc, on a589b93d = int/j2 incl. sch17, mr1, kfix1)
New leaves XTopJointJAtZRM, XTopJointRecvSigRetM, XTopJointFaultRecvM, XTopJointKEntry16M (imported from
Fl4Proofs.lean). Nothing existing edited; JAtZ, ScPPR/SpecPPR*/CnDel/WJL*/Tcb*/UtReset*/PP*/Preempt*/ScCharge*/
ScTmoCt*/Entry/Irq*/MR*/XTopJointRecv* untouched.
- (a) sig SC return at a switch DONE (XTopJointJAtZRM + XTopJointRecvSigRetM): `Sched.maybeReturn_midR`
  (maybeReturn_mid with CurInvR in/out); scripted JAtZR copies (sch9gen/gen.py root `JAtZ.maybeReturnJQ`,
  sch18gen/mk.py drops the four already in JAtZRA and patches `JAtZR.sc_frame`'s hcur to CurInvR):
  sc_frame/sc_buf/sc_apart/sc_jpl/sc_kern/sc_utc/deadY_tcb/ymd/sc_out_keep/deadP_sc_stepQm/Q/G/step/
  spec_of_words/words_of_spec/maybeReturnJQ. `Sched.recvSigBlockPre_act`, `JAtZ.recvSigBlockPreJM` (post JAtZR,
  switch kept; recvSigBlockJM's changes), `JAtZ.recvSigRetJM`, `jRecvSigHypM2_of` (every notification receive at a
  switch mid state).
- (b) fault send to a waiting receiver at a switch DONE except the donating case (XTopJointFaultRecvM). FINDING:
  sendTailJ is generic in the action (possible_switch_to under a switch = reschedule_required + enqueue on both
  sides), and before the tail the faulting ct is Inactive / BlockedOnReply with its SC, so CurInv holds there
  (NotIpcBlk admits both): `JAtZ` with `Or.inr CurInv` instead of choose. `ciSt_actN/curInv/sched`,
  `ps_actN/curInv/sched`; `JAtZ.sendFaultIJM`, `JAtZ.sendFaultPJM` (sch18gen/mkf.py patches of sendFaultIJ/PJ:
  action word = u ≠ ct, receiver (blocked, u schedulable); ct's SC word ∈ Ac from `curScAc` (ct is not `Sch` under a
  switch); ActIdle by CFr.sched + ciSt/ps_sched), `JAtZ.faultRecvJM` (canBlockCurM; PDJ branch excluded by
  `FltDon`), `JAtZ.faultHypJZM2`. NOT DONE: `FltDon σ` (grant/grant-reply handler, head receiver with a reply
  object and no SC: ct donates its SC; `pd_eq` takes "no switch" and after the donation neither CurInv nor choose
  holds, so needs a JAtZR route through pushDonJ + sendTailJ (gen.py root JAtZ.sendTailJ: 5 new copies
  switchJ/unblockRJ/sendUnblockJ/sendSwitchJ/sendTailJ beyond JAtZRM's set) and a switch version of pd_eq).
- XTopJointKEntry16M: `JRecvLeavesRN7` (ipc and sig only under chooseNewThread, flt only under choose ∨ FltDon),
  `.toRN6`, `JMidLeavesHyp7` [W], `jMidLeavesHyp_of7`, `KDispHyps16M.to15M`, NEW TOP `kernel_entryJ16M`.
- Premise change at the top (kernel_entryJ16M vs J15M): `JMidLeavesHyp6` [W] NARROWED to `JMidLeavesHyp7` [W] :=
  JMidLeavesHyp6's premises concluding `JRecvLeavesRN7`: `receive_ipc` and `receive_signal` only under
  `chooseNewThread`, the cap fault's `handle_fault` only under `chooseNewThread ∨ FltDon`. Same l4v counterpart and
  truth argument (receive_ipc_corres / receive_signal_corres / handle_fault_corres under scheduler_act_sane); each
  case is a case of JMidLeavesHyp6. Nothing added. Other premises as J15M.
- NOT DONE (handoff): (1) FltDon at a switch (above). (2) item 5, chooseNewThread mid states, every leaf: route
  unchanged (a first-phase post fact "chooseNewThread → CurInv ∨ ct SC-less", then the resumed leaves' `hsa`
  second disjunct / CurInv copies).
- Builds (tokyo, b.sh): sch18-b1 `XTopJointJAtZRM` (4 decls already in JAtZRA: dropped 3 more), sch18-b2
  `JAtZRM` + `RecvSigRetM` OK, `FaultRecvM` (Ipc.SKeep vs P3.SKeep once FaultM is imported; `by cases h,` parsing),
  sch18-b3 `XTopJointFaultRecvM` + `XTopJointKEntry16M` OK (5594 jobs), all on a589b93d, no sorry. Axioms
  (axsch18.sh, untracked; sch18-ax1): propext, Classical.choice, Quot.sound only for kernel_entryJ16M,
  KDispHyps16M.to15M, jMidLeavesHyp_of7, JRecvLeavesRN7.toRN6, jRecvSigHypM2_of, JAtZ.recvSigRetJM/recvSigBlockPreJM,
  Sched.recvSigBlockPre_act/maybeReturn_midR, JAtZR.maybeReturnJQ/sc_frame, JAtZ.faultHypJZM2/faultRecvJM/
  sendFaultIJM/sendFaultPJM, ciSt_actN/curInv/sched, ps_actN/curInv/sched, kernel_entryJ15M. No sorry/admit/
  native_decide/bv_decide. Generators sch18gen/{mk.py,mkf.py,hdrf.lean} in the worktree root, untracked.
## mr4 (branch par/mr4 in FL4-tcbj, on fbd8d1f4 = int/j2 incl. mr3)
New leaves UtResetLoopJM, XTopJointKEntry13P (imported from Fl4Proofs.lean; KEntry13P generated by
scratch/mr4/gen.py from the originals + head/mid/tail.lean). Nothing existing edited; sch18's modules untouched.
Goal: mr3 NEXT (b) family by family, then (c) kernel_entryJ13P. DONE: (b) for the untyped reset loop only, (c) with
the rest of (b) as ONE path-restricted premise.
- DONE (UtResetLoopJM, ab54c2a4): `JAtZ.ppJSM` (ppJS from mr3's ppJDMV: MachPlat + PPPlatA, MR/VMT/VIM at the
  pre-state, NoSwitch from PPR0; continuing JAtZ+PPR0 or preempted JAtPreMV, MR/VMT/VIM after, FL4's frame);
  `ResetJPostM` (JAtPreMV at a preempted reset); `JAtZ.reset_loopJM` (the chunk loop with MR ∧ VMT ∧ VIM in the
  invariant: clear and free-index write are store-only, the spec slot write `setCnodeSlot` touches only kheap, so
  the invariant reaches the pp by defeq). Not yet lifted to UtResetTopJ/UtRetResetJ (copies of reset_untypedJ,
  utResetJ, jUtRetHypR_of with the M lemma: next step to shrink the premise below).
- DONE (XTopJointKEntry13P, 98e242bb): NEW TOP `kernel_entryJ13P` = kernel_entryJ15M's premises with
  * `PPPlat`, `IrqPlat` gone: `MachPlat arI MR` [P], `MRKeep arI MR` [P], `PPPlatA` [P], `IrqPlatA` [P] (arch-only);
  * at the entry `MR a σ.machineState` and `ValidIrqMasks σ` [J] (l4v shared machine_state, valid_irq_masks);
  * hK : … → `KDispHyps13P` = KDispHyps15M with `JEntryGlobM` (JEntryGlob with `pp : PPPlat` replaced by
    `ppA : PPPlatA`), `JPreDecHyp` beside each invocation path (inv and mid), and `vmt : ValidMachineTime σb` [J] at
    the dispatch state (l4v valid_machine_time kept by check_budget_restart; not transported: needs a curTime FK
    family through checkBudget's timeout fault path).
  Pieces: `MachF.mfk_checkBudgetRestart`, `budget_ok_mr` (FL4 budget_ok = one clock read: update_timestamp_mr +
  MK.sched_check_budget walk), `budget_mr_at` (MR a1 σb.ms ∧ VIM σb at the spec budget outcome), `XCapP.reXP`,
  `HIPostMXP.toPreMV`, `decOK_JM` (decOK_J with JEntryGlobM/JAtPreMV, CNode/Thread/Untyped by JPreDecHyp, every
  other kind by its J lemma + reXP), `handle_invocation_entryJM`, `invoke_afterJM`, `dispatch_invokeJM`,
  `dispatch_invokeJAllM` (hPre_ofZQIM), `mid_invRecvJM` (preempted branch on the JAtPreMV outcome), `dispatch_midJM`,
  `dispatch_all13P` (mid leaves narrowed jMidLeavesHyp_of6…of2, jMidRecvHypS_of, jMidRecvHyp_of), `kernel_entryJ13P`.
- NEW PREMISE `JPreDecHyp AR MR Z H Cs D s ar σ ct` [W] (exact statement in XTopJointKEntry13P): `MR ar σ.ms →
  ValidMachineTime σ → ValidIrqMasks σ → ∀ lbl length blk call don fp buf extra slbl argsU, decOK_J's front-end
  hypotheses (hlen, hargs, hbuf, ≤120 args, CNode slot sl, capAt … = ok c) → (NoPreKind c → False) → ExtraOK →
  ExtraNamed → lbl.bv = slbl → ArgRel … 5 → JPath … c → XCapP (JAt) (JAtPreMV MR) s ar σ …`. Path-restricted: asked
  at the dispatch state (with MR there, which the top transports through budget_ok), at the decode's own values,
  only for the cap kinds whose spec decode can yield a preemptible invocation (CNode revoke/delete, Thread caps/
  sched install, Untyped retype/reset). True in reachable states: those families are proved at J from PPPlat only
  at their preemption points (ppJD); l4v invoke_cnode_corres / invoke_tcb_corres / invoke_untyped_corres with
  preemption_point_corres under the shared machine state. It replaces (b); each family moved to MachPlat removes a
  kind from it.
- Non-vacuity: `j13P_platform : MachPlat modelArch modelMR ∧ MRKeep modelArch modelMR ∧ (∀ ms i, gaiLine true ms =
  some i → modelArch.take_pending_irq ms ⦃ r.1 ≠ NO_IRQ ∧ r.1.val = i.toNat ⦄)` (modelArch raises interrupts; no
  PPPlat/IrqPlat/JEntryGlob in J13P's premises, checked through JDelParts/JEntryAt/JPath/KFinAtR/KBudget/KDispHyps).
  Remaining ∀σ platform premise: `JEntryGlobM.portIn` (PortInVal; MR has no device part, as before).
- NEXT (handoff): (1) lift reset_loopJM: copies of UtResetTopJ.reset_untypedJ, UtRetResetJ.utResetJ/jUtRetHypR_of
  with MachPlat (their only PPPlat use is reset_loopJ), and of JAtZ.jUtRetHyp/UtRetPostJ at JAtPreMV (the no-reset
  retypes never preempt: SpecNoPre perform_noErr for reset = false, or reXP-style); then decOK_JM's Untyped RAM
  branch from them, device branch by jUtRetHypDev + not-preempted; JPreDecHyp loses Untyped. (2) CNode revoke/delete
  (CnodeRevoke/DelRound/XTopJointDelR WJL loops: WJL/WJP invariant + MR/VMT/VIM, ppJDMV, MK walks, mfk_* spec;
  IRQ handler deletion's mask_irq by MachPlat.mask + setIrqState pair lemma). (3) Thread installs (XTopJointTcb*,
  WJLPP/WJLDel/WJLRestart). (4) VMT through budget_ok (curTime FK) to drop KDispHyps13P.vmt.
- Builds (tokyo, scratch/mr4build.sh, scratch/mr4/b.sh, warm mirror): mr4-b1 warm (UtResetLoopJ, MRHole2,
  KEntry15M OK), mr4-b2 (`-` in fun pattern), mr4-b3 UtResetLoopJM OK (5572 jobs), mr4-b4/b5 KEntry13P (mfk leaf
  checkBudget, MK walk needs LawfulStore, anonymous-constructor post, σ0 unification), mr4-b6 XTopJointKEntry13P OK
  (5612 jobs). Root Fl4Proofs.lean not rebuilt (two leaf imports). Axioms (scratch/axmr4.lean, untracked; mr4-b6):
  propext, Classical.choice, Quot.sound only for kernel_entryJ13P, dispatch_all13P, dispatch_invokeJAllM,
  dispatch_midJM, handle_invocation_entryJM, decOK_JM, budget_ok_mr, budget_mr_at, MachF.mfk_checkBudgetRestart,
  XCapP.reXP, j13P_platform, JAtZ.reset_loopJM, JAtZ.ppJSM, kernel_entryJ15M. No sorry/admit/native_decide/bv_decide.
## sch19 (branch par/sched19 in FL4-sc, on 78fc5942 = int/j2 incl. sch18, mr1-mr3)
New leaves XTopJointFaultDonM, XTopJointKEntry17M (imported from Fl4Proofs.lean). Nothing existing edited; JAtZ,
ScPPR/SpecPPR*/CnDel/WJL*/Tcb*/UtReset*/PP*/Preempt*/ScCharge*/ScTmoCt*/Entry/Irq*/MR*/XTopJointRecv* untouched.
- (1) FltDon at a switch DONE (XTopJointFaultDonM). FINDING (corrects the sch18 handoff): no JAtZR copy of
  sendTailJ's cone is needed. Under `switchThread u` (u ≠ ct) the sender's block on the reply keeps the switch and
  CurInv (`ps_actN`/`ps_curInv`), so before the donation the state is `JAtZ` with `Or.inr CurInv`; the donation's
  `test_reschedule` of the current thread is `reschedule_required`, which enqueues u and sets `chooseNewThread` on
  both sides (FL4's `push_donate_refinesW` and `ipc.push_don.blk` are generic in the action: they only ask that
  the action word names neither thread). After it the action is `chooseNewThread`, `JAtZ` holds, and sendFaultPDJ's
  tail (`stsIJ`, `sendTailJ`) is reused unchanged.
  * spec: `enqRQ`, `pdStS` (= pdSt with u enqueued: `dnSt {bdSt .. with readyQueues := RQ, action := choose}`),
    `pdS_*` (act/rq/ct/csc/rel/idle/isc/tm/arch/kd/ko/kt/kp), `donate_sw_eq` (donate_curN_eq under a switch:
    `rescheduleRequired_sched` + `tcbSchedAction_gen`), `pd_eqS` (ActReady after the unbind from ActReady before:
    u's TCB and SC kept; u's SC ≠ the donated one by `Inv.back`).
  * `JAtZ.pushDonJS` (pushDonJ under the switch, scripted: action word u ≠ t, d; `dn_*` at the enqueued state with
    `(σ := σBS)`; BlockedScActive re-packed), `JAtZ.sendFaultPDJM` (sendFaultPDJ with sch18's PJM patches + the
    switch donation), `JAtZ.faultRecvJM2` (faultRecvJM without `¬ FltDon`, the donating branch by PDJM),
    `JAtZ.faultHypJZM3` (handle_fault at every switch mid state). Generator sch19gen/{gen.py,hdr.lean} (untracked).
- XTopJointKEntry17M: `JRecvLeavesRN8` (ipc, sig and flt only under chooseNewThread), `.toRN7`, `JMidLeavesHyp8` [W],
  `jMidLeavesHyp_of8`, `KDispHyps17M.to16M`, NEW TOP `kernel_entryJ17M`.
- Premise change at the top (kernel_entryJ17M vs J16M): `JMidLeavesHyp7` [W] NARROWED to `JMidLeavesHyp8` [W] :=
  JMidLeavesHyp7's premises concluding `JRecvLeavesRN8`: `receive_ipc`, `receive_signal` and the cap fault's
  `handle_fault` each ONLY under `chooseNewThread`. Same l4v counterpart and truth argument (receive_ipc_corres /
  receive_signal_corres / handle_fault_corres inside handle_recv_corres under scheduler_act_sane); each case is a
  case of JMidLeavesHyp7. Nothing added. Every switch mid state is now proved; the residue is exactly the
  chooseNewThread mid states.
- NOT DONE (handoff), item 5, what JMidLeavesHyp8 still contains: every receive leaf (ipc, sig, flt) at a
  chooseNewThread mid state. The first phase is `fl4HandleInvocationR true false false true true cptr`, i.e. ANY
  invocation's `fl4PerformInvocation` (canDonate, firstPhase), so "chooseNewThread → CurInv ∨ ct SC-less" is a
  spec theorem over every invocation (a post fact to carry through `fl4PerformInvocation`'s cases, like
  JMidPerfHypQ), not one lemma. Watch for SchedControl Configure of ct's own SC (l4v postpones it: ct in the
  release queue with chooseNewThread, so CurInv.notRel fails while ct keeps its SC; CanBlock needs ct ∉ release
  queue) — check that case first, it may need a weaker disjunct than CurInv. Then per leaf: the SC-less case via
  the resumed leaves' `hsa` second disjunct (recvIpcBlockJG/recvIpcBlockNJG/recvSendPJG/... already take it;
  recvSigBlockJ / faultHypJZ take `Entered` and need the same `hsa` generalisation), the CurInv case via MidE-style
  copies with `chooseNewThread` in place of the switch (post JAtZ by `Or.inl`, so no JAtZR is needed).
- Builds (tokyo, b.sh): sch19-b1 (Ipc.SKeep vs P3.SKeep, `schedulable` unqualified), sch19-b2 (`rw [if_pos]` on
  test_reschedule's condition → `split_ifs`; BlockedScActive is a structure, re-packed), sch19-b3
  `XTopJointFaultDonM XTopJointKEntry17M` OK (5598 jobs), on 78fc5942, no sorry. Axioms (axsch19.sh, untracked;
  sch19-ax1): propext, Classical.choice, Quot.sound only for kernel_entryJ17M, KDispHyps17M.to16M,
  jMidLeavesHyp_of8, JRecvLeavesRN8.toRN7, JAtZ.faultHypJZM3/faultRecvJM2/sendFaultPDJM/pushDonJS, pd_eqS,
  donate_sw_eq, kernel_entryJ16M; pdS_ko/kt/kp propext only. No sorry/admit/native_decide/bv_decide.
## mr5 (branch par/mr5 in FL4-tcbj, on 845eb021 = int/j2 incl. mr4, sch18)
New leaves UtRetResetJM (generated: scratch/mr5/genU.py + headU/tailU.lean), XTopJointKEntry14P, 15P, 16P (imported
from Fl4Proofs.lean). Nothing existing edited. Goal: mr4 NEXT (1)–(4). DONE: (1) Untyped out of JPreDecHyp (VT-x types
stay, [scope]), (4) vmt gone, the P line rebased onto sch18's receive premise (J16P). NOT done: (2) CNode, (3) Thread.
- DONE (UtRetResetJM, 700de14b): `UtRetPostJM` (UtRetPostJ with `JAtPreMV`), `UtRetPostJ.toM` (spec side has no error
  outcome after the restart ⇒ FL4 not Preempted ⇒ both posts agree), `NoPre.NoErrAt`/`noErrAt_bind`/
  `noErrAt_liftE_single`, `noErr_retypeNoReset` (the spec retype without a reset never errs), `noErrAt_resetDev`/
  `noErrAt_retypeDev` (a device cap's reset, read at the state, never errs: no clear, no preemption point);
  `JAtZ.reset_untypedJM` (reset_untypedJ under MachPlat + PPPlatA, MR/VMT/VIM at the start; at `delSt` they hold by
  definition: detype changes only kheap/memory; chunk loop by mr4's reset_loopJM, ends in ResetJPostM);
  `JAtZ.utResetJM` (utResetJ likewise; the restart keeps machineState, curTime, interruptStates);
  `JUtRetHypDM`, `JAtZ.jUtRetHypM` (RAM: native type (`hNat`, < 14 with RetCtx.ty) with a reset by utResetJM, without
  by JAtZ.jUtRetHyp — its residual JUtRetHypR is vacuous there: `reset` is fixed by RetCtx.resetEq — and toM; so
  UtRetResetJ's JUtRetHypR2 [W] is not used on this path), `JAtZ.jUtRetHypDevM` (jUtRetHypDev + toM, getCap at the
  restart state via restartJ/restart_dstate), `decode_invocation_untypedJM`.
- DONE (XTopJointKEntry14P, 700de14b): `JPreDecHypK K` (JPreDecHyp with the cap condition `K c argsU`; JPreDecHyp =
  JPreDecHypK (fun c _ => NoPreKind c → False) by definition), `PreKind14` (CNode | Thread | Untyped with
  `∃ x, argsU.head? = some x ∧ 14 ≤ x.val ∧ x.val < 19`), `KDispHypsK K`, `KDispHypsK.to` (family premise converted
  per dispatch state), `.to13P`, `jPreDecHyp_of14` (the Untyped cap by decode_invocation_untypedJM from its JPath),
  NEW TOP `kernel_entryJ14P` (= J13P with `KDispHypsK PreKind14`; a wrapper, no body copy), `j14P_platform`.
- DONE (XTopJointKEntry15P, 30e62373): `budget_vmt_at`/`BudgetAt.vmt`: ValidMachineTime at every dispatch state with
  NO premise (the time stamp sets curTime = lastMachineTime = gctVal, validMachineTime_gct; a `true`
  checkBudgetRestart changes nothing, ScEntryRd's checkBudgetRestart_true — the timeout-fault path runs only on
  `false`), `KDispHypsKV K` (no vmt field), NEW TOP `kernel_entryJ15P`. KDispHyps13P.vmt [J] is GONE.
- DONE (XTopJointKEntry16P, 66382f12): `KDispHypsKV7` (mid leaves = sch18's JMidLeavesHyp7, `.to6` via jMidLeavesHyp_of7),
  NEW TOP `kernel_entryJ16P` (the narrowest receive premise, kernel_entryJ16M's, on the P line).
- Premises now (J16P): JPreDecHypK PreKind14 [W] (narrowed: CNode revoke/delete, Thread installs, Untyped VT-x types
  14..18 — the last are `JUtPath.vtx` [scope] anyway, stated at JAtPre); vmt removed; nothing added.
- NEXT (handoff): (2) and (3) are ONE job: both reach the deletion loop through `delHypsJL` (XTopJointWJLDel:
  CNode revoke/delete via decode_invocation_cnodeJ_stepsL's `JDelParts.jDelHypL`/`jPreemptHypL`, Thread installs via
  XTopJointTcbInsL `tcbInsW_wjl` and XTopJointTcb:2801's hPP). Plan: W' := `WJL ∧ MR a σ.ms ∧ VMT σ ∧ VIM σ`,
  Wp' := WJP + JAtPreMV-style MR/VMT/VIM at the pp pre-state; a combinator lifting `DelHypsWRZ W Wp` to W' given
  per-field "keeps MRV" lemmas (fin, triv, pp, post, zomb, swap, empty: FL4 side MK walks / store-only, pp by
  ppJDMV (curTime moves only there), post_cap_deletion of an IRQ handler by MachPlat.mask + a spec pair lemma
  (setIrqState irqInactive with maskInterrupt true keeps VIM, l4v deleting_irq_handler_valid_irq_masks)); spec side
  MachFieldFam's mfk_* (msF ⊇ MR fields + interruptStates) PLUS a curTime family (msF lacks curTime; VMT needs it
  at each pp pre-state) — fin's FPU save/switchLocalFpuOwner and VSpace TLB flush leaves are missing in
  MachFieldFam (skip.txt), add MKF leaves. Then delete_one/revoke loops at W', the CNode decode, the TCB installs,
  and `PreKind14` loses CNode/Thread (JPreDecHypK with `PreKindV` = VT-x Untyped only, or deleted with JUtPath.vtx).
- Builds (tokyo, scratch/mr5/b.sh, warm mirror): mr5-b1 (noErrAt_resetDev: returnOk binds), mr5-b2 UtRetResetJM OK
  (5574 jobs) + XTopJointKEntry14P OK (5618), mr5-b3 XTopJointKEntry15P OK (5620), mr5-b4 XTopJointKEntry16P OK (5630).
  Root Fl4Proofs.lean not rebuilt (four leaf imports). Axioms (scratch/axmr5*.lean, untracked): propext,
  Classical.choice, Quot.sound only for kernel_entryJ14P/15P/16P, jPreDecHyp_of14, KDispHypsK.to, KDispHypsKV7.to6,
  JAtZ.jUtRetHypM/jUtRetHypDevM/utResetJM/reset_untypedJM, decode_invocation_untypedJM, UtRetPostJ.toM,
  NoPre.noErrAt_retypeDev/noErr_retypeNoReset, budget_vmt_at, BudgetAt.vmt, j14P_platform. No sorry/admit/
  native_decide/bv_decide.
## sch20 (branch par/sched20 in FL4-sc, on a8ae2275 = int/j2 incl. sch19, mr4)
New leaves XTopJointRecvSigC, XTopJointFaultC (scripted: sch20gen/gen.py `sig` / `fault`, hdr.lean, hdr2.lean,
untracked), XTopJointKEntry18M, XTopJointKEntry19M (imported from Fl4Proofs.lean). Nothing existing edited; JAtZ,
ScPPR/SpecPPR*/CnDel/WJL*/Tcb*/UtReset*/PP*/Preempt*/ScCharge*/ScTmoCt*/Entry/Irq*/MR*/XTopJointRecv* untouched.
- STEP 1 (is JMidLeavesHyp8 true at chooseNewThread mid states?): NO counterexample; the SchedControl case is
  unreachable. The first phase is `fl4HandleInvocationR true false false true true cptr` (ReplyRecv / NBSendRecv /
  NBSendWait) and its decode has `firstPhase = true`: the spec's `fl4DecodeInvocation` (Ext/Invocation.lean:181-203),
  FL4's `decode_invocation` (crates/fl4-core/src/syscall.rs:119-151, `first_phase`) and C seL4 c98d70ad
  (src/object/objecttype.c:719-771 `decodeInvocation`, "Cannot invoke ... in the first phase") all reject thread,
  domain, SchedContext, SchedControl and CNode caps; `okAll_decodeFirst` (XTopJointMidRunS) proves the spec side
  yields only `FirstInv` invocations. So SchedControl Configure (on ct's own SC or any other) never runs before a
  mid receive, and l4v's postponement of ct does not arise there. (Even outside the first phase, Configure on ct's
  own SC does not postpone ct in reachable states: C asserts checkBudget() before commitTime(), so the head refill
  stays ready (l4v cur_sc_offset_ready) and sufficient (cur_sc_offset_sufficient); refill_update then resets its
  time to now and keeps >= MIN_BUDGET, and schedContext_resume's guard is false. Not needed here.)
  Of the FirstInv performs (Untyped, endpoint send, notification signal, reply, IRQ control / handler, arch) none
  binds an SC to ct, moves ct into the release queue, or changes the current SC; ct stops satisfying CurInv while
  runnable only by giving its SC away (send donating to a passive receiver, reply returning a donated SC). So at a
  chooseNewThread mid state "CurInv ∨ ct has no SC" holds in reachable states, and `JAtZ` there is satisfiable
  (`JAtZ.cur` allows chooseNewThread without CurInv). JMidLeavesHyp8 is true in reachable states.
- STEP 2, CurInv half, DONE for the notification receive and the cap fault outside a waiting receiver:
  * `MidC σ` := not idle ∧ CurRun ∧ action = chooseNewThread ∧ CurInv; `JAtZ.canBlockCurMC` (canBlockCurM's
    switch branch: no switch to ct, ct's SC word in Ac by curScAc).
  * XTopJointRecvSigC: `JAtZ.recvSigActiveJC/recvSigBlockJC/recvSigBlockPreJC/recvSigRetJC`, `jRecvSigHypC_of`,
    `jRecvSigHypC2_of` (every receive_signal at a MidC state): copies of the switch-mid M lemmas with
    `J.curInv hni.ncn` → MidC's CurInv, `canBlockCurM … (hni.sa …)` → `canBlockCurMC … hni`, and the "switch target
    ≠ ct" steps closed by the action being chooseNewThread. Nothing else changed: the spec and FL4 code are generic
    in a non-resume action.
  * XTopJointFaultC: `JAtZ.stsCurJC/noFaultJC/faultBlockJC`, `FltRecv σ` (ct's fault handler an endpoint with a
    waiting receiver), `JAtZ.faultHypJZC` (handle_fault of a cap fault at a MidC state outside FltRecv).
  * XTopJointKEntry18M: `JRecvLeavesRN9` (sig only under choose ∧ ¬CurInv), `.toRN8`, `JMidLeavesHyp9` [W],
    `jMidLeavesHyp_of9`, `KDispHyps18M.to17M`, TOP `kernel_entryJ18M`. XTopJointKEntry19M: `JRecvLeavesRN10` (flt
    only under choose ∧ (¬CurInv ∨ FltRecv)), `.toRN9`, `JMidLeavesHyp10` [W], `jMidLeavesHyp_of10`,
    `KDispHyps19M.to18M`, NEW TOP `kernel_entryJ19M`.
- Premise change at the top (kernel_entryJ19M vs J17M): `JMidLeavesHyp8` [W] NARROWED to `JMidLeavesHyp10` [W] :=
  JMidLeavesHyp8's premises concluding `JRecvLeavesRN10`: receive_ipc under chooseNewThread (unchanged);
  receive_signal under chooseNewThread ∧ ¬CurInv; the cap fault's handle_fault under chooseNewThread ∧
  (¬CurInv ∨ FltRecv). Same l4v counterpart (receive_ipc_corres / receive_signal_corres / handle_fault_corres inside
  handle_recv_corres); each case is a case of JMidLeavesHyp8, true in reachable states by STEP 1. Nothing added.
- NOT DONE (handoff), what JMidLeavesHyp10 still contains:
  (a) receive_ipc at a MidC state: same recipe over the ipc cone (XTopJointRecvIpcBlockM, RecvRetM (hni.sw,
      MidE.swNe), RecvSendPM, KEntry13M/14M/15M's jRecvIpcDoneM2/M3, ipcDoneM3_of, jRecvIpcUM, jRecvIpcLinkM with
      `cancelOther_keep`); gen.py needs patches for RecvRetM's `hni.sw`/`MidE.swNe` and the `hni.2.2.resolve` in
      KEntry13M; the woken sender's possible_switch_to under chooseNewThread is reschedule_required (no enqueue) +
      enqueue, check the RecvSendPM switch-specific `switchThread` spots (10) against the resumed JG lemmas, whose
      `hsa` already admits chooseNewThread (with ct SC-less: extend that disjunct to `∨ CurInv`).
  (b) the cap fault at a MidC state with FltRecv (FaultRecvM sendFaultIJM/PJM, FaultDonM sendFaultPDJM): the action
      word facts (`hna3`, `hdu0`: action word = u0) need the chooseNewThread encoding instead; under chooseNewThread
      the donation's test_reschedule enqueues nothing, so the resumed `pd_eq` (no switch) may apply directly.
  (c) the ¬CurInv half (ct SC-less, chooseNewThread): either the first-phase spec fact "chooseNewThread ∧ ct has an
      SC → CurInv" over the FirstInv performs (frame over curSc / ct's SC field / release queue, like
      XTopJointMidRunK/P/Q for CtRs), after which ¬CurInv means SC-less, and then the resumed lemmas' `hsa` second
      disjunct (choose ∧ SC-less: recvIpcBlockJG/NJG, recvSendPJG, canBlockCurG) with new top dispatchers.
- Builds (tokyo, b.sh): sch20-b1 `XTopJointRecvSigC` OK, sch20-b2 + `XTopJointKEntry18M` OK (5602 jobs), sch20-b3
  `XTopJointFaultC` OK, sch20-b4 `XTopJointFaultC XTopJointKEntry18M XTopJointKEntry19M` OK (5606 jobs), all on a8ae2275, first try, no sorry. Axioms
  (axsch20.sh, untracked; sch20-ax1, sch20-b4): propext, Classical.choice, Quot.sound only.
## sch21 (branch par/sched21 in FL4-sc, on 6683b87a = int/j2 incl. sch20, mr5)
New leaves XTopJointRecvSendPC, XTopJointRecvIpcC, XTopJointKEntry20M, XTopJointFaultRecvC, XTopJointKEntry21M
(imported from Fl4Proofs.lean; scripted: sch21gen/{gen.py `pc`/`c`, genf.py, hdr*.lean, mid.lean, tail.lean},
untracked). Nothing existing edited; JAtZ, ScPPR/SpecPPR*/CnDel/WJL*/Tcb*/UtReset*/PP*/Preempt*/ScCharge*/ScTmoCt*/
Entry/Irq*/MR*/XTopJointRecv* untouched.
- (a) receive_ipc at a MidC state (chooseNewThread ∧ CurInv) with a null or free reply DONE.
  * FINDING: RecvSendPM (the switch copies of the reply-pushing senders) is not needed. The resumed
    `recvSendPJG`/`FPJG` read the sender's SC under chooseNewThread only for "the push does not donate" (`hnd`:
    sender SC-less or receiver with an SC); XTopJointRecvSendPC's `recvSendPJGC`/`FPJGC` widen hAct's reschedule
    branch to `xs.sc = none ∨ xt.sc ≠ none` (two-line patch), and under CurInv the receiver has the current SC.
    The timeout-fault sender with an SC: the resumed `recvSendFPTJ`'s hAct already admits chooseNewThread ∧ notRel.
  * XTopJointRecvIpcC: copies of the switch-mid leaves with MidC (`recvIpcActJC`, `recvIpcBlockJGC/JC/NJGC`,
    `recvIpcRetJC`, `recvSendRetJC/RetPJC/RetPDJC/RetTJC`; patches: `J.curInv hni.ncn` → `hni.2.2.2`,
    `canBlockCurM … (hni.sa hcur)` → `canBlockCurMC … hni`, `hni.swNe` / the switch-target rcases closed by the
    action being chooseNewThread), hand-written `recvSendP0XC`/`T0XC`, dispatchers `jRecvIpcDoneC/C2/C3` and
    `jRecvIpcUC` (`ipcDoneM3_of` is state-only, reused).
  * NOT DONE in (a): a reply linked to another thread at MidC (`IpcLinked`). `cancelOther_keep` keeps ct's TCB,
    the action and the ready queues, but `JAtZ.cancelLinkJ` (via `cancelReplyJ`/`cancelRecvJ`) returns only
    `chooseNewThread ∨ CurInv` at the state after, so MidC there is not available. Route: a variant of
    cancelReplyJ's `hcur` (XTopJointCancelReply:465, inline via `J.curInv h0`) / of the receive cancel giving
    `CurInv σ → CurInv σ'` (the reply_remove_tcb SC writes keep the current SC an active SC; release queue kept
    by `ikm_cancelIpc`), then `jRecvIpcUC` at σ' exactly as `jRecvIpcLinkM` does for MidE.
- (b) the cap fault at a MidC state with a waiting receiver (FltRecv) DONE (XTopJointFaultRecvC). FINDING: copy
  the RESUMED sends, not the switch-mid ones: a resumed entry becomes chooseNewThread when ct blocks, so
  `sendFaultIJ/PJ/PDJ` already reason about a chooseNewThread state after that step; at MidC the action is
  chooseNewThread throughout. Patches: `hres` → `hcn0` + `CurInv σ` premise; the action word is 1 (P1's
  chooseNewThread encoding) below every TCB (`P1.notT_small`) instead of 0; ct's SC word ∈ Ac by `curScAc`
  (sch18 patch) instead of `BoundInv.sact`; `ciSt_act`/`ps_act` → `ciSt_actN`/`ps_actN`. The donation
  (`sendFaultPDJC`) is the resumed `pd_eq`/`pushDonJ` unchanged (no switch, so `test_reschedule` enqueues
  nothing). `faultRecvJC` (CurInv at σf after set_fault: only ct's fault field written), `faultHypJZC2` (every
  handle_fault at MidC).
- Tops: XTopJointKEntry20M: `IpcLinked`, `JRecvLeavesRN11` (ipc only under choose ∧ (¬CurInv ∨ IpcLinked)),
  `.toRN10`, `JMidLeavesHyp11` [W], `jMidLeavesHyp_of11`, `KDispHyps20M.to19M`, TOP `kernel_entryJ20M`.
  XTopJointKEntry21M: `JRecvLeavesRN12` (flt only under choose ∧ ¬CurInv), `.toRN11`, `JMidLeavesHyp12` [W],
  `jMidLeavesHyp_of12`, `KDispHyps21M.to20M`, NEW TOP `kernel_entryJ21M`.
- Premise change at the top (kernel_entryJ21M vs J19M): `JMidLeavesHyp10` [W] NARROWED to `JMidLeavesHyp12` [W]
  := JMidLeavesHyp10's premises concluding `JRecvLeavesRN12`: receive_ipc under chooseNewThread ∧ (¬CurInv ∨
  IpcLinked); receive_signal under chooseNewThread ∧ ¬CurInv; the cap fault's handle_fault under
  chooseNewThread ∧ ¬CurInv. Same l4v counterpart (receive_ipc_corres / receive_signal_corres /
  handle_fault_corres inside handle_recv_corres); every case is a case of JMidLeavesHyp8, true in reachable
  states by sch20 STEP 1. Nothing added. Other premises as J19M.
- NOT DONE (handoff), what JMidLeavesHyp12 still contains:
  (c1) the first-phase spec fact. Shape: from the entry state σ (Entered, CurInv σ by JAtZ.cur, Inv σ, CQ/NQ as
       in XTopJointMidRunQ), every outcome y of `fl4HandleInvocationR true false false true true cptr` satisfies
       `CtOK y := CurInv y ∨ (∃ x, y.kheap y.curThread = some (.tcb x) ∧ x.tcbSchedContext = none)`. Then ¬CurInv
       at the mid state means ct SC-less. Recipe as XTopJointMidRunK/P/Q (FK frames, scripted kf_ lemmas): view
       `cV σ := (curThread, curSc, idleSc, ct ∈ releaseQueue, ct's TCB SC field and NotIpcBlk, the SC object at
       curSc up to scActive)`; most leaves keep cV exactly (decode/lookup/arch/IRQ, other TCBs, non-curSc SCs:
       needs "the SC written ≠ curSc", from Inv.back and the written SC being bound to another thread); the
       two moves of ct's SC: endpoint send donating to a passive receiver (ct SC → none) and doReplyTransfer
       returning a donated SC (ct SC → none), both landing in the second disjunct, which every later step keeps
       (nothing binds an SC to ct in FirstInv performs: sch20 STEP 1). PerfW (Untyped, IRQ handler, ASID control)
       via a MidPerfAt-restricted premise like JMidPerfHypQ if not provable directly.
  (c2) SC-less leaves (choose ∧ ct SC-less): the resumed lemmas' `hsa` second disjunct already exists for
       recvIpcBlockJG/NJG, recvSendPJG/FPJG (sender SC-less; with a sender holding an SC the push DONATES to ct:
       a new case, cf. pushDonJ), recvSendFPTJ; to do: recvIpcActJ (uses CurInv's hscc for the badge path),
       the bound-SC return (LendM gives ct an SC, so it is the CurInv side under CtOK), receive_signal
       (recvSigBlockJ / recvSigActiveJ take Entered), handle_fault (faultHypJZ takes Entered; with ct SC-less
       `hcA` is vacuous since ct's SC word is 0, and FltDon cannot donate). "SC-less ct not in the release
       queue" needs an invariant fact (release-queue threads have SCs; check Inv).
  (c3) IpcLinked at MidC (above).
- Builds (tokyo, b.sh): sch21-b1 `XTopJointRecvSendPC` OK, sch21-b2 (`rTcbA` ambiguous with P1 open → `Endp.rTcbA`),
  sch21-b3 `XTopJointRecvIpcC XTopJointKEntry20M` OK (5612 jobs), sch21-b4 (`SKeep σ` ambiguous → `Ipc.SKeep`,
  as sch19), sch21-b5 `XTopJointFaultRecvC XTopJointKEntry21M` OK (5616 jobs), all on 6683b87a, no sorry. Axioms (axsch21.sh,
  untracked; sch21-ax1, sch21-ax2): propext, Classical.choice, Quot.sound only.
## mr6 (branch par/mr6 in FL4-tcbj, on 6a51cd48 = int/j2 incl. mr5, sch19)
New leaves MachFieldFamT, MachKeepD, XTopJointMRDel, XTopJointMRCnode, XTopJointKEntry17P (imported from
Fl4Proofs.lean; generated parts by scratch/mr6/{mtgen.py,mk.sh}, {mkdgen.py,mkD.sh,cg.py,topo.py}, gencn.py). Nothing
existing edited; sch20's modules untouched. Goal: mr5 NEXT (2)+(3). DONE: the deletion loop at MachPlat, CNode out of
PreKind (J17P). NOT done: Thread (PreKind17 = Thread | VT-x Untyped).
- DONE (MachFieldFamT, 336b8411): `msFT σ` = (MachFieldFam's msF σ, σ.curTime), `MTK m := FK msFT m`; MKF leaves
  for the TLB flushes (invalidateASID, invalidateTranslationSingleASID, invalidateLocalPageStructureCacheASID) and the
  FPU ops (readFpuState, writeFpuState, enableFpu, disableFpu, isFpuEnable), getFaultAddress, ackInterrupt; 227 `mtk_*`
  lemmas (DK family renamed, skip: portIn, setIrqState, preemptionPoint, invokeSchedContext and the time/IRQ/port/
  memory-clearing ops). FINDING: `finaliseCap` reaches `setIrqState` only syntactically: the IRQ handler's
  `deletingIrqHandler` → `capDeleteOne` empties with a NULL cleanup (`mtk_emptySlotNull`: postCapDeletion nullCap does
  nothing), so `mtk_finaliseCap` holds with no premise (generator cuts capDeleteOne's call edge).
- DONE (MachKeepD, 595172cb): `MRKeepD arI AR` [P] = MRKeep's fields + invalidate_ept/page/asid/page_structures,
  set_vspace, dma_frame, irq_free (each keeps AR at every 2nd arg; with AR := MR: no IRQ mask, pending line or clock
  changes; l4v machine_op_lifts outside irq_masks/irq_state/time_state/last_machine_time; irq_free/dma_frame are FL4
  IOAPIC/IOMMU bookkeeping with no spec machine field). Arch-only; `MRKeepD.toK`; `modelArch_mrKeepD` (in
  XTopJointMRDel: MachKeepD must not import P1-level modules). `MKD.*`: 32 walks over finalise_cap's arch-threading
  call graph (scripted), the two fuel loops by loop.spec_decr_nat with AR as invariant, `MKD.cdt_empty_slot` for a
  Null cleanup only (mask_irq is reached only through the cleanup's post_cap_deletion). Top `MKD.objects_finalise_cap`.
- DONE (XTopJointMRDel, 6f2c21aa): `MRV MR a σ` := MR a σ.ms ∧ ValidMachineTime σ ∧ ValidIrqMasks σ [J] (carried),
  `WMR MR W` := W ∧ MRV; `mrv_keep` (msFT kept ⇒ MRV kept at the same a). Generic lifts for ANY W: `ZombieHypWZ.mrv`,
  `SwapHypWZ.mrv`, `EmptyHypWR.mrv`, `RdTrivHyp.mrv`, `FinObjHypWRcZ.mrv` (MKD walk + mtk_finaliseCap),
  `PostDelHypW.mrv` from `post_mrv` (IRQ handler: FL4 mask_irq irq true by `MachPlat.mask`, irq_free by MRKeepD;
  spec `setIrqState irqInactive` has the one outcome `setIrqSt` (`setIrqInactive_out`), line inactive and masked, so
  VIM after; the masks agree by `BitVec.ofNat_toNat`; IO port: FL4 keeps a, spec `mtk_archPostCapDeletion'`).
  `WJPM` := WJP ∧ JAtPreMV; `jPreemptHypLM` (jPreemptHypL with ppJDMV, MachPlat + PPPlatA, no PPPlat);
  `delHypsJLM : DelHypsWRZ (WMR MR WJL) WJPM RdLO RzJ`; `JDelHypLM`, `JDelParts.jDelHypLM` (delHyp_fullWRZ).
- DONE (XTopJointMRCnode + XTopJointKEntry17P, 025a842e): scripted copies `EJLM`/`EJPM`, `EJLM.restart` (MRV through
  the restart's setThreadState: mtk_setThreadState'), `cn_del_topJLM` (preempted branch reads JAtPreMV off WJPM),
  `decode_invocation_cnode_{revoke,delete}JLM`, `decode_invocation_cnodeJ_stepsLM` (XCapP JAt (JAtPreMV MR) from
  `hmv : MRV MR ar σ`, MachPlat, MRKeepD, PPPlatA). `PreKind17` (Thread | Untyped with a VT-x type 14..18),
  `KDispHypsKV7.toK`, `jPreDecHyp_of17` (CNode case as decOK_J's, by stepsLM with MRV from JPreDecHypK's own
  MR/VMT/VIM premises), NEW TOP `kernel_entryJ17P`.
- Premise change at the top (kernel_entryJ17P vs J16P): `KDispHypsKV7 PreKind14` NARROWED to `KDispHypsKV7 PreKind17`
  (the [W] JPreDecHypK no longer asked for CNode caps); `MRKeep arI MR` [P] WIDENED to `MRKeepD arI MR` [P] (seven more
  arch-op fields, same arch-only shape, satisfied by modelArch: `modelArch_mrKeepD`). Nothing else.
- NEXT (handoff): Thread out of PreKind. The installs go through XTopJointTcbInstall/TcbSsp/TcbInsL whose structures
  hard-wire the preempted invariant: `TcbInsW.del : DelHypsWRZ (W kb) (WJP ..)`, `InstPostWP W (WJP ..)`,
  `top_of_instJ` (WJP → JAtPre), ~50 occurrences (grep `WJP\|JAtPre` in XTopJointTcbInstall/TcbSsp/Tcb). Route: a
  scripted copy (gencn.py style) of the install chain with `WJP (L := L) arI AR Z H Cs kb` → `WJPM .. MR ..`,
  `JAtPre` → `JAtPreMV MR`, W := `WMR MR (WJL ..)`; `InsWJ` at WMR needs the cap insert to keep MRV (FL4 store-only,
  a kept; spec capInsert keeps msFT: MachFieldFamT's `mtk_capInsert`); TcbInsL's
  `tcbInsW_wjl` → `delHypsJLM`; XTopJointTcb:2790's decode (hPP used for `jPreemptHyp`/`tcbInsW_wjl` and
  `hPP.minBudget` = `PPPlatA.minBudget`) with `hmv` and the restart via `EJLM.restart`-style MRV; then PreKind = VT-x
  Untyped only (or JPreDecHypK replaced by JUtPath.vtx's scope premise).
- Builds (tokyo, scratch/mr6/b.sh, warm mirror): mr6-b1 (b.sh grep typo), b2 (multi-line macro_rules), b3
  MachFieldFamT OK (4594 jobs); b4–b6 MachKeepD (tail arch op, delete_asid simp recursion → mkd_walk', leftover ok),
  b7 MachKeepD OK (3612); b8 (bullet lost in the pp copy), b9 XTopJointMRDel OK (5576); b10 (hM shadowed, segment
  cut a docstring), b11 XTopJointMRCnode OK (5578); b12 XTopJointKEntry17P OK (5640). Root Fl4Proofs.lean not rebuilt
  (five leaf imports). Axioms (scratch/mr6/chk6.lean, untracked; mr6-ax1): propext, Classical.choice, Quot.sound only
  for kernel_entryJ17P, jPreDecHyp_of17, KDispHypsKV7.toK, decode_invocation_cnodeJ_stepsLM/revokeJLM/deleteJLM,
  cn_del_topJLM, EJLM.restart, JDelParts.jDelHypLM, delHypsJLM, jPreemptHypLM, post_mrv, PostDelHypW.mrv,
  FinObjHypWRcZ.mrv, ZombieHypWZ.mrv, SwapHypWZ.mrv, EmptyHypWR.mrv, mrv_keep, modelArch_mrKeepD,
  MKD.objects_finalise_cap/vcpu_revoke_ports_loop/vspace_delete_asid_pool_loop, MachT.mtk_finaliseCap/emptySlotNull,
  kernel_entryJ16P; setIrqInactive_out propext only. No sorry/admit/native_decide/bv_decide.
## sch22 (branch par/sched22 in FL4-sc, on 37c70ce1 = int/j2 incl. sch21)
New leaves XTopJointRecvIpcLinkC, XTopJointKEntry22M (imported from Fl4Proofs.lean; hand-written, no generator).
Nothing existing edited; JAtZ, ScPPR/SpecPPR*/CnDel/WJL*/Tcb*/UtReset*/PP*/Preempt*/ScCharge*/ScTmoCt*/Entry/Irq*/MR*/
XTopJointRecv* untouched.
- (c3) IpcLinked at MidC DONE. FINDING: sch21's worry ("the cancel may hand ct's current SC back via reply_remove")
  does not arise: the spec's `cancel_ipc` of a thread blocked on a reply calls `replyRemoveTcb`
  (Fl4Spec/IpcCancel.lean:145), which only trims `scReplies` of the SC the reply is at and unlinks the reply; no SC
  moves between threads (l4v: that is `reply_remove`, used by do_reply_transfer, not `reply_remove_tcb`). So
  `CurInv` is kept, no CurInv-keeping variant of cancelReplyJ/cancelRecvJ was needed:
  * `cancelLink_curInv` (spec only, Sched.SchedValid σ, i ≠ ct blocked on reply q or receiving with q): reply case by
    `ikm_cancelIpc` (IK i: TCB SC fields, SC refill max, release queue), `cancelOther_keep` (ct, ct's TCB),
    `rsf_replyRemoveTcb` (curSc, idleSc); receive case by `cancelIpc_recv_cfr … |>.1.curInv`.
  * `jRecvIpcLinkC`: `jRecvIpcLinkM` with MidC (MidC at the state after by `cancelLink_curInv`) and `jRecvIpcUC`.
- Top: XTopJointKEntry22M: `JRecvLeavesRN13` (ipc, sig, flt all only under chooseNewThread ∧ ¬CurInv), `.toRN12`
  (`jRecvIpcLinkC` when CurInv and IpcLinked), `JMidLeavesHyp13` [W], `jMidLeavesHyp_of13`, `KDispHyps22M.to21M`,
  NEW TOP `kernel_entryJ22M`; also `Sched.Inv.notRel_of_noSc` (an SC-less thread is in no release queue, from
  `Inv.rel`; for (c2)).
- Premise change at the top (kernel_entryJ22M vs J21M): `JMidLeavesHyp12` [W] NARROWED to `JMidLeavesHyp13` [W] :=
  JMidLeavesHyp12's premises concluding `JRecvLeavesRN13`: receive_ipc, receive_signal and the cap fault's
  handle_fault each only under chooseNewThread ∧ ¬CurInv (the IpcLinked disjunct of receive_ipc is gone). Same l4v
  counterpart (receive_ipc_corres / receive_signal_corres / handle_fault_corres inside handle_recv_corres); a case of
  JMidLeavesHyp8, true in reachable states by sch20 STEP 1. Nothing added. Other premises as J21M.
- NOT DONE (handoff), what JMidLeavesHyp13 still contains (only the ¬CurInv half, = sch21 (c1)+(c2)):
  (c1) the first-phase spec fact `CtOK y := CurInv y ∨ ct SC-less`. FINDING: it is NOT a pure projection frame
  (FK view) like MidRunK/Q: SCs other than curSc change (sendSignal / send to a receiver wake threads:
  schedContextResume / refill_unblock_check / possible donation on the woken thread's SC), and other threads enter
  the release queue (postpone). The preserved predicate must be invariant-carrying, PQ-style (`PQ ct m`: from a
  CQ-like state every outcome is CQ-like), with view facts "ct ∉ releaseQueue", "ct's SC field", "curSc/idleSc",
  "scActive of the SC at curSc" and a side invariant "every written SC is bound (scTcb) to a thread ≠ ct" (from
  Inv/SchedValid: the woken thread's SC has scTcb = that thread, and curSc's scTcb = ct under CurInv). The two moves
  to the SC-less disjunct (endpoint send donating ct's SC to a passive receiver; doReplyTransfer returning a donated
  SC) then need a "SC-less stays SC-less" frame (nothing binds an SC to ct in FirstInv performs, sch20 STEP 1).
  PerfW (Untyped, IRQ handler, ASID control) via a MidPerfAt-restricted premise like JMidPerfHypQ. Estimate: a
  MidRunQ-sized scripted module plus hand lemmas for sendIpc/sendSignal/doReplyTransfer.
  (c2) SC-less leaves (choose ∧ ct SC-less). FINDING: not just copies with `hsa`'s second disjunct: an SC-less ct
  receiving from an ACTIVE notification with a bound SC is GIVEN that SC (`specRecvTail` → `maybeDonateSc`:
  schedContextDonate + schedContextResume; FL4 `notification.maybe_donate_sched_context`), then
  `ifSporadicCurScTestRefillUnblockCheck` on an SC ≠ curSc. Same for receive_ipc's bound-notification path
  (complete_signal tail `specCompleteTail`). These are new donating cases (cf. the signal-donation proofs of
  IpcSignalDonSpec / XTopJointRecvSigRet for the donating direction). The rest as sch21 (c2): recvIpcActJ (hscc
  badge path), recvSigBlockJ / recvSigActiveJ (Entered), faultHypJZ (Entered; with ct SC-less hcA vacuous since ct's
  SC word is 0, FltDon cannot donate: genf.py's `HCA_N` replacement becomes `fun h0 => absurd (SC word = 0) h0`,
  and the `hCI` uses go away), and the reply-push sender with an SC donating to ct (pushDonJ). Release-queue fact: done
  (`Sched.Inv.notRel_of_noSc`).
  Once (c1) holds, the cleanest top is `JRecvLeavesRN14` (leaves under choose ∧ ct SC-less) with `.toRN13` from the
  c1 fact at the mid state (y.2), so each SC-less family can be removed one at a time.
- Builds (tokyo, b.sh): sch22-b1 `XTopJointRecvIpcLinkC` OK (5618 jobs), sch22-b2 `XTopJointRecvIpcLinkC
  XTopJointKEntry22M` OK (5620 jobs), both on 37c70ce1, first try, no sorry. Axioms (axsch22.sh, untracked;
  sch22-ax1): propext, Classical.choice, Quot.sound only (Sched.Inv.notRel_of_noSc: propext, Classical.choice).
## mr7 (branch par/mr7 in FL4-tcbj, on 0e0fb140 = int/j2 incl. mr6, sch21)
New leaves XTopJointMRTcb, XTopJointMRTcbL, XTopJointKEntry18P, XTopJointKEntry19P (imported from Fl4Proofs.lean;
generated by scratch/mr7/{gentcb.py+headT.lean, gentcbl.py+headTL.lean, gen18.py+t18.lean}). Nothing existing edited;
sch22's modules (XTopJointRecv*/Fault*/JAtZR*/MidRun*/KEntry1x-2xM) only imported. Goal: mr6 NEXT (Thread out of
PreKind), then join the P line to sch21's receive top. DONE both.
- DONE (XTopJointMRTcb): scripted copy of XTopJointTcbInstall 734–1929 (install_tcb_capJ … tcb_configureJ, TcbInsW,
  JAtZ.restartW) and XTopJointTcbSsp 467–1450 (install_fhJ/OkJ, ssp_tailJ, tcb_set_sched_paramsJ), every name with an
  `M` suffix, `WJP .. kb` → `WJPM .. MR .. kb`, `JAtPre` → `JAtPreMV MR`; `TcbInsWM AR MR Z H Cs W Rd Rz` (MR explicit:
  `del : ∀ kb, DelHypsWRZ (W kb) (WJPM ..)`); the only body patches are top_of_instJM's and ssp_tailJM's preempted
  branch (read `JAtPreMV` off `WJPM.2`). FINDING: the install bodies never look inside WJP (only the type mentions it),
  so the copy is text-only; ~2000 lines rebuild in seconds (warm).
- DONE (XTopJointMRTcbL): `BufHypW.mrv` (threadSet / the tail's rescheduleRequired keep msFT: mtk_threadSet',
  mtk_rescheduleRequired'), `insWJ_wjlM` (InsWJ at WMR MR WJL; capInsert keeps msFT), `tcbInsWM_wjl` (with delHypsJLM),
  `decode_invocation_threadJ_stepM` (copy: hPP → hMP/hKD/hPA/hmv, restart keeps MRV by mtk_setThreadState',
  hPP.minBudget → hPA.minBudget).
- DONE (XTopJointKEntry18P): `PreKind18` (Untyped with a VT-x type 14..18 only), `jPreDecHyp_of18` (Thread case =
  decOK_J's, scripted, by decode_invocation_threadJ_stepM with MRV from JPreDecHypK's own MR/VMT/VIM; SetEPTRoot's
  [scope] JVtxScope is at JAtPre, lifted by `XCapP.reXP` + `thread_noPre_of` since EPTRoot is no installing label),
  TOP `kernel_entryJ18P` (= J17P with KDispHypsKV7 PreKind18).
- DONE (XTopJointKEntry19P): `KDispHypsKV12 K` (KDispHypsKV7 with sch21's JMidLeavesHyp12), `.to7` (jMidLeavesHyp_of12
  … of8, hAT/hmax/htu from the top), NEW TOP `kernel_entryJ19P` (wrapper over J18P), `j19P_platform` (non-vacuity:
  MachPlat modelArch modelMR ∧ MRKeepD modelArch modelMR ∧ modelArch raises interrupts).
- Premise change at the top (kernel_entryJ19P vs J17P): `JPreDecHypK PreKind17` [W] NARROWED to `JPreDecHypK
  PreKind18` [W] (Thread caps no longer asked); the receive premise `JMidLeavesHyp7` [W] NARROWED to sch21's
  `JMidLeavesHyp12` [W]. Nothing added.
- NOT DONE: discharging JPreDecHypK PreKind18 from `JUtPath.vtx` [scope]. It does NOT reduce exactly: JUtPath.vtx /
  JDevPath.vtx state the VT-x retype at `XCapP .. JAtPre` (JVtxScope), JPreDecHypK asks `XCapP .. (JAtPreMV MR)`, and a
  VT-x retype may preempt (reset), so XCapP.reXP does not apply. Options (handoff): restate JVtxScope for the Untyped
  case at JAtPreMV (edits XTopJointEntry's JPath: lead's call; then jPreDecHyp_of18's Untyped case is `hN.vtx`/
  `hDv.vtx`), or prove the VT-x type's spec decode non-preempting. Then JPreDecHypK disappears from the P top.
- Builds (tokyo, scratch/mr7/b.sh, warm mirror): mr7-b1 warm (XTopJointTcb, MRCnode, KEntry17P, KEntry21M OK), mr7-b3
  (structure docstring cut by the segment), mr7-b4 XTopJointMRTcb (5578 jobs) + XTopJointMRTcbL (5580) OK, mr7-b5
  XTopJointKEntry18P OK (5646), mr7-b6 XTopJointKEntry19P OK (5670). Root Fl4Proofs.lean not rebuilt (four leaf
  imports). Axioms (scratch/mr7/chk7.lean, untracked; mr7-b6): propext, Classical.choice, Quot.sound only for
  kernel_entryJ19P, j19P_platform, KDispHypsKV12.to7, kernel_entryJ18P, jPreDecHyp_of18,
  decode_invocation_threadJ_stepM, tcbInsWM_wjl, insWJ_wjlM, BufHypW.mrv, tcb_set_{timeout,space,ipc,sched_params}JM,
  tcb_configureJM, ssp_tailJM, top_of_instJM, thread_control_capsJM, install_fhOkJM. No sorry/admit/native_decide/
  bv_decide.
## mr8 (branch par/mr8 in FL4-tcbj, on 30875146 = int/j2 incl. mr7, sch22)
New leaves XTopJointKEntry20P, XTopJointKEntry21P (imported from Fl4Proofs.lean; hand-written). Nothing existing
edited (JPath / XTopJointEntry untouched, per the lead's decision on mr7's open question); sch23/sch23b's modules
(XTopJointRecv*/Fault*/Mid*/KEntry2xM) only imported.
- DONE (XTopJointKEntry20P, 5165a606): `JVtxScopeM AR MR …` [S] = XTopJointEntry's `JVtxScope` with `JAtPreMV MR`
  as the preempted post (docstring: same DESIGN §9 scope; MachPlat form because a VT-x Untyped retype may run the
  reset, whose preemption point can preempt, so `XCapP.reXP` cannot bridge from `JAtPre`). `JVtxHypM AR MR Z H Cs D s
  ar σ ct` [S]: at the dispatch state, with MR/VMT/VIM and exactly the decode facts `JPreDecHypK PreKind18` took,
  for `capAt … = ok (.Untyped p sb fi dev)` and `argsU.head? = some x`, `14 ≤ x.val < 19`, `JPath … (.Untyped …) →
  JVtxScopeM …`. `jPreDecHyp_of20 : JVtxHypM → JPreDecHypK PreKind18` (an unfold: cases on the cap, PreKind18 is
  False off Untyped). `KDispHypsKV20` (KDispHypsKV12 PreKind18 with `JVtxHypM` in inv and mid), `.to12`, NEW TOP
  `kernel_entryJ20P` (wrapper over J19P), `j20P_platform` (= j19P_platform).
- DONE (XTopJointKEntry21P, cb7d3ede): `KDispHypsKV21` (KDispHypsKV20 with sch22's `JMidLeavesHyp13`), `.to20`
  (`jMidLeavesHyp_of13 hA hmax htu`), NEW TOP `kernel_entryJ21P` (wrapper over J20P), `j21P_platform`.
- Premise change at the top (kernel_entryJ21P vs J19P): `JPreDecHypK PreKind18` [W] REPLACED by `JVtxHypM` [S]
  (scope, same statement restricted to VT-x Untyped retypes, no l4v counterpart: l4v has no VT-x objects);
  `JMidLeavesHyp12` [W] NARROWED to `JMidLeavesHyp13` [W]. No [W] invocation premise is left on the P line.
- PREMISES of `kernel_entryJ21P` (every hypothesis; bundles with their fields' tags as at their definitions):
  * `[PlainStore st]` (instance: the plain store model, P1).
  * `J : JAtZ … s a σ` [J] (the joint invariant at the entry: l4v invs + state_relation, JointAt.lean).
  * `hni : Entered σ` [J] (ct_running, resume_cur_thread).
  * `hR : MR a σ.machineState` [J] (shared machine_state), `hVI : ValidIrqMasks σ` [J] (valid_irq_masks).
  * `hn : NativeSys n c` (the syscall number names c: the statement's own relation, not a gap).
  * `hflag` [S] (l4h trap mode: TRAP_SYSCALLS clear after the FAULT_IP write).
  * `hB : ∀ x, kheap ct = tcb x → KBudget arI a (faultIPSt …)`: `now` NowAgree [P] (per state; MachPlat.nowAgree from
    MR + VMT), `cur` CurInv [J], `off` OffReady [J], `tmo` [J] — FINDING: this is the OLD `KBudget.tmo`, which budtr
    showed FALSE in reachable states (a receiver waiting on the timeout-handler endpoint with a non-RR SC); budtr's
    fix (`KBudgetB`, `JAtZ.budgetOkB`, J8B) was never carried onto the J9+/M/P lines (XTopJointKEntry13P:876 reads
    `hBu.tmo` in the old shape). Handoff: a `budget_ok_mr`-level copy of budgetOkB (budgetOkTR for recvEP) and
    `KBudgetB` at the top (KBudget.toB shows it is strictly weaker).
  * `hK : ∀ σb, BudgetAt σ σb true → ∀ Z' H' Cs' Ac' Lst' D' s' a', JAtZ … σb → KDispHypsKV21 …`:
    `inv`: `JEntryGlobM` (ari [P], tot [P], delParts [J]/[P] (archRef [P], arKeep [P], vt [J], thr), nd [P], ppA [P],
    dom [P], portIn [P] (∀σ PortInVal), sigRest [J], timeAg [P], maxTU/tu [P]); `JEntryAt` (ni, ctnq, sg, rd0, flags,
    epQ, handlers, ports, vfh, cnf, vsTyp, live, fnz, urz, utks [J]; stall, ioapics, archIrq [P]); `JPathAt` (per cap
    kind JPath, fields tagged in XTopJointEntry's table: [P] config constants/one core, [J] invariant facts, [S]
    `JVtxScope` for VT-x decodes, and `JUtPath.ret`: `JUtRetHypR2` [W], only the VT-x types, NOT used by the P
    line's untyped decode (decode_invocation_untypedJM) but still a field of JPath); `JVtxHypM` [S] (new).
    `recv`: ct_not_in_q, valid_fault_handler [J]. `mid`: JEntryGlobM, JEntryAt, JPathAt as above,
    `MidRun.JMidPerfHypQ` [W], `JMidVfhHyp` [J], `JMidLeavesHyp13` [W] (sch22), `JVtxHypM` [S].
  * `hFin : ∀ x ∈ (specFront c σ).1, ∀ …, JAtZR … x.2 → KFinAtR …`: hd (domainTime ≠ 0 ∨ NdOK) [J], vt [J],
    arch/archNd (ArchSwF/ArchNdF) [P], fo FpuOwnOK [J], sni/send (SniHyp/SendHyp) [P], tail (schedule's CR3 tail) [P].
  * `hARI : ARIface` [P], `hA : P0.ArchTotal` [P], `hnd : numDomains = 1` [P], `hM : MachPlat arI MR` [P],
    `hKD : MRKeepD arI MR` [P], `hPA : PPPlatA` [P], `hIA : IrqPlatA` [P], `hmrt` (MAX_RELEASE_TIME) [P], `hmb`
    (MIN_BUDGET) [P], `hT : TimeAgree` [P], `hmax : maxTicksToUs = U64.MAX` [P], `htu` (ticks_to_us) [P].
  * `hNS : ∀ s a σ, JHoleAt … → NativeScope σ` [S], `hNSR : ∀ …, JAtZR … → NativeScope σ` [S] (VT-x RunningVM out of
    the native scope).
  Non-vacuity of the platform premises: `j21P_platform` (MachPlat ∧ MRKeepD for modelArch/modelMR, interrupts
  raised).
- Builds (tokyo, scratch/mr8/b.sh, warm mirror): mr8-b1 `XTopJointKEntry20P` OK (5672 jobs), `XTopJointKEntry21P` OK
  (5678 jobs), first try. Root Fl4Proofs.lean not rebuilt (two leaf imports). Axioms (scratch/mr8/chk8.lean,
  untracked; mr8-b1): propext, Classical.choice, Quot.sound only for kernel_entryJ21P, j21P_platform,
  KDispHypsKV21.to20, kernel_entryJ20P, j20P_platform, KDispHypsKV20.to12, jPreDecHyp_of20, kernel_entryJ19P. No
  sorry/admit/native_decide/bv_decide.
## sch23b (branch par/sched23b in FL4-rb, on 331a39e0 = int/j2 incl. sch22, mr6)
New leaves XTopJointMidN, XTopJointFaultN, XTopJointRecvSigN, XTopJointRecvIpcN, XTopJointKEntry23M (imported from
Fl4Proofs.lean; FaultN and the copied parts of RecvSigN / RecvIpcN scripted: sch23bgen/{common.py,genf.py,gens.py,
hdr*.lean,dsig.lean,dipc.lean,k23.lean} in the worktree root, untracked). Nothing existing edited; JAtZ, ScPPR/SpecPPR*/
CnDel/WJL*/Tcb*/UtReset*/PP*/Preempt*/ScCharge*/ScTmoCt*/Entry/Irq*/MR*/MidChoose*/XTopJointRecv* untouched.
- (c2) SC-less leaves (chooseNewThread ∧ ct SC-less) DONE except the two SC donations to ct and the linked reply.
  * XTopJointMidN: `MidN σ` := ct ≠ idle ∧ CurRun ∧ action = chooseNewThread ∧ (∀ x, ct's TCB x → x.tcbSchedContext =
    none); `JAtZ.canBlockCurMN` (= resumed `canBlockCurG` with its `hsa` SC-less disjunct). ct out of the release
    queue everywhere by sch22's `Sched.Inv.notRel_of_noSc`.
  * XTopJointFaultN (scripted from XTopJointFaultC / XTopJointFaultRecvC): `stsCurJN`, `noFaultJN`, `faultBlockJN`,
    `sendFaultIJN`, `sendFaultPJN`, `faultRecvJN`, `faultHypJZN` (EVERY cap-fault `handle_fault` at a MidN state).
    Patches: CurInv's notRel → notRel_of_noSc; `BlockedScActive` for ct: an SC bound to ct would be ct's SC
    (`scBack_of`), so `rw [hsc0] at hxs; cases hxs`; ct's SC word ∈ Ac vacuous (word is 0, `optRef_none`); the
    donation flag is false (`hd0`), so the PDJ (donating) send does not arise.
  * XTopJointRecvSigN: `recvSigBlockJN` (scripted from recvSigBlockJC; no SC-return case: ntfnSc = ct's SC = none
    is impossible), `recvSigActiveJN` (an active notification whose SC is none or bound to a thread: FL4
    `maybe_donate_sched_context` / spec `maybeDonateSc` no-ops by ScDonate's `maybe_donate_nodonate` with
    `NoDon.wordsR` (NoDon.words from NtfnStateRel + SchedRel instead of IRel); `receive_signal_active_eqN`
    (FL4: `sc_sporadic(0)` is false), `specRecvTail_noSc` (spec: `ifSporadic… none` is nothing)), `SigDon σ p`,
    `jRecvSigHypN_of` (every receive_signal at MidN outside SigDon).
  * XTopJointRecvIpcN: `recvIpcActJN` (scripted from recvIpcActJ; `complete_signal_eqN`, `completeSignal_noSc`),
    `IpcActDon σ`, `IpcPushDon σ p rc`, `jRecvIpcUN` (every receive_ipc at MidN with a null or free reply outside the
    two donations): FINDING: no other new copies needed: the blocking receives are the RESUMED `recvIpcBlockJG` /
    `recvIpcBlockNJG` (their `hsa` second disjunct), the plain head sender `recvSendJ0X` (generic), a reply-pushing
    sender WITHOUT an SC `recvSendPJGC` / `recvSendFPJGC` (sch21's widened hAct: `xs.sc = none`), the timeout-fault
    sender `recvSendFPTJ` / `recvSendFTJ` (hAct: chooseNewThread ∧ ct ∉ releaseQueue), and every IpcRetM (SC-return)
    case is vacuous (`LendM` needs ntfnSc = ct's SC ≠ none).
- Top: XTopJointKEntry23M: `CtSc σ` (ct has an SC), `midN_of`, `JRecvLeavesRN14`, `.toRN13`, `JMidLeavesHyp14` [W],
  `jMidLeavesHyp_of14`, `KDispHyps23M.to22M`, NEW TOP `kernel_entryJ23M`.
- Premise change at the top (kernel_entryJ23M vs J22M): `JMidLeavesHyp13` [W] NARROWED to `JMidLeavesHyp14` [W] :=
  JMidLeavesHyp13's premises concluding `JRecvLeavesRN14`, whose leaves are JRecvLeavesRN13's with one more premise:
  cap fault: `CtSc σ`; receive_signal: `CtSc σ ∨ SigDon σ p.bv`; receive_ipc: `CtSc σ ∨ IpcLinked s rc ∨ IpcActDon σ ∨
  IpcPushDon σ p.bv rc`. Same l4v counterpart (receive_ipc_corres / receive_signal_corres / handle_fault_corres in
  handle_recv_corres); each case is a case of JMidLeavesHyp13 (true in reachable states, sch20 STEP 1). Nothing added.
  The CtSc disjunct is exactly what sch23's first-phase fact (jMidChooseFact: chooseNewThread ∧ ct has an SC →
  CurInv) removes.
- NOT DONE (handoff), what JMidLeavesHyp14 still contains besides CtSc:
  (d1) `SigDon` / `IpcActDon`: ct SC-less receives from an active notification (directly or ct's bound one in
       receive_ipc) whose SC is bound to no thread: `maybeDonateSc` = schedContextDonate (ntfn SC → ct; ct is the
       RUNNING current thread, unlike ScSignalDonJ's woken blocked thread) + schedContextResume (ct schedulable: if the
       head refill is not ready/sufficient ct is postponed into the release queue), then the sporadic
       refill_unblock_check on the SC (≠ curSc). FL4: notification.maybe_donate_sched_context → schedcontext::donate
       + resume. Needs a J-level donate-to-running-thread lemma (cf. ScSignalDonJ's signal_waitDJ, IpcSignalDonFr's
       DWFr frame, ScDonate/ScDonateRef `maybe_donate_refines`).
  (d2) `IpcPushDon`: the head sender (call / fault with reply) has an SC and ct (receiver) has none: reply_push
       donates the sender's SC to ct (`pushDonJ` / XTopJointFaultDonM's donation, here with the RECEIVER being ct
       and the action chooseNewThread, so `test_reschedule` enqueues nothing: resumed `pd_eq` may apply).
  (d3) `IpcLinked` at MidN: as jRecvIpcLinkC (cancel the linked thread i; cancelOther_keep keeps ct's TCB, action,
       ready queues, so MidN holds after), but jRecvIpcUN at σ' needs ¬IpcActDon σ' / ¬IpcPushDon σ' p rc: transfer
       from σ through cancelIpc of i (notifications and SC scTcb untouched; endpoint p's queue changes only by
       removing i, a receiver), or carry the two donation predicates as "at the state after the cancel".
- Builds (tokyo, b.sh): sch23b-b1 `XTopJointMidN XTopJointFaultN` OK (5624 jobs; cache warmed from FL4-audit by
  cp -cR), sch23b-b2 `XTopJointRecvSigN` OK, sch23b-b3 `XTopJointRecvIpcN` OK (5626), sch23b-b4
  `XTopJointKEntry23M` OK (5630 jobs), all on 331a39e0, first try, no sorry. Axioms (axsch23b.sh, untracked): propext, Classical.choice, Quot.sound only for kernel_entryJ23M, KDispHyps23M.to22M, jMidLeavesHyp_of14,
  JRecvLeavesRN14.toRN13, canBlockCurMN, faultHypJZN/faultRecvJN/sendFaultPJN/sendFaultIJN/faultBlockJN/noFaultJN/stsCurJN,
  jRecvSigHypN_of, recvSigActiveJN, recvSigBlockJN, receive_signal_active_eqN, specRecvTail_noSc, NoDon.wordsR, jRecvIpcUN,
  recvIpcActJN, complete_signal_eqN, completeSignal_noSc, kernel_entryJ22M (midN_of: none). No sorry/admit/native_decide/bv_decide.
## mr9 (branch par/mr9 in FL4-tcbj, on 001e5ffd = int/j2 incl. mr8)
New leaves XTopJointKEntry22P (hand-written), XTopJointKEntry23P (generated: scratch/mr9/gen23.py + head23/tail23.lean
from XTopJointEntry/XTopJointDispatch/KEntry13P/14P/17P/18P/20P/22P), imported from Fl4Proofs.lean. Nothing existing
edited (XTopJointEntry untouched); sch23/sch23b's modules only imported.
- GOAL 1 DONE (XTopJointKEntry22P, 3f5b5c8a): the budget premise of the P line was the OLD `KBudget` (mr8 finding:
  `KBudget.tmo` FALSE in reachable states). `kernel_entryJ13PB` = kernel_entryJ13P with `hB : … → KBudgetB …`; its
  `hBud` is budtr's `JAtZ.budgetOkB` verbatim (its post is exactly J13P's `hBud` post; it has no PPPlat/IrqPlat
  inside, and MR is carried beside it by the existing `WP.spec_and … (budget_ok_mr …)` and `budget_mr_at`), with
  `NativeScope` at the entry from the existing [S] `hNSR … J0.toR`. So the "MachPlat copy of budgetOkB" is
  budgetOkB itself: no KBudget field is re-derived and no `KBudget.toB` appears at the top (toB only shows the new
  premise is weaker). `KDispHypsKV21.to13P` (the J14P…J21P wrapper conversions composed: to20, to12, to7, toK with
  jPreDecHyp_of18/of17, to6, BudgetAt.vmt, KDispHypsK.to with jPreDecHyp_of14, to13P). NEW TOP `kernel_entryJ22P`
  = J21P with `KBudgetB`; `j22P_platform` (= j21P_platform).
- GOAL 2 DONE (XTopJointKEntry23P, 93bfd0ab): `JUtPathM` = JUtPath without `ret` (`JUtRetHypR2` [W], VT-x types);
  `JPathM` = JPath with JUtPathM for RAM Untyped (every other case textually JPath's); `JPathAtM`; `JUtPath.toM`,
  `JPathM.of`, `JPathAt.toM` (the new path premise is strictly weaker). `JPreDecHypKM`/`JPreDecHypM`/`JVtxHypMU`
  (= JPreDecHypK/JPreDecHyp/JVtxHypM with JPathM). J13P's dispatch layer re-elaborated at JPathM (decOK_JMU,
  handle_invocation_entryJMU, invoke_afterJMU, dispatch_invokeJMU, mid_invRecvJMU, dispatch_midJMU,
  dispatch_invokeJAllMU, KDispHyps13PU, dispatch_all13PU; bodies unchanged: the Untyped case only forwards the path
  fact to the pre-decode premise), `kernel_entryJ13PU` (= J13PB), `jPreDecHyp_of14U/17U/18U/20U` (bodies unchanged:
  of14 reads fan/bufObj/heapH/core0/rcb/vsReach, never ret). `KDispHypsKV23` (= KDispHypsKV21 with JPathAtM and
  JVtxHypMU), `.to13PU`, `KDispHypsKV21.to23` (given JVtxHypMU), NEW TOP `kernel_entryJ23P`, `j23P_platform`.
  Note: `JVtxHypMU` [S] is asked with the weaker path fact (JPathM), so it is not implied by JVtxHypM; it is the
  same VT-x scope (the dropped `ret` was itself only about VT-x retypes 14..18).
- PREMISES of `kernel_entryJ23P` (every hypothesis; bundles with their fields' tags as at their definitions):
  * `[PlainStore st]` (instance: plain store model, P1).
  * `J : JAtZ … s a σ` [J] (joint invariant at the entry: l4v invs + state_relation, JointAt.lean).
  * `hni : Entered σ` [J] (ct_running, resume_cur_thread).
  * `hR : MR a σ.machineState` [J] (shared machine_state), `hVI : ValidIrqMasks σ` [J] (valid_irq_masks).
  * `hn : NativeSys n c` (the statement's own syscall-number relation).
  * `hflag` [S] (l4h trap mode: TRAP_SYSCALLS clear after the FAULT_IP write).
  * `hB : ∀ x, kheap ct = tcb x → KBudgetB arI a (faultIPSt …)` (CHANGED from KBudget): `now` NowAgree [P] (FL4's
    clock read agrees with the spec's getCurrentTime at that state; MachPlat.nowAgree from MR + VMT), `cur` CurInv
    [J] (l4v ct bound to cur_sc, not IPC-blocked, cur_sc active, ct_not_in_release_q), `off` OffReady [J] (l4v
    cur_sc_offset_ready), `tmo : NoTmoSend σ0 ∨ ∀ d p, ct ∉ readyQueues d p` [J] (l4v ct_not_in_q under
    resume_cur_thread; true in reachable states, budtr).
  * `hK : ∀ σb, BudgetAt σ σb true → ∀ Z' H' Cs' Ac' Lst' D' s' a', JAtZ … σb → KDispHypsKV23 …` (asked only at the
    budget outcome): `inv`: `JEntryGlobM` (ari [P], tot [P], delParts [J]/[P] (archRef [P], arKeep [P], vt [J], thr),
    nd [P], ppA [P], dom [P], portIn [P] (∀σ PortInVal), sigRest [J], timeAg [P], maxTU/tu [P]); `JEntryAt` (ni,
    ctnq, sg, rd0, flags, epQ, handlers, ports, vfh, cnf, vsTyp, live, fnz, urz, utks [J]; stall, ioapics, archIrq
    [P]); `JPathAtM` (CHANGED: per cap kind JPathM, fields tagged as XTopJointEntry's table: [P] config constants /
    one core, [J] invariant facts, [S] JVtxScope for VT-x decodes; NO [W] field any more: `JUtPath.ret` gone);
    `JVtxHypMU` [S] (VT-x Untyped retype 14..18, no l4v counterpart). `recv`: ct_not_in_q, valid_fault_handler [J].
    `mid`: JEntryGlobM, JEntryAt, JPathAtM as above, `MidRun.JMidPerfHypQ` [W], `JMidVfhHyp` [J],
    `JMidLeavesHyp13` [W] (sch22; sch23/sch23b's line), `JVtxHypMU` [S].
  * `hFin : ∀ x ∈ (specFront c σ).1, ∀ …, JAtZR … x.2 → KFinAtR …` (asked only at the front end's outcomes): hd
    (domainTime ≠ 0 ∨ NdOK) [J], vt [J], arch/archNd (ArchSwF/ArchNdF) [P], fo FpuOwnOK [J], sni/send
    (SniHyp/SendHyp) [P], tail (schedule's CR3 tail) [P].
  * `hARI : ARIface` [P], `hA : P0.ArchTotal` [P], `hnd : numDomains = 1` [P], `hM : MachPlat arI MR` [P],
    `hKD : MRKeepD arI MR` [P], `hPA : PPPlatA` [P], `hIA : IrqPlatA` [P], `hmrt` (MAX_RELEASE_TIME) [P], `hmb`
    (MIN_BUDGET) [P], `hT : TimeAgree` [P], `hmax : maxTicksToUs = U64.MAX` [P], `htu` (ticks_to_us) [P].
  * `hNS : ∀ s a σ, JHoleAt … → NativeScope σ` [S], `hNSR : ∀ …, JAtZR … → NativeScope σ` [S] (VT-x RunningVM out of
    the native scope).
- Check: no premise of kernel_entryJ23P is known false in reachable states (KBudget.tmo, the last one, is gone;
  KBudgetB.tmo is ct_not_in_q). ∀-over-states hypotheses that the operation cannot establish itself: the [P]
  `JEntryGlobM.portIn` (PortInVal, ∀σ: a platform/config fact about port I/O, as before) and the [S] scope premises
  `hNS`/`hNSR` (∀ states satisfying JHoleAt/JAtZR: native scope, no VT-x RunningVM) and `hflag` (∀ ct v, l4h trap
  mode); `hK`/`hFin` are path-restricted (only at the budget/front-end outcome states). The remaining [W] are
  `JMidPerfHypQ` and `JMidLeavesHyp13` (mid receive path, the sch23 lines).
- Builds (tokyo, scratch/mr9/b.sh, warm mirror): mr9-b1 (docstring before `set_option … in`; b.sh grepped mr8's log),
  mr9-b2 XTopJointKEntry22P OK (5684 jobs), mr9-b3 XTopJointKEntry23P OK (5686 jobs), first try; mr9-b4 both OK after a docstring fix. Root
  Fl4Proofs.lean not rebuilt (two leaf imports). Axioms (scratch/mr9/chk9.lean, chk23.lean, untracked): propext,
  Classical.choice, Quot.sound only for kernel_entryJ23P, kernel_entryJ22P, kernel_entryJ13PU, kernel_entryJ13PB,
  KDispHypsKV23.to13PU, KDispHypsKV21.to23, KDispHypsKV21.to13P, JPathAt.toM, JPathM.of, JUtPath.toM,
  dispatch_all13PU, decOK_JMU, jPreDecHyp_of14U/17U/18U/20U, j22P_platform, j23P_platform, JAtZ.budgetOkB. No
  sorry/admit/native_decide/bv_decide.
## mr10 (branch par/mr10 in FL4-tcbj, on 4f1495ba = int/j2 incl. mr9, sch23b)
New leaves XTopJointPortInM, XTopJointKEntry25P (imported from Fl4Proofs.lean; hand-written). Nothing existing
edited (XTopJointMachRel, XTopPortIn, KEntry23P/23M untouched); sch23/sch24's modules not touched.
- GOAL 1 = FINDING (formal: XTopJointPortInM's `MachPortIn` + `MachPortIn.frameAll`), `JEntryGlobM.portIn`
  (`PortInVal`, ∀σ) KEPT. The per-state form `MachPortIn arI MR` (MR a σ.ms → port_in a p z = ok (v, a') → ∃ ms,
  memory kept ∧ the spec's `In` at σ returns [v] with machine state ms ∧ MR a' ms: MachPlat.irqPending/take's
  shape) is NOT weaker in substance: (i) the spec's read is `machineOpLift (inNImpl port); gets inNVal`
  (Fl4Spec/Machine.lean:868-889), `inNImpl` an opaque nondeterministic op on `machineStateRest`, `inNVal` an opaque
  function of the whole machine state; (ii) `MachPlat.frame` (MR reads only irqMasks/irqState/timeState/
  lastMachineTime) is required by the P line: `MachPlat.mfKeep` carries MR over every spec step keeping those four
  fields, including every `machineOpLift` (MachFieldFam `mkf_machineOpLift`: invalidateASID, writeCR3, FPU ops,
  out8, …, whose opaque rest outcomes FL4 does not see). Hence `MachPortIn.frameAll`: under MachPlat, MachPortIn at
  one related ms gives PortInVal's conclusion at EVERY σ agreeing with ms on the four fields (any rest, device
  state, memory, FPU flag, kernel state): the same ∀-over-states content, restricted only in fields the read does
  not depend on. Neither form is provably satisfiable (inNVal opaque; `modelArch.port_in` returns 0), so a J24P
  with MachPortIn would trade one unprovable [P] for an equivalent one; not stated. What would remove it: a second
  machine relation seeing `machineStateRest` (l4v: the whole machine_state is shared), carried from the entry [J]
  WITHOUT frame, with every spec machineOpLift matched by an FL4 arch op reproducing its opaque outcome (an arch-
  backend obligation per machine op; the mfKeep/frame uses, 9 `.frame` sites + the MF family, would need it).
- GOAL 2 DONE (XTopJointKEntry25P): `KDispHypsKV25` (= KDispHypsKV23 with sch23b's `JMidLeavesHyp14` in `mid`),
  `.to23` (`jMidLeavesHyp_of14 hA hmax htu`), NEW TOP `kernel_entryJ25P` (wrapper over J23P), `j25P_platform`
  (= j23P_platform). (J24P left unused: it was reserved for GOAL 1.)
- Premise change at the top (kernel_entryJ25P vs J23P): `JMidLeavesHyp13` [W] NARROWED to `JMidLeavesHyp14` [W]
  (sch23b: JMidLeavesHyp13 concluding JRecvLeavesRN14, whose leaves carry one more premise each: cap fault `CtSc σ`;
  receive_signal `CtSc σ ∨ SigDon σ p`; receive_ipc `CtSc σ ∨ IpcLinked s rc ∨ IpcActDon σ ∨ IpcPushDon σ p rc`;
  l4v receive_ipc_corres / receive_signal_corres / handle_fault_corres in handle_recv_corres). Nothing added.
- PREMISES of `kernel_entryJ25P` (every hypothesis; bundles with their fields' tags as at their definitions):
  * `[PlainStore st]` (instance: plain store model, P1).
  * `J : JAtZ … s a σ` [J] (joint invariant at the entry: l4v invs + state_relation, JointAt.lean).
  * `hni : Entered σ` [J] (ct_running, resume_cur_thread).
  * `hR : MR a σ.machineState` [J] (shared machine_state), `hVI : ValidIrqMasks σ` [J] (valid_irq_masks).
  * `hn : NativeSys n c` (the statement's own syscall-number relation).
  * `hflag` [S] (l4h trap mode: TRAP_SYSCALLS clear after the FAULT_IP write).
  * `hB : ∀ x, kheap ct = tcb x → KBudgetB arI a (faultIPSt …)`: `now` NowAgree [P] (per state; MachPlat.nowAgree
    from MR + VMT), `cur` CurInv [J], `off` OffReady [J], `tmo : NoTmoSend σ0 ∨ ct ∉ readyQueues` [J] (ct_not_in_q).
  * `hK : ∀ σb, BudgetAt σ σb true → ∀ Z' H' Cs' Ac' Lst' D' s' a', JAtZ … σb → KDispHypsKV25 …` (asked only at
    the budget outcome): `inv`: `JEntryGlobM` (ari [P], tot [P], delParts [J]/[P] (archRef [P], arKeep [P], vt [J],
    thr), nd [P], ppA [P], dom [P], portIn [P] (∀σ PortInVal: kept, GOAL 1 FINDING), sigRest [J], timeAg [P],
    maxTU/tu [P]); `JEntryAt` (ni, ctnq, sg, rd0, flags, epQ, handlers, ports, vfh, cnf, vsTyp, live, fnz, urz,
    utks [J]; stall, ioapics, archIrq [P]); `JPathAtM` (per cap kind JPathM: [P] config constants / one core, [J]
    invariant facts, [S] JVtxScope for VT-x decodes; no [W]); `JVtxHypMU` [S] (VT-x Untyped retype 14..18).
    `recv`: ct_not_in_q, valid_fault_handler [J]. `mid`: JEntryGlobM, JEntryAt, JPathAtM as above,
    `MidRun.JMidPerfHypQ` [W], `JMidVfhHyp` [J], `JMidLeavesHyp14` [W] (CHANGED, sch23b), `JVtxHypMU` [S].
  * `hFin : ∀ x ∈ (specFront c σ).1, ∀ …, JAtZR … x.2 → KFinAtR …` (only at the front end's outcomes): hd
    (domainTime ≠ 0 ∨ NdOK) [J], vt [J], arch/archNd (ArchSwF/ArchNdF) [P], fo FpuOwnOK [J], sni/send
    (SniHyp/SendHyp) [P], tail (schedule's CR3 tail) [P].
  * `hARI : ARIface` [P], `hA : P0.ArchTotal` [P], `hnd : numDomains = 1` [P], `hM : MachPlat arI MR` [P],
    `hKD : MRKeepD arI MR` [P], `hPA : PPPlatA` [P], `hIA : IrqPlatA` [P], `hmrt` (MAX_RELEASE_TIME) [P], `hmb`
    (MIN_BUDGET) [P], `hT : TimeAgree` [P], `hmax : maxTicksToUs = U64.MAX` [P], `htu` (ticks_to_us) [P].
  * `hNS : ∀ s a σ, JHoleAt … → NativeScope σ` [S], `hNSR : ∀ …, JAtZR … → NativeScope σ` [S].
- Check: no premise known false in reachable states. ∀-over-states hypotheses the operation cannot establish:
  `JEntryGlobM.portIn` [P] (see FINDING), the [S] `hNS`/`hNSR`/`hflag`. Remaining [W]: `JMidPerfHypQ`,
  `JMidLeavesHyp14` (sch23 lines).

- Builds (mr10-b1, tokyo): XTopJointPortInM OK (5530 jobs), XTopJointKEntry25P OK (5698 jobs). #print axioms: kernel_entryJ25P, KDispHypsKV25.to23, j25P_platform, MachPortIn.frameAll — propext, Classical.choice, Quot.sound only.
## sch24 (branch par/sched24 in FL4-rb, on f3492a34 = int/j2 incl. sch23b, mr8)
New leaves XTopJointRecvIpcLinkN, XTopJointKEntry24M (imported from Fl4Proofs.lean; hand-written, no generator).
Nothing existing edited; JAtZ, ScPPR/SpecPPR*/CnDel/WJL*/Tcb*/UtReset*/PP*/Preempt*/ScCharge*/ScTmoCt*/Entry/Irq*/MR*/
MidChoose*/XTopJointRecv* untouched.
- (d3) IpcLinked at MidN DONE (XTopJointRecvIpcLinkN):
  * `jRecvIpcLinkN`: as sch22's `jRecvIpcLinkC` (`JAtZ.cancelLinkJ` of the linked thread i, `receiveIpc_linked`), MidN
    after by `cancelOther_keep` (ct's TCB, action, idle), then `jRecvIpcUN` at the state after. Its ¬IpcActDon σ' /
    ¬IpcPushDon σ' are carried back from σ (`CancelLinkAt` bundles the cancel facts):
  * `cancelLink_ntfn` (every notification after was the same before) and `cancelLink_sendEP` (a send queue
    `sendEP (sd :: l)` after was the same before). i blocked on a reply: the spec cancel is `reply_remove_tcb`, which
    keeps every notification and endpoint: `neV p` (the ntfn/ep object at p) is a projection frame `FK`
    (`ne_replyRemoveTcb` from `ne_setObject` + `ne_getSimpleKo` + VsDom's `dk_step0`; `cancelReply_ne`). i receiving:
    IpcSignalBoundSpec's `cancelIpc_recv_cfr` with `r := i` (a TCB, so no notification changes: `cfr_ntfn`); the
    endpoint i waits on loses i; FINDING: `CFr` does not fix the kind of the dequeued endpoint, so the send-queue
    case uses FL4's queue codes (`JAtZ.epQ_code`: a send-queue member has tsCode 4, a receive-queue member 3, from
    `EpObjRel`'s `QueuedOn` + `TcbRelE.st`, l4v valid_ep): i (code 3) is in no send queue, and the head of a send
    queue after the cancel would have been a receiver before (kept by cancelOther_keep, code 3 ≠ 4) or i (inactive).
  * `cancelLink_actDon`: ct's TCB by `cancelOther_keep` + `IK` backward, the notification by cancelLink_ntfn, the
    SC's scTcb by `IK` (`ScIK`); `cancelLink_pushDon`: the head sender is not i (code 4 vs i's 5/3), so its TCB is kept.
- Top: XTopJointKEntry24M: `JRecvLeavesRN15` (= RN14 with receive_ipc's premise `CtSc σ ∨ IpcActDon σ ∨
  IpcPushDon σ p rc`), `.toRN14` (the IpcLinked case by `jRecvIpcLinkN`), `JMidLeavesHyp15` [W],
  `jMidLeavesHyp_of15`, `KDispHyps24M.to23M`, NEW TOP `kernel_entryJ24M`.
- Premise change at the top (kernel_entryJ24M vs J23M): `JMidLeavesHyp14` [W] NARROWED to `JMidLeavesHyp15` [W]:
  receive_ipc's disjunct `IpcLinked s rc` is gone (now `CtSc σ ∨ IpcActDon σ ∨ IpcPushDon σ p.bv rc`); signal and
  fault as JMidLeavesHyp14. Same l4v counterpart (receive_ipc_corres / receive_signal_corres / handle_fault_corres
  in handle_recv_corres); a case of JMidLeavesHyp14. Nothing added.
- NOT DONE (handoff), what JMidLeavesHyp15 still contains besides CtSc (= sch23b (d1), (d2)):
  (d1) `SigDon` / `IpcActDon`: maybeDonateSc to the RUNNING ct (schedContextDonate + schedContextResume: ct may be
       postponed into the release queue, then the sporadic refill_unblock_check on the SC ≠ curSc). Needs the J-level
       donate-to-running-thread lemma (models: ScSignalDonJ's signal_waitDJ, IpcSignalDonFr's DWFr, ScDonate /
       ScDonateRef `maybe_donate_refines`). Not started.
  (d2) `IpcPushDon`: reply_push donating the head sender's SC to ct (receiver) under chooseNewThread (pushDonJ /
       XTopJointFaultDonM's pd_eq). Not started.
  Then a JRecvLeavesRN16 whose receive premise asks only CtSc, and kernel_entryJ25M via .to24M (CtSc is what sch23's
  jMidChooseFact removes).
- Builds (tokyo, b.sh; cache warmed from FL4-audit by cp -cR, sch24-w1): sch24-b1 `XTopJointRecvIpcLinkN` failed
  (3 small errors: getSimpleKo leaf, anonymous-constructor nesting, an exists goal), fixed; sch24-b3
  `XTopJointRecvIpcLinkN XTopJointKEntry24M` OK (5634 jobs) on f3492a34, no sorry. Axioms (axsch24.sh, untracked;
  sch24-ax1): propext, Classical.choice, Quot.sound only for kernel_entryJ24M, KDispHyps24M.to23M, jMidLeavesHyp_of15,
  JRecvLeavesRN15.toRN14, jRecvIpcLinkN, cancelLink_actDon/pushDon/sendEP/ntfn, JAtZ.epQ_code, cancelReply_ne,
  ne_replyRemoveTcb, ne_setObject, neO_of_aType (neO_some: propext; cfr_ntfn: none).
## sch23 (branch par/sched23 in FL4-sc, on 331a39e0 = int/j2 incl. sch22)
Goal (c1) only: `jMidChooseFact`, every outcome of the first phase satisfies `CtOK := CurInv ∨ ct SC-less`.
New leaves XTopJointChooseF and XTopJointChooseB (both imported from Fl4Proofs.lean). Generator: sch23gen/{genA.py, hdrA.lean, tailA.lean, setmrs.lean, mkA.sh, fixB*.py}
(untracked; `bash sch23gen/mkA.sh` regenerates XTopJointChooseF from MidRunQ). Nothing existing edited.
- DESIGN (no new premise except one [W] restricted to PerfW paths):
  * View `sV σ := (curSc, idleSc, releaseQueue, mV σ)`, `mV σ p := (TCB SC field at p, (scTcb, scRefillMax) of the SC
    at p)`; `SV m := FK sV m`. FINDING: every SC write in the FirstInv cone except the SC/TCB binding writes goes
    through `updateSchedContext` with a refill / reply-stack / consumed update (keeps scTcb and refill max, hence
    scActive), every TCB write keeps the SC field, so the whole cone is an SV frame except `schedContextDonate`
    (sendIpc's donation to a passive receiver, replyPush, replyRemove, maybeDonateSc) and the release-queue writes
    (`tcbReleaseRemove` in the donation, `tcbReleaseEnqueue` in `postpone` / `schedContextResume`). setObject trap: a
    CNode with an ill-formed table and an SC with an invalid size share `aGarbage`, so the generic setObject leaf
    excludes CNodes and `setCap` is proved from the object it reads.
  * `BIV ct c i rq M` (XTopJointChooseB): ct holds a TCB; its SC field is none, or `c` which is an SC, active unless
    `c = i`, with ct ∉ rq; `back` (every TCB's SC is an SC bound back to it, Inv.back); no reference both TCB and SC.
    `BI ct σ := BIV ct` of `sV σ`, kept by every SV frame (`BI.of_sV`). From CurInv + Inv.back at the dispatch state
    (`bi_of`); CQ ∧ BI give CtOK (`ctOK_of`).
  * Hand lemmas: `biv_donate`/`bi_donate` (donation of sc to t ≠ ct: the old holder's SC field is cleared, so ct
    either keeps curSc or becomes SC-less; back kept), `pcp_postpone`/`pcp_resume` (the enqueued thread is sc's
    scTcb = the TCB holding sc ≠ ct, by back), `pc_maybeDonateSc`, `pc_replyRemove`, `pc_replyPush`,
    `pc_sendIpc(_recv)`, `pc_sendFaultIpc`, `pc_handleTimeout`, `pc_drt_tail`, `pc_doReplyTransfer`, `pc_sendSignal`
    (PQ-style `PCP ct P m`: from CQ ∧ BI (∧ P) every outcome is CQ ∧ BI); `perf_firstB`, `midRunB_shell`,
    `jMidChooseFact (rep don cptr σ) (hs : CQ ct σ) (hq : NQ ct σ) (hC : CurInv σ) (hI : Sched.Inv σ)
    (hW : JMidPerfHypQ don cptr σ) (hWB : JMidPerfHypB don cptr σ) : ∀ y ∈ first phase, CtOK y.2`.
  * NEW premise (residue) `JMidPerfHypB don cptr σ` [W] := ∀ inv σ1, MidPerfAt cptr σ inv σ1 → PerfW inv →
    BI σ.curThread σ1 → ∀ y ∈ perform inv from σ1, BI σ.curThread y.2 (Untyped, IRQ handler set/clear, ASID control
    only, only at the states where they start on a run from the dispatch state; l4v invoke_untyped /
    invoke_irq_handler / perform_asid_control_invocation keep sym_refs of the SC/TCB binding, cur_sc_tcb_are_bound,
    cur_sc_active, ct_not_in_release_q). Same shape as JMidPerfHypQ.
- DONE: `jMidChooseFact` (XTopJointChooseB) proved, standalone (not wired into a top; the lead combines it with
  sch23b's SC-less leaves (c2): ¬CurInv at a mid state then means ct SC-less). Its premises: `CQ ct σ`, `NQ ct σ`
  (as XTopJointMidRunQ), `CurInv σ` (JAtZ.cur at the dispatch state), `Sched.Inv σ`, `JMidPerfHypQ` [W] (existing)
  and the NEW `JMidPerfHypB` [W] above. FINDING (Lean): a `by` block nested in `exact` inside `first` LOGS its unsolved
  goals instead of failing, so `first | exact f (by tac) | …` never falls through; `pc_step` uses
  `refine …; case h2 => (tac; done)` to make the alternative fail.
- Builds (tokyo, b23.sh): sch23-b1..b4 XTopJointChooseF iterations (sv_leaf name clash with IpcSV -> sck_ prefix;
  setSimpleKo / setMrs / setCap leaves); sch23-b5 ChooseF OK (5cc00c40), ChooseB errors; sch23-b6/b7 lost (station
  unreachable); sch23-b8..b10 ChooseB fixes (subst direction, `to` keyword, join points of sendIpc's receive branch /
  replyRemove / updateWaitingNtfn, post_liftE needs `Q :=`); sch23-b11 `XTopJointChooseB` OK (5392 jobs), no sorry.
  Axioms (axsch23.sh, untracked; sch23-ax1): jMidChooseFact, midRunB_shell, perf_firstB, bi_donate, pc_sendSignal,
  pc_doReplyTransfer, pc_sendIpc, kernel_entryJ22M (newest top, unchanged): propext, Classical.choice, Quot.sound.
## sch25 (branch par/sched25 in FL4-rb, on 04f4ee64 = int/j2 incl. sch24, mr10)
New leaves XTopJointRecvSigDonD, XTopJointKEntry25MD (imported from Fl4Proofs.lean; hand-written, no generator).
Nothing existing edited; JAtZ, ScPPR/SpecPPR*/CnDel/WJL*/Tcb*/UtReset*/PP*/Preempt*/ScCharge*/ScTmoCt*/Entry/Irq*/MR*/
MidChoose*/XTopJointRecv* untouched.
- (d1) signal half DONE (`SigDon`): XTopJointRecvSigDonD. FINDING: the wake machinery of ScSignalDonJ is generic in
  the donee, so no new frame was needed; ct (running, any runnable state, in no queue at MidN) is the donee:
  * `recvCheck_eq` / `recvCheck_of`: FL4's check after the donation in `receive_signal` (`rustRecvTail`'s tail:
    compare with cur_sc, then `sc_sporadic`) equals `notification.unblock_sporadic` (two pure reads swapped).
  * `P1.notification.recv_donate_tail.foot`: set_state(IDLE) + `rustRecvTail` write inside `KW` (EH H) under
    `DonCore` (P1's `maybe_donate_sched_context.tinvF`, `unblock_sporadic.kw`; prefix as P1 `receive_signal.ipc`),
    so core 0's debug word is kept (`wake_postD`'s `hfoot`).
  * `Sched.recv_tailDN`: `wake_tailD` without `possible_switch_to`: `donate_dfr`, `Inv.donate`, `unblock_frameS`,
    `Inv.unblockTail`: Inv, BlockedScActive, `DWFr n t`, ActIdle, action kept, CurRunM.
  * `Ipc.recvTail_irelD`: `donate_irelF` + `unblock_irel` / `unblock_sporadic_kfoot` (FinStep, IFrame).
  * `JAtZ.recvSigDonJN`: EVERY active-notification receive at MidN (donating or not; no SigDon premise): badge write
    by `regWrJ` (J1), then `J1.wake_postD` with `(DWFr.ofNFr F1.weak).trans FF` (F1: the idle write, NFr true);
    BlkOK from P1 `receive_signal.ipc` on the whole call; hRR vacuous (ct runnable), ct not dead.
  * `jRecvSigHypDN`: every `receive_signal` at MidN (= jRecvSigHypN_of without ¬SigDon).
- Top: XTopJointKEntry25MD: `JRecvLeavesRN16` (= RN15 with receive_signal's premise `CtSc σ` only), `.toRN15`
  (jRecvSigHypDN via midN_of), `JMidLeavesHyp16` [W], `jMidLeavesHyp_of16`, `KDispHyps25M.to24M` (takes hmb), NEW TOP
  `kernel_entryJ25M` (same premises as J24M with KDispHyps25M).
- Premise change at the top (kernel_entryJ25M vs J24M): `JMidLeavesHyp15` [W] NARROWED to `JMidLeavesHyp16` [W]:
  receive_signal's disjunct `SigDon σ p.bv` is gone (now `CtSc σ`); receive_ipc (`CtSc σ ∨ IpcActDon σ ∨
  IpcPushDon σ p.bv rc`) and the cap fault (`CtSc σ`) as JMidLeavesHyp15. Same l4v counterpart (receive_signal_corres
  / receive_ipc_corres / handle_fault_corres in handle_recv_corres); a case of JMidLeavesHyp15. Nothing added.
- NOT DONE (handoff), what JMidLeavesHyp16 still contains besides CtSc:
  (d1') `IpcActDon` (receive_ipc, ct's bound notification active with an unbound SC; FL4 `complete_signal`, spec
       `completeSignal`). Plan (reuse everything above): `receive_ipc_preA` (XTopJointRecvIpcAct) takes ANY post of
       `complete_signal`, `receiveIpc_active` reduces the spec to `completeSignal n t σ`. Write
       `JAtZ.recvIpcActDJN` = recvSigDonJN with complete_signal (is_null t false: `ht0` as recvIpcActJN; `i != ACTIVE`
       false). The only new parts: the complete tail (`rustCompleteTail`'s check: sporadic, `i1 = ntfn.sc`, cur_sc,
       unblock_check; spec `specCompleteTail`'s maybeM) equals the recv check at the state after the donation, because
       there ct's SC is `none` (FL4 word 0, sc_sporadic(0) false on both sides) or the notification's SC (a
       `maybeDonateSc` shape lemma: t SC-less before ⇒ after, t's SC none, or some p with ntfn n's SC = some p and n's
       object unchanged; FL4 side from SchedRel/NtfnStateRel at the IRel after `donate_irelF`). Prove
       `completeCheck_eq` (FL4, under `mem s (scA t) = 0 ∨ mem s (scA t) = mem s (ntfnScA n)`) and
       `specCompleteCheck_eq` (spec, ScTails' `specCompleteCheck` = `specUnblock` under the shape), a P1 foot copy
       for the complete tail (or the same `recv_donate_tail.foot` after rewriting by completeCheck_eq). Then
       `jRecvIpcUDN`: jRecvIpcUN's first case (hca) without `hnd`/`hAD`.
  (d2) `IpcPushDon`: reply_push donating the head sender's SC to ct (receiver) under chooseNewThread. Not started.
       NOTE the direction: donor = the blocked sender sd, donee = running ct (XTopJointPushDon's pushDonJ is caller
       ct → blocked receiver); `schedcontext::donate` from sd (sd ≠ ct, not the action target at chooseNewThread:
       no reschedule), then ct owns sd's SC; no `resume` in reply_push. Model the spec frame on `DWFr` / `dnSt`.
  Then JRecvLeavesRN17 with receive_ipc asking only CtSc, kernel_entryJ26M via .to25M.
- Builds (tokyo, b.sh; cache warmed from FL4-audit by cp -cR, sch25-w1: XTopJointKEntry24M up to date, 5634 jobs):
  sch25-b1 `XTopJointRecvSigDonD` failed (2 errors: rw of `sc_ne_eq` under a binder, a `by` block swallowing a
  comma), fixed; sch25-b2 `XTopJointRecvSigDonD XTopJointKEntry25MD` OK (5638 jobs) on 04f4ee64, no sorry. Axioms
  (axsch25.sh, untracked; sch25-ax1): propext, Classical.choice, Quot.sound only for kernel_entryJ25M,
  KDispHyps25M.to24M, jMidLeavesHyp_of16, JRecvLeavesRN16.toRN15, jRecvSigHypDN, JAtZ.recvSigDonJN,
  Ipc.recvTail_irelD, Sched.recv_tailDN, recvCheck_eq, recvCheck_of, P1.notification.recv_donate_tail.foot.
## sch26 (branch par/sched26 in FL4-sc, on 9c0b6488 = int/j2 incl. sch23, sch24, mr10)
Goal: the two [W] premises on the first-phase PerfW performs (`JMidPerfHypQ` CQ kept, `JMidPerfHypB` BI kept).
New leaves XTopJointPerfU, XTopJointPerfW (imported from Fl4Proofs.lean). Nothing existing edited.
- FINDING: no spec frame alone can prove them. The spec's `retype_region` writes default objects at the addresses
  the invocation gives and `delete_objects` detypes the whole region, both without a freeness check (l4v keeps the
  region free by the invariants `valid_untyped` / `descendants_range_in` / `if_live_then_nonz_cap`). From a state
  where the region holds ct's TCB or an SC some TCB is bound to, CQ / BI break. So a region fact at the perform's
  start state is genuinely needed; everything else (reset loop incl. the preemption points, which write only the
  machine/extended state, curTime, consumedTime, domainTime: none in ctV/qV/sV; cap writes; createCap;
  initArchObjects / copyGlobalMappings; ASID table) is a ctV/qV/sV frame (MidRunK/MidRunQ/ChooseF leaves by
  `kf_auto2`/`qv_auto2`/`sck_auto2`).
- XTopJointPerfU: `PW I m` (invariant kept) + combinators, `IStable` (I determined by ctV, qV, sV), `pw_of`;
  hand steps `pw_deleteObjects` (I kept by `detype (rgn ptr bits)`), `pw_retypeRegionWith` (I kept by writing an
  object binding no SC, `TPN`, at an address of `rtPtrs`; `tpn_default`); `RegC ct D σ := ct ∉ D ∧ no TCB's SC
  field points into D`; `IB D := CQ ∧ BI ∧ RegC D`, `IQ D := CQ ∧ ct ∉ D` with `ib_/iq_detype` (R ⊆ D),
  `ib_/iq_upd` (p ∈ D) via `biv_frame` / `regc_frame`; `reset_post` (resetUntypedCap, region of the cap read at
  the start), `ut_post` (FL4's invokeUntypedWith fl4ObjBitsApi), `pw_asidControl`; `utD sl σ reset rb ty objSz n`
  (reset region of every cap at sl at σ if reset, ∪ rtPtrs), `asidD frame` (rgn frame page_bits ∪ {frame}).
- XTopJointPerfW: ADDED `JPerfRegHyp cptr σ` [J] := `∀ inv σ1, MidPerfAt cptr σ inv σ1 → PerfRegOK σ.curThread inv σ1`,
  `PerfRegOK`: Untyped `.retype srcSlot reset _ rb ty objSz slots _` ↦ `RegC ct (utD srcSlot σ1 reset rb ty objSz
  slots.length) σ1`; ASID control `.makePool frame ..` ↦ `RegC ct (asidD frame) σ1`; else True. l4v: invoke_untyped's
  `valid_untyped_inv` (retyped range free; a reset untyped is childless so by valid_untyped + if_live_then_nonz_cap
  no live object, not cur_thread, not a bound SC (sym_refs), lies in it), perform_asid_control_invocation's
  `valid_aci`. True in reachable states. NARROWED residue `JPerfIrqHypQ` / `JPerfIrqHypB` [W]: the old premises
  for the IRQ handler set/clear performs only. `midPerfAt_cq` (CQ ∧ NQ at σ1 from the dispatch state),
  `perfU_post`, `perfA_post`, `jMidPerfHypQ_of (hs : CQ ct σ) (hq : NQ ct σ) (hR : JPerfRegHyp) (hIq :
  JPerfIrqHypQ) : JMidPerfHypQ`, `jMidPerfHypB_of (hs) (hq) (hR) (hIb : JPerfIrqHypB) : JMidPerfHypB`.
- NOT DONE (handoff): (a) top wrapper: `jMidPerfHypQ_of` needs `CQ ∧ NQ` at the dispatch state, which
  `JAtZ.midCQ` gives from `Entered σb` + JEntryAt; the *M tops' `hK` gets σb with only `BudgetAt σ σb true` and
  JAtZ, and no exported lemma gives `Entered σb` from BudgetAt (KEntry.lean:439 derives it inline from the budget
  check's post). So a KDispHyps26M replacing `JMidPerfHypQ` by `JPerfRegHyp ∧ JPerfIrqHypQ` needs either that
  lemma or the wiring at dispatch_all*M (where `hni`/`J.midCQ` are in scope, as in dispatch_all9M). (b) IRQ
  handler family: route = `capDeleteOne irqSlot` with the cap null or a notification cap (needs the [J] fact "the
  IRQ slot holds null or a notification cap", l4v valid_irq_handlers/valid_irq_node; other caps reach
  fast_finalise's reply/endpoint branches, `NonDet.fail` for the rest); KF leaves exist (kf_emptySlot',
  kf_schedContextMaybeUnbindNtfn', kf_unbindMaybeNotification', kf_isFinalCap'), QK via SpecPPRQ's
  qk_cancelAllSignals/nq_ntfnBody pattern (ct ∉ the queue from MidRun.NQ at σ1 = midPerfAt_cq's NQ, kept by the
  two unbinds: they keep ntfnObj); SV: sck_tcbNtfnDequeue/sck_possibleSwitchTo/sck_rescheduleRequired/
  sck_setThreadState exist, SV of the unbinds and ifSporadicCurScAssertRefillUnblockCheck to check.
  (c) the [J] `JPerfRegHyp` from JAtZ: the J-side reset/retype proofs (UtResetTopJ `JAtZ.rgClear_drop`, UtDropJ2
  `RegionD`, `JUtPath`) show the region is clear of the sets incl. Z.T/Z.C at the kernel side; transporting that to
  the spec heap (ct ∈ Z.T, bound SCs ∈ Z.C, ObjCover) is the route.
- Builds (tokyo, b26.sh = b23.sh with the State-record lines filtered): sch26-b1/b2 (`first` layout; `bitsOf` is
  shadowed by Fl4Proofs.P3.bitsOf (CapRel) -> `Fl4Spec.bitsOf`; getCap state rewrite), sch26-b3
  `XTopJointPerfU XTopJointPerfW` OK (5396 jobs). Axioms (axsch26.sh, untracked; sch26-ax1): propext, Classical.choice, Quot.sound only for jMidPerfHypQ_of, jMidPerfHypB_of, perfU_post, perfA_post, midPerfAt_cq, ut_post, reset_post, pw_asidControl, ib_detype, ib_upd, pw_retypeRegionWith. No sorry/admit/native_decide/bv_decide.
## sch27 (branch par/sched27 in FL4-rb, on a67f50b6 = int/j2 incl. sch25, sch23)
New leaves XTopJointRecvIpcActDonD, XTopJointKEntry26MD (imported from Fl4Proofs.lean; hand-written, no generator).
Nothing existing edited; JAtZ, ScPPR/SpecPPR*/CnDel/WJL*/Tcb*/UtReset*/PP*/Preempt*/ScCharge*/ScTmoCt*/Entry/Irq*/MR*/
XTopJointRecv*/XTopJointPerf* untouched (KEntry26MD imports XTopJointMachRel for `doMachineOp_single`).
- (1) IpcActDon DONE (XTopJointRecvIpcActDonD), sch25's handoff plan:
  * spec: `Sched.donate_kh` (`maybeDonateSc t n` for an SC-less `t` in no queue keeps the heap or is `donSt` of the
    notification's SC; donate_dfr's case split), `donShape_of` / `DonShape` (after it ct's SC is none or the
    notification's), `donate_tcb`, `specCompleteCheck_eqU` (ScTails' `specCompleteCheck` = `specUnblock` under
    DonShape).
  * FL4: `completeCheck_eq` (complete_signal's check = receive_signal's check under `scA t = 0 ∨ scA t = nScA n`),
    `completeCheck_of_recv`, `completeCheck_of` (no shape: nothing, or what `unblock_sporadic` does);
    P1 `notification.complete_donate_tail.foot` (recv_donate_tail.foot for `rustCompleteTail`),
    P1 `notification.complete_signal.ipcC` (complete_signal.ipc from CanBlock); `Ipc.completeTail_irelD`
    (recvTail_irelD for rustCompleteTail; the FL4 shape from DonShape through SchedRel.tcb / NtfnRel1.sc).
  * `JAtZ.recvIpcActDJN`: every active-bound-notification receive_ipc at MidN, donating or not (recvSigDonJN
    with `receive_ipc_preA` + `receiveIpc_active` + the complete_signal prefix); `jRecvIpcUDN` (jRecvIpcUN
    without ¬IpcActDon); `jRecvIpcLinkDN` (sch24's jRecvIpcLinkN without ¬IpcActDon, via jRecvIpcUDN).
- (3) jMidChooseFact WIRED (XTopJointKEntry26MD): `BudgetAt.entered` (the dispatch state is Entered: faultIPSt
  changes one TCB, updateTimeStamp the clock fields, checkBudgetRestart `true` nothing), `not_ctSc_of`
  (CtOK ∧ ¬CurInv → ¬CtSc), `JRecvLeavesRN17` (receive_ipc only, premise `IpcPushDon σ p.bv rc`; no sig / flt
  fields), `.toRN16` (CtSc contradicts CtOK; IpcActDon or anything not IpcPushDon at MidN by jRecvIpcUDN /
  jRecvIpcLinkDN), `JMidLeavesHyp17` [W], `jMidLeavesHyp_of17` (from jMidChooseFact's conclusion),
  `KDispHyps26M` (mid adds `MidRun.JMidPerfHypB true cptr σ`), `.to25M` (jMidChooseFact's own premises all from
  the dispatch state: CQ ∧ NQ by `JAtZ.midCQ` (Entered + JEntryAt), CurInv by `JAtZ.cur` + Entered, Sched.Inv by
  `JAtZ.inv`, JMidPerfHypQ/B from KDispHyps26M.mid; nothing left unstated), NEW TOP `kernel_entryJ26M`.
- Premise change at the top (kernel_entryJ26M vs J25M): `JMidLeavesHyp16` [W] NARROWED to `JMidLeavesHyp17` [W]:
  the notification receive and the cap fault are GONE from the mid premise (their only premise was CtSc, which
  jMidChooseFact excludes at ¬CurInv), receive_ipc's `CtSc σ ∨ IpcActDon σ ∨ IpcPushDon σ p.bv rc` is now
  `IpcPushDon σ p.bv rc` only (chooseNewThread ∧ ¬CurInv still in the leaf). Same l4v counterpart
  (receive_ipc_corres inside handle_recv_corres); a case of JMidLeavesHyp16, true in reachable states.
  ADDED at the mid: sch23's `JMidPerfHypB` [W] (existing definition, XTopJointChooseB; PerfW performs keep BI on
  MidPerfAt paths; l4v invoke_untyped / invoke_irq_handler / perform_asid_control_invocation keep sym_refs of
  the SC/TCB binding, cur_sc_tcb_are_bound, cur_sc_active, ct_not_in_release_q). sch26 (FL4-sc) proves
  JMidPerfHypQ/B; once in, both go.
- NOT DONE (handoff), what JMidLeavesHyp17 still contains: (2) `IpcPushDon` — receive_ipc at MidN whose head
  sender sd (call, or fault with a reply, with grant / grant-reply and a reply cap) HAS an SC: reply_push(sd, ct,
  r, can_donate) donates sd's SC to ct (spec replyPush's guard `xt.sc ≠ none ∧ xd.sc = none ∧ b`, see
  XTopJointRecvSendP's `replyPush_don_irrel`). Needed: donating copies of XTopJointRecvSendP's
  `JAtZ.recvSendPJG` / `recvSendFPJG` (scripted, ~1000 lines each; the push stage currently goes through
  `receiveIpc_sendPush_eq` + `replyPush_don_irrel`), with the donation part from XTopJointPushDon's
  machinery in the reverse direction: donor = blocked sender sd (≠ ct, not the action target at
  chooseNewThread), donee = running SC-less ct (cf. `push_donate_refinesW`, `bdSt`/`pdSt`, `JAtZ.pushDonJ`;
  `pd_eq`'s `testReschedule_curN` does not apply since the donor is not ct: test_reschedule on sd's SC, sd not
  current; then ct owns sd's SC: CurInv-like facts for ct after). Then JRecvLeavesRN18 = {} and the mid premise
  disappears (kernel_entryJ27M with JMidPerfHypQ/B only).
- Builds (tokyo, b2.sh = b.sh with longer error context, untracked; cache warmed from FL4-audit by cp -cR, sch27-w2:
  KEntry25MD + ChooseB up to date, 5642 jobs): sch27-b1..b4 fixes (a `rfl` after a closing simp, the sporadic
  branch of specCompleteCheck_eqU, a `rw` into an unreduced match after spec_bind -> completeCheck_of_recv,
  ambiguous rTcbA, doMachineOp_single from XTopJointMachRel); sch27-b5 `XTopJointRecvIpcActDonD
  XTopJointKEntry26MD` OK (5648 jobs) on a67f50b6, no sorry. Axioms (axsch27.sh, untracked; sch27-b5): propext,
  Classical.choice, Quot.sound only for kernel_entryJ26M, KDispHyps26M.to25M, jMidLeavesHyp_of17,
  JRecvLeavesRN17.toRN16, BudgetAt.entered, JAtZ.recvIpcActDJN, jRecvIpcUDN, jRecvIpcLinkDN,
  Ipc.completeTail_irelD, Sched.donate_kh/donShape_of/specCompleteCheck_eqU/donate_tcb, completeCheck_eq/_of/_of_recv,
  P1.notification.complete_donate_tail.foot, P1.notification.complete_signal.ipcC (not_ctSc_of: none).
## sch28 (branch par/sched28 in FL4-sc, on effe1c53 = int/j2 incl. sch26, sch25)
Goal: sch26's handoff: (1) the IRQ handler set/clear family, (2) `JPerfRegHyp` [J] from the J side, (3) a top.
New leaves XTopJointPerfI, XTopJointPerfK (imported from Fl4Proofs.lean). Nothing existing edited.
- (1) DONE (XTopJointPerfI): `JPerfIrqHypQ` / `JPerfIrqHypB` [W] are no longer needed. ADDED
  `MidRun.JPerfIrqSlotHyp cptr σ` [J] := `∀ i σ1, MidPerfAt cptr σ (.invokeIRQHandler i) σ1 → IrqSlotNC σ1`,
  `IrqSlotNC σ := ∀ irq c σ', (c, σ') ∈ (getCap (σ.interruptIrqNode irq, []) σ).1 → c = .nullCap ∨ ∃ r b rs,
  c = .notificationCap r b rs` (l4v valid_irq_node + the IRQ handler slots' contents; FL4's `IrqSlotOK`, SpecGlob.irq
  at the dispatch state; the first phase writes no cap). True in reachable states; only at MidPerfAt states.
  Proof: `post_capDeleteOne` (null: nothing; notification: `fast_finalise` then `empty_slot _ nullCap`),
  `irqH_post` (getIrqSlot, cap_delete_one, cap_insert for set). BI: everything is an sV frame (`sck_ntfnFin` from
  `sck_schedContextMaybeUnbindNtfn` / `sck_unbindMaybeNotification` / `sck_cancelAllSignals` by sck_auto2,
  `sck_emptySlotN`, `sck_capInsert`). CQ: `pwq_of` (KF + QK + the notification view `nV`) for the two unbinds
  (`nv_*`: they keep every notification's `ntfnObj`: `nv_updSk_ntfn`, `nv_setObject_nn`, `nv_threadSet`,
  `nv_updateSchedContext`), so MidRun.NQ (ct waits on no notification, from `midPerfAt_cq`) holds at
  `cancel_all_signals`, whose restarted threads are therefore `≠ ct` (`cq_cancelAllSignals`,
  `pq_removeAndRestartNtfnQueuedThread`, `pq_mapMx_mem`). The preemption-point question does not arise here
  (no preemption point in invoke_irq_handler). Lemmas `jPerfIrqHypQ_of (hs : CQ ct σ) (hq : NQ ct σ) (hIs)`,
  `jPerfIrqHypB_of (hIs)`, and `jMidPerfHypQ_of2 / jMidPerfHypB_of2 (hs hq) (hR : JPerfRegHyp) (hIs :
  JPerfIrqSlotHyp)`: JMidPerfHypQ / JMidPerfHypB from the two [J] facts only.
- (3) DONE (XTopJointPerfK): `BudgetAt.entered (hnd) (hni : Entered σ) : BudgetAt σ σb true → Entered σb`
  (sch26's missing export: fl4SyscallFaultIP changes only ct's TCB, update_time_stamp the machine state / clock,
  a `true` check_budget_restart nothing: checkBudgetRestart_true). `KDispHyps25MP` = KDispHyps25M with mid's
  `JMidPerfHypQ` [W] REPLACED by `JPerfRegHyp ∧ JPerfIrqSlotHyp` [J]; `.to25M J hni` (JAtZ.midCQ for CQ ∧ NQ);
  NEW TOP `kernel_entryJ25MP` (= kernel_entryJ25M with KDispHyps25MP). JMidPerfHypB is in no top yet (only in
  sch23's jMidChooseFact): whoever wires jMidChooseFact (sch27) should pass `jMidPerfHypB_of2 hs hq hR hIs`.
- (2) NOT DONE: `JPerfRegHyp` [J] stays named. Finding: `JAtZ.rgClear_drop` / `RegionD` are not freeness facts:
  they describe the J state after the region's objects are DROPPED from the kept sets (a TCB in the region would
  be dropped too), so they do not show ct / bound SCs lie outside it. A proof needs a liveness argument at J:
  ct ∈ Z.T and every bound SC ∈ Z.C are live objects; a reset untyped has no children (decode's
  ensure_no_children at the spec, JUtPath at J) and the retype region is free (`descendants_range_in`), so by
  JCovD (every live object's memory is covered only by its ancestor untypeds' caps with the object as a
  descendant) no live object lies in it; then transport ct / the bound SCs from Z.T / Z.C to the spec heap
  (ObjCover, TopSR.cur_mem) and the region from the spec cap at MidPerfAt's σ1 (the first phase keeps caps) to the
  J cap. Also needs MidPerfAt related to a J run (it is spec-only), e.g. state JPerfRegHyp at J (the J
  decode's JUtPath / JAsidCPath posts) and carry it to σ1.
- Builds (tokyo, b26.sh): sch28-b1/b2 (heartbeat timeouts of auto-unfold nv leaves -> hand-written with
  explicit arguments; perform error type Unit; NonDet.when split), sch28-b3 `XTopJointPerfI XTopJointPerfK` OK
  (5652 jobs).
  Axioms (axsch28.sh, untracked; sch28-ax1): propext, Classical.choice, Quot.sound only for kernel_entryJ25MP,
  KDispHyps25MP.to25M, BudgetAt.entered, jPerfIrqHypQ_of, jPerfIrqHypB_of, jMidPerfHypQ_of2, jMidPerfHypB_of2,
  irqH_post, post_capDeleteOne, cq_cancelAllSignals, cq_ntfnFin, sck_ntfnFin, nv_schedContextMaybeUnbindNtfn,
  nv_unbindMaybeNotification. No sorry/admit/native_decide/bv_decide.
## sch29 (branch par/sched29 in FL4-rb, on f22e8409 = int/j2 incl. sch27, sch26)
Goal: sch27's handoff (2), the last receive case `IpcPushDon`, and the mid premise on the receive leaves gone.
New leaves XTopJointRecvSendPDD (scripted: sch29gen/gen.py, untracked), XTopJointRecvIpcPushDonD (scripted:
sch29gen/gen2.py, untracked), XTopJointKEntry27MD (hand-written), imported from Fl4Proofs.lean. Nothing existing
edited (JAtZ, XTopJointRecv*, XTopJointPerf*, PP*/Preempt*/ScPPR/SpecPPR*/UtReset*/Tcb*/WJL*/CnDel/Entry/Irq*/
ScCharge*/ScTmoCt* untouched).
- FINDING: the reverse-direction donation already existed: XTopJointRecvSendRD (passive server after
  `maybe_return_sc`) has `testReschedule_cnN` / `donate_cnN_eq` / `pd_eqN` (donor not current, a reschedule
  pending: `test_reschedule` is a no-op), `JAtZ.pushDonRJ` and the donating copies `JAtZ.recvSendFPDJ` /
  `JAtZ.recvSendPDJ` of recvSendFPJG / recvSendPJG (SC released at the block by `Inv.rd` / `Inv.scRef`). Their only
  extra premise is "the current SC is in Z.C and bound to no thread" (`hcsC`, `hcsx`, `hk0`, `hcsF`), which is FALSE
  at reachable MidN states (ReplyRecv: the reply returns the passive server's SC to the caller, who then owns the
  current SC while ct receives SC-less). So instead of new donating copies, sch29 removes that premise:
  * `JAtZ.pushDonRJW`: CurOwnW / OffOK after the donation from `JAtZ.own` / `JAtZ.off` in all cases: the donated SC
    is the current one (its new owner is the receiver d: `dn_kp`, d in no queue, refills unchanged); another current
    SC owned by u (u ≠ donor, whose SC is the donated one; u ≠ d, SC-less), untouched; the current SC unbound (as
    before). The current SC's object from `Inv.back` (owned) or `SchedSpec.scs` (unbound).
  * `JAtZ.recvSendFPDJW`, `JAtZ.recvSendPDJW`: recvSendFPDJ / recvSendPDJ with the four premises and their
    current-SC blocks removed, calling pushDonRJW.
  * `jRecvIpcUD` (gen2 from jRecvIpcN's `jRecvIpcUN` without ¬IpcPushDon): the pushing head sender WITH an SC
    (PushOK: call, or a fault that is not a timeout) by recvSendPDJW / recvSendFPDJW; its SC word nonzero, in Z.C by
    `SchedSpec.scMem`; ct SC-less, out of the release queue, chooseNewThread from MidN.
  * `jRecvIpcUDD`, `jRecvIpcLinkDD`: jRecvIpcUDN / jRecvIpcLinkDN without ¬IpcPushDon.
- Top (XTopJointKEntry27MD): `JRecvLeavesRN17.of_ok` (RN17 from CtOK alone = sch27's "JRecvLeavesRN18 = {}"),
  `jMidLeavesHyp17_of` (JMidLeavesHyp17 from jMidChooseFact's conclusion), `KDispHyps27M` (mid: entry facts,
  `JMidPerfHypQ` [W], `JMidPerfHypB` [W], `JMidVfhHyp` [J]; NO JMidLeavesHyp), `.to26M` (jMidChooseFact from the
  dispatch state as KDispHyps26M.to25M), NEW TOP `kernel_entryJ27M` (same premises as J26M with KDispHyps27M).
- Premise change at the top (kernel_entryJ27M vs J26M): `JMidLeavesHyp17` [W] REMOVED (proved). Nothing added.
  The mid bundle keeps `JMidPerfHypQ` / `JMidPerfHypB` [W] (sch26's jMidPerfHypQ_of / jMidPerfHypB_of on
  FL4-sc narrow them to JPerfRegHyp [J] + JPerfIrqHypQ/B [W]; wiring is sch28's) and `JMidVfhHyp` [J] (unchanged).
- Builds (tokyo, b2.sh; cache warmed from FL4-audit by cp -cR, sch29-w1: KEntry26MD up to date, 5648 jobs):
  sch29-b1 `XTopJointRecvSendPDD XTopJointRecvIpcPushDonD` OK (5640 jobs), sch29-b2 + `XTopJointKEntry27MD` OK
  (5654 jobs) on f22e8409, first try, no sorry. Axioms (axsch29.sh, untracked; sch29-b2): propext, Classical.choice,
  Quot.sound only for kernel_entryJ27M, KDispHyps27M.to26M, jMidLeavesHyp17_of, JRecvLeavesRN17.of_ok, jRecvIpcUD,
  jRecvIpcUDD, jRecvIpcLinkDD, JAtZ.pushDonRJW, JAtZ.recvSendFPDJW, JAtZ.recvSendPDJW.
## fin1 (branch par/fin1 in FL4-tcbj, on f9fa0192 = int/j2 incl. sch29, sch28, mr10)
Goal: one final top combining the M line (sch29's J27M, no receive premise), sch28's PerfW [J] facts and the
MachPlat line (mr10's J25P). New leaves XTopJointKEntry28M, XTopJointKEntry26P (hand-written wrappers, imported
from Fl4Proofs.lean). Nothing existing edited.
- (1) DONE (XTopJointKEntry28M): `KDispHyps28M` = KDispHyps27M with mid's `JMidPerfHypQ` [W] ∧ `JMidPerfHypB` [W]
  REPLACED by `MidRun.JPerfRegHyp ∧ MidRun.JPerfIrqSlotHyp` [J]; `.to27M J hni` (CQ ∧ NQ by `JAtZ.midCQ`, then
  `jMidPerfHypQ_of2` / `jMidPerfHypB_of2`); NEW TOP `kernel_entryJ28M` (wrapper over J27M, Entered σb by
  `BudgetAt.enteredP hnd hni`). CAVEAT: J28M's `hB` is still the M line's old `KBudget` (from kernel_entryJ9M);
  its `tmo` is FALSE in reachable states (mr8/budtr finding). Fixing it on the M line means copying J9M's body
  onto `JAtZ.budgetOkB` (as mr9's J13PB did for the P line); not done, since the P line below already has
  `KBudgetB` and subsumes the M line's mid results. So J28M is an intermediate, not the final top.
- (2) DONE (XTopJointKEntry26P): `KDispHypsKV26` = KDispHypsKV25 with mid's `JMidPerfHypQ` [W] and
  `JMidLeavesHyp14` [W] REMOVED and `JPerfRegHyp ∧ JPerfIrqSlotHyp` [J] ADDED. `.to25 hA hmax htu hmb J hni`:
  JMidPerfHypQ/B by `jMidPerfHypQ_of2`/`B_of2` (CQ ∧ NQ from JAtZ.midCQ); `CtOK` after the first phase by
  sch23's `MidRun.jMidChooseFact true true` (CurInv by JAtZ.cur + Entered, Sched.Inv by JAtZ.inv);
  `JMidLeavesHyp17` by sch29's `jMidLeavesHyp17_of`; then the existing chain `jMidLeavesHyp_of17` → `_of16` →
  `_of15` gives JMidLeavesHyp14. NEW TOP `kernel_entryJ26P` (wrapper over J25P, Entered σb by
  BudgetAt.enteredP); `j26P_platform` (= j25P_platform: MachPlat ∧ MRKeepD for modelArch/modelMR, interrupts
  raised).
- (3) NOT DONE, `JMidVfhHyp` [J] stays named. It is not derivable cheaply: ct's `tcbFaultHandler` after the
  first phase is written by the TCB invocations on ct itself (SetSpace / Configure / SetTimeoutEndpoint, guarded
  by decode's `checkHandlerEp`), and every other cap write of the first phase (cte_insert of a derived cap,
  IRQ control's handler cap, arch cap updates) misses the TCB's handler field only by `valid_cap` of the looked-up
  slot (KEntry9M docstring): a frame over every perform plus decode's check, i.e. the l4v `hinv_invs` part for
  `valid_tcb`'s `valid_fault_handler`. Path-restricted (only the `.ok` outcomes of the first phase from the
  dispatch state), true in reachable states (l4v invariant).
- PREMISES of `kernel_entryJ26P` (every hypothesis; bundles with their fields' tags as at their definitions):
  * `[PlainStore st]` (instance: plain store model, P1).
  * `J : JAtZ … s a σ` [J] (joint invariant at the entry: l4v invs + state_relation, JointAt.lean).
  * `hni : Entered σ` [J] (ct_running ∧ scheduler_action = resume_cur_thread).
  * `hR : MR a σ.machineState` [J] (shared machine_state), `hVI : ValidIrqMasks σ` [J] (valid_irq_masks).
  * `hn : NativeSys n c` (the statement's own syscall-number relation, not a gap).
  * `hflag` [S] (∀ ct v: l4h trap mode, TRAP_SYSCALLS clear after the FAULT_IP write; no l4v counterpart).
  * `hB : ∀ x, kheap ct = tcb x → KBudgetB …`: `now` NowAgree [P] (MachPlat.nowAgree from MR + VMT), `cur`
    CurInv [J] (ct bound to cur_sc, not IPC-blocked, cur_sc active, ct_not_in_release_q), `off` OffReady [J]
    (cur_sc_offset_ready), `tmo : NoTmoSend σ0 ∨ ct ∉ readyQueues` [J] (ct_not_in_q).
  * `hK : ∀ σb, BudgetAt σ σb true → ∀ Z' … a', JAtZ … σb → KDispHypsKV26 …` (path-restricted: only at the budget
    outcome):
    - `inv` (invocation path): `JEntryGlobM` (ari ARIface [P], tot ArchTotal [P], delParts: archRef [P], arKeep
      [P], vt JVtHyps [J] (VT-x placement), thr: obj [S] (native thread's VCPU word zero), ticks [P]; nd
      numDomains = 1 [P], ppA PPPlatA [P], dom DomConfig [P], portIn PortInVal [P] (∀σ, mr10 FINDING), sigRest
      SignalRestJHyp [J] (remote RunningVM signal, VT-x), timeAg [P], maxTU/tu [P]); `JEntryAt` (ni, ctnq, sg,
      flags, epQ, handlers, ports, vfh, cnf, vsTyp, live, fnz, urz, utks [J] (l4v invs + state_relation parts);
      stall, ioapics, archIrq [P]); `JPathAtM` (per cap kind JPathM: [P] config constants / one core, [J]
      invariant facts, [S] JVtxScope for VT-x decodes; no [W]); `JVtxHypMU` [S] (VT-x Untyped retype 14..18, no
      l4v counterpart).
    - `recv`: ct_not_in_q [J], valid_fault_handler of ct [J] (valid_tcb).
    - `mid` (ReplyRecv / NBSendRecv / NBSendWait): JEntryGlobM, JEntryAt, JPathAtM as above; `JPerfRegHyp` [J]
      (CHANGED; l4v invoke_untyped's valid_untyped_inv, perform_asid_control_invocation's valid_aci; only at
      MidPerfAt states); `JPerfIrqSlotHyp` [J] (CHANGED; l4v valid_irq_node + IRQ handler slots hold null or a
      notification cap; only at MidPerfAt states); `JMidVfhHyp` [J] (l4v valid_fault_handler kept by
      handle_invocation; only at the first phase's .ok outcomes); `JVtxHypMU` [S]. REMOVED: `JMidPerfHypQ` [W],
      `JMidLeavesHyp14` [W].
  * `hFin : ∀ x ∈ (specFront c σ).1, ∀ …, JAtZR … x.2 → KFinAtR …` (only at the front end's outcomes): hd
    (domainTime ≠ 0 ∨ NdOK) [J], vt [J], arch/archNd (ArchSwF/ArchNdF) [P], fo FpuOwnOK [J], sni/send
    (SniHyp/SendHyp) [P], tail (schedule's CR3 tail) [P].
  * `hARI : ARIface` [P], `hA : P0.ArchTotal` [P], `hnd : numDomains = 1` [P], `hM : MachPlat arI MR` [P],
    `hKD : MRKeepD arI MR` [P], `hPA : PPPlatA` [P], `hIA : IrqPlatA` [P], `hmrt` (MAX_RELEASE_TIME) [P], `hmb`
    (MIN_BUDGET) [P], `hT : TimeAgree` [P], `hmax : maxTicksToUs = U64.MAX` [P], `htu` (ticks_to_us) [P].
  * `hNS : ∀ s a σ, JHoleAt … → NativeScope σ` [S], `hNSR : ∀ …, JAtZR … → NativeScope σ` [S] (VT-x RunningVM out of
    the native scope).
- [W] remaining in kernel_entryJ26P: NONE (top-level or inside any bundle; JPathAtM has none since mr9, the mid
  bundle none since fin1). ∀-over-states hypotheses the operation cannot establish itself: `JEntryGlobM.portIn`
  [P] (PortInVal, mr10 FINDING: equivalent per-state form not weaker), the [S] scope premises `hNS` / `hNSR`
  (native scope at every JHoleAt / JAtZR state), `hflag` (∀ ct v, l4h trap mode), and the [S]/[J] VT-x fields
  quantified over JAtZ states (`delParts.thr.obj` [S], `delParts.vt` [J], `sigRest` [J]); every other bundle is
  path-restricted (`hK` at the budget outcome, `hFin` at the front end's outcomes, the mid facts at MidPerfAt /
  first-phase outcomes). No premise is known false in reachable states (KBudget.tmo, the last one, is not in
  J26P; it remains only in the intermediate M-line tops incl. J28M).
- Builds (tokyo, scratch/fin1/b.sh; mirror warmed from FL4-audit by cp -cR): fin1-b1 `XTopJointKEntry28M` OK (5664
  jobs), `XTopJointKEntry26P` OK (5730 jobs) on f9fa0192, first try. Root Fl4Proofs.lean not rebuilt (two leaf
  imports). Axioms (scratch/fin1/ax.lean, untracked; fin1-b1): propext, Classical.choice, Quot.sound only for
  kernel_entryJ28M, KDispHyps28M.to27M, kernel_entryJ26P, KDispHypsKV26.to25, j26P_platform. No
  sorry/admit/native_decide/bv_decide.

## invB (branch par/invB in FL4-rb, on 6809c6cd = int/j2, PR #51) — INV-PLAN §4 G1, fields OffReady, CtNQR, ValidMachineTime, ValidIrqMasks
Spec-only leaves, outside the JAtZ cone (imports: MachFieldFamT (spec frames), Fl4Spec.Ext.Entry; nothing
existing edited; root Fl4Proofs.lean imports the six new modules). All in namespace `Fl4Proofs.P3.SInv`.
- Infrastructure (SpecInvValidMachineTimeKit + SpecInvValidMachineTimeGen, generated by scratch/invB/mk.sh):
  `IK P m` (l4v `⦃P⦄ m ⦃λ_. P⦄`), view `vw` = (curTime, lastMachineTime, interruptStates, irqMasks), leaves
  `WL P` (view-invariance; `updateTimeStamp`; `setIrqState`; machine ops keeping lastMachineTime and only
  masking (`MaskT`); the IRQ ack `maskInterrupt false`; ReadFPU's `fpuStep`), `GK m := ∀ P, WL P → IK P m`.
  `gk_fl4KernelEntrySyscall rep c : GK (fl4KernelEntrySyscall rep c)` and `gk_fl4CallKernel_irq` — the whole
  syscall entry (FaultIP write, both phases, every decode/perform incl. rec_del/cap_revoke by their pre-fixed
  points, the preemption path, fl4Awaken, schedule, activateThread) keeps every predicate with the leaves. 190
  lemmas; MachFieldFamT's MTK family as the frames. Reusable for any later field that reads only `vw`.
- **FINDING (ValidMachineTime, ValidIrqMasks): the spec's ReadFPU sets the whole machine state.**
  Ext/Tcb `invokeFl4Tcb (.fpuTransfer _ true _)` = `doMachineOp (select univ >>= modify (fun _ => ms))`
  (`invokeFl4Tcb_readFpu`, `fpuStep`): any `MachineState`, so any lastMachineTime, IRQ masks, IRQ/time oracle
  positions. Trace: a thread with a TCB cap and a writable non-device frame cap (offset 64-aligned, 576 bytes
  of room) calls ReadFPU (`fl4TcbExtLabelNum .readFpu`, sysCall/sysSend, second phase); `decodeFl4FpuTransfer
  true` succeeds; perform = `fpuStep`, an outcome with `lastMachineTime = allOnes` (> the clock cap) and every
  mask false; the rest of the entry (reply, fl4Awaken, schedule, activateThread) never calls
  `getCurrentTime` and only masks, so the entry's outcome violates both fields. Proved:
  `readFpu_breaks_vmt σ : ∃ y ∈ (fpuStep σ).1, ¬ ValidMachineTime y.2`, `readFpu_breaks_vim σ i (hi : i
  inactive) : ∃ y ∈ (fpuStep σ).1, ¬ ValidIrqMasks y.2`. FL4's ReadFPU writes only the frame (and the FPU):
  the spec step should change only `underlyingMemory` (frame bytes). It also breaks the mr line's `MR`
  (shared machine state: irqState/timeState/lastMachineTime) — worth checking how XTopJointMR* treat
  ReadFPU. Stopped on both fields.
- ValidMachineTime (SpecInvValidMachineTime): (a) `ValidMachineTime` (same body as XTopJointMachRel's, in the
  cone; `Iff.rfl` at the wiring site). (b) only the reduction `wl_vmt_of (hF : IK ValidMachineTime fpuStep) :
  WL ValidMachineTime` / `kentry_vmt_of hF c : ValidMachineTime σ → ∀ y ∈ (fl4KernelEntrySyscall true c
  σ).1, ValidMachineTime y.2` — every other leaf proved (`uts_out`: updateTimeStamp sets both times to the
  capped clock value); `hF` is FALSE today (FINDING), so not a top; once ReadFPU keeps lastMachineTime, `hF`
  is `fk_tl_dmo` and `kentry_vmt_of` is the entry theorem with no side condition. (c) Fl4Spec's step relation
  (Ext/Entry) has only the syscall entry; `gk_fl4CallKernel_irq` covers `fl4CallKernel true .interrupt` the
  same way. (d) `boot_vmt : ValidMachineTime initASt`.
- ValidIrqMasks (SpecInvValidIrqMasks): (a) `ValidIrqMasks` (same body as XTopJointMRPath's). (b) leaves
  `vim_view`, `vim_uts`, `vim_sis` (setIrqState masks exactly the lines it makes inactive), `vim_msk`
  (MaskT ops); FINDING above; and an independent gap: the IRQ ack unmasks without reading the state, so
  `WL.ack` needs l4v `valid_irq_handlers` (every IRQHandlerCap irq issued) plus decode's lookup of the cap in
  the perform's state — not carried, not attempted. (d) `boot_vim`.
- CtNQR (SpecInvCtNQR): (a) `CtNQR σ := schedulerAction = resumeCurThread → ∀ d p, curThread ∉ readyQueues d
  p` (no existing def; at `Entered` it is ScPPR's `CtNQ`, the J26P fields JEntryAt.ctnq / recv ct_not_in_q /
  KBudgetB.tmo: `CtNQR.ctnq`). (d) `boot_ctNQR` (empty queues). (b) NOT DONE: not a stepwise invariant
  (handleYield appends ct before rescheduleRequired; possibleSwitchTo/enqueue of a woken thread needs
  "target ≠ ct", i.e. ct_in_state/valid_queues), so `WL`-style leaves don't apply; needs l4v's
  `ct_not_in_q` lemmas per compound op over the whole entry (M–L).
- OffReady (SpecInvOffReady): (a) ScCur's `Sched.OffReady` (KBudgetB.off). (d) `boot_offReady` (idle SC head at
  0, consumed = curTime = 0). (b) NOT DONE: writers are every refill/charge/SC-config/switch op; at exit it
  needs the switched-to SC's head ready, i.e. `valid_ready_qs`-style facts for every queued thread (M–L).
- Builds (tokyo, b.sh in the worktree root; mirror warmed from FL4-audit by cp -cR): invB-b9 `SpecInvValidMachineTimeGen
  SpecInvValidMachineTime SpecInvValidIrqMasks SpecInvCtNQR SpecInvOffReady` OK (4610 jobs). Axioms
  (scratch/invB/ax.lean, untracked): propext, Classical.choice, Quot.sound at most for gk_fl4KernelEntrySyscall,
  gk_fl4CallKernel_irq, gk_recDel, gk_capRevoke, readFpu_breaks_vmt/vim, wl_vmt_of, kentry_vmt_of, vim_*,
  boot_*. No sorry/admit/native_decide/bv_decide, no premise tagged.
## invC (branch par/invC in FL4-tcbj, on 6809c6cd = int/j2, PR #51)
Goal: INV-PLAN §4 G1 for SpecGlob (sg), EpQAll (epQ), FpuOwnOK (fo), DomListOK (F1's DomListOK half), each as a
spec-only SInv field with whole-entry preservation, in leaf modules SpecInv* outside the JAtZ cone (checked by an
import-ancestry script: SpecInvDom's cone has no JointAt/XTopJoint* module; it reaches ScNextDom, the module that
defines `DomListOK`, which is itself outside the JAtZ cone).
- DomListOK: DONE. Modules (new leaves, nothing existing edited; root Fl4Proofs.lean imports SpecInvDom):
  * `SpecInvDomF`: view `dlV σ := (domainList, domainStartIndex, domainIndex)`, `DL m := FK dlV m` (VsDom's
    projection frame), `dl_auto` (dk_step0 + leaves + `sf_unfold`, a copy of sch12's `fv_unfold`, which lives in
    XTopJointMidRunS inside the JAtZ cone), `dle_rab`, `dl_zipWithMx`, `dle_returnOk_bind`.
  * `SpecInvDomL`: CnodeRevoke's `lfp_le_prefixed` verbatim (CnodeRevoke's cone reaches FL4; stated before any
    `open Fl4Spec`: inside a file that opens Fl4Spec the same text fails to find the lattice instance).
  * `SpecInvDomG`: 264 `DL` leaves, a scripted copy of the `DK` lemmas of VsDom/VsDomOps/DomRecDel/TcbDom/
    CnodeDom/AllDom (scratch-invC/genDL.py, untracked: `DK`->`DL`, `dk_auto`->`dl_auto0`), with `rec_del` /
    `cap_revoke` by the lfp pre-fixed point over `dlV`.
  * `SpecInvDomE`: `DL` of fl4Awaken (ReflTransGen of send_signal outcomes), fl4SyscallFaultIP, updateTimeStamp,
    checkBudgetRestart, handleFault/Recv/Yield, preemptionPath, activateThread, the invocation front, the decode
    (`dle_fl4Decode`, every cap, both phases), every perform but invokeDomain (`dle_fl4Perform`), every
    non-syscall event (`dle_handleEvent_other`).
  * `SpecInvDom`: `DP m` (DomListOK kept) with combinators/`dp_auto`; the three writers: `dp_nextDomain` (the new
    index stays below the final end marker: the start entry is no end marker), `dp_domainSetStart`,
    `dp_domainScheduleConfigure`, from `DomInvOK σ inv` (the decode's checks, read only from `dlV`);
    `okd_fl4Decode` (every `.ok` decode outcome satisfies DomInvOK at its end state); the invocation shell
    `dpe_handleInvocationR` (copy of sch12's `syscall_post`, DomInvOK carried across `set_thread_state Restart` by
    the frame); `dp_schedule`, `dp_fl4CallKernel` (every event), `dp_fl4KernelEntrySyscall`.
- STATEMENTS (namespace Fl4Proofs.P3.SInvDom):
  * (a) `DomListOK` (ScNextDom, existing definition reused; consumer: KFinAtR.hd's `NdOK`).
  * (b) `kentry_domListOK (hnd : numDomains = 1) (h : DomListOK σ) : ∀ y ∈ (fl4KernelEntrySyscall (Z := Unit) true c σ).1, DomListOK y.2`.
  * (c) `kirq_domListOK (hnd) (h : DomListOK σ) : ∀ y ∈ (fl4CallKernel (Z := Unit) true .interrupt σ).1, DomListOK y.2`
    (Fl4Spec's Ext/Entry has no separate interrupt entry; `dp_fl4CallKernel` holds for every event and rep).
  * (d) `domListOK_init : DomListOK (initASt (Z := Unit))`.
  * The one hypothesis `hnd : numDomains = 1` [P] (FL4's one-domain configuration, already a top premise of
    kernel_entryJ26P / JEntryGlob.nd): DomainScheduleConfigure's decode checks `domain < numDomains`, and
    `DomListOK.dom` asks every entry's domain to be 0. No other premise.
- Builds (tokyo, ./b.sh untracked; mirror warmed from FL4-audit by cp -cR): invC-9 `SpecInvDomG` OK (1016 jobs),
  invC-12 `SpecInvDomE` OK, invC-14 `SpecInvDom` OK (4240 jobs: ScNextDom's cone for the definition; the frame
  modules F/L/G/E alone are 5 P3 modules over Fl4Spec). Axioms (scratch-invC/ax.lean, untracked): propext,
  Classical.choice, Quot.sound only for kentry_domListOK, kirq_domListOK, dp_fl4CallKernel, domListOK_init. No
  sorry/admit/native_decide/bv_decide.
- Consumer wiring (G3, not done here): KFinAtR.hd asks `NdOK` at the front end's outcomes; `dpe_fl4HandleEvent`
  gives DomListOK at every outcome of the front (`fl4HandleEvent`), and `dp_fl4KernelEntrySyscall` at the exit.
- SpecGlob / FpuOwnOK / EpQAll: NOT DONE (no module). Each is not inductive on its own, so a whole-entry proof
  needs other carried facts first (no counterexample in reachable states: each is an l4v invariant slice):
  * SpecGlob: `objRefs (untypedCap ..) = ∅`, so SpecGlob says nothing about untyped regions, and a retype from an
    untyped whose region holds an IRQ-node CNode or the idle thread would create caps naming them. Inductive form
    needs l4v valid_global_refs' cap_range clause for untyped caps (global refs outside every untyped range) plus
    the retype's region-is-free facts; the rest (copy/mint/move: derived caps name the same objects; IRQ control
    issue writes an IRQ handler cap, not into the IRQ node; TCB installs copy derived caps) are frames over
    SpecGlobFK/SpecGlob's SlotK machinery.
  * FpuOwnOK: writers are `setX64CurrentFpuOwner` (owner a TCB by asUser/archThreadSet's asserts) and the two heap
    writes that bypass set_object's type assertion: `retypeRegion` (overwrites) and `deleteObjects` (detype). Both
    need l4v's chain X64 arch_tcb_live (tcb_cur_fpu) -> if_live_then_nonz_cap -> untyped_children_in_mdb ->
    descendants_range of the retyped/reset untyped. Everything else is a frame over (owner, TCB-ness of every
    object); the same DL-style generator would give it.
  * EpQAll (`∀ e, EpQPre σ e`): needs valid_sched slices (released_ipc_queues for MemOKE of queued threads,
    ScBack = sym_refs SC<->TCB, ActReady): L, the scheduler/IPC writers all over the entry.
## invA (branch par/invA in FL4-sc, on 6809c6cd = int/j2): invariant line G1, VfhAll / FaultTcbs / NativeScope (spec only)
Goal (INV-PLAN §2/§4 G1): the three spec-only SInv fields as predicates on `Fl4Spec.State Unit`, kept across the whole
syscall entry, in leaves `SpecInv*` that import only Fl4Spec (+ Mathlib.Data.Set.Lattice.Order for `NonDet.lfp`), out
of the JAtZ cone. Nothing existing edited.
- Infrastructure (SpecInvNativeScopeK, SpecInvNativeScopeT): `IK P m` (every outcome of `m` from a `P` state is `P`;
  l4v `⦃P⦄ m ⦃λ_. P⦄`), `IKE` (abbrev, the exception monads); combinators mirroring VsDom's `FK` (`ik_step0` =
  `dk_step0` for IK, plus value-keeping `pure`/`returnOk` binds), `ik_lfp` (rec_del / cap_revoke via CnodeRevoke's
  pre-fixed-point argument, copied), `ik_unfold`. `TI Q σ` (every TCB satisfies `Q`) with the spec's TCB writers as
  leaves, each with a side condition on `Q`: `ti_setObject` (new object no TCB or a `Q` TCB), `ti_setSimpleKo` (by
  the two type assertions never a TCB), `ti_threadSet` / `ti_archThreadSet` / `ti_asUser` / `ti_setMrs` (pinned
  read of the old TCB: `IKp`, `ik_getsThe_bind`), `ti_setCap` (`CapSlotsOK`: the six TCB slots), `ti_retypeRegion(With)`
  (default objects), `ti_deleteObjects` (detype). These are generic and reusable by every per-TCB SInv field.
- DONE, built (tokyo, ib.sh/ibe.sh; mirror warmed by cp -cR from FL4-audit): `SpecInvNativeScopeK`, `SpecInvNativeScopeT`
  (aa4e154a, 7151c0bc), `SpecInvVfhAll`, `SpecInvFaultTcbs` (7151c0bc), each a few seconds over Fl4Spec (~1010 jobs).
  * VfhAll (a)+(d): `vfhQ x := validFaultHandler x.tcbFaultHandler`, `VfhAll σ := TI vfhQ σ` (l4v valid_tcb's
    valid_fault_handler); `VfhAll.ct : VfhAll σ → ∀ x, σ.kheap σ.curThread = some (.tcb x) → validFaultHandler
    x.tcbFaultHandler` (= `JEntryAt.vfh`, `KDispHyps*.recv`'s ct handler; `JMidVfhHyp` [J] needs it at the first
    phase's outcomes, i.e. (b)); `boot_vfhAll : VfhAll initASt`.
  * FaultTcbs (a)+(d): `activeSt` (Running ∨ Restart, l4v `active`), `ftQ x := x.tcbFault ≠ none → ¬ activeSt
    x.tcbState`, `FaultTcbs σ := TI ftQ σ`; l4v's stronger `FaultTcbsS` (`faultTcbSt`: Inactive / BlockedOnSend /
    BlockedOnReply) with `FaultTcbsS.weak`; `FaultTcbs.ct` (an active ct has no fault = `JEntryAt.cnf`);
    `boot_faultTcbsS`, `boot_faultTcbs`.
- DONE, built: NativeScope (b)/(c)/(d) (SpecInvNativeScopeF1..F6, SpecInvNativeScope, SpecInvNativeScopeBridge).
  `nsQ x := x.tcbState ≠ .runningVM`, `NativeScopeS := TI nsQ` (defeq IpcLeaves' `NativeScope`:
  `nativeScopeS_iff : NativeScopeS σ ↔ Endp.NativeScope σ := Iff.rfl`, Bridge, the only module importing the cone).
  The spec writes `runningVM` nowhere (every setThreadState has a literal non-runningVM state; new TCBs are
  `defaultTcb`, Inactive), so every TCB writer is a `TI` leaf with a side condition closed by `ns_side`; the 414
  monadic spec functions reachable from `fl4KernelEntrySyscall` get one `NSK`/`NSKE` lemma each, bottom-up
  (`ns_auto` = leaves | `ik_step0` | unfold), generated from the spec's call graph by proofs/scratch/invA/gen.py
  (untracked; `sh proofs/scratch/invA/mkns.sh` regenerates F1..F6 and SpecInvNativeScope). By hand (manual.py):
  resolveAddressBits' (wf recursion), transferCapsLoop (list recursion), rec_del / cap_revoke (`ik_lfp`), fl4Awaken
  (ReflTransGen of sendSignal), getExtraCptrs, receiveIpc (4M heartbeats), decodeTcbInvocation /
  fl4DecodeTcbInvocation stated at `.threadCap p` (their register decodes are `undefined` for any other cap;
  decodeCopy/Read/WriteRegisters are inlined there). Functions over monadic parameters (syscall, withoutPreemption,
  the *OnFailure wrappers, checkCapAt, orChoiceE, decodeIrqControlInvocationWith) take `NSK`/`NSKE` hypotheses.
  * `kentry_nativeScope (c) : NativeScopeS σ → ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1,
    NativeScopeS y.2` (b); `kentry_nativeScope'` the same in IpcLeaves' `NativeScope` (Bridge).
  * `kcall_nativeScope (rep) (ev : Event) : NativeScopeS σ → ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1,
    NativeScopeS y.2` (c: every event, interrupts / faults / timer, through l4v's handleEvent and fl4Awaken).
  * `boot_nativeScope : NativeScopeS initASt` (d).
  * Consumers: `kernel_entryJ26P`'s `hNS` / `hNSR` [S] become per-state facts once NativeScope is carried in the
    bundle (G3 wiring): no hypothesis needed.
  Builds: tasks invA-d5 (mirror FL4-invA, a detached worktree of par/invA used because FL4-sc's mirror sync kept
  timing out): F1..F6, SpecInvNativeScope (1026 jobs), Bridge (4550 jobs) OK. Root Fl4Proofs.lean imports the 12
  new leaves (root not rebuilt).
- VfhAll (b)/(c) and FaultTcbs (b)/(c): NOT DONE. Handoff:
  * VfhAll's only writer is `setCap` into a TCB's slot 3 (`ti_setCap`'s `CapSlotsOK`). Most setCap sites write caps
    of other kinds into slots from lookups (cte_insert/move/swap, retype's defaultCap, IPC cap transfer, arch cap
    updates, untyped free-index updates, deletion's zombies/remainders): the proof needs l4v's facts that the
    written slot is a CNode slot or already holds a non-handler cap (cte_wp_at / valid_cap), plus `checkHandlerEp` at
    decode for the TCB installs (ThreadControl, Configure, SetSpace, SetTimeoutEndpoint). A `TI`-pointwise family is
    not enough; it needs a pinned (Hoare) family at those sites.
  * FaultTcbs (weak) is not inductive alone (a faulted BlockedOnReceive thread woken to Running would break it);
    carry `FaultTcbsS`. Its writers: `sendFaultIpc`'s fault write (the faulting thread is active until the send
    blocks it), every wake-up to Running/Restart (send/receive/reply/restart/cancel paths: the woken thread's fault
    is none by `FaultTcbsS` and its state), `handleFaultReply`'s clear. Per-call-site Hoare reasoning (l4v's
    fault_tcbs_valid_states lemmas); the `IK`/`TI` frames give every other function.
  * No FINDING: no step of the spec was found to break any of the three fields.
- Axioms (proofs/scratch/invA/ax.lean, untracked; task invA-ax1): kentry_nativeScope, kcall_nativeScope,
  boot_nativeScope, kentry_nativeScope', boot_vfhAll, boot_faultTcbsS, boot_faultTcbs, ik_lfp: propext,
  Classical.choice, Quot.sound; VfhAll.ct: propext, Classical.choice; FaultTcbs.ct: propext; nativeScopeS_iff: none.
  No sorry/admit/native_decide/bv_decide in SpecInv*.
## invC2 (branch par/invC2 in FL4-tcbj, on 3cd6199c = int/j2 incl. invA/invB/invC) — CtNQR (b)/(c)
Goal: `kentry_ctNQR : CtNQR σ → ∀ y ∈ (fl4KernelEntrySyscall true c σ).1, CtNQR y.2` and the `.interrupt` form
(SpecInvCtNQR, invB). NOT PROVED; no module added. Analysis of what a proof needs (all l4v `valid_sched` /
`invs` pieces; no counterexample found in reachable states):
- Shape. The entry ends with `schedule; activateThread`, and every outcome of `schedule` has action =
  resumeCurThread (resume branch keeps it; chooseNew/switch branches end in `setSchedulerAction .resumeCurThread`).
  `activateThread` (completeYieldTo, setThreadState ct running) at most sets chooseNew (CtNQR vacuous) and
  enqueues nothing else. So the exit's CtNQR is "ct ∉ any ready queue after schedule", by schedule's branch:
  * chooseNew / switchThread: ct := the chosen thread, which `switchToThread` removes from the queue
    (tcbDomain t, tcbPriority t) only (`tcbSchedDequeue` = filter on that one queue). Needs
    T1 `∀ d p t, t ∈ readyQueues d p → kheap t = tcb x ∧ x.tcbDomain = d ∧ x.tcbPriority = p`
    (l4v valid_queues' domain/priority half), kept by `archSwitchToThread` (setVmRoot, lazyFpuRestore: arch
    fields only) and by schedule's own enqueues (ct's, the candidate's: own queue). `switchToIdleThread` needs
    T2 `idleThread ∉ readyQueues d p` (l4v `valid_idle` + not_queued idle).
  * resume branch: needs CtNQR at schedule's start after `awaken` and `checkDomainTime`. `awaken` releases the
    release-queue head through `possibleSwitchTo` (enqueue or switch); under resume it may enqueue only if the
    head is not ct: T3 `action = resume → ct ∉ releaseQueue` (l4v ct_not_in_release_q; CurInv carries it at the
    entry only), kept by awaken (removes only).
- The front (`fl4HandleEvent` + preemption path + `fl4Awaken`) must keep CtNQR. Stepwise it does not
  (invB's note): every `tcbSchedEnqueue`/`tcbSchedAppend` of a thread t under resume needs t ≠ ct. Callers and
  the fact each needs (l4v's per-op ct_not_in_q lemmas):
  * `possibleSwitchTo t` (IPC wake-ups, signal, reply, cancel_all_ipc/signals restarts, restart, SC resume,
    awaken): its only enqueue-under-resume branch is `tcbDomain t ≠ curDomain`; with FL4's one domain this is
    vacuous given T4 `∀ t x, kheap t = tcb x → x.tcbDomain = curDomain` (DomListOK.dom gives curDomain's entry 0;
    setDomain's decode checks `< numDomains = 1`) — then possibleSwitchTo never enqueues under resume.
  * direct `tcbSchedAction tcbSchedEnqueue t` with action possibly resume: `setPriority`/`setDomain`/
    `setSchedParams` (dequeue, write, enqueue if schedulable, then `rescheduleRequired` if t = ct: compound op
    keeps CtNQR), `schedContextResume`/`schedContextBindTcb`/`restart` (t runnable and ≠ ct needs ct's state:
    ct is Restart during a perform, set by fl4HandleInvocationR, and these enqueue only a thread that is
    schedulable and not ct, or ct followed by rescheduleRequired), `handleYield` (append ct then
    rescheduleRequired: compound), `rescheduleRequired` itself (enqueues the pending switch target, action :=
    chooseNew). Each needs a compound-op lemma "outcome action ≠ resume, or ct ∉ rq"; the ct-identity facts come
    from ct's thread state (running/restart at the perform) and l4v valid_queues' "queued ⇒ runnable"
    (to exclude enqueueing ct as a woken blocked thread).
- Missing, by name (to define with boot and preservation): T1 (valid_queues prio/domain), T2 (idle not queued),
  T3 (ct_not_in_release_q under resume), T4 (one-domain uniformity), plus the compound-op lemmas over the whole
  front. Size L (l4v: DetSchedSchedule_AI's ct_not_in_q family). invA's IK combinators and invB's GK kit give the
  frames for every op that touches neither readyQueues, schedulerAction, curThread, releaseQueue nor a TCB's
  domain/priority/state.
## ctnq1 (branch par/invC2 in FL4-tcbj, on e189d612 = int/j2 incl. invC2) — CtNQR's auxiliaries, T4 first
Goal (invC2's plan): `kentry_ctNQR` / the event form / boot, for `I` = CtNQR ∧ T1..T4 (+ "queued ⇒ runnable").
Done: **T4** (one domain), modules SpecInvQDomK, SpecInvQDomF1..F5 (generated), SpecInvQDom; namespace
`Fl4Proofs.P3.SInvQ`; imports only SpecInvNativeScopeT (Fl4Spec) and, for the last module, invC's SpecInvDom
(ScNextDom's cone, outside JAtZ). Root Fl4Proofs.lean imports the seven. Nothing existing edited.
- `T4 σ := DLOK σ.domainList σ.domainStartIndex σ.domainIndex ∧ σ.curDomain = 0 ∧ TI dom0 σ` (`dom0 x :=
  x.tcbDomain = 0`; `DLOK` = ScNextDom's `DomListOK` restated over the three fields, `dlok_of` /
  `T4.domListOK` convert; a structure on the state is not definitionally kept by a `modify` of another field,
  so the generated `ik_step0` frames need the field form). DomListOK is part of T4 because `next_domain` sets
  `curDomain := (the domainList[index']?).1` and `the none` is `undefined`: the index must stay in range.
- Leaves (SpecInvQDomK): copies of invA's `ti_*` keeping the two heap-free conjuncts (`q4_setObject` …
  `q4_deleteObjects`), `q4_retypeRegionWith` (a new TCB is `defaultTcb curDomain`, read at the same state),
  `q4_nextDomain`, `q4_setThreadState`, `q4_optionUpdateThread`, `q4_side`/`q4_leaf`/`q4_auto`.
- Generated (proofs/scratch/q4/mkq4.sh, untracked: invA's gen.py/manual.py with prefix q4, family Q4K, skip
  list skipq4.txt = invA's + the Domain invocation (threadSetDomain, setDomain, invokeSetDomain, invokeDomain,
  domainSetStart, domainScheduleConfigure, nextDomain), the perform/shell (fl4PerformInvocation,
  fl4HandleInvocationR), l4v's syscall path (performInvocation, handleInvocation, handleCall, handleSend,
  handleEvent) and the entries): 396 lemmas in F1..F5.
- By hand (SpecInvQDom): `q4_setDomain0`, `q4_domainSetStart`, `q4_domainScheduleConfigure`, `q4_invokeDomain`
  from invC's `DomInvOK` and the new `SetDom0` (`decode_domain_set` checks `domain < numDomains`;
  `okq_fl4Decode`); `q4_fl4PerformND` (every other perform), `q4_perform`, the shell `q4_handleInvocationR`
  (invC's `syscall_post'`; DomInvOK carried across `set_thread_state Restart` by the DL frame, SetDom0 is
  state-free), `q4_handleEvent_other`, `q4_fl4HandleSyscall`, `q4_fl4HandleEvent`, `q4_fl4CallKernel`,
  `q4_fl4KernelEntrySyscall`.
- STATEMENTS:
  * (b) `kentry_t4 (hnd : numDomains = 1) (h : T4 σ) : ∀ y ∈ (fl4KernelEntrySyscall (Z := Unit) true c σ).1, T4 y.2`
  * (c) `kcall_t4 (hnd) (rep) (ev : Event) (h : T4 σ) : ∀ y ∈ (fl4CallKernel (Z := Unit) rep ev σ).1, T4 y.2`
    (every event; `.interrupt` included)
  * (d) `boot_t4 : T4 (initASt (Z := Unit))`
  * premise: only `hnd : numDomains = 1` [P] (FL4's configuration, = invC's / JEntryGlob.nd).
- Builds (tokyo, ./b.sh untracked; mirror warmed from FL4-audit by cp -cR): ctnq-b2 `SpecInvQDomK SpecInvQDomF1..F5
  SpecInvQDom` OK (F1..F5 ≈ 1016..1024 jobs over Fl4Spec; SpecInvQDom 4258 jobs, SpecInvDom's cone). Under load
  (loadavg ~30) F4/F5 took ~35/~90 min each: build them alone. Axioms (scratch/q4/ax.lean, untracked; task ctnq-ax1): kentry_t4, kcall_t4, boot_t4, q4_fl4CallKernel: propext, Classical.choice, Quot.sound; T4.domListOK: propext. No sorry/admit/native_decide/bv_decide.
- NOT DONE: T2, T1, T3, CtNQR (b)/(c). What the reading of the spec showed (handoff, sharper than invC2's list):
  * T2 (`∀ d p, idleThread ∉ readyQueues d p`) is NOT a cheap frame. Its writers are every `tcbSchedAction
    tcbSchedEnqueue/Append t`; each needs `t ≠ idleThread` at that point:
    - guarded by `schedulable t` (schedule's ct enqueue, setDomain, setPriority/setMCP's tcb_sched path,
      schedContextBindTcb/Resume, yieldTo's tcbPtr, rescheduleRequired's switchThread target): need l4v
      `valid_idle` (idle's `tcbState = idleThreadState`, so `runnable` false); restart already skips the idle state;
    - `possibleSwitchTo t` (a woken thread: its old state was blocked, so `≠ idle` by valid_idle) and schedule's
      switch branch (`switchThread candidate`): need T2' `schedulerAction = switchThread t → t ≠ idleThread`;
    - ct appends (handleYield, yieldTo's `enqueue ctPtr`, Ipc's endTimeslice `tcbSchedAppend ct`): need ct ≠ idle.
      At the syscall entry this is l4v's `ct_active` precondition of handle_event (not an invariant: an exit may
      leave ct = idle), i.e. a per-state premise of the syscall entry [P]-style; for the interrupt path's
      checkBudget/endTimeslice it must come from the charge path's own guard (to check).
    - valid_idle's own preservation needs: no thread-state write reaches idle — TCB caps never name idle (l4v
      valid_global_refs = SpecGlob, invC: not inductive alone, untyped-range clause missing), endpoint /
      notification / reply queues never hold idle (valid_objs' ep queue facts), ct ≠ idle at the invocation.
    So T2 sits on SpecGlob's idle clause + queue facts; size L, not M.
  * T1 (queued ⇒ TCB with that domain/priority): `tcbSchedAction` itself is a pinned leaf (reads the thread's
    domain/priority at the same state, so an enqueue lands in its own queue); setPriority/setDomain/setSchedParams
    dequeue-write-enqueue (hand lemma: by T1 t is only in its own queue, so after the dequeue it is in none);
    every other TCB write keeps domain/priority (invA's TI leaves). Two obstacles: `retypeRegion` overwrites its
    pointers without a freeness check (a new defaultTcb over a queued TCB breaks T1) and `deleteObjects` removes
    objects (weaken T1 to `t ∈ rq d p → ∀ x, kheap t = some (.tcb x) → …` for detype; retype still needs l4v's
    descendants_range / untyped_children chain: a queued thread is live, so it lies outside a free untyped — the
    same chain invC names for FpuOwnOK).
  * T3 / CtNQR: as invC2. With T4 in hand, `possibleSwitchTo`'s `targetDom ≠ curDom` branch is dead
    (`T4.2.2` + `T4.2.1`), so it never enqueues under resume; its other enqueue is after rescheduleRequired
    (action := chooseNew, CtNQR vacuous).
  * Infrastructure for the next family: SpecInvQDomK is a template (copy, swap `dom0`/`DLOK`); invA's gen.py
    with a skip list and manual top (SpecInvQDom's shell) carries over; the shell needs only the decode facts the
    family's writers read (here SetDom0 / DomInvOK).

## invA2 (branch par/invA2 in FL4-sc, on e189d612 = int/j2 incl. invA): FaultTcbsS (b)/(c), VfhAll (b)/(c)
Goal: FaultTcbsS (l4v fault_tcbs_valid_states, the strong form) and VfhAll kept by the syscall entry and every event.
- DONE, built (d078e63e): SpecInvFaultTcbsT (`TP Q σ := ∀ p x, σ.kheap p = some (.tcb x) → Q p x`, the
  pointer-dependent `TI`, with SpecInvNativeScopeT's TCB-writer leaves as `tp_*`) and SpecInvFaultTcbsF1..F6
  (generated by proofs/scratch/invA/gen.py + mkft.sh, untracked): `ftlQ L p x := ftsQ x ∧ (p ∈ L → x.tcbFault =
  none)`, `FTL L := TP (ftlQ L)` (`FTL.nil_iff : FTL [] σ ↔ FaultTcbsS σ`); `ft_setThreadState (h : faultTcbSt ts ∨
  t ∈ L)`; one `FTK L` lemma (∀ L) for each of the 359 spec functions reachable from fl4KernelEntrySyscall that wake
  no thread and set no fault (the other 58, skipFT.txt, are the 16 below and the functions reaching them).
- DONE, built (8a606aa4): SpecInvFaultTcbsW: `ftl_cons` / `ftl_tail` / `ftl_noFault` / `ikp_cons` (a thread enters
  `L` at a read showing no fault), `ik_threadGet_bind` (pinned read), `HK` (pre/post), `hk_clearFault`,
  `hk_cancelIpc : HK (FTL L) (FTL (t :: L)) (cancelIpc t)` (cancel_ipc clears the fault first), `ftw_auto` (state
  and fault reads add the thread to `L`, fault clears too); `ft_restartThreadIfNoFault`, `ft_activateThread`,
  `ft_restart : FTK L (restart t)` for every L.
- NOT DONE (FaultTcbsS): the other direct wake-ups / fault writes:
  * sendIpc, doReplyTransfer: `ftw_auto` reaches the wake-up but leaves goals (the receiver-state match is not
    reduced after the state case split: the fault-ok branches keep the BlockedOnReceive continuation); needs a
    structured proof (read dest's state, `cases`, `ikp_cons` only in the BlockedOnReceive branch) — same for
    receiveIpc's sender (its fault read is direct, `ftw_rdf`).
  * receiveIpcBlocked / receiveSignalBlocked / receiveIpc / receiveSignal (the receiver blocks: BlockedOnReceive /
    BlockedOnNotification) and fl4HandleInvocationR / handleInvocation (`setThreadState ct .restart`): true only
    when the thread has no fault: a precondition `t ∈ L`; at the top ct ∈ L from ct active ([J] l4v ct_active,
    with FaultTcbsS) carried through the syscall by the generated lemmas (faults are set only by sendFaultIpc).
    The syscall shell needs mixed pre/posts (handleFault leaves ct faulted): sch12's `syscall_post` with
    `I := FTL [ct]`, `Q := FTL []`.
  * updateWaitingNtfn, removeAndRestartNtfnQueuedThread (and so sendSignal, cancelAllSignals, finaliseCap and the
    whole deletion path, fl4Awaken): they wake a thread taken from a notification's queue without reading its
    state or fault. MISSING INVARIANT [J] (l4v valid_ntfn: the threads of a waiting notification queue are
    BlockedOnNotification on it; with FaultTcbsS they have no fault): `NtfnQNoFault σ := ∀ n x q t, σ.kheap n =
    some (.notification x) → x.ntfnObj = .waitingNtfn q → t ∈ q → ∀ y, σ.kheap t = some (.tcb y) → y.tcbFault =
    none`, to carry beside FaultTcbsS (its own preservation: queue appends of ct, fault writes of non-queued threads).
  * sendFaultIpc (the fault write; via handleFault, handleTimeout, chargeBudget/endTimeslice, checkBudget(Restart)):
    the faulting thread is exempt until sendIpc blocks it (BlockedOnSend / BlockedOnReply / Inactive); needs an
    exempt set in `ftlQ` and the thread not BlockedOnReceive (so it is not sendIpc's woken receiver).
- VfhAll (b)/(c): NOT STARTED this round.
## fpu1 (branch par/fpu1 in FL4-rb, on be7b67d7 = int/j2 incl. invB, invC) — ReadFPU's spec step narrowed (invB's FINDING)
- LEAD DECISION implemented: Ext/Tcb `invokeFl4Tcb (.fpuTransfer _ true frame)` = `doMachineOp (fl4FpuToFrame frame)`,
  `fl4FpuToFrame frame : MachineMonad Unit` (new, Ext/Tcb, FL4 extension with no l4v counterpart): select a new
  `underlyingMemory` agreeing with the old one at every `a` with `fl4FpuStateSize ≤ (a - frame).toNat` (offset from
  the frame modulo 2^64 at least 2696), every other machine field kept. Was `select univ >>= modify (fun _ => ms)`.
- FL4 check (crates/fl4-core tcb.rs `fpu_transfer`, extracted Fl4Core `tcb.fpu_transfer`): `restart_caller` (the
  spec's setThreadState Restart before the perform), `a.fpu_flush(target)`, `copy_words(target.fpu_addr(), frame,
  (FPU_STATE_SIZE+7)/8 = 337)` with `wrapping_add` addresses: exactly the bytes frame+0 .. frame+2695 (2696 = 337*8;
  the brief's "576" is not FL4's x86 size: `FPU_STATE_SIZE` = 2696 on x86, 520 on AArch64). `fpu_flush`
  (fl4-arch-x86_64 fpu::flush/flush_local) saves the owner's live registers into the TCB image and restores CR0.TS:
  registers, FPU owner and enable state unchanged, so `fpuEnabled` and `machineStateRest` stay kept (the TCB's FPU
  image is not in the spec). No IRQ/timer/device effect.
- Refinement repaired:
  * XTopTcbFpu: `fpuToFrame_mem` (the spec step's outcome at any agreeing `um`), `fpu_store_other` (an X64
    `storeWord` at a word of the frame leaves the bytes outside the 2696); `FpuFrameXHyp` [W] now yields
    `∃ um, agree ∧ XTopAt … (setUm σ um)`; `fpuFrameX_of` from the frame words being `(w, w)` words of `B`
    (`bufw_inv`); `fpuHypX_of` exhibits the spec outcome by `fpuToFrame_mem`.
  * XTopJointReadFpu: `JAtZ.copyFrameJ` now writes every frame word as the IPC-buffer word `(w, w)` of `B`
    (JointAt's `FrameCover`, the frame inside a spec data page) by `JAtZ.userWrJ`, with the agreement carried;
    its premises `hVR` (VSpace objects) and `hksR` (kernel-global data) are gone. **`FpuFrameJHyp` [J] narrowed**
    to clause (a) only (the frame cap's range in a spec data page, l4v `valid_cap`); clauses (b) CNodes, (c) FL4
    tables/pools, (d) kernel-global data removed (they served only words outside `B`). JThreadPath.hFr docstring
    updated.
  * XTopJointTcb `tcb_read_fpuJ`: the spec outcome `setUm σ1 um` by `fpuToFrame_mem`.
- invB kit (SpecInvValidMachineTimeKit): `WL.fpu` removed; `mt_select`, `mt_fl4FpuToFrame` (MaskT: only the user
  memory changes), added to `mt_auto`; `gk_fpuAny` deleted. SpecInvValidMachineTime: `fpuStep`,
  `invokeFl4Tcb_readFpu`, `fpuStep_any`, `readFpu_breaks_vmt`, `wl_vmt_of`, `kentry_vmt_of` deleted (the FINDING
  lemmas are false for the new step); new `wl_vmt : WL ValidMachineTime`, **`kentry_validMachineTime : ValidMachineTime
  σ → ∀ y ∈ (fl4KernelEntrySyscall (Z := Unit) true c σ).1, ValidMachineTime y.2`** and `kirq_validMachineTime`
  (`fl4CallKernel true .interrupt`), no side condition.
- ValidIrqMasks: `readFpu_breaks_vim` deleted; `wl_vim_of (hA : ∀ i, IK ValidIrqMasks (doMachineOp (maskInterrupt
  false i)))` — every leaf but the IRQ ack. Remaining gap named in the module docstring: the ack
  (`invokeIrqHandler (.aCKIrq irq)`) needs `σ.interruptStates irq ≠ .irqInactive` at the perform, i.e. a carried
  `ValidIrqHandlers` invariant (l4v `valid_irq_handlers`: every IRQ handler cap of the CSpace names a line that is
  not inactive; writers invokeIrqControl, postCapDeletion/deletedIrqHandler (final cap), cap copy/mint/move) and the
  ack leaf restated at the decode's outcome. `hA` as a ∀-states statement is false; `wl_vim_of` is not a top.
- Builds (tokyo, ./fb.sh / ./ffull.sh untracked): fpu1-1 caught TcbExt's old-level ReadFPU membership (fixed by
  `fpuToFrame_mem`, now in TcbExt), fpu1-2/3 an omega/size normalisation in `fpuFrameX_of`; fpu1-4 `XTopTcbFpu
  SpecInvValidIrqMasks TcbNil SpecNoPre TcbDom SpecInvDomG XTopJointReadFpu XTopJoint` OK (5108 jobs); fpu1-5
  `XTopJointTcb XTopJointMRTcbL XTopJointEntry XTopJointKEntry26P` OK (5730 jobs); **fpu1-full: full `lake build`
  OK (5799 jobs)**. Axioms (scratch/fpu1/ax.lean, untracked): kentry_validMachineTime, kirq_validMachineTime,
  kernel_entryJ26P, tcb_read_fpuJ, JAtZ.copyFrameJ, fpuHypX_of: propext, Classical.choice, Quot.sound; wl_vim_of:
  propext, Quot.sound; mt_fl4FpuToFrame: none. No sorry/admit/native_decide/bv_decide; no premise added; one [J]
  premise narrowed (FpuFrameJHyp).
## ut1 (branch par/ut1 in FL4-tcbj, on aea8be68 = int/j2 incl. ctnq1) — untyped free-region invariant (UtFree and its carried facts)
Goal: the l4v untyped facts that make `retype_region` / `delete_objects` safe for per-object invariants
(SpecGlob, FpuOwnOK, ctnq1's T1/T2). Spec-only leaves, namespace `Fl4Proofs.P3.SInvU`, imports only Fl4Spec via
SpecInvNativeScopeT (outside the JAtZ cone); root Fl4Proofs.lean imports the eight. Nothing existing edited.
- View and frame (SpecInvUtK): `capView o` (the caps `get_cap` reads: a well-formed CNode's slots, a TCB's six,
  nothing else), `capAt σ sl` (l4v `caps_of_state`), `uV σ := (heap addresses in use, capAt σ, cdt,
  isOriginalCap)`, `UK v m := IK (uV · = v) m`. Leaves: `setObject` with the old object's caps (the `aType`
  assertion makes every non-CNode/TCB write cap-free, `cv_noCap`), `threadSet`/`optionUpdateThread` with
  `tcbCnodeMap (f x) = tcbCnodeMap x` (closed by `rfl` at every call site), `archThreadSet`, `asUser`,
  `setMrs`, `setSimpleKo`, `setThreadState`, machine/extended ops. `ik_of_uk`: a predicate that reads only the
  view is kept by every `UK` function.
- Generated frames (SpecInvUtF1..F4, 346 lemmas `uk_<f> : UK uvw (f …)` / `UKE`; proofs/scratch/ut1/mkut.sh,
  untracked: invA's gen.py/manual.py, prefix uk, skip list skipuk.txt = the leaves + every ancestor of
  `setCap`/`setCdt`/`updateCdt`/`setOriginal`/`retypeRegion(With)`/`deleteObjects` (scratch/ut1/anc.txt, 75
  functions: cap insert/move/swap/delete, rec_del, cap_revoke, IPC cap transfer and everything above it — the
  receive/fault/timeout paths, the perform/entry shell). Covered: every decode (all caps, both phases, incl.
  `decodeUntypedInvocation(With)`, `ensureNoChildren`, `lookupTargetSlot`), the scheduler, IPC without cap
  transfer, signals, SC/refill ops, VSpace map/unmap, IRQ state, `preemptionPoint`, `fl4Awaken`.
- Invariants (SpecInvUt), each a predicate on the view (`UtInvV`, so every UK function keeps it,
  `ik_utInv_of_uk`):
  * `UtFree` [J] (l4v `valid_untyped`, base-pointer form): no heap address lies in `utFr b n fi = [b+fi, b+2^n)`
    of any untyped cap `(dev,b,n,fi)` in any slot.
  * `UtWf` [J] (l4v `valid_cap` UntypedCap): `n ≤ 47`, `b` aligned to `2^n`, `fi ≤ 2^n` (so the region does not
    wrap, `UtWf.fit`).
  * `UtDisj` [J] (l4v `untyped_inc`, usable ranges): free parts of untyped caps in different slots are disjoint.
  * `UtDesc` [J] (l4v `untyped_inc`): two untyped caps in different slots whose regions overlap are CDT
    ancestor/descendant, and the descendant's region misses the ancestor's free part. `UtDesc.noKids`: a
    childless untyped's region meets no other free part — with `ensure_no_children` this is what makes a reset
    safe. (The weaker "free part meets region ⇒ descendant" is not kept by a reset, which grows the free part:
    a parent's full-index child must already be a descendant; hence l4v's form.)
  * `UtOrig` [J] (l4v: untyped caps are original, `is_cap_revocable`): needed for `cap_insert` of an untyped copy
    to make the copy a child (`should_be_parent_of`).
  * `UtInv` = the five. (d) `boot_utInv : UtInv initASt`.
- FINDING (vacuity, not a counterexample): `initASt` has only null caps (`init_capAt`), and only a retype from an
  untyped cap creates an untyped cap, so Fl4Spec's reachable states have no untyped cap: every Untyped
  invocation and AsidControl MakePool fails at the cap lookup in the spec's reachable states. The invariants
  are stated for arbitrary states; a boot state with untyped caps (FL4's root task) needs `UtInv` there.
- Consequences (SpecInvUt, SpecInvUtR):
  * (i) `retypeRegionWith_out` (the outcome: old state, or the heap `retKh` with default objects at
    `retPtrs rb n o`), `retPtrs_fresh` / `retype_keeps_old (hF : UtFree σ) (hc : capAt σ sl = some (untypedCap
    dev b bits fi)) (hfit) (h1 : b+fi ≤ rb) (h2 : rb + n·2^o ≤ b+2^bits) : y ∈ retypeRegionWith … σ → ∀ q,
    σ.kheap q ≠ none → y.2.kheap q = σ.kheap q`. At the decode's region: `UtRetOK σ ui` (the decode's checks:
    source cap, object size ≤ 47, window ≥ 1, `rb = alignUp (getFreeRef base F) o`, NotEnoughMemory, reset ⇒ no
    CDT child), `utRetOK_view` (reads only the view, so it crosses `set_thread_state Restart`), `utRet_region`
    (space accounting, `ut_region` = UntypedRetype's `retype_region` over spec words),
    `utRet_fresh (hI : UtInv σ) (hok : UtRetOK σ (.retype s false …)) : ∀ q ∈ retPtrs …, σ.kheap q = none`,
    `utRet_fresh_after_reset (hI) (hok : UtRetOK σ (.retype s true …)) : ∀ y ∈ resetUntypedCap s σ, ∀ q ∈ retPtrs …,
    y.2.kheap q = none`.
  * (ii) `deleteObjects_kheap` (exactly the objects of `delR ptr bits` go, cdt/orig/curDomain kept),
    `deleteObjects_range` (at an untyped's region, UtWf: the Nat range `utR b n`), `deleteObjects_empty`;
    `reset_region_empty (hI) (hc) : ∀ y ∈ resetUntypedCap s σ, ∀ q, q ∈ utR b n → y.2.kheap q = none`.
- Writer leaves (SpecInvUtW): `CapShrink w' w` / `utInvV_shrink` (UtInv is downward closed: fewer untyped caps,
  larger free indices up to the size, fewer heap addresses, new addresses outside every free part, same CDT,
  more original flags). `ik_setCap_nonUt` (every `set_cap` of a non-untyped cap), `ikp_setCap_raise`
  (`invoke_untyped`'s free-index write, `set_untyped_cap_as_full`), `ik_deleteObjects_utInv`,
  `ik_setOriginal_true`, `ikp_retype_utInv` (fresh addresses outside every free part), `utRet_new` (for a
  decoded non-reset retype: the new addresses are fresh, below the raised free index, and outside every other
  slot's free part by UtDisj). `setCap_out` (the outcome of `set_cap`: addresses, CDT, flags kept; other slots
  kept; the slot holds its old or the new cap).
- NOT DONE: (b) `kentry_utInv` / (c) `kcall_utInv`. What each remaining writer needs (all l4v `valid_mdb` /
  `untyped_inc` / `invs` pieces; no counterexample found):
  * `invoke_untyped`, non-reset: the chain is `ikp_setCap_raise` (new fi = `rb + len·2^o - base`, `utRet_new`) →
    `ikp_retype_utInv` (`utRet_new`) → `initArchObjects` (`uk_initArchObjects`) → `mapMx (createCap …)`.
    `createCap` writes `cdt dest := src`, `isOriginal dest := true`, `defaultCap` at `dest`. For a non-untyped
    type: UtFree/UtWf/UtDisj/UtOrig by `ik_setCap_nonUt`/`ik_setOriginal_true`; UtDesc needs that the old CDT
    has no child of `dest` (then no chain between untyped slots passes through `dest`): l4v `mdb_cte_at` for the
    empty slot `dest` (`ensureEmpty` at decode; carry `CdtNull σ : capAt σ sl = some nullCap → (∀ c, cdt c ≠ some
    sl) ∧ cdt sl = none` as a sixth fact). For an untyped child: the new cap `(dev, p, sz, 0)` has region
    `[p, p+2^sz) ⊆ [rb, rb+len·2^o)` (below the parent's raised fi): UtFree from `retPtrs_fresh`-style freshness
    (the retype wrote nothing, `type = untyped`), UtDisj from the parent's old free part (UtDisj) and sibling
    disjointness, UtDesc: `dest` is a child of `src`, and every cap whose free part meets the child's region
    is `src` itself (raised) or a descendant of `src` — needs UtDesc at `src` plus the new edge.
  * `invoke_untyped`, reset: after `reset_region_empty` the region is empty; `UtDesc.noKids` +
    `ensure_no_children` (`UtRetOK`'s last clause) give that no other untyped cap's free part meets the region,
    so the reset's `set_cap (untypedCap dev b n i·chunk)` keeps UtFree/UtDisj, and UtDesc's pairs with the
    source keep their clause (the source is never the ancestor: no children). Missing for `kentry`: that
    `set_cap` of a lower free index is not a `CapShrink` (state it as its own leaf with these facts), and the reset's other
    fact — every CDT link into a slot of a deleted CNode/TCB — needs `CdtNull` for detype: l4v gets it from
    `untyped_children_in_mdb` + `if_unsafe_then_cap` (objects in a childless untyped have no caps pointing to
    them, so their slots are empty). Same chain for AsidControl MakePool (`delete_objects frame 12`,
    `set_cap (max_free_index_update)` = `ikp_setCap_raise` with fi' = 2^n, `retype_region` one pool, `cap_insert`
    of the pool cap).
  * `cap_insert` (CNode Copy/Mint, IPC grant, TCB installs via `check_cap_at`/`cap_insert`, IRQ issue, MakePool):
    non-untyped `newCap`: `set_untyped_cap_as_full` is a no-op, `set_cap` non-untyped, CDT edge at the asserted-
    null `dest` (CdtNull). Untyped copy (`derive_cap` ran `ensure_no_children src`): `set_untyped_cap_as_full`
    = `ikp_setCap_raise` to 2^n (src's free part becomes empty, so UtDisj holds for the copy), the copy is a
    child of src (UtOrig + `should_be_parent_of`: `sameRegionAs` holds under UtWf), and UtDesc for the copy
    as `s1` needs "no other free part meets src's region" — from UtDesc + no children of src, which must be
    carried from the decode to the perform (`set_thread_state` keeps the CDT: `UtRetOK`-style view predicate).
  * `cap_move` / `cap_swap` (CNode Move/Mutate/Rotate, `cap_swap_for_delete`): rename slots in caps and CDT
    (UtDesc under the renaming; `dest` empty needs CdtNull).
  * `empty_slot` (all deletions): removes a cap and reparents its children to its parent: UtDesc by "a chain
    through the deleted slot is shortened" (TransGen induction), the rest `ik_setCap_nonUt`.
  * Everything else: the generated frames. The shell (fl4KernelEntrySyscall, fl4HandleInvocationR, the
    receive/fault/timeout paths through `do_ipc_transfer`'s cap transfer) is invA's `syscall_post'` shape with
    the writer lemmas above as leaves.
- Builds (tokyo, ./ut.sh untracked; FL4-tcbj mirror warm): ut1-b3 SpecInvUtK (1014 jobs), ut1-b6 SpecInvUtF1,
  ut1-b7 SpecInvUtF2..F4 (1018/1020/1022 jobs; F4 ~6 min under load ~22), ut1-b8 SpecInvUt (1016) + SpecInvUtW
  (1018), ut1-b13 SpecInvUtR (1028) + axioms (scratch/ut1/ax.lean, untracked): boot_utInv, ik_utInv_of_uk,
  retype_keeps_old, utRet_region, utRet_fresh(_reset), deleteObjects_kheap/_range, UtDesc.noKids,
  ik_setCap_nonUt, ikp_setCap_raise, ik_deleteObjects_utInv, ik_setOriginal_true, ikp_retype_utInv, utRet_new,
  reset_region_empty, utRet_fresh_after_reset, uk_preemptionPoint, uk_decodeUntypedInvocationWith, uk_schedule:
  propext, Classical.choice, Quot.sound at most. No sorry/admit/native_decide/bv_decide, no named premise. Root
  Fl4Proofs.lean not rebuilt.
## vih1 (branch par/vih1 in FL4-rb, on 239de0f8 = int/j2 incl. fpu1) — ValidIrqHandlers and the IRQ-ack leaf of ValidIrqMasks
- DONE (new leaf SpecInvValidIrqHandlers, namespace SInvV, imports SpecInvValidIrqMasks + CnodeOther + DelAbs + SpecCnK,
  outside the JAtZ cone (ancestry script); root Fl4Proofs.lean imports it):
  * `ValidIrqHandlers σ := ∀ p cref irq, capOpt (σ.kheap p) cref = some (.irqHandlerCap irq) → σ.interruptStates irq ≠
    .irqInactive` (l4v valid_irq_handlers; `capOpt` = what `getCap` returns, CnodeOther's `getCap_set_iff`).
    `boot_vih : ValidIrqHandlers initASt` (no handler cap in initKheap).
  * Step relation `HK σ σ'` (every line named by a handler cap of σ' is not inactive in σ', or was named in σ and did not
    become inactive), `HK.refl/trans`, `ValidIrqHandlers.hk`, `HKM m` (HK of every outcome) with `hkm_bind`,
    `ValidIrqHandlers.hkm`. Leaves: `hk_of_kheap_is` (heap and interruptStates kept), `vih_setCap_out` (SpecGlob's
    `setCap_capOpt` outside the cone, plus interruptStates kept), `hk_setCap` (written cap not a handler cap, or its line
    named / not inactive), `hk_setCap_named` (copy of a cap read from a slot of the same state), `hk_setCap_active` (IRQ
    control issue after its setIrqState IRQSignal), `hk_setIrqState_active`, `hk_setIrqState_inactive` (line named by no
    slot), `final_handler_unique` (`isFinalCap' (.irqHandlerCap irq)` + the cap at `sl` ⇒ `sl` is the only slot naming
    irq: gen_obj_refs holds `iRQRef irq`), `setCap_null_unique` (then after `setCap .nullCap sl` no slot names irq).
  * The ack restated: `vim_ack` (maskInterrupt false irq keeps ValidIrqMasks when the line is not inactive), `hkm_ack`,
    **`vimh_ack : ValidIrqMasks σ → ValidIrqHandlers σ → HIrq σ irq → ∀ x ∈ (doMachineOp (maskInterrupt false irq) σ).1,
    ValidIrqMasks x.2 ∧ ValidIrqHandlers x.2`** (replaces invB's false ∀-states `hA`).
- NOT DONE (handoff, in order):
  1. Decode→perform carry of `HIrq σ irq` for the ack (invC's DomInvOK pattern): (a) `lookupCapAndSlot` outcome
     `.ok (cap, slot)` keeps the state and has `capOpt (σ.kheap slot.1) slot.2 = some cap` (getCap_set_iff);
     (b) `fl4DecodeInvocation fp label args cptr slot cap excaps buf` with an `.ok (.invokeIRQHandler (.aCKIrq irq))`
     outcome has `cap = .irqHandlerCap irq` (Ext/Invocation.lean:177, the only producer; `decodeIrqHandlerInvocation`);
     (c) HIrq kept by the decode (reads only; a kheap frame `FK (·.kheap)` over the decode, e.g. a DL-style generated
     family as SpecInvDomG) and by `setThreadState thread .restart` (TCB state only: tcbCnodeMap unchanged);
     (d) a copy of the invocation shell (invC's `dpe_handleInvocationR`, sch12's syscall_post) whose perform leaf for
     `.invokeIRQHandler (.aCKIrq irq)` is `vimh_ack`, the other performs by the GK kit (`gk_auto`) at VIM ∧ VIH; then
     `kentry_validIrqMasks`/`kirq_validIrqMasks` for `ValidIrqMasks ∧ ValidIrqHandlers` from (2).
  2. `kentry_vih`/`kirq_vih` (VIH alone, whole entry): an `HKM` family over the ~414 functions of the entry (invA's
     gen.py/mkns.sh call-graph generator with HKM leaves). Frames: everything keeping capOpt of every slot and
     interruptStates (most functions; a generated `FK (fun σ => (capOpt-view, σ.interruptStates))` or per-object
     TCB/CNode cap-field frames: threadSet/archThreadSet/asUser/setThreadState/schedContext/ep/ntfn writes keep
     tcbCnodeMap). Writers needing pinned (Hoare) provenance at their call sites:
     - setIrqState: invokeIrqControl / X64 Arch.lean:40,46 / Ext/IrqControl.lean:131 (IRQSignal, `hk_setIrqState_active`);
       deletedIrqHandler via postCapDeletion (IpcCancel.lean:509) inside emptySlot (IpcCancel.lean:515): needs the
       slot's cap final (`final_handler_unique`), finality computed in recDel's finaliseSlotCall (CSpace.lean:435) and
       carried through finaliseCap's `deletingIrqHandler irq` (capDeleteOne of the IRQ-node slot: a notification cap,
       never a handler cap) to cTEDeleteCall's emptySlot (CSpace.lean:428) / capDeleteOne's emptySlot (only
       `.nullCap` cleanup there): `setCap_null_unique` then `hk_setIrqState_inactive`. The lfp (rec_del) needs the
       carried fact as part of the pre-fixed-point predicate (SpecGlob's NSK proof for rec_del is the model).
     - setCap of a handler cap: capInsert (.irqHandlerCap irq) after setIrqState IRQSignal (`hk_setCap_active`);
       cteInsert/cteMove/capSwap/rotate and IPC transferCaps/TCB installs of caps read from slots (deriveCap and
       updateCapData keep a handler cap): `hk_setCap_named` with the source slot's capOpt at the write (the write of
       the destination precedes the source's clearing in cteMove; decode-time lookups carried to the perform across
       setThreadState Restart as in 1(c)); zombies/nullCap/retype default caps are not handler caps (`hk_setCap`).
     - retypeRegion (default objects: empty CNodes, defaultTcb's null slots) and deleteObjects (objects removed):
       capOpt of the new/removed objects has no handler cap; interruptStates kept.
- Builds (tokyo, ./fb.sh untracked): vih1-1/2 fixed two proof terms (setIrqState_out, the uniqueness rewrite); vih1-3
  `SpecInvValidIrqHandlers` OK (4608 jobs). Axioms (scratch/vih1/ax.lean, untracked): boot_vih, vimh_ack, hk_setCap,
  final_handler_unique, setCap_null_unique, hk_setIrqState_active/inactive: propext, Classical.choice, Quot.sound.
  No sorry/admit/native_decide/bv_decide; no premise. Root Fl4Proofs.lean not rebuilt (one import line added).
## ut2 (branch par/ut2 in FL4-tcbj, on a57950a3 = int/j2 incl. ut1) — UtInv' and the CDT writers (not yet the entry)
Goal (ut1's handoff): `kentry_utInv` / `kcall_utInv` for `UtInv' = UtInv ∧` the carried CDT facts. Spec-only leaves,
namespace `Fl4Proofs.P3.SInvU`, importing only SpecInvUtR (Fl4Spec); root Fl4Proofs.lean imports the seven new
modules. Nothing existing edited. NOT reached: the entry/event theorems (see handoff); the writers below are done.
- Carried facts (SpecInvUtC): `CdtOK` [J] (l4v `mdb_cte_at`, parent half: `cdt c = some p → capAt p` is a non-null
  cap; so a null slot or a slot of no object has no CDT child — stronger and more robust than ut1's `CdtNull`, which
  says nothing about slots of absent objects that a retype later recreates), `CdtAcyc` [J] (l4v `no_mloop`; needed
  by `empty_slot`: with `cdt s = some s` the emptied slot would keep a child). `UtInv' σ := UtInvV (uV σ) ∧ CdtOKV ∧
  CdtAcycV` (a view predicate: `ik_utInv'_of_uk` makes every generated `UK` frame of SpecInvUtF1..F4 a leaf).
  `boot_utInv' : UtInv' initASt`.
- Infrastructure (SpecInvUtC): `HV P Q m` (view Hoare triple; `hv_bind`, `hv_pin`, `hv_gets_bind`,
  `hv_getCap_bind`, `hv_uk`, `hv_ret`), exact view writers `hv_setCdt`/`hv_setOriginal`/`hv_setCap` (`setCap_at`: the
  written slot holds the new cap — ut1's `setCap_out` only had "old or new"), `CapShrinkD` (CapShrink with a CDT
  change that keeps descendant pairs of untyped slots), `vCap_cap`/`vCC_cap`.
- Writers proved (each an `IK UtInv'` / `HV UtInv'V UtInv'V` or an outcome statement):
  * `ik_emptySlot' s info : IK UtInv' (emptySlot s info)` (SpecInvUtC; `es_tg_new`/`es_tg_old`: chains through the
    emptied slot are shortened, never created).
  * `hv_createCap` + `utInv'_cc` (cap not untyped) / `utInv'_ccU` (new untyped child: region inside the source's,
    outside its raised free part, no object in it, every other overlapping untyped cap an ancestor of the source
    whose free part misses the source's region) (SpecInvUtCC; `lu_tg`: a CDT leaf update keeps all other chains).
  * `invokeUntyped_utInv' (hI : UtInv' σ) (hok : UtRetOK σ (.retype s false base rb ty sz slots dev)) (hdn : DestNull σ
    (.retype …)) : ∀ y ∈ (ExceptT.run (invokeUntypedWith fl4ObjBitsApi (.retype s false …)) σ).1, UtInv' y.2`
    (SpecInvUtI: `utInv'_raise`, `utInv'_retype`, `hv_ccLoop`, `hv_ccLoopU` with `ItemU`/`RDisj`, `retPtrs_pw`,
    `fi_new` — the free-index arithmetic incl. a region ending at 2^64). `DestNull σ ui` = the decode's `ensure_empty`
    of every destination (`destNull_view`).
  * `ik_capInsert_nonUt c (hnu : c not untyped) src dest : IK UtInv' (capInsert c src dest)` — no decode fact
    (cap_insert asserts the destination is null; the new parent is the source by `same_region_as`, non-null, or the
    source's parent) (SpecInvUtIns). Covers CNode Copy/Mint/Mutate of non-untyped caps, IPC grant, TCB installs,
    IRQ issue, MakePool's pool cap.
  * `reset_utInv' (hI) (hDT : DetypeOK σ) (hc : capAt σ src = some (.untypedCap dev b n fi)) (hk : ∀ c, σ.cdt c ≠
    some src) : ∀ y ∈ (ExceptT.run (resetUntypedCap src) σ).1, PR src dev b n σ.cdt y.2` (finished or preempted;
    `PR = UtInv' ∧ RSV`, the reset facts: the region is empty, no other free part meets it, every overlapping untyped
    cap is an ancestor; `rs_setCap`: set_cap of the source with ANY free index ≤ 2^n keeps both — this is what makes
    the reset's lowering writes and the following retype's write leaves) (SpecInvUtRs).
  * `invokeUntyped_reset_utInv' (hI) (hDT : DetypeOK σ) (hok : UtRetOK σ (.retype s true …)) (hdn : DestNull σ …) :
    ∀ y ∈ …, UtInv' y.2` (SpecInvUtRsI).
  * `utInv'_rename` (UtInv' invariant under a slot involution), `hv_capSwap_same` (cap_swap of the slots' own caps),
    `ik_capSwapForDelete s1 s2 : IK UtInv' (capSwapForDelete s1 s2)` (SpecInvUtSw).
- NAMED PREMISE (new): **`DetypeOK σ` [J]** := `∀ u dev b n fi, capAt σ u = some (.untypedCap dev b n fi) → (∀ c,
  σ.cdt c ≠ some u) → ∀ c p, σ.cdt c = some p → p.1 ∉ delR b n` — no CDT parent slot lies in an object inside the
  region of a childless untyped cap. Only the detype of the reset (and of MakePool) uses it: it is what keeps
  `CdtOK` when the objects of the region vanish (a parent slot of a deleted CNode/TCB would otherwise survive as a
  dangling parent, and a later retype at that address would resurrect it with children). l4v counterpart:
  `untyped_children_in_mdb` + `if_unsafe_then_cap` + `mdb_cte_at` (an object in a childless untyped's region is
  referenced by no cap, so its slots are empty, so they are no CDT parents); true in every `invs` state. It is a
  fact of the invocation's start state, read through the view (`detypeOK_view` carries it across the decode and
  `set_thread_state`), not a ∀-states hypothesis. Narrower than carrying the l4v chain; discharging it needs that
  chain (or "slots of objects inside a childless untyped's region hold only null caps", whose preservation runs
  through finalisation/zombies — L).
- No FINDING: no writer step from a `UtInv'` state was found to break `UtInv'`.
- HANDOFF for `kentry_utInv` / `kcall_utInv` (in order):
  1. Decode → perform facts: `UtRetOK σ ui ∧ DestNull σ ui` from `decodeUntypedInvocationWith fl4ObjBitsApi`'s ok
     outcomes (cap = the invoked slot's cap via `lookupCapAndSlot`; the checks are listed in UtRetOK's docstring;
     `ensureNoChildren` → reset clause; `mapMEx ensureEmpty slots` → DestNull), carried across `set_thread_state
     Restart` by `utRetOK_view`/`destNull_view` (invC's DomInvOK pattern, `okq_fl4Decode`). Same for MakePool:
     `MakePoolOK` (parent = `untypedCap false frame pageBits fi`, no CDT child, dest null).
  2. MakePool (`performAsidControlInvocation (.makePool …)`): `deleteObjects frame 12` = the parent's region
     (DetypeOK, as `reset_utInv'`'s `hz0`, giving `PR`), `setCap (maxFreeIndexUpdate pcap) parent` = `rs_setCap` with
     f = 2^12, `retypeRegion frame 1 0 asidPool` (`utInv'_retype`, fresh by RSV), `ik_capInsert_nonUt` (pool cap),
     the ASID-table `modify` (UK).
  3. `cap_insert` of an UNTYPED copy (CNode Copy/Mint of an untyped cap; `updateCapData` leaves untyped caps alone):
     carry `derive_cap`'s `ensure_no_children src` decode→perform. Then `set_untyped_cap_as_full` = `utInv'_raise`
     to 2^n, the copy (`src`'s old cap, same region) becomes a child of src (`should_be_parent_of`: UtOrig, and
     `same_region_as` from UtWf arithmetic), and UtDesc for the copy follows from UtDesc(src, ·) + no kids exactly as
     `rsv_mk` (every overlapping cap is an ancestor of src whose free part misses src's region); UtDisj: the copy's
     free part is src's old one, src's new one is empty. Use `utInv'_ccU`'s proof as template (dest a CDT leaf).
  4. `cap_move` (CNode Move/Mutate): dest null (decode `ensure_empty`) → leaf; the view is `vRen (sw src dest)` with
     src then nulled and parentless (src has no child after the move): prove as `utInv'_rename` + a null-slot write.
     `cap_swap` with transformed caps (CNode Rotate/Swap: `updateCapData` keeps untyped caps): `hv_capSwap_same`
     needs the written caps to be the stored ones for untyped caps; generalise with "non-untyped written caps".
  5. `set_cap` of a non-null, non-untyped cap for UtInv' (CdtOK needs non-null): extend ut1's `ik_setCap_nonUt`
     (zombies, arch cap updates, TCB installs). rec_del's `setCap remainder`: needs finaliseCap's value fact
     (remainder is null or a zombie; null is removeable, so the written one is a zombie).
  6. The ancestors (scratch/ut1/anc.txt, 75 functions): invA's gen.py with family `IK UtInv'` (prefix ui, leaves =
     `ik_utInv'_of_uk` for every UK lemma + the writers above), by hand: rec_del/cap_revoke (`ik_lfp`), the IPC cap
     transfer loop (`ik_capInsert_nonUt` needs the transferred cap non-untyped or the untyped copy case 3), the
     perform/shell `fl4HandleInvocationR` with `syscall_post'` carrying UtRetOK/DestNull/MakePoolOK/no-children and
     `DetypeOK` (as a view fact of the entry state), then `kentry_utInv (hDT : DetypeOK σ) : UtInv' σ → …` and
     `kcall_utInv` (interrupt/fault/timer paths reach only `empty_slot`/`cap_delete_one`/the frames).
- Builds (tokyo, ./ut2.sh untracked = ut1's ut.sh with compact error output; mirror warm): ut2-b2 SpecInvUtC (1030
  jobs) + SpecInvUtCC (1032), ut2-b7 SpecInvUtI (1034), ut2-b8 SpecInvUtIns (1036), ut2-b9 SpecInvUtRs (1038),
  ut2-b10 SpecInvUtRsI (1040), ut2-b11 SpecInvUtSw (1038) + axioms (scratch/ut2/ax.lean, untracked): boot_utInv',
  ik_utInv'_of_uk, ik_emptySlot', hv_createCap, utInv'_retype, hv_ccLoop, hv_ccLoopU, invokeUntyped_utInv',
  ik_capInsert_nonUt, reset_utInv', invokeUntyped_reset_utInv', hv_capSwap_same, ik_capSwapForDelete: propext,
  Classical.choice, Quot.sound; utInv'_cc, utInv'_ccU, utInv'_raise, rs_setCap: propext, Quot.sound; utInv'_rename:
  propext. No sorry/admit/native_decide/bv_decide. Root Fl4Proofs.lean imports the seven (root not rebuilt).
## ft2 (branch par/ft2 in FL4-sc, on cb5885f8 = int/j2 incl. invA2): FaultTcbsS (b)/(c) with NQB
Goal (invA2 handoff): FaultTcbsS kept by the syscall entry and every event, with the notification-queue invariant.
- Design (why not invA2's `FTL` + NtfnQNoFault): the fault write needs "the faulted thread is in no notification
  queue", which "no fault for queued threads" alone does not give; l4v's valid_ntfn (queued => BlockedOnNotification
  on that notification) does, but it is broken by retype of a TCB over a queued pointer unless the untyped
  freshness chain is proved. Used instead: **NQB** `σ := ∀ t, queued σ t → ∀ y, kheap t = tcb y → fault = none ∧
  ¬ sndRpl state` (sndRpl = BlockedOnSend / BlockedOnReply; a fresh defaultTcb satisfies it). Its writers: queue
  additions (`tcb_ntfn_append` of the blocking receiver, `reorder_ntfn` of a thread read BlockedOnNotification),
  fault writes and BoS/BoReply writes (the thread must be in no queue: tracked in a list `K`).
- Carried bundle (SpecInvFaultTcbsN): `B L E K C σ := OPG (fqX L E) univ C σ ∧ NQB σ ∧ ∀ u ∈ K, ¬ queued σ u ∧
  ¬ isBoN (u's state)`; `fqX L E` = FaultTcbsS except the exempt threads `E` (active while their fault is sent,
  and `E`-members are active or in a fault state), no fault at `L`; `C` at the current thread (ct tracking).
  `b_nil_iff : B [] [] [] ⊤ σ ↔ FaultTcbsS σ ∧ NQB σ`.
- Generic frame (SpecInvFaultTcbsG, G1..G7, generated by proofs/scratch/ft2/mkfg.sh = invA's gen.py + ONLY mode):
  `OPG F S C σ` (every TCB satisfies `F.R p fault state`, every notification queue ⊆ S, `C curThread`), `FQ`
  closed under fault clear / Inactive / defaultTcb; one `FGK F S C` lemma for each of the 352 reachable functions
  that wake no thread, set no fault / BoS / BoReply and add no thread to a notification queue (skipFG.txt = invA2's
  skipFT + replyPush setPriority reorderNtfn tcbNtfnAppend sendIpcBlocked + the scheduler, which is G7 at
  `C := fun _ => True` because it switches threads). `b_of_gf`: every such function keeps `B` for all lists
  (instances fq1 / fqT / fqN give queue shrinking, the queued threads' facts and K's facts).
- DONE, built (tokyo, FL4-invA mirror, tasks ft2-b2..b14; each module ~1016..1056 jobs over Fl4Spec):
  * 2e3a3958 SpecInvFaultTcbsG, G1..G7 (generic frame, 352 + 6 generated lemmas).
  * 192a842c SpecInvFaultTcbsN (NQB, `fqX`/`fqT`/`fqN`/`fq1`, `B`, `b_of_gf`, `b_nil_iff`, `b_mono`, `b_addE`,
    `b_dropE`, `b_cons`, `b_queue_cons`, `b_setThreadState t ts (h1 : faultTcbSt ts ∨ t ∈ L ∨ (t ∈ E ∧ activeSt ts))
    (h2 : t ∈ K → ¬ isBoN ts) (h3 : ¬ sndRpl ts ∨ t ∈ K) (h4 : t ∈ E → activeSt ts ∨ faultTcbSt ts)`) and
    SpecInvFaultTcbsH1 (`b_auto`: lifted frame | b_setThreadState | state read adding to L (state holds no fault
    and is not active; with E = [] also active states) | fault read none | fault clear / cancel_ipc; uniform
    `BK L E K C` for all lists: restartThreadIfNoFault, removeAndRestartEp/BadgedThread, cancelAllIpc,
    cancelBadgedSends, restart, cancelAllSignals, sendSignal, fl4Awaken; `b_removeAndRestartNtfnQueuedThread (t ∈ L)`,
    `b_updateWaitingNtfn (queue ⊆ L)`, `b_activateThread : BK L [] K C`).
  * fa9f9a3d SpecInvFaultTcbsH2: `b_sendIpc … (hK : thread ∈ K) (hb : block = true ∨ thread ∈ L) :
    HK (B L (thread :: E) K C) (B L E K C) (sendIpc …)` (receiver read BlockedOnReceive -> no fault; sender's
    exemption ends: BoS / BoReply / Inactive (`b_sts_drop`, `sts_post`) or a fault read none), `b_replyPush`.
  * c0aca9b3 SpecInvFaultTcbsH3: `b_setNtfn_add`, `b_tcbNtfnAppend`, `b_reorderNtfn` (added thread: no fault, not
    BoS/BoReply, not in K), `b_receiveSignalBlocked` / `b_receiveSignal (t ∈ L) (t ∉ E) (t ∉ K)`,
    `b_receiveIpcBlocked (t ∈ L) (t ∉ E)`, `b_replyPushK (caller ∈ K)`, the BoS/BoReply read rule (`ikp_bconsK`).
  * (this commit) SpecInvFaultTcbsH4: `b_setFault t f (t ∈ E) (t ∈ K) : HK (B L E K C) (B (L.filter (· ≠ t)) E K C)`,
    `b_handleFault t ex (t ∈ K) : HK (B L (t :: E) K C) (B (L.filter (· ≠ t)) E K C)` (with handler: fault write +
    sendIpc; without: Inactive), `b_handleTimeout t ex (t ∈ L) (t ∈ K)` (same post), `boot_nqb`, `boot_B`.
    Root Fl4Proofs.lean imports G..G7, N, H1..H4 (root not rebuilt).
- No sorry/admit/native_decide/bv_decide; no premise added so far (all lemmas are unconditional or carry their
  call-site facts as hypotheses). Axioms: scratch/ft2/ax.lean (task ft2-ax2), see the report.
- NOT DONE (handoff, in order):
  1. receiveIpc: `unfold; b_auto` does not close (4M heartbeats timeout + leftover goals); prove it structured like
     b_sendIpc: reply-cap branch (cancelIpc hk, `ik_bhk_bind`), completeSignal / maybeReturnSc (frame), the sendEP
     branch: sender read BoS -> `ikp_bconsK` (sender joins K), doIpcTransfer.., fault read: none -> L, then
     replyPush (`b_replyPushK`) / Inactive / Running; else `b_receiveIpcBlocked`. Precondition t ∈ L, t ∉ E.
  2. setPriority (`b_setPriority` dropped: the non-BoN cases with b_auto left goals; the BoN case was written: read
     BoN -> tptr ∈ L facts via `opg_fqT`, tptr ∉ K since K's threads are not BoN, threadSetPriority keeps
     `OPG (fqT tptr)`, then `b_reorderNtfn`). Do each runnable/non-runnable case explicitly.
  3. Budget charge (draft in scratch/ft2/H5wip.lean: `fqA c`, `sched_runnable`, `b_endTimeslice`,
     `b_chargeBudget c (c ∈ K) (c ∈ E → c ∈ L) : HK (B L E K (· = c)) (B (L.filter (· ≠ c)) E K (· = c))`); its
     remaining errors: the getThreadState peel in endTimeslice (`obtain` on the `if ts = runningVM` bind: split
     the do-block bind before obtaining) and `{y3.2 with consumedTime := 0}.kheap` needing `show`/`dsimp only`
     before `hb4.1.1 c _ hz`. Then checkBudget / checkBudgetRestart with a result-dependent post (`true` keeps L).
  4. doReplyTransfer: receiver read BoReply -> receiver ∉ queue (NQB) -> joins K; fault none -> L, Running; some ->
     handleFaultReply (frame), clear (L), Restart/Inactive; the timeout branch after the `runnable` read needs
     the receiver in E (`b_addE`: track active-or-fault-state from the state write with an `fqA`-like FQ, no
     runningVM) and `b_handleTimeout`; its post removes the receiver from L: the caller's L must not contain a
     BlockedOnReply thread (ct during a perform is Restart): carry `OPG (not-BoReply at ct)` or state the lemma
     with L ⊆ {threads read not BlockedOnReply}.
  5. Callers by b_auto at the uniform level (`BK L E K C`): the deletion path (finaliseCap, fastFinalise,
     capDelete(One), recDel(F) / capRevoke(F) via ik_lfp as manual.py, deletingIrqHandler, invokeCnode,
     invokeIrqHandler), installTcbCap(Frame), invokeTcb (needs b_setPriority, b_restart), fl4PerformInvocation /
     performInvocation (endpoint send: b_sendIpc with ct ∈ K, ct ∈ L; reply: doReplyTransfer), handleYield
     (chargeBudget false), handleInterrupt / maybeHandleInterrupt (sendSignal), preemptionPath (checkBudget).
  6. Shell: handleInvocation / fl4HandleInvocationR with SpecInvDom's `syscall_post'`: invariant
     `B [ct] [ct] [ct] (· = ct)` across the phases, the fault phase `b_handleFault ct` ending in `B [] [] [ct]`;
     handleRecv: drop ct from E (ct ∈ L), weaken K to [] before receiveSignal; fl4HandleEvent / handleEvent
     (checkBudgetRestart's result), fl4CallKernel (fl4Awaken, schedule = G7 at C := ⊤ via `b_of_gf`,
     activateThread at E = []), fl4KernelEntrySyscall.
  7. Top: `kentry_faultTcbsS (hJ : CtEntry σ) : FaultTcbsS σ ∧ NQB σ → ∀ y ∈ entry, FaultTcbsS y.2 ∧ NQB y.2` with
     **[J] `CtEntry σ`** := ct's TCB state is active and ct is in no notification queue (l4v `ct_active` +
     `valid_ntfn`; true at every syscall entry from user mode; ct ∉ queue is the J layer's `not_in_ntfnQueue`).
     It gives `B [ct] [ct] [ct] (· = ct) σ` (`b_cons` from active + FaultTcbsS, `b_addE`, K). The event form
     (kcall_faultTcbsS) needs `CtEntry'` := ct active or idle, in no queue. FaultTcbs (weak) by `FaultTcbsS.weak`.
- No FINDING: no reachable-state counterexample met.
## vih2 (branch par/vih2 in FL4-rb, on b2f74572 = vih1) — ValidIrqHandlers frames and the ack's decode carry
- DONE, built (new leaves, namespace SInvV, outside the JAtZ cone; root Fl4Proofs.lean imports all six):
  * `SpecInvValidIrqHandlersK`: view `hV σ := (fun sl => capOpt (σ.kheap sl.1) sl.2, σ.interruptStates)`;
    **class `WLH P`** (P reads only `hV` and invB's `vw`; kept by `updateTimeStamp` and by `MaskT` machine ops).
    Instances: `hV · = v`, `ValidIrqMasks` (vim_view/uts/msk), `ValidIrqHandlers`, `HK σ0 ·`, any predicate of
    `hV` alone (`wlh_of_hV`), conjunctions. `hkm_of_ikh : (∀ σ0, IKH (HK σ0 ·) m) → HKM m`. Leaves (ut1's UtK,
    adapted to an abstract `P`): setObject of an object with the same `capOpt` (`hv_noCap`: the `aType` assertion,
    garbage CNodes included), setSimpleKo, threadSet (cap fields kept), archThreadSet, asUser, setMrs,
    setThreadState, optionUpdateThread; `hv_auto` with the modify / extended-op / machine-op leaves
    (`WLH.view _ _ (by rfl) (by rfl)`, `WLH.msk` + invB's `mt_auto`, `WLH.uts`).
  * `SpecInvValidIrqHandlersF1..F4` (generated: `sh proofs/scratch/vih2/mkhv.sh`, invA's gen.py/manual.py via ut1,
    skip list skiphv.txt = ut1's skipuk + setIrqState, deletedIrqHandler, postCapDeletion, archInvokeIrqHandler,
    updateTimeStamp): **`hv_f : [WLH P] → IKH P (f …)` for the 341 spec functions reachable from
    fl4KernelEntrySyscall that write no cap, CDT link, original flag, heap address or IRQ state and do not ack**
    (incl. the whole decode `hv_fl4DecodeInvocation`, lookups, IPC without cap transfer, scheduler, timer,
    VSpace ops without cap writes, fl4Awaken; not receiveIpc/sendIpc, which may transfer caps). One family gives at once: `HKM` (via `HK σ0 ·`),
    `ValidIrqMasks ∧ ValidIrqHandlers` (no ack inside), and pinned facts of the caps (a slot's cap, `HIrq`).
  * `SpecInvValidIrqHandlersD` (the ack's carry, vih1 handoff step 1(a)-(c)): `vih_mem_getCap`,
    `okCap_lookupCapAndSlot` (every `.ok (cap, slot)` has `capOpt slot = some cap` at its state),
    `okdAt_capFault`, `okdAt_mono`, `okAck_decodeIrqHandler`, **`okAck_fl4Decode`** (a decoded
    `.invokeIRQHandler (.aCKIrq i)` comes only from `cap = .irqHandlerCap i`), `capOpt_of_ikh` / `hIrq_of_hV`
    (the slot's cap survives lookupIpcBuffer / lookupExtraCaps / getMrs / the decode / setThreadState Restart),
    **`vimh_invokeIrqHandler_ack`** (the perform of the ack keeps `ValidIrqMasks ∧ ValidIrqHandlers` from `HIrq`).
- NOT DONE (handoff, in order; everything below composes with the family above, `IKH P` for `P := ValidIrqMasks ∧
  ValidIrqHandlers` (+ pinned conjuncts), all as `WLH` instances):
  1. Writer leaves (new module, e.g. SpecInvValidIrqHandlersW): `CapAct c σ := ∀ irq, c = .irqHandlerCap irq →
     σ.interruptStates irq ≠ .irqInactive` (a `WLH` instance by `wlh_of_hV`); `ca_of_slot` (VIH + cap in a slot);
     `setCap c` keeps `VIM ∧ VIH` from `CapAct c` (vih1's `hk_setCap`, plus `vw` kept: setCap is a setObject);
     `setCdt`/`setOriginal`/`updateCdt` keep every `WLH` predicate (no cap, no vw); `setIrqState` keeps VIM
     (`vim_sis`) and VIH when the state is not inactive (`hk_setIrqState_active`) or the line is unnamed
     (`hk_setIrqState_inactive`). Then pinned compositions `IKH (fun σ => J σ ∧ CapAct c σ)` for capInsert /
     cteInsert (setUntypedCapAsFull writes an untyped cap: CapAct trivially), capMove, capSwap /
     capSwapForDelete (both caps CapAct), createCap / retypeRegion (default caps, heap: retype's new objects hold
     only null caps — VIH needs `capOpt` of new objects: emptyCnode / defaultTcb give null caps; `hV` changes so
     not a frame), deleteObjects (removes objects: a `capOpt` of `none` names nothing).
  2. Decode → perform carry for all cap writes (DomInvOK pattern, generalising `okAck_fl4Decode`): `InvCA σ inv`
     := every cap the invocation will write is `CapAct` at σ (cnode insert/move/rotate/swap caps, TCB install caps
     (`checkCapAt` re-reads them at the perform: use that read), IRQ setNotification cap (a notification cap:
     CapAct trivially), untyped/arch/IO-port caps (not handler caps: CapAct trivially)), proved by an `OkDAt`
     traversal of `fl4DecodeInvocation` with leaves: `deriveCap` / `updateCapData` / `maskCapRights` map a
     handler cap only from a handler cap of the same line, and caps read by `getCap`/`lookupCapAndSlot`/
     `lookupExtraCaps` are `CapAct` by VIH at the reading state (`okCap_lookupCapAndSlot` + `ca_of_slot`),
     carried by the frame family (`CapAct` is `WLH`). IPC `transferCaps`: the extra caps are looked up inside
     `doNormalTransfer` at the same state as the transfer starts (CapAct carried through transferCapsLoop's own
     writes, which write only CapAct caps into empty slots).
  3. Deletion (the only IRQ-state inactivation): `deletedIrqHandler` via `postCapDeletion` inside `emptySlot`:
     needs the emptied slot's cap final (`isFinalCap'`) for `final_handler_unique` + `setCap_null_unique` +
     `hk_setIrqState_inactive`. Finality is computed in recDel's `finaliseSlotCall` (CSpace.lean:435) and must be
     carried (as a pinned conjunct of the `ik_lfp` pre-fixed-point predicate, SpecInvNativeScopeK's `ik_lfp`) to
     `cTEDeleteCall`'s emptySlot (CSpace.lean:428); `capDeleteOne`'s emptySlot (invokeIrqHandler set/clear,
     deletingIrqHandler) computes finality itself (`isFinalCap` read before `finaliseCap`). Also invokeIrqControl /
     archInvokeIrqControl / Ext IrqControl issue: setIrqState IRQSignal then capInsert of the new handler cap
     (`hk_setCap_active`).
  4. The shell: copy invC's `dpe_handleInvocationR` (SpecInvDom) with `I := VIM ∧ VIH`; front by the family;
     at the perform state `HIrq` from `okCap_lookupCapAndSlot` (through `okdAt_capFault`, `capOpt_of_ikh` over
     lookupIpcBuffer / lookupExtraCaps / getMrs / setThreadState) and `okAck_fl4Decode`; perform: ack →
     `vimh_invokeIrqHandler_ack`, others by 1–3. Then `kentry_validIrqMasks` / `kirq_validIrqMasks` for
     `ValidIrqMasks ∧ ValidIrqHandlers` and `kentry_vih` / `kirq_vih` (corollaries, or via `hkm_of_ikh`).
- Builds (tokyo, ./fb.sh): vih2-2 (HV-equality version) OK; vih2-3/5/6/7/8 fixed the WLH leaves (`(by rfl)` for
  the view equalities, fl4Awaken's reprogramTimer step via `WLH.view`, portIn/portOut by hand with `MaskT f`),
  getCap's membership and the decode traversal (`nomatch`); **vih2-9 `SpecInvValidIrqHandlersD` OK (4636 jobs;
  K, F1..F4 built in vih2-7)**. Root Fl4Proofs.lean imports K, F1..F4, D (root not rebuilt). Axioms
  (scratch/vih2/ax.lean, untracked; ./vax2.sh): hkm_of_ikh, wlh_of_hV, hv_fl4DecodeInvocation, hv_lookupExtraCaps,
  vih_mem_getCap, okCap_lookupCapAndSlot, okAck_fl4Decode, capOpt_of_ikh, vimh_invokeIrqHandler_ack: propext,
  Classical.choice, Quot.sound; okdAt_capFault: propext. No sorry/admit/native_decide/bv_decide; no premise.
- No FINDING: no step was found to break either invariant (the writers above are the l4v ones).
## ft3 (branch par/ft3 in FL4-sc, on 769f55eb = int/j2 incl. ft2): FaultTcbsS (b)/(c) finished
Goal (ft2 handoff 1-7): FaultTcbsS (l4v fault_tcbs_valid_states) with NQB kept by the syscall entry and every event.
- DONE, built (tokyo, FL4-invA mirror as sync vehicle, tasks ft3-b1..b12, ft3-ax1; each module ~1058..1068 jobs over
  Fl4Spec, seconds to ~3 min):
  * f1e0f6e6 SpecInvFaultTcbsH5 (ft2's H5wip fixed): `b_endTimeslice`, `b_chargeBudget n cto c (c ∈ K) (c ∈ E → c ∈ L) :
    HK (B L E K (· = c)) (B (L.filter (· ≠ c)) E K (· = c))`.
  * 794c0c0a SpecInvFaultTcbsH6: `b_setPriority t p : BK L E K C` (each state case explicitly; BlockedOnNotification:
    no fault, not BoS/BoReply, not in K, `TT t` kept by the frame, then `b_reorderNtfn`); `b_receiveIpc t … (t ∈ L)
    (t ∉ E)` (`b_auto3`: `ik_fail_bind` closes the 12 non-BoS sender-state branches at once, `if` branches whose condition
    simplifies to False closed by `simp at`); `b_doReplyTransfer s r g : HK (B L E K C ∧ NoRpl L) (B L E K C)`
    (receiver read BoReply joins K and is not in L since `NoRpl L`; after its state write `fqC receiver`
    (active or fault state, frame-kept) so a runnable read is active and `b_addE` exempts it for `handle_timeout`;
    `b_replyTail`).
  * a5e7a742 SpecInvFaultTcbsH7: `b_checkBudget c (c ∈ K) (c ∈ E → c ∈ L)` (`true` result ⇒ state unchanged; post
    `B (L.filter (· ≠ c)) E K`), `b_checkBudgetRestart c (c ∈ L) (c ∈ K) (c ∉ E)` from `B L (c :: E) K` (a runnable c
    after the charge has no fault since not exempt, so the Restart write is allowed); 16 generated uniform `BK L E K C`
    callers (fastFinalise, capDeleteOne, deletingIrqHandler, finaliseCap, recDel(F), capDelete, capRevoke(F),
    installTcbCap(Frame), invokeCnode, invokeIrqHandler, invokeTcb, handleInterrupt, maybeHandleInterrupt;
    proofs/scratch/ft3/gen.py with `ONLY=…`, family `BK ' L E K C'`, tactic `b_autoE`: `b_auto`'s plain
    `show IK _ (ite …)` rule dropped the `ExceptT.run` of exception goals, so the `ike_ite`/`ike_whenE` rules go first).
  * 8c131ef1 SpecInvFaultTcbsH8: exception pre/posts (`HKE`, result-dependent `HKR` with `okErr ok err`, `hk_catch`,
    `ft_syscall_post` = SpecInvDom's `syscall_post'` copied, that module being outside this closure);
    `b_chargeBudget_nil` / `b_checkBudget_nil` (L = [] makes the charge an IK; b_leaf rules), `b_preemptionPath ct` /
    `b_handleYield ct : BK [] [] [ct] (· = ct)`, `b_fl4PerformInvocation ct : HKE (B [ct] [ct] [ct] (· = ct) ∧ NoRpl [ct])
    (B [ct] [ct] [ct] (· = ct))` (send: ct the sender, exempt twice by `b_addE`; reply: `b_doReplyTransfer`; the rest
    uniform or frame).
  * ad9f82ef SpecInvFaultTcbsH9 / H10: `b_fl4HandleInvocationR ct … : HKE (B [ct] [ct] [ct] (· = ct)) (fun s => B [ct] [ct]
    [ct] (· = ct) s ∨ (blocking = true ∧ B [] [] [ct] (· = ct) s))` (lookups/decode frame; lookup fault:
    `b_handleFault ct` with E = []; perform after `set_thread_state ct Restart`, which gives `NoRpl [ct]`);
    `b_handleRecv ct : HK (B [ct] [ct] [ct] (· = ct)) (B [] [] [] (· = ct))` (receive with ct's exemption ended, for a
    notification also K = []; lookup fault `b_handleFault ct`); `b_fl4HandleSyscall`, `b_fl4HandleEvent_sys` (via
    `b_checkBudgetRestart`'s "true ⇒ unchanged"), `b_evShell` / `b_fl4HandleEvent_user` (user faults), `b_fl4HandleEvent_irq`
    (from `B [] [] [ct]`), `b_fl4CallKernel` (errors = preemption, from `B [] [] [ct]` into `preemption_path`; ok ends in
    `B [] [] [] (· = ct)`; fl4Awaken; schedule at C := ⊤; activate_thread at E = []).
- Shell invariant: `B [ct] [ct] [ct] (· = ct)` (ct no fault, exempt = active or in a fault state, in no queue and not
  BoN, ct current). It needs no premise inside the syscall; every fault on ct (handleFault, the charge's
  handle_timeout) is taken with E = [] so ct ends in a fault state with no exemption left, and the syscall ends there.
- **Tops** (SpecInvFaultTcbsH10, namespace Fl4Proofs.P3.SInv):
  * `kentry_faultTcbsS (rep) (c : Syscall) (hJ : CtEntry σ) (h : FaultTcbsS σ ∧ NQB σ) : ∀ y ∈
    ((fl4KernelEntrySyscall (Z := Unit) rep c) σ).1, FaultTcbsS y.2 ∧ NQB y.2`.
  * `kcall_faultTcbsS (rep) (ev : Event) (hJ : CtEntryEv ev σ) (h : FaultTcbsS σ ∧ NQB σ) : ∀ y ∈ ((fl4CallKernel (Z :=
    Unit) rep ev) σ).1, FaultTcbsS y.2 ∧ NQB y.2` (every event).
  * weak form: `kentry_faultTcbs`, `kcall_faultTcbs` (… → FaultTcbs y.2, by `FaultTcbsS.weak`); boot:
    `boot_faultTcbsS_nqb` (= `boot_faultTcbsS`, `boot_nqb`).
- **Premise [J] `CtEntry σ`** := `(∀ x, σ.kheap σ.curThread = some (.tcb x) → activeSt x.tcbState) ∧ ¬ queued σ
  σ.curThread` (l4v `ct_active` + `valid_ntfn`'s queue states: queued threads are BlockedOnNotification); for
  interrupts `CtEntryI` (active or `idleThreadState`, l4v `ct_running ∨ ct_idle`), `CtEntryEv ev := if ev = .interrupt
  then CtEntryI else CtEntry`. True at every entry from user mode (the trapping thread runs; a running thread is in no
  notification queue). Discharge at G4: the active part from the J layer's entry facts (`Entered` + `JAtZ.curRun` give
  `CurRun`: ct Running); the queue part needs a carried spec invariant "every queued thread is BlockedOnNotification"
  (l4v valid_ntfn's ntfn_q part) — not NQB, which is weaker by design (ft2: the strong form breaks at TCB retype
  without the untyped-freshness chain), so either a new SInv field `QueuedBoN` (its own preservation: queue additions
  are BoN writers (`receive_signal_blocked`; `reorder_ntfn` of a thread read BoN); BoN is left only through the
  dequeue in cancel/wake paths; retype needs the fresh-object fact) or JAtZ's notification-queue relation (IpcQP/IpcRel
  queue lists are BoN threads) projected to the spec state at entry.
- No sorry/admit/native_decide/bv_decide; no new axioms. `#print axioms` (scratch/ft3/ax.lean, task ft3-ax1):
  kentry_faultTcbsS, kcall_faultTcbsS, kentry_faultTcbs, kcall_faultTcbs, boot_faultTcbsS_nqb, b_fl4CallKernel,
  b_fl4HandleSyscall, b_fl4HandleInvocationR, b_handleRecv, b_fl4PerformInvocation, b_doReplyTransfer, b_receiveIpc,
  b_setPriority, b_chargeBudget, b_checkBudgetRestart, b_invokeTcb, b_recDel, b_capRevoke: propext, Classical.choice,
  Quot.sound. Root Fl4Proofs.lean imports H5..H10 (root not rebuilt).
- No FINDING: no reachable-state counterexample met.
- Left: discharging `CtEntry` (above); VfhAll (b)/(c) (invA handoff, not started).
## vih3 (branch par/vih3 in FL4-rb, on 3017a034 = int/j2 incl. vih2) — kentry_validIrqMasks / kentry_vih (vih2 handoff steps 1-4)
- DONE (new leaves, namespace SInvV, spec only, outside the JAtZ cone; root Fl4Proofs.lean imports all five):
  * `SpecInvValidIrqHandlersW` (step 1): `CA c is` (a handler cap names a non-inactive line), `ca_of_slot`,
    `VH R σ := ValidIrqMasks σ ∧ ValidIrqHandlers σ ∧ R σ.interruptStates` (`WLH` instance, so vih2's frames keep
    it), `VI := VH (fun _ => True)`, `RM R`. Leaves: `vh_setCap` (CA cap; machine fields by MachFieldFamT's
    `mtk_setCap`), `hv_setCdt`/`hv_updateCdt`/`hv_setOriginal` (every WLH), `vh_setUntypedCapAsFull`,
    `vh_capInsert`/`vh_capMove`/`vh_capSwap` (CA caps from `R`), `vh_capSwapForDelete` (caps read from slots),
    `vh_createCap` (default caps), `vh_retypeRegion(With)` (default objects hold no handler cap; ut1's
    `retypeRegionWith_out`), `vh_deleteObjects`, `vh_setIrqState_active` (`RM R`).
  * `SpecInvValidIrqHandlersX` (step 3, deletion): `Uniq irq sl σ` (only `sl` names irq, WLH), Hoare triples with
    results `HT`, **`ht_lfp`** (pre-fixed point with a result-dependent post), `RV` (result values),
    `rv_finaliseCap` (remainder never a handler cap; a handler cleanup cap only from the finalised handler cap),
    `vi_emptySlot_p` (cleanup cap's line named only by the emptied slot → `setCap_null_unique` +
    `hk_setIrqState_inactive`), `vi_capDeleteOne_u` (cleanup NullCap: keeps `VI ∧ U` for every WLH `U` closed under
    `setCap NullCap`, e.g. `Uniq`), `vi_deletingIrqHandler_uniq`, `vi_finaliseCap`; **`vi_recDel : HT VI (RDPost k)
    (recDel k)`** where `RDPost k r s := VI s ∧ (k = FinaliseSlotCall sl _ → r = ok (_, IRQHandlerCap irq) →
    Uniq irq sl s)`: finality read by `isFinalCap` in finaliseSlotCall (`final_handler_unique`), kept through
    `deleting_irq_handler`, consumed by cTEDeleteCall's `emptySlot`; `vi_capDelete`, `vi_capRevoke`.
  * `SpecInvValidIrqHandlersY` (steps 1-2): `OkV σ0 Pr m` (ok outcomes keep `hV` and satisfy `Pr`), `okv_mapME`,
    `okv_lookupCap` / `okv_lookupExtraCaps` (looked-up caps CA by VIH at the lookup), `okv_deriveCap`;
    `vh_transferCapsLoop` / `vh_transferCaps` (R = every transferred cap CA), `vi_doNormalTransfer` (extra caps
    looked up in the same transfer), `vi_irqIssue` (set_irq_state IRQSignal; cap_insert IRQHandlerCap: IRQ control,
    arch IOAPIC/MSI, FL4 remapped IOAPIC), `vi_checkCapAt_ins` (TCB installs: `check_cap_at` re-reads the source
    slot; `sameObjectAs (IRQHandlerCap i) c → c = IRQHandlerCap i`), `vi_setCap_bind_dead` + page / PT / PD / PDPT
    maps (the continuation fails unless the cap is an arch cap), `vi_performAsidControlInvocation` (parent cap
    re-read), `vh_invokeCnode` (`CnCA`), `vi_invokeIrqHandler` (`IhCA`: ack's `HIrq` → vih1's `vimh_ack`; set-handler
    cap CA kept across `capDeleteOne`).
  * `SpecInvValidIrqHandlersG` (generated: `sh proofs/scratch/vih3/mkvi.sh`, targets.txt / skipvi.txt, invA's gen.py
    with a target filter; untracked like vih2's scripts): `IKH VI` for 29 functions (IRQ control, arch / untyped
    performs, TCB installs, invokeTcb, IPC with cap transfer, fault/timeout paths, budget, preemption path).
  * `SpecInvValidIrqHandlersS` (step 2 decode carry + step 4 shell): `InvCAd is inv` (CNode insert/move/rotate caps
    and the set-handler cap CA); `okv_decodeCnode` (get_cap + mask_cap / update_cap_data / derive_cap keep CA:
    `ca_maskCap`, `ca_updateCapData`), `okd_decodeIrqHandler`, `okd_fl4Decode`; `vi_fl4Perform` (from `InvCAd` and
    the ack's `HIrq`, which comes from vih2's `okAck_fl4Decode` + the invoked cap's slot `okCap_front`, carried by the
    frames across getMRs/decode/setThreadState); `vi_handleInvocationR` (invC's shell), `vi_fl4HandleSyscall`,
    `vi_handleEvent_other`, `vi_fl4HandleEvent`, `vi_fl4CallKernel` (every event), `vi_fl4KernelEntrySyscall`.
- STATEMENTS (no premise): **`kentry_validIrqMasks (hm : ValidIrqMasks σ) (hh : ValidIrqHandlers σ) : ∀ y ∈
  (fl4KernelEntrySyscall true c σ).1, ValidIrqMasks y.2 ∧ ValidIrqHandlers y.2`**, **`kirq_validIrqMasks`** (same for
  `fl4CallKernel true .interrupt`), `kentry_vih` / `kirq_vih` (their second conjunct). `vi_fl4CallKernel rep ev`
  holds for every event and `rep`.
- Builds (tokyo, ./vb.sh untracked: module build, compact error output): vih3-3 W OK; vih3-4..7 X (rv closers,
  ESQ instance, spurious `split` branches of recDelF's / postCapDeletion's matches) OK at vih3-7; vih3-8..10 Y
  (`as` keyword, do-join points of doNormalTransfer's `if`, the page map's matched entry); vih3-11 G (ASID control
  re-writes the parent cap read from its slot: moved to Y by hand); **vih3-12: W, X, Y, G OK; vih3-13
  `SpecInvValidIrqHandlersS` OK (4650 jobs)**. Root Fl4Proofs.lean imports W, X, Y, G, S (root not rebuilt).
  Axioms (scratch/vih3/ax.lean, ./vax3.sh untracked, task vih3-ax2): kentry_validIrqMasks, kirq_validIrqMasks,
  kentry_vih, kirq_vih, vi_fl4CallKernel, vi_recDel, vi_handleInvocationR, okd_fl4Decode, vi_doNormalTransfer,
  vh_setCap: propext, Classical.choice, Quot.sound. No sorry/admit/native_decide/bv_decide/axiom in the new files;
  no named premise.
- Notes: `kentry_vih` keeps the joint hypothesis `ValidIrqMasks σ` (it is the second conjunct of the joint
  theorem; ValidIrqHandlers alone would need its own copy of the shell over `VH` without VIM — not needed since both
  are G1 fields). The reachable-only route through l4v's `handleEvent` syscall branches is not used: non-syscall
  events go through `fl4HandleEvent_other` (as invC). No FINDING: every writer is l4v's (deletion inactivates a line
  only after emptying its final handler cap's only slot; every handler cap written is read from a slot, re-read by
  `check_cap_at`, or issued after `set_irq_state IRQSignal`; the page maps fail on a non-arch cap).
- Handoff: G3 wiring of `ValidIrqMasks ∧ ValidIrqHandlers` into the SInv bundle (consumer XTopJointMRPath's
  `ValidIrqMasks`); `boot_vih` / `boot_vim` give the initial state.
## ut3 (branch par/ut3 in FL4-tcbj, on c24106cd = int/j2 incl. ut2) — `kentry_utInv` / `kcall_utInv`
Goal (ut2's handoff, steps 1–6): UtInv' (= UtInv ∧ CdtOK ∧ CdtAcyc) kept by the syscall entry and every event. DONE.
Spec-only leaves, namespace `Fl4Proofs.P3.SInvU`, importing only SpecInvUtSw/SpecInvUtRsI (Fl4Spec); root Fl4Proofs.lean
imports the eight new modules. Nothing existing edited.
- Writers (SpecInvUtMv, step 3–5): `NNU c` (non-null, not untyped), `hv_setCap_nn` / `ik_setCap_nn` (no decode fact);
  `CapRel c0 c` (both non-null, `c = c0` or neither untyped: what `mask_cap` / `update_cap_data` / `derive_cap` give);
  `utInv'_vCap_rel`, `utInv'_cut` (cut a null childless slot from its parent), `utInv'_vOrig`; `utInv'_ccG`
  (= ut2's `utInv'_ccU` with any free index); `sameRegionAs_self` (UtWf arithmetic); `CIOK w c src` (c untyped ⇒ it is
  src's cap and src has no CDT child) and **`hv_capInsert c src dest : HV (UtInv'V ∧ CIOK · c src) UtInv'V`** (untyped
  copy: `set_untyped_cap_as_full` empties src's free part, the copy is src's CDT child); **`hv_capMove`** (CapRel cap to
  a null destination: renamed view + destination overwritten + null source cut; post also gives the slots' caps, so
  Rotate's two moves chain); **`hv_capSwap`** (CapRel caps; Rotate with src = dest).
- MakePool (SpecInvUtMp, step 2): `detype_PR` (reset_utInv's detype half), `MpOK σ (makePool frame slot parent base)` :=
  `∃ dev fi, capAt σ parent = some (untypedCap dev frame page_bits fi) ∧ ∀ c, σ.cdt c ≠ some parent`;
  **`makePool_utInv' (hI : UtInv' σ) (hDT : DetypeOK σ) (hm : MpOK σ a) : ∀ y ∈ (performAsidControlInvocation a σ).1,
  UtInv' y.2`** (detype, `ik_PR_setCap` to 2^12, `utInv'_retype` at `frame` fresh by RSV, `ik_capInsert_nonUt`).
- Decode facts (SpecInvUtD, SpecInvUtDA, step 1): `OkV w P m` (every `.ok` outcome from a state of view `w` satisfies
  `P`; every decode function is a `UK` frame, so a check made on the start view holds at the end and, across
  `set_thread_state Restart`, at the perform); leaves `okv_ensureEmpty`, `okv_ensureNoChildren`,
  `okv_mapMEx_ensureEmpty`, `okv_reset_bind` (const_on_failure), `okv_deriveCap` (`UtKeep`), `okv_lookupCapAndSlot`,
  `okv_lookupExtraCaps`; `utKeep_mask` / `utKeep_upd` (mask_cap / update_cap_data keep untyped caps and make none).
  `InvOKV w : Fl4Invocation → Prop`: untyped `UtRetOKV ∧ DestNullV` (= ut1/ut2's UtRetOK/DestNull on the view,
  `utRetOK_of_V`), CNode `CnOKV` (insert: CIOK; move: src cap c0 with CapRel, null dest, src ≠ dest; rotate: CapRel for
  both, pivot ≠ src/dest, dest null unless src = dest), MakePool `MpOKV`, SetIRQHandler's cap not untyped (`isNtfnCap`),
  else True. `okv_decodeUntyped` (all of UtRetOK's clauses incl. NotEnoughMemory and the reset's
  ensure_no_children), `okv_decodeCnode`, `okv_decodeIrqHandler`, `okv_archDecode` (MakePool; no other arch decode
  yields a MakePool: `okv_noasid` traversal), **`okv_fl4Decode (hc : w.2.1 sl = some cap) (hex : ∀ p ∈ ex, w.2.1 p.2 =
  some p.1) : OkV w (InvOKV w) (fl4DecodeInvocation fp label args ci sl cap ex buf)`**.
- Hand-written leaves (SpecInvUtA): the VSpace map performs (`setCap cap` then a match that fails unless `cap` is the
  matching arch cap: no outcome for a null/untyped cap, `ik_of_empty`), `ik_checkCapAt_ins` (TCB installs:
  `same_object_as (UntypedCap ..) _ = False`, so an untyped newCap is never inserted), `finaliseCap_nu` (remainder never
  untyped; with `cap_removeable NullCap` it makes rec_del's `set_cap remainder` an NNU write), `getReceiveSlots_len`
  (≤ 1 slot), `ui_transferCapsLoop` / `ui_transferCaps` / **`ui_doNormalTransfer : IK UtInv' (doNormalTransfer …)`**
  (the extra caps are still in their slots when derived; derive_cap of an untyped cap ran ensure_no_children).
- Generated frames (SpecInvUtG, step 6; proofs/scratch/ut3/mkui.sh, untracked: ut1's gen.py, family `IK UtInv'`, prefix
  ui, skipui.txt = every reachable function but the 28 non-conditional ancestors and the combinators with monadic
  parameters; manual.py: rec_del (finaliseSlot case by `ike_bind_v` + `finaliseCap_nu`) and cap_revoke by `ik_lfp`,
  receiveIpc). 39 lemmas: capDeleteOne, deletingIrqHandler, finaliseCap, recDel, capDelete, capRevoke, doIpcTransfer,
  sendIpc, sendFaultIpc, handleTimeout, endTimeslice, chargeBudget, checkBudget(Restart), doReplyTransfer, handleFault,
  receiveIpc, handleRecv, handleYield, installTcbCap, installTcbFrameCap, invokeIrqControl, invokeFl4IrqControl,
  archInvokeIrqControl, invokeTcb, performAsidPoolInvocation, performDeriveSubframe, performIoportControlInvocation,
  performPageInvocationUnmap, preemptionPath, withoutPreemption, capFaultOnFailure, constOnFailure, emptyOnFailure,
  lookupErrorOnFailure, orChoiceE, unifyFailure.
- Entries (SpecInvUtE): `uiP_invokeCnode`, `uiP_fl4Perform (hI) (hD : DetypeOK σ) (hok : InvOKV (uV σ) inv)`,
  `syscall_postU` (invC's shell), `IKD` (UtInv' kept from UtInv' ∧ DetypeOK), `uiD_handleInvocationR`,
  `uiD_fl4HandleSyscall`, `checkBudget_true` / `checkBudgetRestart_true` (the budget check keeps the view whenever it
  returns True, i.e. whenever the syscall runs), `uiD_fl4HandleEvent`, `ui_handleEvent_other`, `uiD_fl4CallKernel`.
  * **`kentry_utInv (c : Syscall) (hI : UtInv' σ) (hDT : DetypeOK σ) : ∀ y ∈ (fl4KernelEntrySyscall true c σ).1,
    UtInv' y.2`**
  * **`kcall_utInv (rep) (ev : Event) (hI : UtInv' σ) (hDT : DetypeOK σ) : ∀ y ∈ (fl4CallKernel rep ev σ).1, UtInv' y.2`**
  * **`kcall_utInv_other (rep) (ev) (h : ∀ c, ev ≠ .syscallEvent c) (hI : UtInv' σ) : …`** (interrupts, faults, unknown
    syscalls, timer: no premise).
- PREMISE: only ut2's **`DetypeOK σ` [J]** (l4v `untyped_children_in_mdb` + `if_unsafe_then_cap` + `mdb_cte_at`), now
  of the ENTRY state (not of the perform's): every step before the perform keeps the view (`fl4SyscallFaultIP`,
  `updateTimeStamp`, the lookups, the decode, `set_thread_state Restart`; `checkBudgetRestart` whenever it lets the
  syscall run). Used only by the untyped reset and MakePool's detype. Per the lead's note this is a [J] stepping stone,
  not a carried invariant (G4 cannot use it yet). No other premise; no ∀-states hypothesis.
- DetypeOK is NOT inductive on its own (nor with UtInv'): from a state with a CNode object X inside a childless
  untyped's region whose slots hold caps but have no CDT links (UtInv' ∧ DetypeOK hold), CNode Copy from a slot of X
  makes that slot a CDT parent inside the region. What its preservation needs (handoff, L): carry l4v's
  `untyped_children_in_mdb` on the view — `UtChildren σ : ∀ u dev b n fi sl c, capAt σ u = some (untypedCap dev b n fi)
  → capAt σ sl = some c → (objRefs c ∩ region(b,n) ≠ ∅) → sl ∈ descendantsOf u σ.cdt` (needs a spec `objRefs`/obj-range
  per cap: zombies, arch frame/table caps, reply, sc caps) — plus `RegNull`: every slot of an object inside a childless
  untyped's region holds a null cap (l4v gets it from `if_unsafe_then_cap` + `valid_objs`). Then `DetypeOK` follows from
  RegNull + CdtOK (a CDT parent holds a non-null cap). Writers: cap_insert / copies (the new cap has the source's refs;
  its CDT parent is src or src's parent, a descendant of u whenever src is), cap_move/swap (rename), create_cap (child of
  the source untyped), empty_slot (children reparented: descendants of u stay descendants), rec_del's zombies (same
  refs), retype (new objects in u's region: default objects, null slots, and u gains children), the reset/MakePool
  detype (objects removed), and every cap lookup that writes into a slot (the slot's object is referenced by a cap, so
  its untyped has a descendant, so RegNull does not constrain it). The generated `IK` frames carry it once the leaves
  exist (same shape as SpecInvUtG). No counterexample in reachable states.
- No FINDING: no reachable step breaks UtInv'.
- Builds (tokyo, ./ut3.sh untracked: ut2.sh with the full log brought back; mirror warm): ut3-b3 SpecInvUtMv (1040 jobs),
  ut3-b5 SpecInvUtMp (1046), ut3-b12 SpecInvUtD (1048), ut3-b13 SpecInvUtDA (1050), ut3-t1 SpecInvUtA (1052),
  ut3-b17 SpecInvUtG (1054, ~8 min), ut3-b19 SpecInvUtE (1056) + axioms (scratch/ut3/ax.lean, untracked):
  kentry_utInv, kcall_utInv, kcall_utInv_other, uiP_fl4Perform, uiD_handleInvocationR, okv_fl4Decode,
  makePool_utInv', hv_capInsert, hv_capMove, hv_capSwap, hv_setCap_nn, ui_doNormalTransfer, ui_recDel, ui_capRevoke,
  finaliseCap_nu, checkBudgetRestart_true: propext, Classical.choice, Quot.sound. No sorry/admit/native_decide/bv_decide.
  Root Fl4Proofs.lean not rebuilt (eight import lines added).
## ut4 (branch par/ut4 in FL4-tcbj, on 202e731c = int/j2 incl. ut3) — removing `DetypeOK` from the entry (NOT finished)
Goal: `kentry_utInv2` / `kcall_utInv2` over `UtInv''` with no `DetypeOK` premise. Done: the invariant, the derivation
of `DetypeOK`, boot, and the first writers. NOT reached: the remaining writers (rec_del above all), the regenerated
frames and the entry theorems. kentry_utInv / kcall_utInv unchanged. Spec-only, namespace `Fl4Proofs.P3.SInvU`; root
imports SpecInvUtN, SpecInvUtN2.
- The invariant (SpecInvUtN), all on the view `uV` (so every generated `UK` frame keeps it: `ik_utInv''_of_uk`):
  `UtInv'' σ := UtInv' σ ∧ UtNV (uV σ)`, `UtNV` = six facts, each [J] with its l4v counterpart:
  * `UtChV` (l4v `untyped_children_in_mdb`): `capAt u = untypedCap dev b n fi → capAt s = c → r ∈ objRefs c →
    r ∈ delR b n → s ∈ descendantsOf u cdt`.
  * `IfUnsafeV` (l4v `if_unsafe_then_cap`, only for objects inside some untyped region, `InUtV`; l4v's
    `valid_global_refs` keeps the IRQ node / kernel objects out of every untyped range): a non-null slot `p` with
    `InUtV w p.1` has a cap `c'` somewhere with `p.1 ∈ sRefs c'` (`sRefs` = the object of a CNode / thread / Zombie
    cap, l4v `cte_refs`).
  * `CapFreeV` (l4v `valid_caps` + `valid_untyped`): no `objRefs` of any cap lies in an untyped's free part (what a
    new untyped child's region needs for UtCh).
  * `CapKindV` (l4v `valid_caps` typing): `r ∈ objRefs c → r ∈ sRefs c' → shp c = shp c'` (`shp`: CNode bits / TCB /
    Zombie's `Option Nat`). Makes a NON-final CNode/thread cap's other reference slot-holding (an endpoint cap to a
    CNode would otherwise let `finalise_cap` drop the last slot reference).
  * `CnShapeV` (l4v `valid_cap` sizes + Zombie ranges): non-null slots `(r,i)` of an object `r ∈ sRefs c` satisfy
    `SlotShape c i` (CNode: `i.length = bits`; TCB: `i = tcbCnodeIndex k`, k<6; Zombie `r b n`: `i = natToCref
    (zombieCteBits b) k`, k<n). With n=0 / cyclic n=1 this is what makes a removeable Zombie safe to empty.
  * `ZFinalV` (l4v `zombies_final`): no other slot's cap has a Zombie's object in its `objRefs`.
- Derivation: `regNull_of : UtChV w → IfUnsafeV w → RegNullV w` (RegNull: every slot of an object inside a childless
  untyped's region is null), **`detypeOK_of : UtInv'' σ → DetypeOK σ`** (RegNull + CdtOK). So `kentry_utInv` /
  `kcall_utInv` already give `UtInv'` from `UtInv''` with no premise; what is missing is `UtInv''` → `UtInv''`.
  `boot_utInv'' : UtInv'' initASt` (vacuous: only null caps; non-vacuity only, per the 2026-11-20 decision).
- Writers proved:
  * `SafeDelV w s c` (removing `c` from `s` keeps IfUnsafe: every `r ∈ sRefs c` keeps another slot-holding reference,
    or has no non-null slot besides `s`); `utN_vEs`, **`hv_emptySlotN s info : HV (UtInv''V ∧ ∀ c, cap s = c →
    SafeDelV w s c) UtInv''V (emptySlot s info)`** (SpecInvUtN).
  * **`ik_capDeleteOneN sl : IK UtInv'' (capDeleteOne sl)`**, no premise (`fastFinalise` has no outcome for a
    slot-holding cap, `fastFinalise_sRefs`, so `SafeDelV` is trivial).
  * `RefRel c0 c` (derived cap: `objRefs c ⊆ objRefs c0`, same `shp`, not a Zombie, nothing derived from a Zombie, not
    untyped), `DestRefV w dest` (a non-Zombie slot-holding cap references `dest.1` with `SlotShape c1 dest.2`: the
    lookup that found `dest`); `utN_leaf` (any null slot made a CDT leaf under `src` or `src`'s parent),
    **`hv_capInsertN c src dest : HV (UtInv''V ∧ (∀ c0, cap src = c0 → RefRel c0 c) ∧ DestRefV w dest) UtInv''V
    (capInsert c src dest)`** (SpecInvUtN2).
- No FINDING: no writer found to break `UtInv''` in a reachable state (all six hold in every l4v `invs` state; the
  rec_del reasoning below is l4v's `rec_del_invs`).
- HANDOFF (in order; every item is an HV/IK lemma for `UtInv''`, then the ut3 shell is replayed):
  1. Lookup facts → `DestRefV`: `resolveAddressBits` / `lookupSlotForCNodeOp` / `lookupTargetSlot` / the receive
     slot of `getReceiveSlots` return slots `(r,i)` with `r ∈ sRefs c1` of a CNode cap c1 in some slot and `i.length =
     bits` (an `OkV` leaf like ut3's `okv_lookupCapAndSlot`; the root is the thread's `tcbCtable`, itself a slot);
     TCB installs: `dest = (t, tcbCnodeIndex k)` with the invoked `threadCap t` in its slot. Add `DestRefV` for every
     destination to `InvOKV` (SpecInvUtD) and to ut3's transfer loop.
  2. `RefRel` from `derive_cap` / `mask_cap` / `update_cap_data` (`utKeep_mask` / `utKeep_upd` pattern, case split on
     the cap; arch caps: `aobjRef` kept). The untyped copy (ut3's `hv_capInsert_ut`): new cap has `objRefs = ∅`; UtCh
     for the copy needs that caps referencing the region are descendants of the copy — the copy is a fresh leaf, so
     this needs RegNull-style "src childless ⇒ no cap references its region" (UtCh + childless: true).
  3. `create_cap` / retype (ut2's `utInv'_cc(U)`, `hv_ccLoop(U)`): new objects fresh (no cap references them:
     CapFree), default objects have only null slots (IfUnsafe/CnShape vacuous), `defaultCap` references the new object
     with its own shape; UtCh by `dest` child of the source untyped + UtDesc (other untyped caps covering the object
     are ancestors). `DestRefV` for `create_cap`'s destinations (decode, item 1). MakePool / reset: detype removes only
     objects no cap references (UtCh + childless), lowering the free index needs CapFree from the same fact.
  4. `cap_move` / `cap_swap` / `cap_swap_for_delete` (rename: all six are invariant under ut2's slot involution; move's
     destination needs `DestRefV`).
  5. rec_del (the hard part): generalise ut1's `ht_lfp` to a call-dependent PRE (`Pre k σ`), and prove l4v's
     `rec_del_call_spec`: `finaliseSlotCall slot e` ends with `(true, _)` only when `SafeDelV w slot (cap slot)` holds
     (non-final cap: `isFinalCap'` false gives another overlapping slot, `CapKindV` makes it slot-holding; final
     CNode/thread → Zombie written (same `sRefs`, `CnShapeV` gives the Zombie range from the CNode bits / TCB indices,
     `ZFinalV` from finality); removeable Zombie: `CnShapeV` with n=0 / cyclic n=1); `reduceZombieCall`: after
     `cTEDeleteCall (ptr, n) false` the end slot is null or the Zombie changed (finaliseCap's `assert final` kills the
     cyclic-not-exposed branch while the outer Zombie still references `ptr`); the swap for `exposed = false` keeps
     CnShape (the Zombie lands at index 0 < n). Lemma needed: `natToCref bits (ofBl i) = i` for `i.length = bits ≤ 64`.
  6. setCap of a non-null cap in an occupied slot (rec_del's remainder: Zombie of the same object, `sRefs` kept;
     arch-cap updates and untyped free-index writes: `sRefs = ∅`, objRefs kept).
  7. Regenerate SpecInvUtG with family `IK UtInv''` (scratch/ut3/mkui.sh, leaves = `ik_utInv''_of_uk` + the above),
     replay SpecInvUtE with `UtInv''` (the `IKD` / `DetypeOK` plumbing disappears: use `detypeOK_of` at the perform),
     then `kentry_utInv2 (c) (hI : UtInv'' σ) : ∀ y ∈ (fl4KernelEntrySyscall true c σ).1, UtInv'' y.2` and
     `kcall_utInv2`.
- Builds (tokyo, ./ut3.sh, mirror warm): ut4-b3 SpecInvUtN (1058 jobs), ut4-b7 SpecInvUtN2 (1060) (b4–b6: the
  `TransGen.cases_tail` name, fixed with `TransGen.tail'_iff` + `reflTransGen_iff_eq_or_transGen`), ut4-ax1 axioms
  (scratch/ut4/ax.lean, untracked): detypeOK_of, regNull_of, boot_utInv'', hv_emptySlotN, ik_capDeleteOneN,
  hv_capInsertN: propext, Classical.choice, Quot.sound; utN_leaf: propext, Quot.sound; utN_vEs: propext. No sorry/admit/native_decide/bv_decide. Root not rebuilt.
## vfh1 (branch par/vfh1 in FL4-sc, on 9c0fa32d = int/j2 incl. ft3): VfhAll (b)/(c), the cap writers
Goal: VfhAll (l4v valid_tcb's valid_fault_handler of tcb_fault_handler) kept by the syscall entry and every event.
- Key idea: restate VfhAll in vih2's cap view so the 341 generated `hv_*` frames (SpecInvValidIrqHandlersF1..F4,
  `[WLH P] → IKH P f`) keep it for free. `VfhV σ := ∀ p c, capOpt (kheap p) (tcbCnodeIndex 3) = some c →
  capOpt (kheap p) (tcbCnodeIndex 6) = none → validFaultHandler c` (a TCB has caps exactly at 0..5, a well-formed
  CNode holding index 3 has radix 3 so holds index 6, other objects none): **`vfhV_iff : VfhV σ ↔ VfhAll σ`**.
  `validFaultHandler .nullCap` holds (Decode_A: `is_ep_cap ∧ has_handler_rights ∨ NullCap`), so every null write
  (deletion, moves' sources) is harmless.
- DONE, built (5e5ca654; tokyo FL4-invA mirror, tasks vfh1-b1..b4; K 4640 jobs (first build rebuilt the vih cone,
  ~25 min), W 4642, P 4644):
  * SpecInvVfhK: `vfh_Bad σ sl` (sl.2 = idx 3 ∧ index 6 of sl.1 empty: "a TCB's fault-handler slot" in view terms),
    `DomK σ σ'` (no slot emptied; Bad is anti-monotone along it, `vfh_Bad.back`), **`VS σ0 σ := VfhV σ ∧ DomK σ0 σ`**
    (WLH instance; `VK m := ∀ σ0, IK (VS σ0) m`), `vfh_setCap_view` (caps after set_cap), **`vfh_setCap_step`**
    (`vfh_Bad σ sl → validFaultHandler c` suffices), `vs_setCap` (side condition at the anchor σ0), sources of ¬Bad:
    `vfh_notBad_old` (slot holds a non-handler, by VfhV), `vfh_notBad_idx` (index ≠ 3), `vfh_notBad_full` (the
    object holds every index of the slot's length: a CNode slot found through a valid CNode cap); `vs_setCdt`,
    `vs_setOriginal`, `vs_doExtendedOp`, `vs_setIrqState`, `vs_reanchor` (pinned fact at a mid state).
  * SpecInvVfhW: pinned combinators (`ikp_getCap_bind`, `ikpE_getCap_bind`, `ikpE_bind`, `ikp_keep_v`);
    `vs_capInsert src dest (hd : vfh_Bad σ0 dest → vfh newCap)`, `vs_capMove`, `vs_capSwap`, `vs_capSwapForDelete`
    (both slots not Bad), `vs_setUntypedCapAsFull_p`; deletion uniform (VK/VKE): `vs_emptySlot`, `vs_capDeleteOne`,
    `vs_deletingIrqHandler`, `vs_finaliseCap`, `vfh_finaliseCap_rem` (the remainder of a valid fault handler is
    null, so finalise_slot's remainder write into a fault-handler slot is null), `vfh_lfp` (lfp with a
    call-dependent relation), **`vs_recDel k σ (VfhV σ) (vfhRecPre k σ)`** (`vfhRecPre`: the unexposed
    reduce-zombie call's slot not Bad, or its cap a valid handler; at the one call site the slot holds the zombie
    just written: the cap read there was no valid handler since its remainder is a zombie; the swap's other slot
    is the zombie's first slot, index `replicate _ false` ≠ idx 3), `vs_capDelete`, `vs_capRevoke`.
  * SpecInvVfhP: **`vs_invokeCnode i (VCn σ0 i)`** (insert/move/rotate/swap targets not Bad at σ0 or the cap a valid
    handler), `vs_invokeIrqControl (VIrqC)`, `vs_archInvokeIrqControl`, `vs_invokeFl4IrqControl (VFl4IrqC)` (the new
    handler slot not Bad), `vs_invokeIrqHandler` (uniform: the IRQ node slot index `[]`), `vs_installTcbCap`
    (`tcbCnodeIndex n = idx 3 → the cap is valid`), `vs_installTcbFrameCap`, **`vs_invokeTcb i (VTcb i)`** (`VTcb`:
    the fault handler a ThreadControlCaps / ThreadControlSched installs is valid = the decode's check_handler_ep;
    installs into slots 0,1,2,4 are not Bad by index), `vs_transferCapsLoop (∀ s ∈ slots, ¬ vfh_Bad σ0 s)`.
  * Root Fl4Proofs.lean imports K, W, P (root not rebuilt). No sorry/admit/native_decide/bv_decide; no premise.
  * Axioms (proofs/scratch/vfh1/ax.lean in FL4-invA, untracked; task vfh1-ax1): vfhV_iff, vfh_setCap_step, vs_setCap,
    vs_capInsert/Move/Swap/SwapForDelete, vs_emptySlot, vs_finaliseCap, vfh_finaliseCap_rem, vs_recDel, vs_capDelete,
    vs_capRevoke, vs_invokeCnode, vs_invokeIrqControl, vs_invokeFl4IrqControl, vs_invokeIrqHandler, vs_installTcbCap,
    vs_invokeTcb, vs_transferCapsLoop: propext, Classical.choice, Quot.sound.
- NOT DONE (handoff, in order). Everything composes as `IK (VS σ0)` / `IKE (VS σ0)` with the anchor σ0 = the
  decode state (facts proved there survive the frames), `hv_*` for the frame functions:
  1. **The one genuinely missing fact: lookups land in CNode slots.** `resolveAddressBits` returns `(oref, offset)`
     from a `cnodeCap oref radix _` with `offset.length = radix` and never checks `oref`'s type; a CNode cap to a TCB
     with radix 3 would make a CNode insert hit the TCB's slot 3 (not reachable in l4v: valid_cap). Needed as
     **[J] premise at the entry `CnDom σ := ∀ sl p r g, capOpt (σ.kheap sl.1) sl.2 = some (.cnodeCap p r g) → ∀ l :
     CnodeIndex, l.length = r → capOpt (σ.kheap p) l ≠ none`** (l4v: `caps_of_state_valid` + `valid_cap_def`,
     CNodeCap ⇒ `cap_table_at r p`, a well-formed CNode of radix r; FL4: the Rust CNode cap's object is a CNode of
     that size, from the J state relation of the slot caps). It is a view predicate (WLH), so the frames carry it to
     the decode and IPC states; `vfh_notBad_full` turns it into ¬Bad. To prove: `OkDAt σ (fun s sl => full σ sl)`
     for `resolveAddressBits'` (wf recursion as invA manual.py; the root is ct's `tcbCtable` = slot (ct, idx 0), or
     a cap read from a slot), then for `lookupSlotForCnodeOp`/`lookupTargetSlot`/`getReceiveSlots`. CnDom is kept by
     every cap copy (deriveCap/updateCapData keep a CNode cap's pointer and radix) but not by retype (detype): within
     one syscall the transfers after a cap write (ReplyRecv's receive after the reply's grant) need CnDom carried
     through `capInsert` of a derived cap (pinned: the cap came from a slot).
  2. Decode → perform carry (vih2's `okAck_fl4Decode` pattern, OkDAt over `fl4DecodeInvocation`): `VInv σ0 inv`
     = `VCn` (targets from `lookupTargetSlot`/`lookupPivotSlot` + CnDom; insert/mint/move/mutate/rotate/swap),
     `VTcb` (`checkHandlerEp`'s `validFaultHandler` test: decodeSetSpace / decodeSetSchedParams), `VFl4IrqC`
     (handler slot from lookupTargetSlot), arch (IOPort control / DeriveSubframe dest slots from lookupTargetSlot;
     in-place cap updates of the invoked cap's slot: ¬Bad by `vfh_notBad_old` since that slot holds an arch cap at
     σ0 (`okCap_lookupCapAndSlot`)), untyped (below). Then `vs_fl4PerformInvocation (VInv σ0 inv)`.
  3. IPC: `getReceiveSlots` returns ¬Bad slots under CnDom (1); then `doNormalTransfer`/`doIpcTransfer` (fault
     transfers write no cap), `sendIpc`, `receiveIpc`, `doReplyTransfer`, `sendFaultIpc`, `handleFault`,
     `handleTimeout`, `chargeBudget`/`checkBudget(Restart)`/`endTimeslice`/`preemptionPath`/`handleYield` (only via
     sendIpc) — copy the generated FT/hv bodies with `vs_transferCaps` as the leaf and CnDom as a pinned conjunct
     (`VS σ0 σ ∧ CnDom σ`, both view predicates).
  4. Retype (`invokeUntyped(With)`, `fl4InvokeUntyped`, `performAsidControlInvocation`): `retypeRegion` /
     `deleteObjects` keep VfhAll (`ti_retypeRegionWith`, `ti_deleteObjects` with `vfhQ defaultTcb`: null handler)
     but break DomK; `createCap`'s destination slots must be not Bad at the write state: they are not Bad at the
     decode (CnDom) and their CNode is not in the retyped region — ut1's `retype_keeps_old`/`utRet_fresh(_reset)`
     (UtInv at the entry, carried by SpecInvUtF*) give that every old object is kept, so `DomK` holds from the
     decode state to the createCap loop; state this as `vs_invokeUntyped (UtInv σ0) (VUt σ0 inv)`.
  5. The shell (`fl4HandleInvocationR`, `handleRecv`, `fl4HandleSyscall`, `fl4HandleEvent`, `fl4CallKernel`,
     `fl4KernelEntrySyscall`) as ft3's H9/H10 with `I := VS σ ∧ CnDom` (no ct tracking needed), then
     `kentry_vfhAll (rep c) (hJ : CnDom σ) (hU : UtInv σ) : VfhAll σ → ∀ y ∈ entry, VfhAll y.2` and `kcall_vfhAll`
     (every event) by `vfhV_iff`; boot: `boot_vfhAll` (exists).
- No FINDING: every cap write met keeps VfhAll under the l4v facts above (no reachable counterexample: the only
  candidate, a lookup through a CNode cap to a TCB, needs a cap l4v's valid_objs excludes).
## nq1 (branch par/nq1 in FL4-rb, on b987a1fa = int/j2 incl. vih3) — NtfnQB (the queue half of valid_ntfn) and CtEntry from "ct active"
Goal (ft3's handoff): a carried spec invariant giving ft3's per-entry [J] `CtEntry`'s "ct in no notification queue".
- **`NtfnQB σ`** (SpecInvNtfnQ) := `∀ n x t, kheap n = notification x → t ∈ x.ntfnObj.ntfnQueue → ∃ y, kheap t = tcb y ∧
  y.tcbState = blockedOnNotification n` (`ntfnQB_iff`: the `waitingNtfn q` form). Corollaries **`ctEntry_of (ha : ∀ x,
  kheap ct = tcb x → activeSt x.tcbState) : NtfnQB σ → CtEntry σ`**, `ctEntryI_of` (active or idle → `CtEntryI`),
  `ctEntryEv_of`, `boot_ntfnQB`. So a G4 user of ft3's `kentry_faultTcbsS` / `kcall_faultTcbsS` needs only "ct active".
- Carried form `NQ K σ := NtfnQB σ ∧ ∀ u ∈ K, ¬ queued σ u ∧ ¬ BlockedOnNotification` (K = threads whose state may be
  written). One write: `nq_update` with `NqOK` (a TCB keeps its state or is in no queue; a TCB is replaced by a non-TCB
  only if in no queue; a notification's new queue lies in its old one; no BoN state created at a K thread). Leaves:
  setObject (aType kept), set_simple_ko, update_sk_obj_ref, thread_set (state kept), arch_thread_set, as_user, set_mrs,
  set_cap, `tcb_ntfn_dequeue` (post: the dequeued thread is in no queue — NtfnQB puts it in that one queue only),
  `set_thread_state` of a K thread to a non-BoN state, dequeue-then-state-write (`ik_nqdq_sts`), state reads (`nq_rds`:
  a non-BoN state adds the thread to K).
- DONE, built (tokyo, FL4-rb mirror, tasks nq1-b1..b14; root Fl4Proofs.lean imports H1 and C4, root not rebuilt):
  * 00b3e003 SpecInvNtfnQ (above) + SpecInvNtfnQF1..F6 (generated, scratch/nq1/mknq.sh = ft3's gen.py with HYP/AUTO/MANUAL
    env options, manual texts in scratch/nq1/manual.py; skip list skipNQ.txt = ft2's skipFG (all three lines) minus the
    scheduler, plus the untyped / MakePool performs): `NQK K` for 346 functions, among them by hand `cancel_signal`
    (unconditional: the asserted queue member is BoN on it), `cancel_ipc` (post: the thread joins K), `suspend`,
    `reply_unlink_tcb` (the asserted BoReply/BoR state), `blocked_cancel_ipc` / `handle_no_fault` (thread ∈ K).
  * 454227a0 SpecInvNtfnQH1: `nq_ntfn_add`, `nq_tcbNtfnAppend_p` / `nq_reorderNtfn_p` (HK from `TS t n`: t BoN on n),
    `nq_setPriority : NQK K` (BoN targets are never in K), `nq_receiveSignalBlocked` / `nq_receiveSignal (thread ∈ K) :
    HK (NQ K) (NQ (K.filter (· ≠ thread)))`, `nq2_auto` (= nq_auto + nq_rds + failing/impossible branches + the ike_ite
    rules first). SpecInvNtfnQC, C1..C4 (scratch/nq1/mkck.sh, manualCK.py = ft3's manual.py): `CTK c` (cur_thread stays
    c) for the 418 functions of the entry other than the scheduler (switchToThread … schedule, fl4CallKernel,
    fl4KernelEntrySyscall) — used where the spec re-reads ct (perform's sender, ReplyRecv's handle_recv, user faults).
- WRITTEN, NOT BUILDING (uncommitted in FL4-rb, untracked): SpecInvNtfnQG (generated by scratch/nq1/mknq2.sh: the 36
  wake-up / IPC / fault / deletion functions with HYP thread ∈ K: sendIpc, receiveIpc, doReplyTransfer, handleFault,
  handleTimeout, sendSignal, restart, cancelAllSignals, the deletion path, invokeTcb …), SpecInvNtfnQH2 (budget:
  `nq_endTimeslice_p` from a runnable ct, chargeBudget/checkBudget(Restart)/preemptionPath/handleYield; `nq_detype`,
  `nq_deleteObjects_p`, `nq_retype_kh`, `nq_retypeRegionWith_p`, `nq_resetUntypedCap`, `nq_invokeUntyped` (from
  `SInvU.UtInv`, `SInvU.UtRetOK` and [J] `NqDet`), `nq_makePool`, `nq_fl4PerformInvocation`), SpecInvNtfnQH3 (shell
  invariant `Iu ct`, `iu_of`, [W] `NqDecW`, `nq_fl4HandleInvocationR`, `nq_handleRecv`, `nq_fl4HandleSyscall`,
  `checkBudgetRestart_true`, events, `nq_fl4CallKernel_of`, tops `kentry_ntfnQB` / `kcall_ntfnQB`). Build nq1-b13: G
  has exactly 4 errors (all other 32 G lemmas incl. sendIpc, receiveIpc, doReplyTransfer, handleFault elaborate); H2/H3
  never reached (G failed).
  * G errors 3 and 4 (installTcbCap: `IK (NQ K) (NonDetE.liftE …)` left by the plain `ite` split; invokeTcb: timeout,
    the same cause) — fixed in H1's nq2_auto (ike_ite/whenE/unlessE/liftE rules first, as ft3's b_autoE), not rebuilt.
  * **G errors 1 and 2 are the real gap**: `remove_and_restart_ep_queued_thread` / `remove_and_restart_badged_thread`
    (from `cancel_all_ipc` / `cancel_badged_sends`, i.e. every endpoint deletion / badge revoke) read the dequeued
    endpoint thread's state and restart it with no BlockedOnNotification check. NtfnQB alone does not exclude an
    endpoint-queued thread that is BlockedOnNotification and in a notification queue, so NtfnQB is NOT inductive on its
    own. No reachable counterexample (l4v's valid_ep: endpoint-queued threads are BlockedOnSend/Receive on that
    endpoint), so no FINDING — a missing carried fact.
- HANDOFF (in order):
  1. Carry the endpoint half too: `EpQB σ := ∀ e x t, kheap e = endpoint x → t ∈ x.epQueue → ∃ y, kheap t = tcb y ∧
     (BoS on e ∨ BoR on e)` (l4v valid_ep, queue part) inside `NQ` (`NQ K := NtfnQB ∧ EpQB ∧ K-facts`, K-facts also
     "in no endpoint queue" for the writers' threads; a BoS/BoR read adds to K the ntfn facts only, so use two lists or
     record per-thread facts as ft2's B did). Writers to add: `NqOK` (endpoint new queue inside the old one; no TCB
     state change of an endpoint-queued thread), `tcb_ep_dequeue` (dequeued thread leaves every endpoint queue: EpQB
     names its endpoint), `tcb_ep_append` (in sendIpcBlocked / receiveIpcBlocked after the BoS/BoR write; the thread
     leaves K), `reorder_ep` (in set_priority, BoS/BoR target). Then `remove_and_restart_*`: the queue snapshot's
     threads are BoS/BoR, so they join K at the endpoint read (as cancelAllSignals' queue), and G errors 1-2 close.
     Regenerate F (mknq.sh) and G (mknq2.sh); `receive_signal_blocked`'s thread = ct is in no endpoint queue because
     it is running (EpQB). Expect the same 346 + 36 functions; the generic leaf changes are in SpecInvNtfnQ only.
  2. Rebuild G, H2, H3 (`./nqb.sh SpecInvNtfnQH3`, ~8 min for G under load); fix the H2/H3 elaboration errors (never
     compiled yet: expect peeling-shape fixes as in ft3's H8-H10, which H3 mirrors).
  3. Premises of the tops as written (H3): **[J] `NqDet σ`** := the region `delR b n` of every childless untyped cap
     holds no queued thread (l4v if_live_then_nonz_cap + untyped_children_in_mdb; read only by the reset's and
     MakePool's detype); ut1's `SInvU.UtInv σ` (a G1 field, carried); **[W] `NqDecW`**: the front end + decode return
     invocations satisfying `NqDec` (untyped: `SInvU.UtRetOK` at the decode's end state; MakePool: the parent slot holds
     a childless page-sized untyped at the frame) — ut2's handoff step 1, a statement about the decode functions, not
     reachable states. Retype at fresh addresses uses ut1's `utRet_fresh` / `utRet_fresh_after_reset` (a fresh address
     holds no object, so it is in no queue by NtfnQB itself).
  4. Then `kentry_faultTcbsS (ctEntry_of ha hN)` closes ft3's [J] CtEntry from "ct active" (G4: `Entered` +
     `JAtZ.curRun`).
- No sorry/admit/native_decide/bv_decide/axiom in the committed files. `#print axioms` (scratch/nq1/ax.lean, task
  nq1-ax1): ctEntry_of / ctEntryI_of / ctEntryEv_of: propext; boot_ntfnQB, nq_update, nq_tcbNtfnDequeue_post,
  nq_cancelIpc_post, nq_suspend, nq_setPriority, nq_receiveSignal(Blocked), nq_tcbNtfnAppend_p, nq_reorderNtfn_p,
  ct_fl4HandleInvocationR, ct_checkBudgetRestart: propext, Classical.choice, Quot.sound.
