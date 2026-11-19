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
