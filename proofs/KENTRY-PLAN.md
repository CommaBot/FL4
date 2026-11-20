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
