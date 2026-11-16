/-
P3 (DESIGN.md §9), scheduling contexts (MCS): top module.

* ScRel: the SC relation `ScRel1` (FL4 SC object ↔ l4v `sched_context`).
* ScFrame, ScSpec: frame lemmas for SC writes, spec-side unfolding lemmas.
* ScUnblock: `refill_unblock_check`; ScNtfn: `unblock_sporadic`
  (`WakeHyps.unblock`).
* ScReturn, ScReady, ScReturnRef: `maybe_return_sched_context`, given
  `ActReady`; `ActReady.transfer`.
* ScDonate: `refill_ready`, `refill_sufficient`, the no-donation cases of
  `maybe_donate_sched_context`.
* ScTails: `RecvHyps`' receive/complete tails and `WakeHyps` from the
  donation hypothesis `DonateHyp`.
* ScRelease: the release queue (`SchedRel.rstep`, `release_enqueue_refines`).
* ScResume: `postpone`, `sched_context_resume`.
* ScDonateRef: the donation branch (`donate_refines`, `maybe_donate_refines`,
  `ActReady.donate`).
* ScHyps: `RecvHyps.returnSc` discharged (`returnSc_of`), `DonateHyp` and
  `WakeHyps` from state facts (`DonatePre`).
* ScRing, ScBudgetSpec, ScBudget, ScBudgetTop: `refill_budget_check`
  (`loop0_refines`, `loop1_refines`, `budget_check_refines`).
* ScInv, ScInvQ, ScInvU, ScInvD, ScInvD2, ScInvR: the scheduler invariant
  `Inv` (fragments of l4v `valid_sched`, `valid_refills`, `heap_refs_inv`)
  and its preservation by the refined operations.
* ScIdle: the switch-thread and idle-thread invariant `ActIdle` (l4v
  `valid_sched_action`'s switch-thread clause, the idle thread's facts) and
  its preservation steps.
* ScInvSR: `SchedHyps` and `RecvHyps` for `SRI` (`SchedRel` ∧ `Inv` ∧ `NSC` ∧
  `ActIdle`).
* ScInvB: `budget_check`'s refill facts from `Inv`, and `Inv` after it.
* ScCharge1–ScCharge6: `charge_budget` (`charge_budget_refines`), with
  `end_timeslice` (`end_timeslice_refines`) restoring `Inv`.
* ScCharge7: `check_budget`, `check_budget_restart`.
* ScCharge8: `commit_time` (`InvBut` for the current thread).
* ScConsumed: `update_consumed` (`sched_context_update_consumed`).
* ScCur: the current-thread invariant `CurInv` (l4v `cur_sc_tcb_are_bound`,
  `cur_sc_active`, `ct_not_in_release_q`, current thread not blocked) and
  its preservation steps; `HeadKeeps`.
* ScTime: `update_timestamp` (`update_time_stamp`); `Inv` under a later time.
* ScEntry: the budget path at kernel entry (`budget_ok_refines`,
  `entry_check_budget_refines`) from `Inv` and `CurInv`, ending in `Inv`.
* ScUpdate: `refill_update` (SchedControl `Configure`'s ring update); the SC
  footprint is the object (`ScObj`), so `REFILL_MAX` may change.
* ScHead, ScOffset: the head after a sufficient charge; l4v
  `cur_sc_offset_ready/sufficient` (`OffOK`) and `commit_time_inv`.
* ScSwitch: `switch_sched_context` (unblock check of the incoming SC,
  `commit_time` of the outgoing one), keeping `Inv` and establishing `CurInv`.
* ScSwitchTo: `switch_to_thread`, `switch_to_idle_thread` (arch switch as a
  hypothesis); writing `CUR_THREAD`.
* ScSchedule: `check_domain_time` (one domain), `guarded_switch_to` of a
  ready-queue head, `choose_thread`.
* ScAwaken: `release_remove` of the release queue's head, `awaken` (after
  FL4's TCB timers, a hypothesis), `SchedPre`.
* ScScheduleTop: the switch-thread branch, `schedule` (`schedule_refines`),
  ending in `Inv` and `CurInv`.
* ScConfig: SchedControl `ConfigureFlags` (`configure_flags_refines`):
  `refill_new`/`refill_update` and `sched_context_resume` restore `Inv`;
  `ActIdle` when the action is `resume_cur_thread` at entry.
* ScUnbind: SchedContext `UnbindObject` (thread) and `Unbind`'s TCB step
  (`unbind_tcb_refines`, `unbind_all_tcbs_refines`), ending in `Inv`.
* ScBind: SchedContext `Bind` (thread) (`bind_tcb_refines`), ending in `Inv`.
* ScPlatform: `TimeAgree`, the platform's timer constants against FL4's arch
  interface (`max_release_time`, `min_budget`, exact `us_to_ticks`).
* ScDecode: SchedControl's decode (`decode_sched_control_refines`).
* ScNtfnBind: SchedContext `Bind`/`UnbindObject` for notifications
  (`bind_ntfn_refines`, `unbind_ntfn_refines`).
* ScDecodeCfg: SchedControl's decode composed with `configure_flags`
  (`decode_configure_refines`; `max_refills_cap` is the spec's `absMax`).
* ScCall: the call-stack relation `CallRel` (`sc_replies`, `reply_sc` ↔ the
  SC's `REPLY` word and the replies' next/prev chain, detached replies
  closed), the replies' placement `RPlaced`; ScCallOps, ScCallFoot: its
  frames (`SFoot`: the scheduler's writes keep the call-stack words).
* ScCallUnbind: `Unbind`'s reply step (`unbind_reply_refines`).
* ScDonateB: `sched_context_donate` of a bound SC (`donate_bound_refines`).
* ScCallPush, ScCallPushRef: `reply_push`'s donation tail
  (`push_donate_refines`: `bind_sc_reply`, `sched_context_donate`).
* ScCallPop, ScCallPopRef: `reply_pop` (`reply_pop_refines`:
  `reply_unlink_sc` of the head, the donation back).
* ScCallCut, ScCallRemove: `reply_remove` (`reply_remove_refines`: the head
  popped, a reply further down cut out with the older ones, a detached one
  spliced out).
* ScYield, ScYieldTo: the yield-to relation `YieldRel` (`tcb_yield_to` ↔ the
  TCB's `YIELD_TO` word, the yield pairs), `complete_yield_to`,
  `set_consumed` (its message writes the Ep side's `MsgOK`), SchedContext
  `YieldTo` (`yield_to_refines`, `yieldto_invoke_refines`, with `ActIdle`)
  and `Consumed` (`sc_consumed_refines`).
* ScFoot: `CKeep` (what the call-stack relation reads of the spec, kept).
* ScCallUnlink: `reply_unlink` (`reply_unlink_refines`, l4v
  `reply_unlink_tcb`) and `reply_remove` in full (`reply_remove_full_refines`,
  l4v `reply_remove`), keeping `RFree` (free replies detached and unlinked,
  ScCallOps; `RFree.push_ready` gives `reply_push` its isolated reply).
* ScKFoot: the scheduling-context code's footprints (`SFoot`: TCB words past
  offset 256 other than `MCP` and `YIELD_TO`, and the node; `KFoot`: also the
  notifications' and the SCs' words other than `REPLY`), the queue and
  unblock-check footprints; ScYield's `TFoot` adds the `YIELD_TO` words.
* ScDecodeSc: the SchedContext labels (the YieldTo checks,
  `yieldto_branch_refines`, with the MCP relation `McpRel`; Bind and
  UnbindObject, `bind_branch_refines`, `unbindobj_branch_refines`; Unbind,
  `unbind_invoke_refines`, carrying the call-stack relation; Consumed), each
  with its footprint and the spec's `SOK`.
* ScMcp: `McpRel` across steps (`McpRel.frame`, `McpRel.set`) and
  `set_mcp_refines` (l4v `set_mcpriority`); `hback_of_tsc` (P1's `TSc`).
* ScPres, ScPresOps: what the spec's SchedContext invocations keep (`SOK`:
  CNodes, TCB caps and MCPs, object kinds and SC sizes, CDT, domain
  schedule; with flags, the yield-to links and the call stacks), by `Pres`
  over the monad.
* ScKeep: the relations' frames from `SOK` and the footprints
  (`KFoot.keep`, `TFoot.keep`, `RFoot.keep`).
* ScDecodeAll: SchedContext invocation decode over every label
  (`sc_decode_refines`), ending in every relation (`ScAll`).
* ScTop: the SchedContext cap at the top level (`decode_invocation_sched_context`
  for `DecOK`, `domFrame_sched_context`, `decode_invocation_sched_contextD`),
  the CSpace relation kept by `crel_of_sok` given `SlotsApart`.
* ScPresCfg: `Pres` for SchedControl `ConfigureFlags` (`commit_time`,
  `refill_new`, `refill_update`, `possible_switch_to`).
* ScTopCfg: the placement record `ScPlaced`; the SchedControl cap at the top
  level (`decode_invocation_sched_control`, `domFrame_sched_control`,
  `decode_invocation_sched_controlP`), `decode_invocation_sched_contextP`.
* ScTcb: the scheduler-side TCB labels of `tcb::decode` (`TcbOK`):
  SetMCPriority, SetPriority (`SetPrioHyp`), Bind/UnbindNotification,
  SetSchedParams (`SchedTailHyp`); the CSpace-keeping steps `CK`/`PresC`; with
  the frame invariant (`TcbOKF`).
* ScTcbHyp: `SetPrioHyp` discharged (`setPrioHyp_of`: P1's `set_priority.blk`,
  `KWOut`, `setPriority_some`); `SchedTailHyp` reduced to the SC step
  (`schedTailHyp_of`, `ScTailHyp`).
* ScTopF: the SchedContext and SchedControl caps with the frame invariant
  (`DecOKF`, `DecOKDF`).
* ScSpecStep: `ScSpecHyp` (`scSpecHyp_of`): the SC step's no-change and
  unbind cases (`PresV`/`VK` across `set_mcpriority` and `set_priority`), the
  bind as `BindSpecHyp`.
* ScBindSpec: `BindSpecHyp` (`bindSpecHyp_of`): the spec's SC bind has an
  outcome (`schedContextBindTcb_some`: the merge loop, the unblock check,
  `sched_context_resume`/`postpone`, `ActReady` before the final
  `reschedule_required`), from `BindOK` after the install.
* ScInstFoot: FL4's `empty_slot` and `insert` write only cap-slot words
  (`empty_ws`, `insert_ws`); with the placement `SlotCapW`, the slot part
  `hslot` of P1's `install_tcb_cap.cai` (`inst_hslot`).
* ScInstSpec: the spec's install keeps the scheduler side (`SK`, `PSK`,
  `install_sk` over a null or non-final old cap); `SpecPost` after the
  caller's restart from `Inv` and the decoder's checks `ScDec`
  (`specPost_restart`) and across `SK`.
* ScCancelFrame: what the spec's `cancel_all_ipc` keeps (`Fr`, with the
  SCs, the ready and release queues, the current thread, the caps, the CDT
  and the original flags; `cancelAllIpc_fr`), `SpecPost` across it
  (`SpecPost.cancel`), and the spec's `cap_delete` of a slot holding an
  endpoint cap (`capDelete_ep_post`, by a pre-fixed point of `rec_del`).
* ScInstPost: `SchedTailHyp` discharged (`schedTailHyp_disch`: P1's
  `install_tcb_cap.cai` with `FhSlotHyp`, `conds_caifr`; `install_sk`, or
  `finEpSpecHyp` for a final endpoint cap), `hRT_of`/`hRS_of` from the
  scheduler relations, and SetSchedParams end to end
  (`tcb_set_sched_params_refines_disch`).
* ScPlace: the joint P1/P3 placement invariant `JPlaced` (P3's typed heap
  against P1's heap `H` and its sets), the placement hypotheses derived
  from it (`JPlaced.ssp`, `JPlaced.kwOut`, `JPlaced.slotCapW`,
  `ntfnP1Hyp_of`, `replyP1Hyp_of`), and its frames (`JPlaced.step`,
  `JPlaced.same`).
-/
import Fl4Proofs.P3.ScBudgetTop
import Fl4Proofs.P3.ScInvB
import Fl4Proofs.P3.ScCharge8
import Fl4Proofs.P3.ScConsumed
import Fl4Proofs.P3.ScEntry
import Fl4Proofs.P3.ScSchedule
import Fl4Proofs.P3.ScScheduleTop
import Fl4Proofs.P3.ScConfig
import Fl4Proofs.P3.ScUnbind
import Fl4Proofs.P3.ScBind
import Fl4Proofs.P3.ScDecode
import Fl4Proofs.P3.ScNtfnBind
import Fl4Proofs.P3.ScDecodeCfg
import Fl4Proofs.P3.ScCallRemove
import Fl4Proofs.P3.ScCallPushRef
import Fl4Proofs.P3.ScCallUnbind
import Fl4Proofs.P3.ScYieldTo
import Fl4Proofs.P3.ScDecodeSc
import Fl4Proofs.P3.ScMcp
import Fl4Proofs.P3.ScDecodeAll
import Fl4Proofs.P3.ScTop
import Fl4Proofs.P3.ScTopCfg
import Fl4Proofs.P3.ScTcb
import Fl4Proofs.P3.ScTcbHyp
import Fl4Proofs.P3.ScTopF
import Fl4Proofs.P3.ScSpecStep
import Fl4Proofs.P3.ScBindSpec
import Fl4Proofs.P3.ScInstFoot
import Fl4Proofs.P3.ScInstSpec
import Fl4Proofs.P3.ScCancelFrame
import Fl4Proofs.P3.ScInstPost
import Fl4Proofs.P3.ScPlace
