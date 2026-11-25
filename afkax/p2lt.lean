import Fl4Proofs.P2.FootTimerIrqRG
import Fl4Proofs.P2.FootTimerIrqRSt
import Fl4Proofs.P2.FootTimerIrqRD
import Fl4Proofs.P2.FootTimerIrqRB
import Fl4Proofs.P2.FootTimerIrqRS
import Fl4Proofs.P2.FootTimerIrqRC
import Fl4Proofs.P2.FootTimerIrqRF
import Fl4Proofs.P2.FootTimerIrqRW
import Fl4Proofs.P2.FootTimerIrqRM
import Fl4Proofs.P2.FootTimerIrqRT
import Fl4Proofs.P2.FootTimerIrqCh
import Fl4Proofs.P2.FootTimerIrqApp
import Fl4Proofs.P2.FootTimerIrqRR
import Fl4Proofs.P2.FootTimerIrqAcc
import Fl4Proofs.P2.FootTimerSetMv
import Fl4Proofs.P2.FootTimerIrqH
import Fl4Proofs.P2.FootTimerIrqW
import Fl4Proofs.P2.FootTimerIrqQF
import Fl4Proofs.P2.FootTimerIrqRe
#print axioms Fl4Proofs.P2.set_timer_accG
#print axioms Fl4Proofs.P2.set_timer_move
#print axioms Fl4Proofs.P2.set_timer_localPathM
#print axioms Fl4Proofs.P2.fire_ok.guard
#print axioms Fl4Proofs.P2.plan_objects.guard
#print axioms Fl4Proofs.P2.round_robin_ok.guard
#print axioms Fl4Proofs.P2.interrupt.irq_state.guard
#print axioms Fl4Proofs.P2.interrupt.handle_interrupt.guard_timer
#print axioms Fl4Proofs.P2.sched.check_budget.guard_suf
#print axioms Fl4Proofs.P2.irq_accept_walk
#print axioms Fl4Proofs.P2.check_budget_suf
#print axioms Fl4Proofs.P2.handle_interrupt_timer
#print axioms Fl4Proofs.P2.handle_interrupt_timer_writes
#print axioms Fl4Proofs.P2.nodue_hw
#print axioms Fl4Proofs.P2.rel_hw
#print axioms Fl4Proofs.P2.action_hw
#print axioms Fl4Proofs.P2.irq_quiet_schedule
#print axioms Fl4Proofs.P2.activate_fp
#print axioms Fl4Proofs.P2.irq_quiet_foot
#print axioms Fl4Proofs.P2.irq_replay
#print axioms Fl4Proofs.P2.vcpu.check.guard_nvm
#print axioms Fl4Proofs.P2.activate_thread.gw
#print axioms Fl4Proofs.P2.irq_quiet_pre
#print axioms Fl4Proofs.P2.irq_accG_quiet_walk
#print axioms Fl4Proofs.P2.irq_accG_quiet
#print axioms Fl4Proofs.P2.sched.charge_budget.guard_rr
#print axioms Fl4Proofs.P2.sched.reschedule_required.guard_resume
#print axioms Fl4Proofs.P2.reschedule_required_resume
#print axioms Fl4Proofs.P2.faults.valid_timeout_handler.guard
#print axioms Fl4Proofs.P2.sched.end_timeslice.guard_rr
#print axioms Fl4Proofs.P2.cbTail.guard
#print axioms Fl4Proofs.P2.tq_append_empty
#print axioms Fl4Proofs.P2.tq_append_ne
#print axioms Fl4Proofs.P2.sched.q_get.guard
#print axioms Fl4Proofs.P2.sched.q_set.guard
#print axioms Fl4Proofs.P2.sched.set_flag.guard
#print axioms Fl4Proofs.P2.tcbqueue.append.guard_sched
#print axioms Fl4Proofs.P2.sched.add_to_bitmap.guard
#print axioms Fl4Proofs.P2.smp.remote_queue_update.guard_local
#print axioms Fl4Proofs.P2.sched.append.guard_local
#print axioms Fl4Proofs.P2.tq_remove_single
#print axioms Fl4Proofs.P2.tcbqueue.prev.guard_sched
#print axioms Fl4Proofs.P2.tcbqueue.next.guard_sched
#print axioms Fl4Proofs.P2.tcbqueue.remove.guard_single
#print axioms Fl4Proofs.P2.sched.remove_from_bitmap.guard
#print axioms Fl4Proofs.P2.sched.dequeue.guard_single
#print axioms Fl4Proofs.P2.sched.switch_to_thread.guard
#print axioms Fl4Proofs.P2.sched.choose_thread.guard_ne
#print axioms Fl4Proofs.P2.sched.schedule_choose_new_thread.guard
#print axioms Fl4Proofs.P2.schedule_choose_eq
#print axioms Fl4Proofs.P2.sched.schedule.guard_choose
#print axioms Fl4Proofs.P2.end_timeslice_rr
#print axioms Fl4Proofs.P2.append_keep
#print axioms Fl4Proofs.P2.sched.end_timeslice.guard_rrT
#print axioms Fl4Proofs.P2.cbTail.guard_rr
#print axioms Fl4Proofs.P2.putS2_frame
#print axioms Fl4Proofs.P2.cbRR_frame
#print axioms Fl4Proofs.P2.sched.charge_budget.guard_rrC
#print axioms Fl4Proofs.P2.sched.check_budget.guard_rr
#print axioms Fl4Proofs.P2.round_robin_ok_true
#print axioms Fl4Proofs.P2.refill_putS_ne
#print axioms Fl4Proofs.P2.cbRR_head
#print axioms Fl4Proofs.P2.rr_wr_out
#print axioms Fl4Proofs.P2.rr_sufficient
#print axioms Fl4Proofs.P2.rr_queue
#print axioms Fl4Proofs.P2.rr_tail_F
#print axioms Fl4Proofs.P2.highest_prio_app
#print axioms Fl4Proofs.P2.charge_budget_rr_run
#print axioms Fl4Proofs.P2.is_schedulable_rel
#print axioms Fl4Proofs.P2.rr_run_writes
#print axioms Fl4Proofs.P2.highest_prio_agree
#print axioms Fl4Proofs.P2.check_budget_ins
#print axioms Fl4Proofs.P2.rrw_keep
#print axioms Fl4Proofs.P2.rr_cb_state
#print axioms Fl4Proofs.P2.rr_nodue
#print axioms Fl4Proofs.P2.rr_rel
#print axioms Fl4Proofs.P2.dequeue_single_writes
#print axioms Fl4Proofs.P2.rr_choose
#print axioms Fl4Proofs.P2.sq_dt
#print axioms Fl4Proofs.P2.rr_s3
#print axioms Fl4Proofs.P2.irq_accG_rr_walk
#print axioms Fl4Proofs.P2.irq_accG_rr
