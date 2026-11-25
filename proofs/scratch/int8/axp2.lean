import Fl4Proofs.P2.AccessCSpace
import Fl4Proofs.P2.AccessFastFault
import Fl4Proofs.P2.AccessFastRR
import Fl4Proofs.P2.AccessFault
import Fl4Proofs.P2.AccessIo
import Fl4Proofs.P2.AccessIoDec
import Fl4Proofs.P2.AccessIoEnt
import Fl4Proofs.P2.AccessIoFin
import Fl4Proofs.P2.AccessIoInv
import Fl4Proofs.P2.AccessIoKeep
import Fl4Proofs.P2.AccessIoMid
import Fl4Proofs.P2.AccessIoMv
import Fl4Proofs.P2.AccessIoObl
import Fl4Proofs.P2.AccessIoRa
import Fl4Proofs.P2.AccessIoSw
import Fl4Proofs.P2.AccessIoWalk
import Fl4Proofs.P2.AccessLeaf
import Fl4Proofs.P2.AccessRefill
import Fl4Proofs.P2.AccessReply
import Fl4Proofs.P2.AccessSc
import Fl4Proofs.P2.AccessSched
import Fl4Proofs.P2.AccessSwitch
import Fl4Proofs.P2.AccessSwitchTo
import Fl4Proofs.P2.AccessSyscall
import Fl4Proofs.P2.AccessTail
import Fl4Proofs.P2.AccessVm
import Fl4Proofs.P2.AccessVmAcc
import Fl4Proofs.P2.AccessVmDec
import Fl4Proofs.P2.AccessVmF
import Fl4Proofs.P2.AccessVmLP
import Fl4Proofs.P2.AccessVmMv
import Fl4Proofs.P2.AccessVmObl
import Fl4Proofs.P2.AccessVmPre
import Fl4Proofs.P2.AccessVmRR
import Fl4Proofs.P2.AccessVmRRA
import Fl4Proofs.P2.AccessVmRRD
import Fl4Proofs.P2.AccessVmRRL
import Fl4Proofs.P2.AccessVmRRM
import Fl4Proofs.P2.AccessVmRRO
import Fl4Proofs.P2.AccessVmTail
import Fl4Proofs.P2.AllCores
import Fl4Proofs.P2.AllKeep
import Fl4Proofs.P2.AllSched
import Fl4Proofs.P2.AllStep
import Fl4Proofs.P2.BlkUCheck
import Fl4Proofs.P2.DecSl
import Fl4Proofs.P2.E2E
import Fl4Proofs.P2.E2EWitness
import Fl4Proofs.P2.FootIoport
import Fl4Proofs.P2.FootN
import Fl4Proofs.P2.FootN10
import Fl4Proofs.P2.FootN2
import Fl4Proofs.P2.FootN3
import Fl4Proofs.P2.FootN4
import Fl4Proofs.P2.FootN5
import Fl4Proofs.P2.FootN6
import Fl4Proofs.P2.FootN7
import Fl4Proofs.P2.FootN8
import Fl4Proofs.P2.FootN9
import Fl4Proofs.P2.FootSlDefs
import Fl4Proofs.P2.FootSlEntry
import Fl4Proofs.P2.FootSlFault
import Fl4Proofs.P2.FootSlRR
import Fl4Proofs.P2.FootSlTail
import Fl4Proofs.P2.FootSyscall
import Fl4Proofs.P2.FootTimer
import Fl4Proofs.P2.FootTimerAcc
import Fl4Proofs.P2.FootTimerAccLoop
import Fl4Proofs.P2.FootTimerFin
import Fl4Proofs.P2.FootTimerGE
import Fl4Proofs.P2.FootTimerGEIns
import Fl4Proofs.P2.FootTimerGELoop
import Fl4Proofs.P2.FootTimerGERem
import Fl4Proofs.P2.FootTimerIns
import Fl4Proofs.P2.FootTimerIrqAcc
import Fl4Proofs.P2.FootTimerIrqApp
import Fl4Proofs.P2.FootTimerIrqCh
import Fl4Proofs.P2.FootTimerIrqDec
import Fl4Proofs.P2.FootTimerIrqF
import Fl4Proofs.P2.FootTimerIrqFC
import Fl4Proofs.P2.FootTimerIrqG
import Fl4Proofs.P2.FootTimerIrqH
import Fl4Proofs.P2.FootTimerIrqLP
import Fl4Proofs.P2.FootTimerIrqObl
import Fl4Proofs.P2.FootTimerIrqOwn
import Fl4Proofs.P2.FootTimerIrqQ
import Fl4Proofs.P2.FootTimerIrqQF
import Fl4Proofs.P2.FootTimerIrqRB
import Fl4Proofs.P2.FootTimerIrqRC
import Fl4Proofs.P2.FootTimerIrqRD
import Fl4Proofs.P2.FootTimerIrqRF
import Fl4Proofs.P2.FootTimerIrqRG
import Fl4Proofs.P2.FootTimerIrqRM
import Fl4Proofs.P2.FootTimerIrqRR
import Fl4Proofs.P2.FootTimerIrqRS
import Fl4Proofs.P2.FootTimerIrqRSt
import Fl4Proofs.P2.FootTimerIrqRT
import Fl4Proofs.P2.FootTimerIrqRW
import Fl4Proofs.P2.FootTimerIrqRe
import Fl4Proofs.P2.FootTimerIrqW
import Fl4Proofs.P2.FootTimerSet
import Fl4Proofs.P2.FootTimerSetLP
import Fl4Proofs.P2.FootTimerSetMv
import Fl4Proofs.P2.FootTimerTree
import Fl4Proofs.P2.FootVm
import Fl4Proofs.P2.GSt
import Fl4Proofs.P2.GuardGE
import Fl4Proofs.P2.InvAff
import Fl4Proofs.P2.InvImpl
import Fl4Proofs.P2.InvKeep
import Fl4Proofs.P2.InvStall
import Fl4Proofs.P2.MoveGap
import Fl4Proofs.P2.MoveOwn
import Fl4Proofs.P2.MoveSl
import Fl4Proofs.P2.MoveStale
import Fl4Proofs.P2.MoveSyscall
import Fl4Proofs.P2.OwnJAtZ
import Fl4Proofs.P2.OwnLayout
import Fl4Proofs.P2.OwnMap
import Fl4Proofs.P2.PathAgree
import Fl4Proofs.P2.PathBridge
import Fl4Proofs.P2.PathObl
import Fl4Proofs.P2.ReadGap
import Fl4Proofs.P2.Runtime
import Fl4Proofs.P2.SafeCert
import Fl4Proofs.P2.SafeGap
import Fl4Proofs.P2.SerExit
import Fl4Proofs.P2.Serial
import Fl4Proofs.P2.SerialSafe
import Fl4Proofs.P2.SlAccJ
import Fl4Proofs.P2.SlAccL
import Fl4Proofs.P2.SlDecG
import Fl4Proofs.P2.SlDecL
import Fl4Proofs.P2.SlEntJ
import Fl4Proofs.P2.SlHereJ
import Fl4Proofs.P2.SlHome
import Fl4Proofs.P2.SlLay
import Fl4Proofs.P2.SlObl
import Fl4Proofs.P2.SlThr
import Fl4Proofs.P2.StallAll
import Fl4Proofs.P2.StallAt
import Fl4Proofs.P2.StallBase
import Fl4Proofs.P2.StallFull
import Fl4Proofs.P2.StallLawNote
import Fl4Proofs.P2.StallPost
import Fl4Proofs.P2.StallView
import Fl4Proofs.P2.XferN
import Fl4Proofs.P1.EntryVacuous
import Fl4Proofs.P2.FootTimerSetG
import Fl4Proofs.P2.FootTimerSetAcc
import Fl4Proofs.P2.MoveTimer
import Fl4Proofs.P2.FootTimerSetOwn
import Fl4Proofs.P2.FootTimerSetObl

-- from proofs/scratch/p2c/ax5.lean
section
open Fl4Proofs.P2.MoveGap
#print axioms mown_deciders
#print axioms mown_move_alt
#print axioms body_not_safe
#print axioms mown_not_moveLocal
#print axioms Fl4Proofs.P2.Serial.moveV_transfer
#print axioms Fl4Proofs.P2.OwnMap.moveLocal
end

-- from proofs/scratch/p2c/ax6.lean
section
#print axioms Fl4Proofs.P2.E2E.serializable_e2e
#print axioms Fl4Proofs.P2.ReadGap.isProg_pOnce
#print axioms Fl4Proofs.P2.ReadGap.not_once_pTwice
end

-- from proofs/scratch/p2vm/ax13.lean
section
open Aeneas Aeneas.Std Result
open Fl4Proofs.P2.PathObl in
#print axioms syscall.handle_vm_fault_local.guard_acc
open Fl4Proofs.P2.PathObl in
#print axioms vm_acc_of_tail
open Fl4Proofs.P2.PathObl in
#print axioms VmMidF.preRW
open Fl4Proofs.P2.PathObl in
#print axioms VmMidF.chk
open Fl4Proofs.P2.PathObl in
#print axioms vm_queue
open Fl4Proofs.P2.PathObl in
#print axioms fastFaultG_checks
open Fl4Proofs.P2.PathObl in
#print axioms faultTailG_split
open Fl4Proofs.P2.PathObl in
#print axioms vmPre14.guard
open Fl4Proofs.P2.PathObl in
#print axioms faultTail3.guard
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
end

-- from proofs/scratch/p2vm/ax14.lean
section
open Fl4Proofs.P2.PathObl
#print axioms vm_acc
#print axioms faultTail3.guardVm
#print axioms VmMidF.tailAcc
#print axioms vmPre14_eq1
#print axioms vmPre2_eq
#print axioms syscall.handle_vm_fault_local.guard_acc
end

-- from proofs/scratch/p2vm/ax15.lean
section
open Fl4Proofs.P2.PathObl
#print axioms vm_acc
#print axioms faultTail3.guardVm
#print axioms VmMidF.tailAcc
#print axioms syscall.handle_vm_fault_local.guard_acc
#print axioms vm_fault_guard_dec
#print axioms vm_local_guard_dec
#print axioms vm_dfOf
#print axioms vm_chk_back
#print axioms vm_alt_not_acc
#print axioms vm_dec_tr
#print axioms vm_dec_m
#print axioms vm_dec_alt
#print axioms VmRep.aligned
#print axioms once_of_guard
#print axioms vm_total
#print axioms vm_pathObl
#print axioms vm_pathSide
#print axioms vm_readOnce
end

-- from proofs/scratch/p2vm/ax16.lean
section
open Fl4Proofs.P2.PathObl
#print axioms vm_acc
#print axioms faultTail3.guardVm
#print axioms VmMidF.tailAcc
#print axioms syscall.handle_vm_fault_local.guard_acc
#print axioms vm_fault_guard_dec
#print axioms vm_local_guard_dec
#print axioms vm_dfOf
#print axioms vm_chk_back
#print axioms vm_alt_not_acc
#print axioms vm_dec_tr
#print axioms vm_dec_m
#print axioms vm_dec_alt
#print axioms VmRep.aligned
#print axioms once_of_guard
#print axioms vm_total
#print axioms vm_pathObl
#print axioms vm_pathSide
#print axioms vm_readOnce
#print axioms vm_accG
#print axioms vm_acc_of_tail
#print axioms vmWd_notDecW
#print axioms vm_acc_gd
#print axioms vm_move
#print axioms vm_pathObl_mv
end

-- from proofs/scratch/p2vm/ax17.lean
section
open Fl4Proofs.P2.PathObl
#print axioms vm_acc
#print axioms faultTail3.guardVm
#print axioms VmMidF.tailAcc
#print axioms syscall.handle_vm_fault_local.guard_acc
#print axioms vm_fault_guard_dec
#print axioms vm_local_guard_dec
#print axioms vm_dfOf
#print axioms vm_chk_back
#print axioms vm_alt_not_acc
#print axioms vm_dec_tr
#print axioms vm_dec_m
#print axioms vm_dec_alt
#print axioms VmRep.aligned
#print axioms once_of_guard
#print axioms vm_total
#print axioms vm_pathObl
#print axioms vm_pathSide
#print axioms vm_readOnce
#print axioms vm_accG
#print axioms vm_acc_of_tail
#print axioms vmWd_notDecW
#print axioms vm_acc_gd
#print axioms vm_move
#print axioms vm_pathObl_mv
#print axioms faults.handle_fault_reply.guardVm
#print axioms fastpath_vm.reply_recv_vm_found.guard
end

-- from proofs/scratch/p2vm/ax18.lean
section
open Fl4Proofs.P2.PathObl
#print axioms vm_acc
#print axioms faultTail3.guardVm
#print axioms VmMidF.tailAcc
#print axioms syscall.handle_vm_fault_local.guard_acc
#print axioms vm_fault_guard_dec
#print axioms vm_local_guard_dec
#print axioms vm_dfOf
#print axioms vm_chk_back
#print axioms vm_alt_not_acc
#print axioms vm_dec_tr
#print axioms vm_dec_m
#print axioms vm_dec_alt
#print axioms VmRep.aligned
#print axioms once_of_guard
#print axioms vm_total
#print axioms vm_pathObl
#print axioms vm_pathSide
#print axioms vm_readOnce
#print axioms vm_accG
#print axioms vm_acc_of_tail
#print axioms vmWd_notDecW
#print axioms vm_acc_gd
#print axioms vm_move
#print axioms vm_pathObl_mv
#print axioms faults.handle_fault_reply.guardVm
#print axioms fastpath_vm.reply_recv_vm_found.guard
#print axioms syscall.handle_reply_recv_vm_local.guard_acc
end

-- from proofs/scratch/p2vm/ax19.lean
section
open Fl4Proofs.P2.PathObl
#print axioms syscall.handle_reply_recv_vm_local.guard_acc
#print axioms rrX_mem
#print axioms rrX_tcb
#print axioms rrX_out
#print axioms VmBase.ntfnRd
#print axioms rr_u_home
#print axioms VmRPre.rrAccV
#print axioms rr_vm_accG
#print axioms rr_vm_acc
end

-- from proofs/scratch/p2vm/ax20.lean
section
open Fl4Proofs.P2.PathObl
#print axioms rr_vm_accG
#print axioms rr_vm_acc
#print axioms rr_acc_gd
#print axioms rr_move
#print axioms rr_total
end

-- from proofs/scratch/p2vm/ax21.lean
section
open Fl4Proofs.P2.PathObl
#print axioms rrTail_fst
#print axioms rr_found_chk
#print axioms rr_found_guard_dec
#print axioms rr_local_guard_dec
#print axioms rr_dr
#print axioms rr_chk_back
#print axioms rr_alt_not_acc
#print axioms rr_dec_tr
#print axioms rr_dec_top
#print axioms rr_dec_alt
#print axioms rr_pathObl
#print axioms rr_pathSide
#print axioms rr_readOnce
end

-- from proofs/scratch/p2vm/ax22.lean
section
open Fl4Proofs.P2.PathObl
#print axioms vm_localPath
#print axioms rr_localPath
end

-- from proofs/scratch/p2j14_ax.lean
section
#print axioms Fl4Proofs.P1.sched.schedule.sN
#print axioms Fl4Proofs.P1.sched.awaken_loop.kwN
#print axioms Fl4Proofs.P1.cand_choose.sN
#print axioms Fl4Proofs.P1.sched.schedule_choose_new_thread.sN
#print axioms Fl4Proofs.P1.sched.set_next_interrupt.sN
#print axioms Fl4Proofs.P1.KpAff.step
#print axioms Fl4Proofs.P1.sched.schedule.cur
#print axioms Fl4Proofs.P2.Stall.AllCores.sched
#print axioms Fl4Proofs.P1.cand_choose.cur
#print axioms Fl4Proofs.P1.sched.switch_to_thread.cur
end

-- from proofs/scratch/p2j15_ax.lean
section
#print axioms Fl4Proofs.P2.Stall.FFoot.okeep
#print axioms Fl4Proofs.P2.Stall.FFoot.cur
#print axioms Fl4Proofs.P2.Stall.FireKeep.ofFF
#print axioms Fl4Proofs.P2.Stall.schedcontext.donate.ff
#print axioms Fl4Proofs.P2.Stall.FFoot.trans
#print axioms Fl4Proofs.P2.Stall.notification.maybe_donate_sched_context.ff
#print axioms Fl4Proofs.P2.Stall.AllCores.step2
#print axioms Fl4Proofs.P2.Stall.CoreInv.keep2
#print axioms Fl4Proofs.P2.Stall.AllCores.sched
#print axioms Fl4Proofs.P2.Stall.signal_tail.ff
#print axioms Fl4Proofs.P2.Stall.signal_vm.ff
#print axioms Fl4Proofs.P2.Stall.notification.maybe_donate_sched_context.ffB
#print axioms Fl4Proofs.P2.Stall.FK.trans
#print axioms Fl4Proofs.P2.Stall.FFoot.fk
#print axioms Fl4Proofs.P2.Stall.FireKeep.ofFK
#print axioms Fl4Proofs.P2.Stall.FK.refl
#print axioms Fl4Proofs.P2.Stall.OKeep2.ofWst
#print axioms Fl4Proofs.P2.Stall.sched.set_thread_state.fk
#print axioms Fl4Proofs.P2.Stall.vcpu.report.fk
#print axioms Fl4Proofs.P2.Stall.ipc.cancel_ipc.kwNR
#print axioms Fl4Proofs.P2.Stall.FFoot.fki
#print axioms Fl4Proofs.P2.Stall.FCtx.step
#print axioms Fl4Proofs.P2.Stall.vcpu.report.fki
#print axioms Fl4Proofs.P2.Stall.notification.send_signal.fk
#print axioms Fl4Proofs.P2.Stall.TW.fn
#print axioms Fl4Proofs.P2.Stall.timer.fire_loop.fki
#print axioms Fl4Proofs.P2.Stall.timer.fire.fki
#print axioms Fl4Proofs.P2.Stall.FCtx.ofAll
#print axioms Fl4Proofs.P2.Stall.AllCores.schedF
#print axioms Fl4Proofs.P2.Stall.sched.schedule.idl
#print axioms Fl4Proofs.P2.Stall.stallAt.all
#print axioms Fl4Proofs.P2.Stall.stallAt.views
end

-- from proofs/scratch/p2j18_ax.lean
section
#print axioms Fl4Proofs.P2.Stall.sched.possible_switch_to.ap
#print axioms Fl4Proofs.P2.Stall.signal_tail.ap
#print axioms Fl4Proofs.P2.Stall.vcpu.report.ap
#print axioms Fl4Proofs.P2.Stall.notification.maybe_donate_sched_context.apB
#print axioms Fl4Proofs.P2.Stall.signal_vm.ap
#print axioms Fl4Proofs.P2.Stall.notification.send_signal.ap
#print axioms Fl4Proofs.P2.Stall.sched.awaken.ap
#print axioms Fl4Proofs.P2.Stall.AllCores.schedE
end

-- from proofs/scratch/p2j7_ax.lean
section
#print axioms Fl4Proofs.P2.Stall.stallAt.all
#print axioms Fl4Proofs.P2.Stall.AllCores.notK
#print axioms Fl4Proofs.P2.Stall.OKeep.ofW
#print axioms Fl4Proofs.P2.Stall.AllCores.step
end

-- from proofs/scratch/p2j9_ax.lean
section
#print axioms Fl4Proofs.P1.stallSeq.entryN
#print axioms Fl4Proofs.P2.Stall.stallAt.views
#print axioms Fl4Proofs.P2.Stall.stallAt.all
#print axioms Fl4Proofs.P2.Stall.AllCores.step
#print axioms Fl4Proofs.P2.Stall.AllCores.step2
#print axioms Fl4Proofs.P2.Stall.CoreInv.keep2
#print axioms Fl4Proofs.P1.endpoint.send_ipc.footN
#print axioms Fl4Proofs.P1.tmoKC_N
#print axioms Fl4Proofs.P1.XferFootOKC.foot
#print axioms Fl4Proofs.P1.xferOK_rs
#print axioms Fl4Proofs.P1.XGR.faultG
#print axioms Fl4Proofs.P1.faults.handle_timeout.footN
end

-- from proofs/scratch/p2j_ax.lean
section
#print axioms Fl4Proofs.P1.stallSeq.entryN
#print axioms Fl4Proofs.P2.Stall.stallAt.views
#print axioms Fl4Proofs.P2.Stall.OKeep.nq
#print axioms Fl4Proofs.P2.Stall.EntryInv.toView
#print axioms Fl4Proofs.P2.Stall.EntryInv.ofView
#print axioms Fl4Proofs.P1.endpoint.send_ipc.footN
#print axioms Fl4Proofs.P1.tmoKC_N
end

-- from proofs/scratch/p2lt/ax_afk.lean
section
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
#print axioms Fl4Proofs.P2.irq_sel
#print axioms Fl4Proofs.P2.irq_accG
#print axioms Fl4Proofs.P2.irq_wr_nondec
#print axioms Fl4Proofs.P2.irq_move_acc
#print axioms Fl4Proofs.P2.irq_rd_own
#print axioms Fl4Proofs.P2.irq_wr_own
#print axioms Fl4Proofs.P2.irq_acc_own
#print axioms Fl4Proofs.P2.tmw_own
#print axioms Fl4Proofs.P2.may_run_here.guardC
#print axioms Fl4Proofs.P2.current_ok.guardC
#print axioms Fl4Proofs.P2.irq_dec_guard
#print axioms Fl4Proofs.P2.IrqEntM.k
#print axioms Fl4Proofs.P2.IrqEnt.dec
#print axioms Fl4Proofs.P2.irq_koF
#print axioms Fl4Proofs.P2.irq_dec_user
#print axioms Fl4Proofs.P2.irq_alt
#print axioms Fl4Proofs.P2.irq_pathObl
#print axioms Fl4Proofs.P2.irq_pathSide
#print axioms Fl4Proofs.P2.irq_localPath
#print axioms Fl4Proofs.P2.may_run_here.guardZ
#print axioms Fl4Proofs.P2.top_ok.guardC
#print axioms Fl4Proofs.P2.wake_ok.guardC
#print axioms Fl4Proofs.P2.fireTail.guardC
#print axioms Fl4Proofs.P2.fire_ok.guardK
#print axioms Fl4Proofs.P2.plan_facts
#print axioms Fl4Proofs.P2.fire_rd
end

-- from proofs/P2ltAx.lean
section
open Fl4Proofs.P2
#print axioms in_core_timer_tree_access
#print axioms ge_remove
#print axioms ge_insert
#print axioms ge_remove_fixup
#print axioms ge_insert_fixup
#print axioms ge_tlinks
#print axioms Fl4Proofs.P2.set_timer_target_ok.guard
#print axioms Fl4Proofs.P2.current_ok.guard
#print axioms Fl4Proofs.P2.sched.schedule.guard_nodue
#print axioms Fl4Proofs.P2.release_due.guard
#print axioms Fl4Proofs.P2.timer_due.guard
#print axioms Fl4Proofs.P2.sched_quiet.guard
#print axioms Fl4Proofs.P2.set_timer_acc
#print axioms Fl4Proofs.P2.MoveTimer.set_height_zero_mguard_fails
#print axioms Fl4Proofs.P2.MoveTimer.set_deadline_mguard_fails
#print axioms Fl4Proofs.P2.set_timer_acc_own
#print axioms Fl4Proofs.P2.set_timer_pathObl
#print axioms Fl4Proofs.P2.set_timer_pathSide
#print axioms Fl4Proofs.P2.wake_ok.guard
#print axioms Fl4Proofs.P2.round_robin_ok.guard
#print axioms Fl4Proofs.P2.set_timer_localPath
end

-- from /private/tmp/claude-502/p2sl_ax.lean
section
#print axioms Fl4Proofs.P2.MoveStale.set_state_stale_mguard_fails
#print axioms Fl4Proofs.P2.PathObl.syscall.handle_syscall_local.guard_acc
#print axioms Fl4Proofs.P2.PathObl.syscall.handle_syscall_local.move_trap
#print axioms Fl4Proofs.P2.PathObl.syscall.handle_syscall_local.move_rr
#print axioms Fl4Proofs.P2.PathObl.syscall.handle_syscall_local.move
#print axioms Fl4Proofs.P2.PathObl.sl_pathObl
#print axioms Fl4Proofs.P2.PathObl.sl_pathSide
#print axioms Fl4Proofs.P2.OwnMap.ko_aligned
#print axioms Fl4Proofs.P2.PathObl.sl_hna
#print axioms Fl4Proofs.P2.PathObl.sl_hra
#print axioms Fl4Proofs.P2.PathObl.sl_pathObl_dr
#print axioms Fl4Proofs.P2.PathObl.sl_pathSide_dr
#print axioms Fl4Proofs.P2.PathObl.slThr_alt
#print axioms Fl4Proofs.P2.PathObl.slThr_acc
#print axioms Fl4Proofs.P2.PathObl.fastpath.fault.guard_dec
#print axioms Fl4Proofs.P2.PathObl.syscall.handle_syscall_local.guard_dec
#print axioms Fl4Proofs.P2.PathObl.fastpath.reply_recv_found.guard_dec
#print axioms Fl4Proofs.P2.PathObl.lp_alt
#print axioms Fl4Proofs.P2.PathObl.sl_home
#print axioms Fl4Proofs.P2.PathObl.sl_away
#print axioms Fl4Proofs.P2.PathObl.slThr_sl
#print axioms Fl4Proofs.P2.PathObl.sl_pathObl_sl
#print axioms Fl4Proofs.P2.PathObl.sl_pathSide_sl
#print axioms Fl4Proofs.P2.PathObl.af_of_tcb
#print axioms Fl4Proofs.P2.PathObl.slThrIn_of
#print axioms Fl4Proofs.P2.PathObl.sl_pathObl_ent
#print axioms Fl4Proofs.P2.PathObl.sl_pathSide_ent
#print axioms Fl4Proofs.P2.PathObl.slDecIn_of
#print axioms Fl4Proofs.P2.PathObl.sl_pathObl_lay
#print axioms Fl4Proofs.P2.PathObl.sl_pathSide_lay
#print axioms Fl4Proofs.P2.PathObl.preAcc_here
#print axioms Fl4Proofs.P2.PathObl.hhd_of
#print axioms Fl4Proofs.P2.PathObl.slPre_of
#print axioms Fl4Proofs.P2.PathObl.slAccC_of
#print axioms Fl4Proofs.P2.PathObl.fltAcc_of
#print axioms Fl4Proofs.P2.PathObl.rrAcc_of
#print axioms Fl4Proofs.P2.PathObl.fltAcc_nd
#print axioms Fl4Proofs.P2.PathObl.rrAcc_nd
#print axioms Fl4Proofs.P2.PathObl.preNd_of
#print axioms Fl4Proofs.P2.PathObl.fltAcc_wn
#print axioms Fl4Proofs.P2.PathObl.rrAcc_wn
#print axioms Fl4Proofs.P2.PathObl.decW_region
#print axioms Fl4Proofs.P2.PathObl.nq_of
#print axioms Fl4Proofs.P2.PathObl.frp_of
#print axioms Fl4Proofs.P2.PathObl.dsc_of
#print axioms Fl4Proofs.P2.PathObl.slAccIn_of
#print axioms Fl4Proofs.P2.PathObl.sl_pathObl_j
#print axioms Fl4Proofs.P2.PathObl.sl_pathSide_j
#print axioms Fl4Proofs.P2.PathObl.SlSets.sc
#print axioms Fl4Proofs.P2.PathObl.SlSets.tcb
#print axioms Fl4Proofs.P2.PathObl.lp_ex
#print axioms Fl4Proofs.P2.PathObl.tm_of
#print axioms Fl4Proofs.P2.PathObl.ntf_of
#print axioms Fl4Proofs.P2.PathObl.scHere_of
#print axioms Fl4Proofs.P2.PathObl.rh_of
#print axioms Fl4Proofs.P2.PathObl.usc_of
#print axioms Fl4Proofs.P2.PathObl.slHere_of
#print axioms Fl4Proofs.P2.PathObl.sl_pathObl_h
#print axioms Fl4Proofs.P2.PathObl.sl_pathSide_h
#print axioms Fl4Proofs.P2.PathObl.fbuf_of
#print axioms Fl4Proofs.P2.PathObl.slAccJ_of
#print axioms Fl4Proofs.P2.PathObl.hthr_of
#print axioms Fl4Proofs.P2.PathObl.slEnt_of
#print axioms Fl4Proofs.P2.PathObl.sl_pathObl_e
#print axioms Fl4Proofs.P2.PathObl.sl_pathSide_e
end

-- from /private/tmp/claude-502/p2io_ax.lean
section
#print axioms Fl4Proofs.P2.PathObl.io_dec_alt
#print axioms Fl4Proofs.P2.PathObl.io_pathObl
#print axioms Fl4Proofs.P2.PathObl.io_pathSide
#print axioms Fl4Proofs.P2.PathObl.io_move
#print axioms Fl4Proofs.P2.PathObl.io_pathObl_mv
#print axioms Fl4Proofs.P2.PathObl.io_ra_dec
end
