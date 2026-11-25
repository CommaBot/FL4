import Fl4Proofs

-- from scratch/int8/axint8.lean
section
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU5
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU7
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU4
#print axioms Fl4Proofs.P3.Sched.sniHyp_of
#print axioms Fl4Proofs.P3.Sched.sendHyp_of
#print axioms Fl4Proofs.P3.JAtZ.scCtxStepP1
#print axioms Fl4Proofs.P3.JAtZ.scCtlStepP1
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU9
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU3L
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachUH2
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU6
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU10
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU8
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU11
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU15
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU16
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU12
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU13
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU14
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU17
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU18
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU19
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU20
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU21
#print axioms Fl4Proofs.P1.TRB.height_le_128
#print axioms Fl4Proofs.P1.CoreTree.height_le
#print axioms Fl4Proofs.P1.TimerRB.no_link
#print axioms Fl4Proofs.P1.TimerRB.links_tz
#print axioms Fl4Proofs.P1.TimerRB.of_writesIn
#print axioms Fl4Proofs.P1.TimerRB.root_tz
#print axioms Fl4Proofs.P1.timer.left.rep
#print axioms Fl4Proofs.P1.timer.is_red.rep
#print axioms Fl4Proofs.P1.TRB.rep_plug
#print axioms Fl4Proofs.P1.TRB.plug_rotL_keys
#print axioms Fl4Proofs.P1.lk_wr_tl
#print axioms Fl4Proofs.P1.trb_node_wr_node
#print axioms Fl4Proofs.P1.TRB.CRep.hole
#print axioms Fl4Proofs.P1.TRB.Ctx.plug_keys
#print axioms Fl4Proofs.P1.TRB.rotL_rep
#print axioms Fl4Proofs.P1.TRB.rotR_rep
#print axioms Fl4Proofs.P1.timer.rotate_left.rep
#print axioms Fl4Proofs.P1.timer.rotate_right.rep
#print axioms Fl4Proofs.P1.timer.replace_child.rw
#print axioms Fl4Proofs.P1.lk_wr_red
#print axioms Fl4Proofs.P1.RW.wr_red
#print axioms Fl4Proofs.P1.timer.insert_loop.desc
#print axioms Fl4Proofs.P1.TRB.attach_rep
#print axioms Fl4Proofs.P1.TRB.attach_sorted
#print axioms Fl4Proofs.P1.TRB.attach_min
#print axioms Fl4Proofs.P1.timer.insert.attach
#print axioms Fl4Proofs.P1.TRB.plug_bal
#print axioms Fl4Proofs.P1.TRB.blk_le_64
#print axioms Fl4Proofs.P1.FB.set_red
#print axioms Fl4Proofs.P1.FB.rotL
#print axioms Fl4Proofs.P1.FB.rotR
#print axioms Fl4Proofs.P1.timer.insert_fixup_loop.rb
#print axioms Fl4Proofs.P1.timer.insert_fixup.rb
#print axioms Fl4Proofs.P1.CoreTree.of_fix
#print axioms Fl4Proofs.P1.timer.insert.core
#print axioms Fl4Proofs.P1.timer.insert.coreW
#print axioms Fl4Proofs.P1.timer.insert.rb
#print axioms Fl4Proofs.P1.CoreTree.keep
#print axioms Fl4Proofs.P1.timer.remove_loop0.lm
#print axioms Fl4Proofs.P1.TRB.splice_rep
#print axioms Fl4Proofs.P1.TRB.transplant_rep
#print axioms Fl4Proofs.P1.delTail.spec
#print axioms Fl4Proofs.P1.timer.remove.struct
#print axioms Fl4Proofs.P1.DelShape.keys
#print axioms Fl4Proofs.P1.rf_init
#print axioms Fl4Proofs.P1.rf_body
#print axioms Fl4Proofs.P1.timer.remove_fixup_loop.rb
#print axioms Fl4Proofs.P1.timer.remove_fixup.rb
#print axioms Fl4Proofs.P1.del_red_bal
#print axioms Fl4Proofs.P1.timer.remove.rb
#print axioms Fl4Proofs.P1.timer.insert.rb_full
#print axioms Fl4Proofs.P1.timer.fire_loop.rb
#print axioms Fl4Proofs.P1.timer.fire.rb
#print axioms Fl4Proofs.P3.JAtZ.unrefB
#print axioms Fl4Proofs.P3.JAtZ.keptB
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU25
#print axioms Fl4Proofs.P3.Vs.mem_L4_of_find
#print axioms Fl4Proofs.P3.JAtZ.vsReachMiss
#print axioms Fl4Proofs.P3.JAtZ.vsReachMissR
#print axioms Fl4Proofs.P3.JAtZ.vsReachAsidC
#print axioms Fl4Proofs.P3.Vs.VsReach.split
#print axioms Fl4Proofs.P3.Vs.VsNamed.frame
#print axioms Fl4Proofs.P3.Vs.VsNamed.step
#print axioms Fl4Proofs.P3.Vs.VsNamed.grow
#print axioms Fl4Proofs.P3.Vs.VsNamed.sub
#print axioms Fl4Proofs.P3.Vs.vsKeep_insert
#print axioms Fl4Proofs.P3.Vs.vsKeep_move
#print axioms Fl4Proofs.P3.Vs.vsKeep_swap
#print axioms Fl4Proofs.P3.Vs.vkey_copied
#print axioms Fl4Proofs.P3.JAtZ.vsNamedDrop
#print axioms Fl4Proofs.P3.JAtZ.vsNamedRestart
#print axioms Fl4Proofs.P3.Vs.VsPath.sub_new
#print axioms Fl4Proofs.P3.Vs.VsPath.sub_down
#print axioms Fl4Proofs.P3.Vs.VsPath.det
#print axioms Fl4Proofs.P3.Vs.VsPath.par_eq
#print axioms Fl4Proofs.P3.Vs.VsNamed.down
#print axioms Fl4Proofs.P3.Vs.VsNamed.shrink
#print axioms Fl4Proofs.P3.Vs.VsNamed.delSlot
#print axioms Fl4Proofs.P3.Vs.VsNamed.mapTab
#print axioms Fl4Proofs.P3.Vs.VsNamed.unmapTab
#print axioms Fl4Proofs.P3.Vs.VsNamed.makePool
#print axioms Fl4Proofs.P3.Vs.VsNamed.unNotWalk
#print axioms Fl4Proofs.P3.Vs.VsNamed.ref_eq
#print axioms Fl4Proofs.P3.Vs.wstep_keep
#print axioms Fl4Proofs.P3.Vs.unEmpty_keep
#print axioms Fl4Proofs.P3.Vs.lvl_disj
#print axioms Fl4Proofs.P3.Vs.esame_of_kheap
#print axioms Fl4Proofs.P3.Vs.VsPath.of_find
#print axioms Fl4Proofs.P3.Vs.VsNamed.mapTabS
#print axioms Fl4Proofs.P3.Vs.VsNamed.pdptMapS
#print axioms Fl4Proofs.P3.Vs.VsNamed.pdMapS
#print axioms Fl4Proofs.P3.Vs.VsNamed.ptMapS
#print axioms Fl4Proofs.P3.Vs.VsNamed.assignS
#print axioms Fl4Proofs.P3.Vs.VsNamed.makePoolS
#print axioms Fl4Proofs.P3.Vs.VsNamed.leafS
#print axioms Fl4Proofs.P3.Vs.VsNamed.own
#print axioms Fl4Proofs.P3.Vs.VsNamed.own_ref
#print axioms Fl4Proofs.P3.Vs.VsNamed.gone
#print axioms Fl4Proofs.P3.Vs.hpar_of
#print axioms Fl4Proofs.P3.Vs.wstep4_inv
#print axioms Fl4Proofs.P3.Vs.wstep5_inv
#print axioms Fl4Proofs.P1.TAgree.of_tmfr
#print axioms Fl4Proofs.P1.notification.send_signal.tm
#print axioms Fl4Proofs.P1.notification.send_signal.tagree
#print axioms Fl4Proofs.P1.timer.fire_loop.rb'
#print axioms Fl4Proofs.P1.timer.fire.rb'
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU26
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU27
#print axioms Fl4Proofs.P3.JAtZ.keptBW
#print axioms Fl4Proofs.P3.JAtZ.unrefBW
#print axioms Fl4Proofs.P1.BndS.pairTN
#print axioms Fl4Proofs.P1.BndS.pairSN
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU28
#print axioms Fl4Proofs.P3.JAtZ.keptCW
#print axioms Fl4Proofs.P3.JAtZ.unrefCW
#print axioms Fl4Proofs.P3.JAtZ.deadUnarmed
#print axioms Fl4Proofs.P3.JAtZ.regionUnrefCU
#print axioms Fl4Proofs.P3.DbgWFL.notMem_of_off
#print axioms Fl4Proofs.P1.fin_cap_thread.td0
#print axioms Fl4Proofs.P3.Vs.VsNamed.ofPendShr
#print axioms Fl4Proofs.P3.Vs.VsNamed.pendPool
#print axioms Fl4Proofs.P3.Vs.VsNamed.retypeGrow
#print axioms Fl4Proofs.P3.JAtZ.vxSet
#print axioms Fl4Proofs.P3.JAtZ.finVsJ
#print axioms Fl4Proofs.P3.emptyHypJL
#print axioms Fl4Proofs.P3.decode_invocation_pml4JV
#print axioms Fl4Proofs.P3.decode_invocation_pml4_fbJV
#print axioms Fl4Proofs.P3.decode_invocation_pml4_fbJVM
#print axioms Fl4Proofs.P3.fb_loopJ
#print axioms Fl4Proofs.P3.fb_loopI
#print axioms Fl4Proofs.P3.fb_entryJ
#print axioms Fl4Proofs.P3.fb_entry_remapJ
#print axioms Fl4Proofs.P3.fb_entry_delJ
#print axioms Fl4Proofs.P3.fb_entry_copyJ
#print axioms Fl4Proofs.P3.JAtZ.batchMapJL
#print axioms Fl4Proofs.P3.JAtZ.fbDelFrameJN
#print axioms Fl4Proofs.P3.JAtZ.fbDelDeferJ
#print axioms Fl4Proofs.P3.decOK_JMM
#print axioms Fl4Proofs.P3.MKD.vspace_decode
#print axioms Fl4Proofs.P3.MKD.decode_quiet
#print axioms Fl4Proofs.P1.vm_fault_same
#print axioms Fl4Proofs.P1.vm_local_same
#print axioms Fl4Proofs.P1.vm_local_decline
#print axioms Fl4Proofs.P1.vm_fault_decline
#print axioms Fl4Proofs.P1.reply_recv_vm_found_decline
#print axioms Fl4Proofs.P1.rr_vm_same
#print axioms Fl4Proofs.P1.rr_vm_local_same
#print axioms Fl4Proofs.P1.rr_prefix_keep
#print axioms Fl4Proofs.P1.update_timestamp_twice
#print axioms Fl4Proofs.P1.vmFault_of
#print axioms Fl4Proofs.P1.RRPreAtG.of_inv
#print axioms Fl4Proofs.P1.fault_same
#print axioms Fl4Proofs.P1.rr_same
#print axioms Fl4Proofs.P1.faultReads_of
#print axioms Fl4Proofs.P1.faultNvm_ofR
#print axioms Fl4Proofs.P3.JAtZ.vmFaultOK
#print axioms Fl4Proofs.P3.JAtZ.rrPreAtG
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU15Vm
#print axioms Fl4Proofs.P3.vfh_eq
#print axioms Fl4Proofs.P3.vfh_ep
#print axioms Fl4Proofs.P3.decode_invocation_tdxJ
#print axioms Fl4Proofs.P3.tdx_perform_out
#print axioms Fl4Proofs.P3.SInvUZ.zr_tdx
#print axioms Fl4Proofs.P3.SInvUZ.okv_fl4Decode_z
#print axioms Fl4Proofs.P3.MKD.tdx_decode
#print axioms Fl4Proofs.P3.SInvR.A13b.perfA_tdx
#print axioms Fl4Proofs.P3.decOK_J
#print axioms Fl4Proofs.P3.kernel_entry_reach
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU2
#print axioms Fl4Proofs.P3.TdxRel.adjust
#print axioms Fl4Proofs.P3.SInvR.G4.kernel_entry_reachN
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachI
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachIF
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachIP
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU2F
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU2L
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU3
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachUH
#print axioms Fl4Proofs.P3.kernel_entry_reachE
#print axioms Fl4Proofs.P3.kernel_entry_reachE2
#print axioms Fl4Proofs.P3.kernel_entry_reachE3
#print axioms Fl4Proofs.P3.kernel_entry_reachE3T
#print axioms Fl4Proofs.P3.kernel_entry_reachE4
#print axioms Fl4Proofs.P3.kernel_entry_reachE5
#print axioms Fl4Proofs.P3.kernel_entry_reachM
#print axioms Fl4Proofs.P3.kernel_entry_reachMD
#print axioms Fl4Proofs.P3.kernel_entry_reachMD2
#print axioms Fl4Proofs.P3.kernel_entry_reachMD3
#print axioms Fl4Proofs.P3.kernel_entry_reachMD4
#print axioms Fl4Proofs.P3.kernel_entry_reachMD4V
#print axioms Fl4Proofs.P3.kernel_entry_reachMI
#print axioms Fl4Proofs.P3.SInvDV.hd_performFrameBatch
#print axioms Fl4Proofs.P3.SInvDV.ob_performFrameBatch
#print axioms Fl4Proofs.P3.Vs.batch_map_rel
#print axioms Fl4Proofs.P3.JAtZ.batchMapJX
#print axioms Fl4Proofs.P3.JAtZ.fbDeferStepJ
#print axioms Fl4Proofs.P3.Vs.unmap_unflushed_rel
#print axioms Fl4Proofs.P3.JAtZ.fbInsJ
#print axioms Fl4Proofs.P3.JAtZR.rootFr
#print axioms Fl4Proofs.P1.fault_accG
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU29
#print axioms Fl4Proofs.P3.JAtZ.vsNamedE
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU28V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU10V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU11V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU12V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU15V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU17V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU18V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU19V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU20V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU21V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU25V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU26V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU27V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU2FV
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU2V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU3LV
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU3V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU4V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU7V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU8V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU9V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachUHV
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachUV
#print axioms Fl4Proofs.P3.kernel_entry_reachE4V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU29S
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU29Vm
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU29I
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU29V
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU29D
#print axioms Fl4Proofs.P1.syscall_local_same
#print axioms Fl4Proofs.P1.ioport_local_same
#print axioms Fl4Proofs.P1.inv_local_same
#print axioms Fl4Proofs.P1.syscall_pre_same
#print axioms Fl4Proofs.P1.vm_pre_same
#print axioms Fl4Proofs.P3.SInvR.G5.jreachU17_tick
#print axioms Fl4Proofs.P3.JAtZ.sbufOK
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU29T
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU29TD
#print axioms Fl4Proofs.P3.SInvR.G5.declIrq_of
#print axioms Fl4Proofs.P3.JAtZ.threadCapT
#print axioms Fl4Proofs.P1.set_timer_local_same
#print axioms Fl4Proofs.P1.set_timer_local_triple
#print axioms Fl4Proofs.P1.set_timer_local_decline
#print axioms Fl4Proofs.P1.irq_local_same
#print axioms Fl4Proofs.P1.irq_local_triple
#print axioms Fl4Proofs.P1.irq_local_decline
#print axioms Fl4Proofs.P1.irq_pre_same
#print axioms Fl4Proofs.P1.lt_prefix
#print axioms Fl4Proofs.P1.found_cap_keep
#print axioms Fl4Proofs.P1.decode_set_timer
#print axioms Fl4Proofs.P0.localtimer.in_core_timer_tree_loop.p0
#print axioms Fl4Proofs.P0.localtimer.handle_set_timer_local.p0
#print axioms Fl4Proofs.P0.localtimer.handle_timer_irq_local.p0
#print axioms Fl4Proofs.P1.kernel_entry.entry
#print axioms Fl4Proofs.P1.kernel_entry.entryXG
#print axioms Fl4Proofs.P1.kernel_entry.entry_of
#print axioms Fl4Proofs.P1.kernel_entry.entry_of2
#print axioms Fl4Proofs.P1.kernel_entry.entry_of3
#print axioms Fl4Proofs.P1.kernel_entry.entry_of4
#print axioms Fl4Proofs.P1.kernel_entry.entry_of4G
#print axioms Fl4Proofs.P1.kernel_entry.entry_of5
#print axioms Fl4Proofs.P1.kernel_entry.entry_of6
#print axioms Fl4Proofs.P1.kernel_entry.entry_of7
#print axioms Fl4Proofs.P1.kernel_entry.entry_of7r
#print axioms Fl4Proofs.P1.kernel_entry.entry_of7r2
#print axioms Fl4Proofs.P1.kernel_entry.entry_of8
#print axioms Fl4Proofs.P1.kernel_entry.entry_of9
#print axioms Fl4Proofs.P1.kernel_entry.entry_of10
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_entryInvU29
#print axioms Fl4Proofs.P3.JAtZ.entryInv
#print axioms Fl4Proofs.P3.JAt.entInvAt
#print axioms Fl4Proofs.P3.JAtZ.canBlockX
#print axioms Fl4Proofs.P3.JAtZ.timeoutTyped
#print axioms Fl4Proofs.P1.blkU_false
#print axioms Fl4Proofs.P1.EntryHyps0.not_bxi
#print axioms Fl4Proofs.P1.P3Place.not_bxi
#print axioms Fl4Proofs.P1.tmoOK_false
#print axioms Fl4Proofs.P1.Hyps4.not_entryInv
#print axioms Fl4Proofs.P1.P3Place.tmoAny_false
#print axioms Fl4Proofs.P1.irqcap_false
#print axioms Fl4Proofs.P1.XferHyps.buf_false
#print axioms Fl4Proofs.P1.InvHyps.not_bxi
#print axioms Fl4Proofs.P1.entAt_self
#print axioms Fl4Proofs.P1.decodeF_reply0
#print axioms Fl4Proofs.P1.decodeF_ntfn0
open Fl4Proofs.P2.MoveGap
#print axioms mown_deciders
#print axioms mown_move_alt
#print axioms body_not_safe
#print axioms mown_not_moveLocal
#print axioms Fl4Proofs.P2.Serial.moveV_transfer
#print axioms Fl4Proofs.P2.OwnMap.moveHeld
#print axioms Fl4Proofs.P2.E2E.serializable_e2e
#print axioms Fl4Proofs.P2.ReadGap.isProg_pOnce
#print axioms Fl4Proofs.P2.ReadGap.not_once_pTwice
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
open Fl4Proofs.P2.PathObl
#print axioms vm_acc
#print axioms faultTail3.guardVm
#print axioms VmMidF.tailAcc
#print axioms vmPre14_eq1
#print axioms vmPre2_eq
#print axioms syscall.handle_vm_fault_local.guard_acc
open Fl4Proofs.P2.PathObl
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
open Fl4Proofs.P2.PathObl
#print axioms vm_accG
#print axioms vm_acc_of_tail
#print axioms vmWd_notDecW
#print axioms vm_acc_gd
#print axioms vm_move
#print axioms vm_pathObl_mv
open Fl4Proofs.P2.PathObl
#print axioms faults.handle_fault_reply.guardVm
#print axioms fastpath_vm.reply_recv_vm_found.guard
open Fl4Proofs.P2.PathObl
#print axioms syscall.handle_reply_recv_vm_local.guard_acc
open Fl4Proofs.P2.PathObl
#print axioms rrX_mem
#print axioms rrX_tcb
#print axioms rrX_out
#print axioms VmBase.ntfnRd
#print axioms rr_u_home
#print axioms VmRPre.rrAccV
#print axioms rr_vm_accG
#print axioms rr_vm_acc
open Fl4Proofs.P2.PathObl
#print axioms rr_acc_gd
#print axioms rr_move
#print axioms rr_total
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
open Fl4Proofs.P2.PathObl
#print axioms vm_localPath
#print axioms rr_localPath
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
#print axioms Fl4Proofs.P2.Stall.FFoot.okeep
#print axioms Fl4Proofs.P2.Stall.FFoot.cur
#print axioms Fl4Proofs.P2.Stall.FireKeep.ofFF
#print axioms Fl4Proofs.P2.Stall.schedcontext.donate.ff
#print axioms Fl4Proofs.P2.Stall.FFoot.trans
#print axioms Fl4Proofs.P2.Stall.notification.maybe_donate_sched_context.ff
#print axioms Fl4Proofs.P2.Stall.AllCores.step2
#print axioms Fl4Proofs.P2.Stall.CoreInv.keep2
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
#print axioms Fl4Proofs.P2.Stall.sched.possible_switch_to.ap
#print axioms Fl4Proofs.P2.Stall.signal_tail.ap
#print axioms Fl4Proofs.P2.Stall.vcpu.report.ap
#print axioms Fl4Proofs.P2.Stall.notification.maybe_donate_sched_context.apB
#print axioms Fl4Proofs.P2.Stall.signal_vm.ap
#print axioms Fl4Proofs.P2.Stall.notification.send_signal.ap
#print axioms Fl4Proofs.P2.Stall.sched.awaken.ap
#print axioms Fl4Proofs.P2.Stall.AllCores.schedE
#print axioms Fl4Proofs.P2.Stall.AllCores.notK
#print axioms Fl4Proofs.P2.Stall.OKeep.ofW
#print axioms Fl4Proofs.P2.Stall.AllCores.step
#print axioms Fl4Proofs.P1.stallSeq.entryN
#print axioms Fl4Proofs.P1.endpoint.send_ipc.footN
#print axioms Fl4Proofs.P1.tmoKC_N
#print axioms Fl4Proofs.P1.XferFootOKC.foot
#print axioms Fl4Proofs.P1.xferOK_rs
#print axioms Fl4Proofs.P1.XGR.faultG
#print axioms Fl4Proofs.P1.faults.handle_timeout.footN
#print axioms Fl4Proofs.P2.Stall.OKeep.nq
#print axioms Fl4Proofs.P2.Stall.EntryInv.toView
#print axioms Fl4Proofs.P2.Stall.EntryInv.ofView
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
#print axioms Fl4Proofs.P2.set_timer_localPath
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
#print axioms Fl4Proofs.P2.PathObl.io_dec_alt
#print axioms Fl4Proofs.P2.PathObl.io_pathObl
#print axioms Fl4Proofs.P2.PathObl.io_pathSide
#print axioms Fl4Proofs.P2.PathObl.io_move
#print axioms Fl4Proofs.P2.PathObl.io_pathObl_mv
#print axioms Fl4Proofs.P2.PathObl.io_ra_dec
#print axioms Fl4Proofs.P1.EntryInv.csc
#print axioms Fl4Proofs.P1.EntryInv.cscS
#print axioms Fl4Proofs.P1.EntryInv.hcsc
#print axioms Fl4Proofs.P1.ObjsOK.of_heap
#print axioms Fl4Proofs.P1.ObjsOK.drop
#print axioms Fl4Proofs.P1.ObjsOK.ksb
#print axioms Fl4Proofs.P1.ObjsOK.any
#print axioms Fl4Proofs.P2.tcbqueue.remove.guardL
#print axioms Fl4Proofs.P2.tcbqueue.prepend.guardL
#print axioms Fl4Proofs.P2.tcbqueue.append.guardL
#print axioms Fl4Proofs.P2.notification.ntfn_dequeue.guard
#print axioms Fl4Proofs.P2.endpoint.ep_dequeue.guard
#print axioms Fl4Proofs.P2.NodeSt.of_wi
#print axioms Fl4Proofs.P2.sched.possible_switch_to.guard_here
#print axioms Fl4Proofs.P2.notification.maybe_donate_sched_context.guard_nd
#print axioms Fl4Proofs.P2.sporadic.sc_sporadic.guardQ
#print axioms Fl4Proofs.P2.notification.unblock_sporadic.guard
#print axioms Fl4Proofs.P2.possible_switch_to_here_st
#print axioms Fl4Proofs.P2.wakeTail.guard
#print axioms Fl4Proofs.P2.send_signal_act
#print axioms Fl4Proofs.P2.send_signal_idle0
#print axioms Fl4Proofs.P2.send_signal_bnr
#print axioms Fl4Proofs.P2.send_signal_recv
#print axioms Fl4Proofs.P2.send_signal_wait
#print axioms Fl4Proofs.P2.notification.set_active.guard
#print axioms Fl4Proofs.P2.notification.send_signal.guardF
#print axioms Fl4Proofs.P2.removeF_kc
#print axioms Fl4Proofs.P2.tq_prepend_empty
#print axioms Fl4Proofs.P2.tq_prepend_ne
#print axioms Fl4Proofs.P2.sched.dequeue.guardG
#print axioms Fl4Proofs.P2.sched.enqueue.guard_local
#print axioms Fl4Proofs.P2.recv_ne_send
#print axioms Fl4Proofs.P2.ipc.cancel_ipc.guard_recv
#print axioms Fl4Proofs.P2.schedule_sw_eq
#print axioms Fl4Proofs.P2.sched.awaken.guard_fire
#print axioms Fl4Proofs.P2.sched.schedule.guard_sw
#print axioms Fl4Proofs.P2.fire_ok_loop_eq
#print axioms Fl4Proofs.P2.fire_body_stop
#print axioms Fl4Proofs.P2.fire_body_done
#print axioms Fl4Proofs.P2.timer.fire.guard_one
#print axioms Fl4Proofs.P2.fire_body_one
#print axioms Fl4Proofs.P1.ScAff.keep
#print axioms Fl4Proofs.P1.ScAffX.keep
#print axioms Fl4Proofs.P1.ScAff.pairX
#print axioms Fl4Proofs.P1.ScAff.coreX
#print axioms Fl4Proofs.P1.ScAffX.restore
#print axioms Fl4Proofs.P1.ScAffX.full
#print axioms Fl4Proofs.P1.XInv.scAff
#print axioms Fl4Proofs.P1.XInv.core_eq
#print axioms Fl4Proofs.P1.BlkOK.core_eq
#print axioms Fl4Proofs.P1.migrate_aff
#print axioms Fl4Proofs.P1.migrate_tail
#print axioms Fl4Proofs.P1.donate_pair
#print axioms Fl4Proofs.P1.donate_tail
#print axioms Fl4Proofs.P1.schedcontext.donate.ipc
#print axioms Fl4Proofs.P1.schedcontext.bind_tcb.blk
#print axioms Fl4Proofs.P1.cfD
#print axioms Fl4Proofs.P1.schedcontext.configure_flags.blk
#print axioms Fl4Proofs.P1.sctcb_zero_all
#print axioms Fl4Proofs.P1.objects.debug_remove.w
#print axioms Fl4Proofs.P2.PathObl.sl_total
#print axioms Fl4Proofs.P2.PathObl.sl_localPath
#print axioms Fl4Proofs.P2.PathObl.once_of_guardG
#print axioms Fl4Proofs.P2.PathObl.io_total
#print axioms Fl4Proofs.P2.PathObl.io_readOnce
#print axioms Fl4Proofs.P2.PathObl.io_localPath
#print axioms Fl4Proofs.P2.Stall.AllCores.schedH
#print axioms Fl4Proofs.P2.Stall.AllCores.schedBH
#print axioms Fl4Proofs.P2.Stall.sched.awaken.rc
#print axioms Fl4Proofs.P2.Stall.sched.possible_switch_to.rd
#print axioms Fl4Proofs.P2.Stall.notification.send_signal.rd
#print axioms Fl4Proofs.P2.Stall.timer.fire_loop.rd
#print axioms Fl4Proofs.P2.Stall.sched.awaken_loop.rd
#print axioms Fl4Proofs.P2.Stall.kw0_ne_cdom
#print axioms Fl4Proofs.P1.DomInv.writesIn
#print axioms Fl4Proofs.P1.obj.Tcb.set_domain.domInv
#print axioms Fl4Proofs.P1.create_tcb_domain.domInv
#print axioms Fl4Proofs.P1.dom_lt_num
#print axioms Fl4Proofs.P3.Sched.SchedRel.domInv
#print axioms Fl4Proofs.P3.sched.next_domain.domInv
#print axioms Fl4Proofs.P3.JAtZ.domInv
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_domInvU29
#print axioms Fl4Proofs.P1.sched.possible_switch_to.domInv
#print axioms Fl4Proofs.P1.sched.reschedule_required.domInv
#print axioms Fl4Proofs.P1.sched.release_remove.domInv
#print axioms Fl4Proofs.P1.sched.dequeue.domInv
#print axioms Fl4Proofs.P2.Stall.FootN.monoK
#print axioms Fl4Proofs.P2.Stall.AllCores.bodyEnd
#print axioms Fl4Proofs.P2.Stall.AllCores.schedB
#print axioms Fl4Proofs.P3.JAtZ.bufUser
#print axioms Fl4Proofs.P3.JAtZ.curBufUser
#print axioms Fl4Proofs.P3.JAtZ.rbufAt
end

-- from scratch/int8/axp2.lean
section
open Fl4Proofs.P2.MoveGap
open Aeneas Aeneas.Std Result
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.PathObl
open Fl4Proofs.P2
end

-- from scratch/actv_ax.lean
section
#print axioms Fl4Proofs.P2.Stall.timer_irq_local.allCores
#print axioms Fl4Proofs.P2.Stall.set_timer_local.allCores
#print axioms Fl4Proofs.P2.Stall.set_timer_tail
#print axioms Fl4Proofs.P2.Stall.AllCores.twStep
#print axioms Fl4Proofs.P2.Stall.sched.activate_thread.tw
#print axioms Fl4Proofs.P2.Stall.vcpu.report.xfP
#print axioms Fl4Proofs.P2.Stall.vcpu.report.tw
#print axioms Fl4Proofs.P2.Stall.vcpu.check.tw
#print axioms Fl4Proofs.P1.vcpu.check.entry
#print axioms Fl4Proofs.P2.Stall.AllCores.tail
#print axioms Fl4Proofs.P2.Stall.AllCores.exit
#print axioms Fl4Proofs.P2.Stall.timer_irq_local.allCoresExit
#print axioms Fl4Proofs.P2.Stall.set_timer_local.allCoresExit
end

-- from scratch/comb_ax.lean
section
#print axioms Fl4Proofs.P2.Stall.timer_irq_local.allCoresBW
#print axioms Fl4Proofs.P2.Stall.timer_irq_local.allCoresW
#print axioms Fl4Proofs.P2.Stall.timer_irq_local.allCoresExitW
#print axioms Fl4Proofs.P2.Stall.set_timer_tailBW
#print axioms Fl4Proofs.P2.Stall.set_timer_local.allCoresBW
#print axioms Fl4Proofs.P2.Stall.set_timer_local.allCoresW
#print axioms Fl4Proofs.P2.Stall.set_timer_local.allCoresExitW
#print axioms Fl4Proofs.P2.Stall.AllCores.exitV
#print axioms Fl4Proofs.P2.Stall.timer_irq_local.allCoresExitV
#print axioms Fl4Proofs.P2.Stall.set_timer_local.allCoresExitV
#print axioms Fl4Proofs.P2.Stall.timer_irq_local.allCoresExitF
#print axioms Fl4Proofs.P2.Stall.set_timer_local.allCoresExitF
end

-- from scratch/hr_ax.lean
section
end

-- from scratch/lay_ax.lean
section
#print axioms Fl4Proofs.P2.PathObl.layoutJ_mv
#print axioms Fl4Proofs.P2.PathObl.slJAt_of_JAtZ_stable
#print axioms Fl4Proofs.P2.PathObl.slJAt_of_reachU17_stable
#print axioms Fl4Proofs.P2.PathObl.sl_localPathK
#print axioms Fl4Proofs.P2.PathObl.sl_pathsK
#print axioms Fl4Proofs.P2.PathObl.sl_pathsK_startAt
#print axioms Fl4Proofs.P2.SerExit.ser_of_JAtZN
#print axioms Fl4Proofs.P2.SerExit.ser_of_reachN
#print axioms Fl4Proofs.P2.SerExit.ser_of_reachU29N
#print axioms Fl4Proofs.P2.SerExit.ser_step_of_JAtZN
end

-- from scratch/ndd_ax.lean
section
#print axioms Fl4Proofs.P3.ndDomOK_of
#print axioms Fl4Proofs.P3.ndDomOK_of_ndOK
#print axioms Fl4Proofs.P3.JAtZ.ndDomOK
#print axioms Fl4Proofs.P3.JAt.entDomNdAt
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_domNdU29
end

-- from scratch/p1cs_ax.lean
section
end

-- from scratch/p1dom_ax.lean
section
end

-- from scratch/p1dom_ax2.lean
section
end

-- from scratch/p2j14_ax.lean
section
end

-- from scratch/p2j15_ax.lean
section
end

-- from scratch/p2j18_ax.lean
section
end

-- from scratch/p2j7_ax.lean
section
end

-- from scratch/p2j9_ax.lean
section
end

-- from scratch/p2j_ax.lean
section
end

-- from scratch/p2je_ax.lean
section
#print axioms Fl4Proofs.P2.Stall.sched.charge_budget.rr
#print axioms Fl4Proofs.P2.Stall.sched.check_budget.rr
#print axioms Fl4Proofs.P2.Stall.interrupt.handle_interrupt.timer
#print axioms Fl4Proofs.P2.Stall.ks_keepB
#print axioms Fl4Proofs.P2.Stall.timer.insert.nb
#print axioms Fl4Proofs.P2.Stall.msg.reply_success_empty.nb
end

-- from scratch/rbuf_ax.lean
section
end

-- from scratch/scks_ax.lean
section
#print axioms Fl4Proofs.P1.SCsOK.scKsOut
#print axioms Fl4Proofs.P1.BlkOK.scKsOut
#print axioms Fl4Proofs.P1.SCsOK.fr
#print axioms Fl4Proofs.P1.SCsOK.mk2
#print axioms Fl4Proofs.P1.SCsOK.drop
#print axioms Fl4Proofs.P1.BlkOK.addSc
end

-- from scratch/scks_ax3.lean
section
end

-- from scratch/sib_ax.lean
section
#print axioms Fl4Proofs.P1.sched.schedule.sfootB
#print axioms Fl4Proofs.P1.sched.schedule.ibFr
#print axioms Fl4Proofs.P2.Stall.schIb_holds
#print axioms Fl4Proofs.P2.Stall.usrW_vcpu
#print axioms Fl4Proofs.P2.Stall.VcpuUsr.of_ent
#print axioms Fl4Proofs.P2.Stall.AllCores.tailV
#print axioms Fl4Proofs.P1.vcpu.check.entryV
end

-- from scratch/slco_ax.lean
section
#print axioms Fl4Proofs.P2.PathObl.core_of
#print axioms Fl4Proofs.P2.PathObl.dco_of
#print axioms Fl4Proofs.P2.PathObl.rbuf_of
end

-- from scratch/slj2_ax.lean
section
#print axioms Fl4Proofs.P2.PathObl.SlJAtZ.ksO
#print axioms Fl4Proofs.P2.PathObl.SlJAtZ.vsNone
#print axioms Fl4Proofs.P2.PathObl.SlJAtZ.asid
#print axioms Fl4Proofs.P2.PathObl.SlJAtZ.pool
#print axioms Fl4Proofs.P2.PathObl.SlJAtZ.cscFacts
#print axioms Fl4Proofs.P2.PathObl.SlJAtZ.regionOKX
#print axioms Fl4Proofs.P2.PathObl.SlJAt.hereJ
#print axioms Fl4Proofs.P2.PathObl.SlJAt.accK
#print axioms Fl4Proofs.P2.PathObl.SlJAt.of_JAtZ
#print axioms Fl4Proofs.P2.PathObl.sl_localPathJ
#print axioms Fl4Proofs.P2.PathObl.slJAt_of_JAtZ
#print axioms Fl4Proofs.P2.PathObl.slJAt_of_reachU17
end

-- from scratch/slj_ax.lean
section
#print axioms Fl4Proofs.P2.PathObl.regionOKX_of
#print axioms Fl4Proofs.P2.PathObl.SlJAtZ.ksNone
#print axioms Fl4Proofs.P2.PathObl.SlJAtZ.tslots
#print axioms Fl4Proofs.P2.PathObl.SlJAtZ.dsR
#print axioms Fl4Proofs.P2.PathObl.SlJAtZ.hep
#print axioms Fl4Proofs.P2.PathObl.SlJAt.entJ
#print axioms Fl4Proofs.P2.PathObl.rs_ks
end

-- from scratch/vmchk_ax.lean
section
#print axioms Fl4Proofs.P1.vcpu.check.vck
#print axioms Fl4Proofs.P1.EntryHyps0.vmchk
#print axioms Fl4Proofs.P1.syscall.finish.entry
#print axioms Fl4Proofs.P1.EntryHyps.of
#print axioms Fl4Proofs.P1.EntryHyps.of_gaps
#print axioms Fl4Proofs.P3.fastFaultOK_of_p1N
end

-- from scratch/wire_ax.lean
section
end

-- from scratch/wire_ax2.lean
section
#print axioms Fl4Proofs.P2.Stall.sched.charge_budget.rrW
end

-- from scratch/p2lt/ax_afk.lean
section
#print axioms Fl4Proofs.P2.schedSw_eq
#print axioms Fl4Proofs.P2.schedSwB.guard
#print axioms Fl4Proofs.P2.schedSw.guard
#print axioms Fl4Proofs.P2.fire_next
#print axioms Fl4Proofs.P2.fire_stop
#print axioms Fl4Proofs.P2.fire_stop_sig
#print axioms Fl4Proofs.P2.irq_accG_fire_walk
#print axioms Fl4Proofs.P2.irq_accG_fire_pre
#print axioms Fl4Proofs.P2.armed.tinv
#print axioms Fl4Proofs.P2.SCq.agree'
#print axioms Fl4Proofs.P2.ntfn_ts_out
#print axioms Fl4Proofs.P2.out_not_tw
#print axioms Fl4Proofs.P2.plan_facts'
#print axioms Fl4Proofs.P2.fire_ok_tail
#print axioms Fl4Proofs.P2.fireTail_idle
#print axioms Fl4Proofs.P2.set_active_wr
#print axioms Fl4Proofs.P2.send_signal_nw
#print axioms Fl4Proofs.P2.rel_agree
#print axioms Fl4Proofs.P2.fire_run
#print axioms Fl4Proofs.P2.fire_tail_nw
#print axioms Fl4Proofs.P2.wakeTail.gw
#print axioms Fl4Proofs.P2.WkPre.agree
#print axioms Fl4Proofs.P2.ntfn_waiting_ne_idle
#print axioms Fl4Proofs.P2.wake_wait_guard
#print axioms Fl4Proofs.P2.sts_ok
#print axioms Fl4Proofs.P2.cancel_recv_st
#print axioms Fl4Proofs.P2.ntfn_idle_ne_waiting
#print axioms Fl4Proofs.P2.recv_ne_vm
#print axioms Fl4Proofs.P2.wake_recv_guard
#print axioms Fl4Proofs.P2.ftree_own
#print axioms Fl4Proofs.P2.fnt_ownE
#print axioms Fl4Proofs.P2.fnt_own
#print axioms Fl4Proofs.P2.fire_rd_own
#print axioms Fl4Proofs.P2.fire_wr_own
#print axioms Fl4Proofs.P2.fire_wr_nondec
#print axioms Fl4Proofs.P2.fire_tmHere
#print axioms Fl4Proofs.P2.fire_eqs
#print axioms Fl4Proofs.P2.irq_acc_fire_nw
#print axioms Fl4Proofs.P2.irq_move_fire_nw
#print axioms Fl4Proofs.P2.irq_localPathW
#print axioms Fl4Proofs.P2.donate_nd_st
#print axioms Fl4Proofs.P2.wakeTail_st
#print axioms Fl4Proofs.P2.glink_own
#print axioms Fl4Proofs.P2.obj_own
#print axioms Fl4Proofs.P2.held_lock
#print axioms Fl4Proofs.P2.wake_wait_st
#print axioms Fl4Proofs.P2.wake_recv_st
#print axioms Fl4Proofs.P2.ntfn_head_ok
#print axioms Fl4Proofs.P2.wake_ok_true
#print axioms Fl4Proofs.P2.fireTail_wake
#print axioms Fl4Proofs.P2.LocRd
#print axioms Fl4Proofs.P2.LocWr
#print axioms Fl4Proofs.P2.LkW
#print axioms Fl4Proofs.P2.ObjLay
#print axioms Fl4Proofs.P2.loc_rd_own
#print axioms Fl4Proofs.P2.loc_wr_own
#print axioms Fl4Proofs.P2.lkw_own
#print axioms Fl4Proofs.P2.loc_wr_nondec
#print axioms Fl4Proofs.P2.lkw_nondec
#print axioms Fl4Proofs.P2.PathObl.switch_hsw_hfr
#print axioms Fl4Proofs.P2.pick_top
#print axioms Fl4Proofs.P2.top_unique
#print axioms Fl4Proofs.P2.choose_head
#print axioms Fl4Proofs.P2.sc_sporadic_true
#print axioms Fl4Proofs.P2.sched.is_schedulable.guardC
#print axioms Fl4Proofs.P2.sched.schedule_tcb.guardC
#print axioms Fl4Proofs.P2.sched.set_thread_state.guardVC
#print axioms Fl4Proofs.P2.set_thread_state.gwC
#print axioms Fl4Proofs.P2.schedule_act_eq
#print axioms Fl4Proofs.P2.fire_tail_of_aw
#print axioms Fl4Proofs.P2.actTail.guard
#print axioms Fl4Proofs.P2.aw_tail_resume
#print axioms Fl4Proofs.P2.qmem_nbrs
#print axioms Fl4Proofs.P2.StW
#print axioms Fl4Proofs.P2.wake_wait_fire
#print axioms Fl4Proofs.P2.scSb_ne
#print axioms Fl4Proofs.P2.recv_rt
#print axioms Fl4Proofs.P2.wake_recv_fire
#print axioms Fl4Proofs.P2.wkpre_fire
#print axioms Fl4Proofs.P2.wkpre_true
#print axioms Fl4Proofs.P2.WkCase
#print axioms Fl4Proofs.P2.wk_sig
#print axioms Fl4Proofs.P2.node_not_tw
#print axioms Fl4Proofs.P2.fire_wk_step
end

-- from P2ltAx.lean
section
open Fl4Proofs.P2
end
