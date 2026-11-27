import Fl4ProofsA64.P1.Queue
import Fl4ProofsA64.P1.QueueAppend
import Fl4ProofsA64.P1.QueueBudget
import Fl4ProofsA64.P1.QueueBudget2
import Fl4ProofsA64.P1.FastDecline
import Fl4ProofsA64.P2.ProgVmF
import Fl4ProofsA64.P1.VcpuReport
import Fl4ProofsA64.P1.QueueBlock
import Fl4ProofsA64.P1.QueueTimerW
import Fl4ProofsA64.P1.TimerRB
import Fl4ProofsA64.P1.TimerRBZip
import Fl4ProofsA64.P1.QueueCallers
import Fl4ProofsA64.P1.QueueCancel
import Fl4ProofsA64.P1.QueueChoose
import Fl4ProofsA64.P1.QueueEp
import Fl4ProofsA64.P1.QueueHeap
import Fl4ProofsA64.P1.QueueInv
import Fl4ProofsA64.P1.QueueObjs
import Fl4ProofsA64.P1.QueuePrio
import Fl4ProofsA64.P1.QueueRelease
import Fl4ProofsA64.P1.QueueRestart
import Fl4ProofsA64.P1.QueueSc
import Fl4ProofsA64.P1.QueueSched
import Fl4ProofsA64.P1.QueueSchedInv
import Fl4ProofsA64.P1.QueueSchedStep
import Fl4ProofsA64.P1.QueueSuspend
import Fl4ProofsA64.P1.Refill
import Fl4ProofsA64.P1.ScAff
import Fl4ProofsA64.P1.Store
import Fl4ProofsA64.P1.TimerRBDef
import Fl4ProofsA64.P1.QueueSwitch
import Fl4ProofsA64.P1.QueueSchedule
import Fl4ProofsA64.P1.RunVcpu
import Fl4ProofsA64.P1.QueueIpc
import Fl4ProofsA64.P1.QueueFoot
import Fl4ProofsA64.P1.QueueTimer
import Fl4ProofsA64.P1.TimerRBFrame
import Fl4ProofsA64.P1.TimerRBRead
import Fl4ProofsA64.P1.TimerRBWr
import Fl4ProofsA64.P1.TimerRBRot
import Fl4ProofsA64.P1.TimerRBRotP
import Fl4ProofsA64.P1.TimerRBRotH
import Fl4ProofsA64.P1.TimerRBRed
import Fl4ProofsA64.P1.TimerRBIns
import Fl4ProofsA64.P1.TimerRBInsH
import Fl4ProofsA64.P1.TimerRBFix
import Fl4ProofsA64.P1.TimerRBFixH
import Fl4ProofsA64.P1.TimerRBFixL
import Fl4ProofsA64.P1.TimerRBInsC
import Fl4ProofsA64.P1.TimerRBInsF
import Fl4ProofsA64.P1.TimerRBDel
import Fl4ProofsA64.P1.TimerRBDelH
import Fl4ProofsA64.P1.TimerRBDelC
import Fl4ProofsA64.P1.TimerRBRfxP
import Fl4ProofsA64.P1.TimerRBRfx
import Fl4ProofsA64.P1.TimerRBRfxL
import Fl4ProofsA64.P1.TimerRBRmv
import Fl4ProofsA64.P1.QueueTimerR
import Fl4ProofsA64.P1.RunVcpuRecv
import Fl4ProofsA64.P1.QueueSignal
import Fl4ProofsA64.P1.QueueFire
import Fl4ProofsA64.P1.QueueTimerSet
import Fl4ProofsA64.P1.RunVcpuKeep
import Fl4ProofsA64.P1.QueueFinal
import Fl4ProofsA64.P1.QueueFinSc
import Fl4ProofsA64.P1.QueueTcbInv
import Fl4ProofsA64.P1.QueueBind
import Fl4ProofsA64.P1.QueueReply
import Fl4ProofsA64.P1.QueueFootD
import Fl4ProofsA64.P1.QueueReplyPop
import Fl4ProofsA64.P1.QueueRecv
import Fl4ProofsA64.P1.FastFault
import Fl4ProofsA64.P1.FastSched
import Fl4ProofsA64.P1.VcpuHooks
import Fl4ProofsA64.P1.VmRootRd
import Fl4ProofsA64.P1.FastFin
import Fl4ProofsA64.P1.QueueSlots
import Fl4ProofsA64.P1.QueueCaiFr
import Fl4ProofsA64.P1.QueueDelete
import Fl4ProofsA64.P1.QueueDeleteRv
import Fl4ProofsA64.P1.QueueFinCap
import Fl4ProofsA64.P1.QueueFootS
import Fl4ProofsA64.P1.QueueInvoke
import Fl4ProofsA64.P1.QueueVsFin
import Fl4ProofsA64.P1.QueueBudgetG
import Fl4ProofsA64.P1.IbKeepHolds
import Fl4ProofsA64.P1.VcpuCheckInv
import Fl4ProofsA64.P1.QueueEntry
import Fl4ProofsA64.P1.QueueKeeps
import Fl4ProofsA64.P1.QueueCbs
import Fl4ProofsA64.P1.QueueFpu
import Fl4ProofsA64.P1.QueueDebug
import Fl4ProofsA64.P1.QueueXferA
import Fl4ProofsA64.P1.QueueEntryA
import Fl4ProofsA64.P1.QueueXfer
import Fl4ProofsA64.P1.QueueInvAll
import Fl4ProofsA64.P1.QueueXferFoot
import Fl4ProofsA64.P1.QueueDecSc
import Fl4ProofsA64.P1.QueueDecDom
import Fl4ProofsA64.P1.QueueDecCnode
import Fl4ProofsA64.P1.QueueDecTdx
import Fl4ProofsA64.P1.QueueEntryGaps
import Fl4ProofsA64.P1.QueueReplyX
import Fl4ProofsA64.P1.QueueDecDel
import Fl4ProofsA64.P1.QueueScBindVm
import Fl4ProofsA64.P1.QueueIpcFoot
import Fl4ProofsA64.P1.EntryXG
import Fl4ProofsA64.P1.EntryXGTop
import Fl4ProofsA64.P1.EntryFin
import Fl4ProofsA64.P1.QueueEntryGaps3
import Fl4ProofsA64.P1.QueueFinFr
import Fl4ProofsA64.P1.QueueYield
import Fl4ProofsA64.P1.QueueDelFin
import Fl4ProofsA64.P1.QueueFinCur
import Fl4ProofsA64.P1.QueueTimerC
import Fl4ProofsA64.P1.QueueFinThr
import Fl4ProofsA64.P1.QueueFinIo
import Fl4ProofsA64.P1.RunVcpuFam
import Fl4ProofsA64.P1.QueueSlots7
import Fl4ProofsA64.P1.QueueFinThr7
import Fl4ProofsA64.P1.QueueDecTcb
import Fl4ProofsA64.P1.QueueDecTcbRR
import Fl4ProofsA64.P1.QueueDecTcb2
import Fl4ProofsA64.P1.QueueSchedCtl
import Fl4ProofsA64.P1.QueueDelRv
import Fl4ProofsA64.P1.QueueIrqWide
import Fl4ProofsA64.P1.QueueDecTcbRv
import Fl4ProofsA64.P1.QueueFinRv
import Fl4ProofsA64.P1.QueueFinRvSt
import Fl4ProofsA64.P1.QueueFinRvReply
import Fl4ProofsA64.P1.QueueDecIrq
import Fl4ProofsA64.P1.QueueDecUt
import Fl4ProofsA64.P1.QueueHeapDrop
import Fl4ProofsA64.P1.QueueRetype
import Fl4ProofsA64.P1.QueueHeapFree
import Fl4ProofsA64.P1.QueueReset
import Fl4ProofsA64.P1.QueueHeapAdd
import Fl4ProofsA64.P1.QueueHeapAddO
import Fl4ProofsA64.P1.QueueHeapAddSc
import Fl4ProofsA64.P1.QueueHeapDbg
import Fl4ProofsA64.P1.QueueHeapAddTcb
import Fl4ProofsA64.P1.QueueRetypeP1
import Fl4ProofsA64.P1.QueueRetypeTcb
import Fl4ProofsA64.P1.QueueUtRetype
import Fl4ProofsA64.P1.QueueDecEpt
import Fl4ProofsA64.P1.QueueDecVs
import Fl4ProofsA64.P1.QueueEntryGaps4
import Fl4ProofsA64.P1.QueueDelVs5
import Fl4ProofsA64.P1.QueueDecDel5
import Fl4ProofsA64.P1.QueueEntryGaps5
import Fl4ProofsA64.P1.QueueDecVcpuA
import Fl4ProofsA64.P1.QueueDecVcpuRegA
import Fl4ProofsA64.P1.QueueDecVcpuStA
import Fl4ProofsA64.P1.QueueEntryGaps7
import Fl4ProofsA64.P1.QueueIrqWideA5
import Fl4ProofsA64.P1.QueueUnbindB
import Fl4ProofsA64.P1.QueueDelVsB
import Fl4ProofsA64.P1.QueueDecTcbB
import Fl4ProofsA64.P1.QueueDecVcpuB
import Fl4ProofsA64.P1.QueueEntryGaps7B
import Fl4ProofsA64.P1.QueueDecVcpuRunB
import Fl4ProofsA64.P1.QueueEntryGaps8
import Fl4ProofsA64.P1.QueueScBindV
import Fl4ProofsA64.P1.QueueDecTcbC
import Fl4ProofsA64.P1.QueueEntryGaps9
import Fl4ProofsA64.P1.QueueDelVsV
import Fl4ProofsA64.P1.QueueDecTcbV
import Fl4ProofsA64.P1.QueueEntryGaps10
import Fl4ProofsA64.P1.QueueDelPlaceFalse
import Fl4ProofsA64.P1.QueueSlotFieldsFalse
import Fl4ProofsA64.P1.QueueSlotTy
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut n : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  for (c, _) in env.constants.map₁.toList do
    if (`Fl4ProofsA64.P1).isPrefixOf c || (`Fl4ProofsA64.P2).isPrefixOf c then
      n := n + 1
      let axs ← Lean.collectAxioms c
      for a in axs do
        if !(ok.contains a) then bad := bad.push (c, a)
  logInfo (s!"A64 P1+P2 constants checked: {n}; outside propext/Classical.choice/Quot.sound: {bad.size} {(bad.toList.take 20).map (fun p => (p.1, p.2))}" : String)
#print axioms Fl4ProofsA64.P1.decGap_sc
#print axioms Fl4ProofsA64.P1.InvGaps2.gaps
#print axioms Fl4ProofsA64.P1.decGap_tdx
#print axioms Fl4ProofsA64.P1.decGap_reply
#print axioms Fl4ProofsA64.P1.decGap_cnode2

#print axioms Fl4ProofsA64.P1.InvGaps3.gaps
#print axioms Fl4ProofsA64.P1.sched.suspend.keepF
#print axioms Fl4ProofsA64.P1.scYieldGap_holds

#print axioms Fl4ProofsA64.P1.delGaps_of
#print axioms Fl4ProofsA64.P1.finGap_reply
#print axioms Fl4ProofsA64.P1.FinGapsAt.kinds
#print axioms Fl4ProofsA64.P1.fin_thread.curR

#print axioms Fl4ProofsA64.P1.finGap_ioPort
#print axioms Fl4ProofsA64.P1.sched.set_thread_state.rvi
#print axioms Fl4ProofsA64.P1.vcpu.run_tail.rvi

#print axioms Fl4ProofsA64.P1.W7.blk_of_capw
#print axioms Fl4ProofsA64.P1.W7.delGaps_of
#print axioms Fl4ProofsA64.P1.W7.decGap_cnode2
#print axioms Fl4ProofsA64.P1.vcpu.detach.w7
#print axioms Fl4ProofsA64.P1.fin_thread.blk7
#print axioms Fl4ProofsA64.P1.fin_thread.curR7
#print axioms Fl4ProofsA64.P1.W7.finGap_thread
#print axioms Fl4ProofsA64.P1.W7.delGaps_of_gaps
#print axioms Fl4ProofsA64.P1.tcb.decode_write_registers.dec
#print axioms Fl4ProofsA64.P1.tcb.decode_get_breakpoint.dec
#print axioms Fl4ProofsA64.P1.tcb.decode_read_registers.dec
#print axioms Fl4ProofsA64.P1.decGap_thread
#print axioms Fl4ProofsA64.P1.tcb.decode.dec
#print axioms Fl4ProofsA64.P1.tcb.decode_set_high_vspace.dec
#print axioms Fl4ProofsA64.P1.tcb.decode_set_pac_keys.dec
#print axioms Fl4ProofsA64.P1.tcb.install_tcb_cap.cur0
#print axioms Fl4ProofsA64.P1.sched.suspend.blk7
#print axioms Fl4ProofsA64.P1.tcb.decode_read_registers.dec7
#print axioms Fl4ProofsA64.P1.decGap_schedControl
#print axioms Fl4ProofsA64.P1.schedcontext.configure_flags.blk
#print axioms Fl4ProofsA64.P1.W7.R.delGaps_of_gaps
#print axioms Fl4ProofsA64.P1.W7.R.decGap_cnode_rv
#print axioms Fl4ProofsA64.P1.W7.R.finGap_reply0
#print axioms Fl4ProofsA64.P1.W7.R.cdt.revoke.cur0
#print axioms Fl4ProofsA64.P1.irq_slotW_a64
#print axioms Fl4ProofsA64.P1.W7.R.decGap_thread
#print axioms Fl4ProofsA64.P1.W7.R.tcb.decode.dec
#print axioms Fl4ProofsA64.P1.Stalled.restart0R
#print axioms Fl4ProofsA64.P1.W7.R.finRvAt_of
#print axioms Fl4ProofsA64.P1.W7.R.decGap_cnode_rv2
#print axioms Fl4ProofsA64.P1.W7.R.decGap_thread2
#print axioms Fl4ProofsA64.P1.fin_ntfn_obj.rvi
#print axioms Fl4ProofsA64.P1.fin_endpoint.rvi
#print axioms Fl4ProofsA64.P1.fin_sc.rvst
#print axioms Fl4ProofsA64.P1.fin_thread.rvi
#print axioms Fl4ProofsA64.P1.sched.suspend.rvi
#print axioms Fl4ProofsA64.P1.W7.R.finRvRest_of3
#print axioms Fl4ProofsA64.P1.W7.R.decGap_cnode_rv3
#print axioms Fl4ProofsA64.P1.W7.R.decGap_thread3
#print axioms Fl4ProofsA64.P1.schedcontext.donate.genR
#print axioms Fl4ProofsA64.P1.ipc.reply_remove.rvi
#print axioms Fl4ProofsA64.P1.fin_reply.rvi
#print axioms Fl4ProofsA64.P1.W7.R.finRvRest3_of4
#print axioms Fl4ProofsA64.P1.W7.R.decGap_cnode_rv4
#print axioms Fl4ProofsA64.P1.W7.R.decGap_thread4
#print axioms Fl4ProofsA64.P1.layout.irq.of.lt
#print axioms Fl4ProofsA64.P1.interrupt.decode_irq_control_msi.dec
#print axioms Fl4ProofsA64.P1.interrupt.decode_irq_control.dec
#print axioms Fl4ProofsA64.P1.decGap_irqControl
#print axioms Fl4ProofsA64.P1.cdt.delete_one.irq_cur0R
#print axioms Fl4ProofsA64.P1.decGap_irqHandler
#print axioms Fl4ProofsA64.P1.decGap_ioPortControl
#print axioms Fl4ProofsA64.P1.decGap_ioPort
#print axioms Fl4ProofsA64.P1.untyped.decode.dec
#print axioms Fl4ProofsA64.P1.decGap_untyped
#print axioms Fl4ProofsA64.P1.ept.decode.dec
#print axioms Fl4ProofsA64.P1.decGap_ept
#print axioms Fl4ProofsA64.P1.BlkOK.drop
#print axioms Fl4ProofsA64.P1.resetP1Step_holds
#print axioms Fl4ProofsA64.P1.retypeP1Step
#print axioms Fl4ProofsA64.P1.UtRetypeP3.utPlace
#print axioms Fl4ProofsA64.P1.Cur0.zr
#print axioms Fl4ProofsA64.P1.Cur0.wrV
#print axioms Fl4ProofsA64.P1.vspace.install_page.cur0
#print axioms Fl4ProofsA64.P1.ept.install_s2_leaf.cur0
#print axioms Fl4ProofsA64.P1.vspace.map_high_page_table.dec
#print axioms Fl4ProofsA64.P1.ept.map_table.dec
#print axioms Fl4ProofsA64.P1.vspace.decode_page_table.dec
#print axioms Fl4ProofsA64.P1.vspace.mapped_entry.vs
#print axioms Fl4ProofsA64.P1.vspace.reply1.bxiA
#print axioms Fl4ProofsA64.P1.vspace.decode_page_flush.dec
#print axioms Fl4ProofsA64.P1.vspace.decode_vspace_flush.dec
#print axioms Fl4ProofsA64.P1.vspace.decode_test_and_clear_accessed.dec
#print axioms Fl4ProofsA64.P1.ept.map_frame.dec
#print axioms Fl4ProofsA64.P1.vspace.decode_high_page_map.dec
#print axioms Fl4ProofsA64.P1.vspace.decode_page_map.dec
#print axioms Fl4ProofsA64.P1.vspace.insert_subframes.cur0
#print axioms Fl4ProofsA64.P1.vspace.derive_subframe.dec
#print axioms Fl4ProofsA64.P1.vspace.decode_frame.dec
#print axioms Fl4ProofsA64.P1.vspace.decode.dec
#print axioms Fl4ProofsA64.P1.decGap_vspace
#print axioms Fl4ProofsA64.P1.InvGaps4.gaps
#print axioms Fl4ProofsA64.P1.kernel_entry.entry_of4
#print axioms Fl4ProofsA64.P1.vspace.unmap_page_table.vsA
#print axioms Fl4ProofsA64.P1.ept.unmap_table.vsA
#print axioms Fl4ProofsA64.P1.vspace.unmap_page.vsA
#print axioms Fl4ProofsA64.P1.W7.R.A5.fin_vs
#print axioms Fl4ProofsA64.P1.W7.R.A5.fin_all
#print axioms Fl4ProofsA64.P1.W7.R.A5.cdt.finalise_slot_immediate.cur0
#print axioms Fl4ProofsA64.P1.W7.R.A5.cdt.finalise_slot_deferred.cur0
#print axioms Fl4ProofsA64.P1.W7.R.A5.delGaps_of
#print axioms Fl4ProofsA64.P1.W7.R.A5.delGaps_of_gaps4
#print axioms Fl4ProofsA64.P1.W7.R.A5.decGap_cnode_rv4
#print axioms Fl4ProofsA64.P1.W7.R.A5.tcb.decode.dec
#print axioms Fl4ProofsA64.P1.W7.R.A5.decGap_thread4
#print axioms Fl4ProofsA64.P1.interrupt.decode_irq_handler.dec5
#print axioms Fl4ProofsA64.P1.decGap_irqHandler5
#print axioms Fl4ProofsA64.P1.InvGaps5.gaps
#print axioms Fl4ProofsA64.P1.kernel_entry.entry_of5A
#print axioms Fl4ProofsA64.P1.vcpu.stall_vcpu.stalled
#print axioms Fl4ProofsA64.P1.Stalled.restartT
#print axioms Fl4ProofsA64.P1.vcpu.decode_ack_vppi.dec
#print axioms Fl4ProofsA64.P1.decGap_vcpuA
#print axioms Fl4ProofsA64.P1.InvGaps6.gaps
#print axioms Fl4ProofsA64.P1.kernel_entry.entry_of6A
#print axioms Fl4ProofsA64.P1.vcpu.reg_set.cur0A
#print axioms Fl4ProofsA64.P1.vcpu.sync_vgic_status.cur0A
#print axioms Fl4ProofsA64.P1.vcpu.reply1.bxiA
#print axioms Fl4ProofsA64.P1.vcpu.decode_read_reg.dec
#print axioms Fl4ProofsA64.P1.vcpu.decode_write_reg.dec
#print axioms Fl4ProofsA64.P1.vcpu.decode_inject_irq.dec
#print axioms Fl4ProofsA64.P1.VcJ.wr
#print axioms Fl4ProofsA64.P1.VcJ.regSet
#print axioms Fl4ProofsA64.P1.VcJ.sync
#print axioms Fl4ProofsA64.P1.VcJ.copyFrom
#print axioms Fl4ProofsA64.P1.VcJ.lrLoop0
#print axioms Fl4ProofsA64.P1.VcJ.setReg
#print axioms Fl4ProofsA64.P1.VcJ.gprLoop
#print axioms Fl4ProofsA64.P1.vcpu.write_state_from_frame.vcj
#print axioms Fl4ProofsA64.P1.vcpu.st_restart
#print axioms Fl4ProofsA64.P1.vcpu.read_state_to_frame.cur0A
#print axioms Fl4ProofsA64.P1.vcpu.decode_state_transfer.dec
#print axioms Fl4ProofsA64.P1.decGap_vcpuB
#print axioms Fl4ProofsA64.P1.InvGaps7.gaps
#print axioms Fl4ProofsA64.P1.kernel_entry.entry_of7A
#print axioms Fl4ProofsA64.P1.W7.R.A5.I.DelCapOK.of7
#print axioms Fl4ProofsA64.P1.W7.R.A5.I.DelCapOK.to7
#print axioms Fl4ProofsA64.P1.W7.R.A5.I.FinGapAt.ofR
#print axioms Fl4ProofsA64.P1.W7.R.A5.I.FinGapAt.toR
#print axioms Fl4ProofsA64.P1.vcpu.complete_run.ub
#print axioms Fl4ProofsA64.P1.vcpu.unbind.ub
#print axioms Fl4ProofsA64.P1.vcpu.detach.ub
#print axioms Fl4ProofsA64.P1.fin_thread.ubR
#print axioms Fl4ProofsA64.P1.UbF.ofW
#print axioms Fl4ProofsA64.P1.sched.set_thread_state.running_ub
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.finGapB_thread
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.finRv_thread
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.fin_all
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.delGaps_of
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.decGap_cnode_rv4
#print axioms Fl4ProofsA64.P1.vcpu.cancel_run.w8
#print axioms Fl4ProofsA64.P1.sched.suspend.blk8
#print axioms Fl4ProofsA64.P1.tcb.decode_read_registers.dec8
#print axioms Fl4ProofsA64.P1.tcb.decode_copy_registers.dec8
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.tcb.decode.dec
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.decGap_thread4
#print axioms Fl4ProofsA64.P1.decGap_irqHandler5B
#print axioms Fl4ProofsA64.P1.vcpu.decode_set_tcb.dec
#print axioms Fl4ProofsA64.P1.decGap_vcpuC
#print axioms Fl4ProofsA64.P1.InvGaps7B.gaps
#print axioms Fl4ProofsA64.P1.kernel_entry.entry_of7B
#print axioms Fl4ProofsA64.P1.vcpu.check.ub
#print axioms Fl4ProofsA64.P1.vcpu.decode_run.dec
#print axioms Fl4ProofsA64.P1.decGap_vcpuD
#print axioms Fl4ProofsA64.P1.InvGaps8.gaps
#print axioms Fl4ProofsA64.P1.kernel_entry.entry_of8A
-- gen 27
#print axioms Fl4ProofsA64.P1.OmS
#print axioms Fl4ProofsA64.P1.ownA_vc
#print axioms Fl4ProofsA64.P1.blkW_wrO
#print axioms Fl4ProofsA64.P1.FootDU.kodO
#print axioms Fl4ProofsA64.P1.ScBindOwnV
#print axioms Fl4ProofsA64.P1.ScBindOwnV.of_rcv
#print axioms Fl4ProofsA64.P1.migrate_tail_fV
#print axioms Fl4ProofsA64.P1.smp.migrate_tcb.frame_fV
#print axioms Fl4ProofsA64.P1.smp.migrate_tcb.kw_fV
#print axioms Fl4ProofsA64.P1.schedcontext.bind_tcb.blkF_fV
#print axioms Fl4ProofsA64.P1.sc_bind_tcb.blkF_fV
#print axioms Fl4ProofsA64.P1.sc_bind_stall.blk_fV
#print axioms Fl4ProofsA64.P1.schedcontext.decode.dec_fV
#print axioms Fl4ProofsA64.P1.decGap_sc_fV
#print axioms Fl4ProofsA64.P1.cfDV
#print axioms Fl4ProofsA64.P1.schedcontext.configure_flags.blkV
#print axioms Fl4ProofsA64.P1.schedcontext.decode_sched_control.decV
#print axioms Fl4ProofsA64.P1.decGap_schedControlV
#print axioms Fl4ProofsA64.P1.tcs_tail2V
#print axioms Fl4ProofsA64.P1.tcb.thread_control_sched.decV
#print axioms Fl4ProofsA64.P1.TcbPlace9
#print axioms Fl4ProofsA64.P1.TcbPlace9.of8
#print axioms Fl4ProofsA64.P1.TcbPlace9.scBindOwnV
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.C.tcb.decode_read_registers.dec8
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.C.tcb.copy_registers.blk8
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.C.tcb.decode_copy_registers.dec8
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.C.Cur0R.resched
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.C.tcb.install_tcb_cap.cur0
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.C.tcb.install_buffer.cur0
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.C.inst_bind
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.C.tcb.decode_set_timeout_endpoint.dec
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.C.tcb.decode_set_space.dec
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.C.tcb.decode_configure.dec
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.C.tcb.decode_set_sched_params.dec
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.C.tcb.decode_set_ipc_buffer.dec7
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.C.tcb.decode_set_high_vspace.dec
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.C.tcb.decode.dec
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.C.decGap_thread
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.C.decGap_thread4
#print axioms Fl4ProofsA64.P1.InvGaps9
#print axioms Fl4ProofsA64.P1.InvGaps9.of8
#print axioms Fl4ProofsA64.P1.InvGaps9.gaps
#print axioms Fl4ProofsA64.P1.kernel_entry.entry_of9A
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.VcCap
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.FrVc
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.FinRvRestKind5
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.FinRvRest5
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.FinGapsAt5
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.FinGaps5
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.FinGapsAt5.of4
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.FinGaps5.of4
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.vcpu.finalise.ub
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.DelGapsAt
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.DelGaps
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.cdt.finalise_slot_immediate.cur0
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.cdt.delete.cur0
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.cdt.revoke.cur0
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.cnode_del
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.cnode_rev
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.cnode.decode.dec2
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.decGap_cnode2
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.DelPlaceAt
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.DelPlace
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.DelPlace.toB
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.DelPlaceAt.frmV
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.fin_vs
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.cdt.empty_slot.cur0
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.cdt.swap.cur0
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.cdt.cap_swap_for_delete.cur0
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.cdt.finalise_slot_deferred.cur0
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.cdt.delete_deferred.cur0
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.cdt.empty_slot.c0
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.finGapB_thread
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.finRv_thread
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.finGap_irq0
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.finRv_irq
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.finRvAt_of
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.finRvRest_of3
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.fin_vcpuV
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.FinRvKindV
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.finRvAtV_of
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.ofC0V
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.fin_all
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.delGaps_of
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.delGaps_of_gaps5
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.decGap_cnode_rv5
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.C.tcb.decode_read_registers.dec8
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.C.tcb.copy_registers.blk8
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.C.tcb.decode_copy_registers.dec8
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.C.Cur0R.resched
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.C.tcb.install_tcb_cap.cur0
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.C.tcb.install_buffer.cur0
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.C.inst_bind
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.C.tcb.decode_set_timeout_endpoint.dec
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.C.tcb.decode_set_space.dec
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.C.tcb.decode_configure.dec
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.C.tcb.decode_set_sched_params.dec
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.C.tcb.decode_set_ipc_buffer.dec7
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.C.tcb.decode_set_high_vspace.dec
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.C.tcb.decode.dec
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.C.decGap_thread
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.C.decGap_thread4
#print axioms Fl4ProofsA64.P1.InvGaps10
#print axioms Fl4ProofsA64.P1.InvGaps10.gaps
#print axioms Fl4ProofsA64.P1.kernel_entry.entry_of10A
-- gen 28
#print axioms Fl4ProofsA64.P1.DPF.spec_tot
#print axioms Fl4ProofsA64.P1.DPF.shr_eq
#print axioms Fl4ProofsA64.P1.DPF.irqW0
#print axioms Fl4ProofsA64.P1.DPF.bigIrq
#print axioms Fl4ProofsA64.P1.DPF.decode_irqH
#print axioms Fl4ProofsA64.P1.DPF.slot_cap_dec
#print axioms Fl4ProofsA64.P1.DPF.wadd0
#print axioms Fl4ProofsA64.P1.DPF.irqH_state
#print axioms Fl4ProofsA64.P1.DPF.bigIrq_ge
#print axioms Fl4ProofsA64.P1.DPF.bigIrq_ge128
#print axioms Fl4ProofsA64.P1.DPF.irq_read_false
#print axioms Fl4ProofsA64.P1.DelPlaceAt.cap_false
#print axioms Fl4ProofsA64.P1.DelGapsAt.cap_false
#print axioms Fl4ProofsA64.P1.W7.DelPlaceAt.cap_false
#print axioms Fl4ProofsA64.P1.W7.DelGapsAt.cap_false
#print axioms Fl4ProofsA64.P1.W7.R.DelPlaceAt.cap_false
#print axioms Fl4ProofsA64.P1.W7.R.DelGapsAt.cap_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.DelPlaceAt.cap_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.DelGapsAt.cap_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.DelPlaceAt.cap_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.DelGapsAt.cap_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.DelPlaceAt.cap_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.DelGapsAt.cap_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.DelPlaceAt.dec_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.DelPlace.entAt_false
#print axioms Fl4ProofsA64.P1.InvGaps3.del_false
#print axioms Fl4ProofsA64.P1.InvGaps4.place_false
#print axioms Fl4ProofsA64.P1.InvGaps5.place_false
#print axioms Fl4ProofsA64.P1.InvGaps6.place_false
#print axioms Fl4ProofsA64.P1.InvGaps7.place_false
#print axioms Fl4ProofsA64.P1.InvGaps7B.place_false
#print axioms Fl4ProofsA64.P1.InvGaps8.place_false
#print axioms Fl4ProofsA64.P1.InvGaps9.place_false
#print axioms Fl4ProofsA64.P1.InvGaps10.place_false
#print axioms Fl4ProofsA64.P1.VcpuObjA.false_at

-- gen 29
#print axioms Fl4ProofsA64.P1.SFF.unpack_vcpu1
#print axioms Fl4ProofsA64.P1.SFF.sext48_one
#print axioms Fl4ProofsA64.P1.SFF.decode_vcpu1
#print axioms Fl4ProofsA64.P1.SFF.decode_ictl
#print axioms Fl4ProofsA64.P1.SFF.badVa
#print axioms Fl4ProofsA64.P1.SFF.shr_u64_eq
#print axioms Fl4ProofsA64.P1.SFF.shl_eq
#print axioms Fl4ProofsA64.P1.SFF.up0
#print axioms Fl4ProofsA64.P1.SFF.upW1
#print axioms Fl4ProofsA64.P1.SFF.bitT
#print axioms Fl4ProofsA64.P1.SFF.bit53
#print axioms Fl4ProofsA64.P1.SFF.bit52
#print axioms Fl4ProofsA64.P1.SFF.bit58
#print axioms Fl4ProofsA64.P1.SFF.asid1
#print axioms Fl4ProofsA64.P1.SFF.fc_small
#print axioms Fl4ProofsA64.P1.SFF.decode_frm
#print axioms Fl4ProofsA64.P1.SFF.badVa_not
#print axioms Fl4ProofsA64.P1.SFF.one_not_aligned
#print axioms Fl4ProofsA64.P1.SFF.wadd0'
#print axioms Fl4ProofsA64.P1.SFF.capw_state
#print axioms Fl4ProofsA64.P1.SFF.tcb_slot
#print axioms Fl4ProofsA64.P1.SFF.tcb_wval
#print axioms Fl4ProofsA64.P1.SFF.next_state
#print axioms Fl4ProofsA64.P1.SFF.prev_state
#print axioms Fl4ProofsA64.P1.SFF.vco_state
#print axioms Fl4ProofsA64.P1.SFF.frm_state
#print axioms Fl4ProofsA64.P1.SFF.irq_state
#print axioms Fl4ProofsA64.P1.SFF.vf_state
#print axioms Fl4ProofsA64.P1.DelPlaceAt.next_false
#print axioms Fl4ProofsA64.P1.DelPlaceAt.prev_false
#print axioms Fl4ProofsA64.P1.DelGapsAt.next_false
#print axioms Fl4ProofsA64.P1.W7.DelPlaceAt.next_false
#print axioms Fl4ProofsA64.P1.W7.DelPlaceAt.prev_false
#print axioms Fl4ProofsA64.P1.W7.DelGapsAt.next_false
#print axioms Fl4ProofsA64.P1.W7.R.DelPlaceAt.next_false
#print axioms Fl4ProofsA64.P1.W7.R.DelPlaceAt.prev_false
#print axioms Fl4ProofsA64.P1.W7.R.DelGapsAt.next_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.DelPlaceAt.next_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.DelPlaceAt.prev_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.DelGapsAt.next_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.DelPlaceAt.next_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.DelPlaceAt.prev_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.DelGapsAt.next_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.DelGapsAt.next_false
#print axioms Fl4ProofsA64.P1.DelPlaceAt.irq_false
#print axioms Fl4ProofsA64.P1.W7.DelPlaceAt.irq_false
#print axioms Fl4ProofsA64.P1.W7.R.DelPlaceAt.irq_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.DelPlaceAt.irq_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.DelPlaceAt.irq_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.DelPlaceAt.frm_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.DelPlaceAt.frm_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.DelGapsAt.frm_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.DelGapsAt.frm_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.DelGapsAt.frm_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.V.DelPlaceAt.vco_false
#print axioms Fl4ProofsA64.P1.VcPl.vcb_false
#print axioms Fl4ProofsA64.P1.VcPl.rcv_false
#print axioms Fl4ProofsA64.P1.W7.R.A5.B.DelPlaceAt.vc_false
#print axioms Fl4ProofsA64.P1.TcbPlace9.rcv_false
#print axioms Fl4ProofsA64.P1.TcbPlace8.rcv_false
#print axioms Fl4ProofsA64.P1.W7.R.ST.okinj
#print axioms Fl4ProofsA64.P1.W7.R.ST.or_and_eq
#print axioms Fl4ProofsA64.P1.W7.R.ST.and_and_self'
#print axioms Fl4ProofsA64.P1.W7.R.ST.link_bits
#print axioms Fl4ProofsA64.P1.W7.R.ST.fb_bits
#print axioms Fl4ProofsA64.P1.W7.R.ST.FB
#print axioms Fl4ProofsA64.P1.W7.R.ST.fbc1
#print axioms Fl4ProofsA64.P1.W7.R.ST.fbc2
#print axioms Fl4ProofsA64.P1.W7.R.ST.fbc3
#print axioms Fl4ProofsA64.P1.W7.R.ST.fb_val
#print axioms Fl4ProofsA64.P1.W7.R.ST.sx_val
#print axioms Fl4ProofsA64.P1.W7.R.ST.hiM
#print axioms Fl4ProofsA64.P1.W7.R.ST.sx_idem
#print axioms Fl4ProofsA64.P1.W7.R.ST.sx_mask
#print axioms Fl4ProofsA64.P1.W7.R.ST.sx0
#print axioms Fl4ProofsA64.P1.W7.R.ST.decode_zero
#print axioms Fl4ProofsA64.P1.W7.R.ST.domW
#print axioms Fl4ProofsA64.P1.W7.R.ST.decode_dom
#print axioms Fl4ProofsA64.P1.W7.R.ST.LinkOK
#print axioms Fl4ProofsA64.P1.W7.R.ST.NextOK
#print axioms Fl4ProofsA64.P1.W7.R.ST.CapIn
#print axioms Fl4ProofsA64.P1.W7.R.ST.CapTy
#print axioms Fl4ProofsA64.P1.W7.R.ST.SlotOK
#print axioms Fl4ProofsA64.P1.W7.R.ST.SlotTy
#print axioms Fl4ProofsA64.P1.W7.R.ST.OSOK
#print axioms Fl4ProofsA64.P1.W7.R.ST.J
#print axioms Fl4ProofsA64.P1.W7.R.ST.CapTy.null
#print axioms Fl4ProofsA64.P1.W7.R.ST.CapTy.domain
#print axioms Fl4ProofsA64.P1.W7.R.ST.wv
#print axioms Fl4ProofsA64.P1.W7.R.ST.OSOK.al
#print axioms Fl4ProofsA64.P1.W7.R.ST.OSOK.al0
#print axioms Fl4ProofsA64.P1.W7.R.ST.OSOK.cw
#print axioms Fl4ProofsA64.P1.W7.R.ST.OSOK.cw0
#print axioms Fl4ProofsA64.P1.W7.R.ST.SlotOK.of_eq
#print axioms Fl4ProofsA64.P1.W7.R.ST.SlotTy.frame
#print axioms Fl4ProofsA64.P1.W7.R.ST.vals
#print axioms Fl4ProofsA64.P1.W7.R.ST.other_keep
#print axioms Fl4ProofsA64.P1.W7.R.ST.slot_prev_eq
#print axioms Fl4ProofsA64.P1.W7.R.ST.slot_next_of
#print axioms Fl4ProofsA64.P1.W7.R.ST.set_next_eq
#print axioms Fl4ProofsA64.P1.W7.R.ST.set_prev_eq
#print axioms Fl4ProofsA64.P1.W7.R.ST.set_fb_eq_t
#print axioms Fl4ProofsA64.P1.W7.R.ST.set_fb_eq_f
#print axioms Fl4ProofsA64.P1.W7.R.ST.clear_eq
#print axioms Fl4ProofsA64.P1.W7.R.ST.pcd_null
#print axioms Fl4ProofsA64.P1.W7.R.ST.J.next
#print axioms Fl4ProofsA64.P1.W7.R.ST.J.prev
#print axioms Fl4ProofsA64.P1.W7.R.ST.J.fb
#print axioms Fl4ProofsA64.P1.W7.R.ST.J.clear
#print axioms Fl4ProofsA64.P1.W7.R.ST.cdt.empty_slot.ty
#print axioms Fl4ProofsA64.P1.W7.R.ST.TrivK
#print axioms Fl4ProofsA64.P1.W7.R.ST.finalise_cap.triv
#print axioms Fl4ProofsA64.P1.W7.R.ST.CapTrivAt
#print axioms Fl4ProofsA64.P1.W7.R.ST.cdt.finalise_slot_immediate.triv
#print axioms Fl4ProofsA64.P1.W7.R.ST.cdt.delete.triv
#print axioms Fl4ProofsA64.P1.W7.R.ST.J.witness
#print axioms Fl4ProofsA64.P1.W7.R.ST.EntApart
#print axioms Fl4ProofsA64.P1.W7.R.ST.SlotTyEnt
#print axioms Fl4ProofsA64.P1.W7.R.ST.SlotTyEnt.entAt
