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
