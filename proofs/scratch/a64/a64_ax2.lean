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
#print axioms Fl4ProofsA64.P1.schedcontext.donate.kwCB
#print axioms Fl4ProofsA64.P1.schedcontext.donate.idle
#print axioms Fl4ProofsA64.P1.ipc.reply_pop.blk
#print axioms Fl4ProofsA64.P1.fin_reply.blk
#print axioms Fl4ProofsA64.P1.faults.set_fault.rv
#print axioms Fl4ProofsA64.P1.syscall.handle_recv.bxi
#print axioms Fl4ProofsA64.P1.faults.handle_fault.bxi
#print axioms Fl4ProofsA64.P1.faults.handle_timeout.bxi
#print axioms Fl4ProofsA64.P1.notification.receive_signal.ipc
#print axioms Fl4ProofsA64.P1.sched.reschedule_required.rv0
#print axioms Fl4ProofsA64.P1.fault_accG
#print axioms Fl4ProofsA64.P1.fault_acc
#print axioms Fl4ProofsA64.P1.fault_sync2
#print axioms Fl4ProofsA64.P1.enqueue_ne
