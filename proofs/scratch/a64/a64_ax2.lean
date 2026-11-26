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
#print axioms Fl4ProofsA64.P1.tcbqueue.append.rel
#print axioms Fl4ProofsA64.P1.sporadic.budget_check.ordered
#print axioms Fl4ProofsA64.P1.smp.add_pending.spec
#print axioms Fl4ProofsA64.P1.smp.remote_queue_update.spec
#print axioms Fl4ProofsA64.P1.smp.send_pending.fp
#print axioms Fl4ProofsA64.P1.sched.suspend.inv
#print axioms Fl4ProofsA64.P1.sched.suspend.all
#print axioms Fl4ProofsA64.P1.vcpu.cancel_run.idle
#print axioms Fl4ProofsA64.P2.PathObl.vm_isProg
#print axioms Fl4ProofsA64.P2.PathObl.vm_noZero
#print axioms Fl4ProofsA64.P2.PathObl.vm_prog
#print axioms Fl4ProofsA64.P1.syscall_decline
#print axioms Fl4ProofsA64.P1.FastAgree.of_acc
#print axioms Fl4ProofsA64.P1.vcpu.report.keep
#print axioms Fl4ProofsA64.P1.set_vm_root_same
#print axioms Fl4ProofsA64.P1.sched.switch_to_thread.inv
#print axioms Fl4ProofsA64.P1.smp.send_pending.two
#print axioms Fl4ProofsA64.P1.RunVcpuInv.zero
#print axioms Fl4ProofsA64.P1.sched.suspend.inv_rv
#print axioms Fl4ProofsA64.P1.sched.suspend.all_rv
#print axioms Fl4ProofsA64.P1.RecvPre.stt
#print axioms Fl4ProofsA64.P1.migrate_vcpu_idle
#print axioms Fl4ProofsA64.P1.smp.migrate_tcb.frame
#print axioms Fl4ProofsA64.P1.migrate_tail
#print axioms Fl4ProofsA64.P1.schedcontext.donate.ipc
#print axioms Fl4ProofsA64.P1.endpoint.send_ipc.ipc
#print axioms Fl4ProofsA64.P1.endpoint.receive_ipc.ipc
#print axioms Fl4ProofsA64.P1.notification.complete_signal.ipc
#print axioms Fl4ProofsA64.P1.smp.remote_tcb_stall.ipi
#print axioms Fl4ProofsA64.P1.sched.schedule.inv
#print axioms Fl4ProofsA64.P1.TFB.tf
