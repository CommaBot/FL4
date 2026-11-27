/-
# P2 (p2lf): `cancel_ipc` of a thread blocked in `Recv`, on the guarded store

`ipc.cancel_ipc.guard_recv`: on any store `gS` answering `R` reads and `W` writes as `st`, `cancel_ipc` of a thread
`t` in `BLOCKED_ON_RECV` (a fired timer's bound thread waiting in `Recv`, the plan's `waiter`) is its real run: the
fault word cleared, its state and `BLOCK_OBJ` read, the guarded `ep_dequeue` from that endpoint, its `REPLY_OBJ`, the
guarded `reply_unlink` when it has a reply, and the guarded `set_thread_state … INACTIVE` (premises at the real
intermediate states).

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireQ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (bind_guard_congr)

section gst
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

theorem recv_ne_send : sched.TS_BLOCKED_ON_RECV ≠ sched.TS_BLOCKED_ON_SEND := by
  unfold sched.TS_BLOCKED_ON_RECV sched.TS_BLOCKED_ON_SEND; decide

set_option maxHeartbeats 4000000 in
/-- **`cancel_ipc` of a thread in `Recv`** (module docstring). -/
theorem ipc.cancel_ipc.guard_recv {A : Type} (ar : machine.Arch A) (X : S) (a : A) (t : U64)
    (wF : W (faultA t)) (rS : R (stA t)) (rB : R (blockA t)) (rRp : R (replyA t))
    (hs : L.mem (L.wr X (faultA t) fl4_abi.consts.fault.NullFault) (stA t) = sched.TS_BLOCKED_ON_RECV)
    (hdq : endpoint.ep_dequeue gS (L.wr X (faultA t) fl4_abi.consts.fault.NullFault)
        (L.mem (L.wr X (faultA t) fl4_abi.consts.fault.NullFault) (blockA t)) t =
      endpoint.ep_dequeue st (L.wr X (faultA t) fl4_abi.consts.fault.NullFault)
        (L.mem (L.wr X (faultA t) fl4_abi.consts.fault.NullFault) (blockA t)) t)
    (hk : ∀ X2, endpoint.ep_dequeue st (L.wr X (faultA t) fl4_abi.consts.fault.NullFault)
        (L.mem (L.wr X (faultA t) fl4_abi.consts.fault.NullFault) (blockA t)) t = ok X2 →
      (L.mem X2 (replyA t) ≠ 0#u64 →
        ipc.reply_unlink gS X2 (L.mem X2 (replyA t)) t = ipc.reply_unlink st X2 (L.mem X2 (replyA t)) t) ∧
      ∀ X3, (if L.mem X2 (replyA t) != 0#u64 then ipc.reply_unlink st X2 (L.mem X2 (replyA t)) t else ok X2) =
          ok X3 →
        sched.set_thread_state gS X3 t sched.TS_INACTIVE = sched.set_thread_state st X3 t sched.TS_INACTIVE) :
    ipc.cancel_ipc gS ar X a t = ipc.cancel_ipc st ar X a t := by
  have e1 : faults.clear_fault st X t = ok (L.wr X (faultA t) fl4_abi.consts.fault.NullFault) := by
    unfold faults.clear_fault
    exact eq_of_spec_fd (obj.Tcb.set_fault_type.spec (L := L) X t _)
  have e1g : faults.clear_fault gS X t = ok (L.wr X (faultA t) fl4_abi.consts.fault.NullFault) := by
    unfold faults.clear_fault
    rw [PathObl.obj.Tcb.set_fault_type.guard (gS := gS) t X _ wF]
    exact eq_of_spec_fd (obj.Tcb.set_fault_type.spec (L := L) X t _)
  unfold ipc.cancel_ipc
  rw [e1, e1g]
  simp only [bind_ok]
  rw [PathObl.obj.Tcb.state.guard (gS := gS) t _ rS, eq_of_spec_fd (obj.Tcb.state.spec (L := L) _ t), hs]
  simp only [bind_ok, if_neg recv_ne_send, eq_self_iff_true, if_true, ↓reduceIte]
  rw [PathObl.obj.Tcb.block_obj.guard (gS := gS) t _ rB, eq_of_spec_fd (obj.Tcb.block_obj.spec (L := L) _ t)]
  simp only [bind_ok]
  rw [hdq]
  refine bind_guard_congr rfl fun X2 h2 => ?_
  obtain ⟨hru, hst⟩ := hk X2 h2
  rw [PathObl.obj.Tcb.reply_obj.guard (gS := gS) t X2 rRp, eq_of_spec_fd (obj.Tcb.reply_obj.spec (L := L) X2 t)]
  simp only [bind_ok]
  refine bind_guard_congr ?_ fun X3 h3 => ?_
  · by_cases hr : (L.mem X2 (replyA t) != 0#u64) = true
    · rw [if_pos hr, if_pos hr]; exact hru (bne_iff_ne.mp hr)
    · rw [if_neg hr, if_neg hr]
  · rw [hst X3 h3]

end gst

end Fl4Proofs.P2
