/-
P3 (line p3J, gen 25): **the SC-period frame of the kernel entry's pieces** (P3JRrF's `RQ` over P3JRrG's leaves), a
scripted copy of gen 21's P3JKtE (`scratch/p3J/genRr.py`). Every non-syscall event's `handle_event` keeps `rpV`
(`rqe_handleEvent_other`).

Named premises: none. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JRrG
open Classical

namespace Fl4Proofs.P3.SInvRr
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

set_option maxRecDepth 20000



/-- FL4's TCB timers keep the domain list (their outcomes are `send_signal`
outcomes and `reprogram_timer` writes). -/
theorem rq_fl4Awaken : RQ (fl4Awaken (Z := Unit)) := by
  intro σ x hx
  obtain ⟨u, s'⟩ := x
  have h : fl4TimerFires σ s' := hx
  show rpV s' = rpV σ
  clear hx
  induction h with
  | refl => rfl
  | tail _ h2 ih =>
    obtain ⟨σ1, h1, rfl⟩ := h2
    rw [← ih]
    rcases h1 with rfl | ⟨n, b, hs⟩
    · rfl
    · have e := rq_sendSignal' n b _ ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
      exact e
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_fl4Awaken)

/-- `whenE` with its decidability instance unified (not synthesized). -/
theorem rqe_whenE' {ε : Type} (P : Prop) (inst : Decidable P) {m : NonDetE (State Unit) ε Unit} (h : RQE m) :
    RQE (@NonDetE.whenE _ _ P inst m) := by
  unfold NonDetE.whenE; split
  · exact h
  · exact dke_pure _
macro_rules | `(tactic| zq_leaf) => `(tactic| refine rqe_whenE' _ _ ?_)

/-! ## The kernel entry's pieces -/

set_option maxHeartbeats 4000000 in
theorem rq_setThreadState (t : ObjRef) (ts : ThreadState) : RQ (setThreadState (Z := Unit) t ts) := by
  zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_setThreadState _ _)

set_option maxHeartbeats 4000000 in
theorem rq_rescheduleRequired : RQ (rescheduleRequired (Z := Unit)) := by
  zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_rescheduleRequired)

set_option maxHeartbeats 4000000 in
theorem rq_fl4SyscallFaultIP (t : ObjRef) : RQ (fl4SyscallFaultIP (Z := Unit) t) := by
  zq_auto

set_option maxHeartbeats 4000000 in
theorem rq_updateTimeStamp : RQ (updateTimeStamp (Z := Unit)) := by
  zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_updateTimeStamp)

set_option maxHeartbeats 4000000 in
theorem rq_checkBudgetRestart : RQ (checkBudgetRestart (Z := Unit)) := by
  zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_checkBudgetRestart)

set_option maxHeartbeats 4000000 in
theorem rq_handleFault (t : ObjRef) (f : Fault) : RQ (handleFault (Z := Unit) t f) := by
  zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_handleFault _ _)

set_option maxHeartbeats 4000000 in
theorem rq_handleRecv (b c : Bool) : RQ (handleRecv (Z := Unit) b c) := by
  zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_handleRecv _ _)

set_option maxHeartbeats 4000000 in
theorem rq_handleYield : RQ (handleYield (Z := Unit)) := by
  zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_handleYield)

set_option maxHeartbeats 4000000 in
theorem rq_preemptionPath : RQ (preemptionPath (Z := Unit)) := by
  zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_preemptionPath)

set_option maxHeartbeats 4000000 in
theorem rq_activateThread : RQ (activateThread (Z := Unit)) := by
  zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_activateThread)

set_option maxHeartbeats 4000000 in
theorem rq_getCapReg (r : Register) : RQ (getCapReg (Z := Unit) r) := by
  zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getCapReg _)

set_option maxHeartbeats 4000000 in
theorem rq_getMessageInfo (t : ObjRef) : RQ (getMessageInfo (Z := Unit) t) := by
  zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getMessageInfo _)

set_option maxHeartbeats 4000000 in
theorem rqe_lookupCapAndSlot (t : ObjRef) (c : CapRef) : RQE (lookupCapAndSlot (Z := Unit) t c) := by
  zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_lookupCapAndSlot _ _)

set_option maxHeartbeats 4000000 in
theorem rq_lookupIpcBuffer (b : Bool) (t : ObjRef) : RQ (lookupIpcBuffer (Z := Unit) b t) := by
  zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_lookupIpcBuffer _ _)

set_option maxHeartbeats 4000000 in
theorem rqe_lookupExtraCaps (t : ObjRef) (b : Option Data) (mi : MessageInfo) :
    RQE (lookupExtraCaps (Z := Unit) t b mi) := by
  zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_lookupExtraCaps _ _ _)

set_option maxHeartbeats 4000000 in
theorem rq_getMrs (t : ObjRef) (b : Option ObjRef) (mi : MessageInfo) : RQ (getMrs (Z := Unit) t b mi) := by
  zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getMrs _ _ _)

set_option maxHeartbeats 4000000 in
theorem rq_replyFromKernel (t : ObjRef) (x : Data × List Data) : RQ (replyFromKernel (Z := Unit) t x) := by
  zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_replyFromKernel _ _)

set_option maxHeartbeats 4000000 in
theorem rq_fl4ReplyFromKernelError (r : Bool) (t : ObjRef) (x : Data × List Data) :
    RQ (fl4ReplyFromKernelError (Z := Unit) r t x) := by
  zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_fl4ReplyFromKernelError _ _ _)

set_option maxHeartbeats 4000000 in
theorem rq_getThreadState (t : ObjRef) : RQ (getThreadState (Z := Unit) t) := by
  zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rq_getThreadState _)

set_option maxHeartbeats 8000000 in
theorem rqe_fl4Decode (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    RQE (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  unfold fl4DecodeInvocation
  split
  all_goals zq_auto
macro_rules | `(tactic| zq_leaf) => `(tactic| with_reducible exact rqe_fl4Decode _ _ _ _ _ _ _ _)

set_option maxHeartbeats 8000000 in
set_option maxHeartbeats 8000000 in
/-- The non-syscall events keep the domain list. -/
theorem rqe_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    RQE (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; zq_auto

end

end Fl4Proofs.P3.SInvRr
