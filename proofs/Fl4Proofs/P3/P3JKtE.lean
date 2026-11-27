/-
P3 (line p3J, gen 21): **the heap-type frame of the kernel entry's pieces** (P3JKtF's `KQ` over P3JKtG's leaves),
a scripted copy of SpecInvDomE (`scratch/p3J/genKt.py`); the domain writers (`next_domain`, ...) need no exception
here (they write no heap). Every non-syscall event's `handle_event` keeps `ktV` (`kqe_handleEvent_other`).

Named premises: none. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JKtG
open Classical

namespace Fl4Proofs.P3.SInvKt
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

set_option maxRecDepth 20000



/-- FL4's TCB timers keep the domain list (their outcomes are `send_signal`
outcomes and `reprogram_timer` writes). -/
theorem kq_fl4Awaken : KQ (fl4Awaken (Z := Unit)) := by
  intro σ x hx
  obtain ⟨u, s'⟩ := x
  have h : fl4TimerFires σ s' := hx
  show ktV s' = ktV σ
  clear hx
  induction h with
  | refl => rfl
  | tail _ h2 ih =>
    obtain ⟨σ1, h1, rfl⟩ := h2
    rw [← ih]
    rcases h1 with rfl | ⟨n, b, hs⟩
    · rfl
    · have e := kq_sendSignal' n b _ ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
      exact e
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_fl4Awaken)

/-- `whenE` with its decidability instance unified (not synthesized). -/
theorem kqe_whenE' {ε : Type} (P : Prop) (inst : Decidable P) {m : NonDetE (State Unit) ε Unit} (h : KQE m) :
    KQE (@NonDetE.whenE _ _ P inst m) := by
  unfold NonDetE.whenE; split
  · exact h
  · exact dke_pure _
macro_rules | `(tactic| kq_leaf) => `(tactic| refine kqe_whenE' _ _ ?_)

/-! ## The kernel entry's pieces -/

set_option maxHeartbeats 4000000 in
theorem kq_setThreadState (t : ObjRef) (ts : ThreadState) : KQ (setThreadState (Z := Unit) t ts) := by
  kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_setThreadState _ _)

set_option maxHeartbeats 4000000 in
theorem kq_rescheduleRequired : KQ (rescheduleRequired (Z := Unit)) := by
  kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_rescheduleRequired)

set_option maxHeartbeats 4000000 in
theorem kq_fl4SyscallFaultIP (t : ObjRef) : KQ (fl4SyscallFaultIP (Z := Unit) t) := by
  kq_auto

set_option maxHeartbeats 4000000 in
theorem kq_updateTimeStamp : KQ (updateTimeStamp (Z := Unit)) := by
  kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_updateTimeStamp)

set_option maxHeartbeats 4000000 in
theorem kq_checkBudgetRestart : KQ (checkBudgetRestart (Z := Unit)) := by
  kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_checkBudgetRestart)

set_option maxHeartbeats 4000000 in
theorem kq_handleFault (t : ObjRef) (f : Fault) : KQ (handleFault (Z := Unit) t f) := by
  kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_handleFault _ _)

set_option maxHeartbeats 4000000 in
theorem kq_handleRecv (b c : Bool) : KQ (handleRecv (Z := Unit) b c) := by
  kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_handleRecv _ _)

set_option maxHeartbeats 4000000 in
theorem kq_handleYield : KQ (handleYield (Z := Unit)) := by
  kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_handleYield)

set_option maxHeartbeats 4000000 in
theorem kq_preemptionPath : KQ (preemptionPath (Z := Unit)) := by
  kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_preemptionPath)

set_option maxHeartbeats 4000000 in
theorem kq_activateThread : KQ (activateThread (Z := Unit)) := by
  kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_activateThread)

set_option maxHeartbeats 4000000 in
theorem kq_getCapReg (r : Register) : KQ (getCapReg (Z := Unit) r) := by
  kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getCapReg _)

set_option maxHeartbeats 4000000 in
theorem kq_getMessageInfo (t : ObjRef) : KQ (getMessageInfo (Z := Unit) t) := by
  kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getMessageInfo _)

set_option maxHeartbeats 4000000 in
theorem kqe_lookupCapAndSlot (t : ObjRef) (c : CapRef) : KQE (lookupCapAndSlot (Z := Unit) t c) := by
  kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_lookupCapAndSlot _ _)

set_option maxHeartbeats 4000000 in
theorem kq_lookupIpcBuffer (b : Bool) (t : ObjRef) : KQ (lookupIpcBuffer (Z := Unit) b t) := by
  kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_lookupIpcBuffer _ _)

set_option maxHeartbeats 4000000 in
theorem kqe_lookupExtraCaps (t : ObjRef) (b : Option Data) (mi : MessageInfo) :
    KQE (lookupExtraCaps (Z := Unit) t b mi) := by
  kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_lookupExtraCaps _ _ _)

set_option maxHeartbeats 4000000 in
theorem kq_getMrs (t : ObjRef) (b : Option ObjRef) (mi : MessageInfo) : KQ (getMrs (Z := Unit) t b mi) := by
  kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getMrs _ _ _)

set_option maxHeartbeats 4000000 in
theorem kq_replyFromKernel (t : ObjRef) (x : Data × List Data) : KQ (replyFromKernel (Z := Unit) t x) := by
  kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_replyFromKernel _ _)

set_option maxHeartbeats 4000000 in
theorem kq_fl4ReplyFromKernelError (r : Bool) (t : ObjRef) (x : Data × List Data) :
    KQ (fl4ReplyFromKernelError (Z := Unit) r t x) := by
  kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_fl4ReplyFromKernelError _ _ _)

set_option maxHeartbeats 4000000 in
theorem kq_getThreadState (t : ObjRef) : KQ (getThreadState (Z := Unit) t) := by
  kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kq_getThreadState _)

set_option maxHeartbeats 8000000 in
theorem kqe_fl4Decode (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    KQE (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  unfold fl4DecodeInvocation
  split
  all_goals kq_auto
macro_rules | `(tactic| kq_leaf) => `(tactic| with_reducible exact kqe_fl4Decode _ _ _ _ _ _ _ _)

set_option maxHeartbeats 8000000 in
set_option maxHeartbeats 8000000 in
/-- The non-syscall events keep the domain list. -/
theorem kqe_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    KQE (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; kq_auto

end

end Fl4Proofs.P3.SInvKt
