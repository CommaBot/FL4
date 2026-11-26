/-
P3 (line p3J, gen 4): **the IOAPIC-count frame, kernel-entry pieces** (spec side only, outside the JAtZ cone): `SpecInvDomE` with the projection
`dlV` (the domain list) replaced by `ioxV` (`x64_num_ioapics`, `x64_ioapic_nirqs`), a scripted renaming
(`scratch/p3J/genIox.py`; VsDom's `FK` combinators are generic in the projection). No sorry.
-/
import Fl4Proofs.P3.SpecInvIoxG
open Classical

namespace Fl4Proofs.P3.SInvIox
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

set_option maxRecDepth 20000



/-- FL4's TCB timers keep the domain list (their outcomes are `send_signal`
outcomes and `reprogram_timer` writes). -/
theorem iox_fl4Awaken : IOX (fl4Awaken (Z := Unit)) := by
  intro σ x hx
  obtain ⟨u, s'⟩ := x
  have h : fl4TimerFires σ s' := hx
  show ioxV s' = ioxV σ
  clear hx
  induction h with
  | refl => rfl
  | tail _ h2 ih =>
    obtain ⟨σ1, h1, rfl⟩ := h2
    rw [← ih]
    rcases h1 with rfl | ⟨n, b, hs⟩
    · rfl
    · have e := iox_sendSignal' n b _ ((), σ1) (by rw [hs]; exact Set.mem_singleton _)
      exact e
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_fl4Awaken)

/-- `whenE` with its decidability instance unified (not synthesized). -/
theorem ioxe_whenE' {ε : Type} (P : Prop) (inst : Decidable P) {m : NonDetE (State Unit) ε Unit} (h : IOXE m) :
    IOXE (@NonDetE.whenE _ _ P inst m) := by
  unfold NonDetE.whenE; split
  · exact h
  · exact dke_pure _
macro_rules | `(tactic| iox_leaf) => `(tactic| refine ioxe_whenE' _ _ ?_)

/-! ## The kernel entry's pieces -/

set_option maxHeartbeats 4000000 in
theorem iox_setThreadState (t : ObjRef) (ts : ThreadState) : IOX (setThreadState (Z := Unit) t ts) := by
  iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_setThreadState _ _)

set_option maxHeartbeats 4000000 in
theorem iox_rescheduleRequired : IOX (rescheduleRequired (Z := Unit)) := by
  iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_rescheduleRequired)

set_option maxHeartbeats 4000000 in
theorem iox_fl4SyscallFaultIP (t : ObjRef) : IOX (fl4SyscallFaultIP (Z := Unit) t) := by
  iox_auto

set_option maxHeartbeats 4000000 in
theorem iox_updateTimeStamp : IOX (updateTimeStamp (Z := Unit)) := by
  iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_updateTimeStamp)

set_option maxHeartbeats 4000000 in
theorem iox_checkBudgetRestart : IOX (checkBudgetRestart (Z := Unit)) := by
  iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_checkBudgetRestart)

set_option maxHeartbeats 4000000 in
theorem iox_handleFault (t : ObjRef) (f : Fault) : IOX (handleFault (Z := Unit) t f) := by
  iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_handleFault _ _)

set_option maxHeartbeats 4000000 in
theorem iox_handleRecv (b c : Bool) : IOX (handleRecv (Z := Unit) b c) := by
  iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_handleRecv _ _)

set_option maxHeartbeats 4000000 in
theorem iox_handleYield : IOX (handleYield (Z := Unit)) := by
  iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_handleYield)

set_option maxHeartbeats 4000000 in
theorem iox_preemptionPath : IOX (preemptionPath (Z := Unit)) := by
  iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_preemptionPath)

set_option maxHeartbeats 4000000 in
theorem iox_activateThread : IOX (activateThread (Z := Unit)) := by
  iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_activateThread)

set_option maxHeartbeats 4000000 in
theorem iox_getCapReg (r : Register) : IOX (getCapReg (Z := Unit) r) := by
  iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getCapReg _)

set_option maxHeartbeats 4000000 in
theorem iox_getMessageInfo (t : ObjRef) : IOX (getMessageInfo (Z := Unit) t) := by
  iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getMessageInfo _)

set_option maxHeartbeats 4000000 in
theorem ioxe_lookupCapAndSlot (t : ObjRef) (c : CapRef) : IOXE (lookupCapAndSlot (Z := Unit) t c) := by
  iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_lookupCapAndSlot _ _)

set_option maxHeartbeats 4000000 in
theorem iox_lookupIpcBuffer (b : Bool) (t : ObjRef) : IOX (lookupIpcBuffer (Z := Unit) b t) := by
  iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_lookupIpcBuffer _ _)

set_option maxHeartbeats 4000000 in
theorem ioxe_lookupExtraCaps (t : ObjRef) (b : Option Data) (mi : MessageInfo) :
    IOXE (lookupExtraCaps (Z := Unit) t b mi) := by
  iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_lookupExtraCaps _ _ _)

set_option maxHeartbeats 4000000 in
theorem iox_getMrs (t : ObjRef) (b : Option ObjRef) (mi : MessageInfo) : IOX (getMrs (Z := Unit) t b mi) := by
  iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getMrs _ _ _)

set_option maxHeartbeats 4000000 in
theorem iox_replyFromKernel (t : ObjRef) (x : Data × List Data) : IOX (replyFromKernel (Z := Unit) t x) := by
  iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_replyFromKernel _ _)

set_option maxHeartbeats 4000000 in
theorem iox_fl4ReplyFromKernelError (r : Bool) (t : ObjRef) (x : Data × List Data) :
    IOX (fl4ReplyFromKernelError (Z := Unit) r t x) := by
  iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_fl4ReplyFromKernelError _ _ _)

set_option maxHeartbeats 4000000 in
theorem iox_getThreadState (t : ObjRef) : IOX (getThreadState (Z := Unit) t) := by
  iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact iox_getThreadState _)

set_option maxHeartbeats 8000000 in
theorem ioxe_fl4Decode (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    IOXE (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  unfold fl4DecodeInvocation
  split
  all_goals iox_auto
macro_rules | `(tactic| iox_leaf) => `(tactic| with_reducible exact ioxe_fl4Decode _ _ _ _ _ _ _ _)

set_option maxHeartbeats 8000000 in
/-- Every perform but the Domain invocation's keeps the domain list. -/
theorem ioxe_fl4Perform (blk call don : Bool) (inv : Fl4Invocation) (h : ∀ d, inv ≠ .invokeDomain d) :
    IOXE (fl4PerformInvocation (Z := Unit) blk call don inv) := by
  cases inv with
  | invokeDomain d => exact absurd rfl (h d)
  | _ => simp only [fl4PerformInvocation]; iox_auto

set_option maxHeartbeats 8000000 in
/-- The non-syscall events keep the domain list. -/
theorem ioxe_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    IOXE (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; iox_auto

end

end Fl4Proofs.P3.SInvIox
