/-
P3 (DESIGN.md §9), invariant line YS (iolay gen 4): **YieldScope — a thread that yields to an SC is not blocked
on receive**, spec side only (outside the JAtZ cone), the base of its preservation (definitions, leaves, boot).

* `notRecvSt ts`: `ts` is not `blockedOnReceive`; `ysQ x := x.tcbYieldTo ≠ none → notRecvSt x.tcbState`;
  **`YieldScopeS σ := TI ysQ σ`** (every TCB). The FL4 side reads it through the scheduling-context relation
  (`ScYield.lean`: `x.tcbYieldTo = optRef (m (yieldA t))`): a receive-blocked thread has `YIELD_TO = 0`, which is
  P2's `hyt` / `ry` / the fast paths' `hy0`.
* **`CurYieldNone σ`**: the current thread's `tcbYieldTo = none` (the entry half: every kernel exit ends with
  `activateThread`, Fl4Spec/Tcb.lean:74, whose `completeYieldTo` clears it, and the idle thread's is `none`,
  `SInvI.ValidIdle`).
* As FaultTcbsS (SpecInvFaultTcbsF*), the preservation carries a list `L` of threads known to have no yield:
  `yslQ L p x := ysQ x ∧ (p ∈ L → x.tcbYieldTo = none)`, `YSL L := TP (yslQ L)`, `YSL [] ↔ YieldScopeS`.
  `ys_setThreadState`: a state that is not `blockedOnReceive`, or a thread of `L` — the only `blockedOnReceive` write
  of the spec is `receiveIpcBlocked` (Fl4Spec/Ipc.lean:284) on the current thread (`handleRecv`), which `L = [ct]`
  covers from `CurYieldNone`. The only `tcbYieldTo := some _` write is `schedContextYieldTo`
  (Fl4Spec/Schedule.lean:263) on the running current thread; it is a hand-proved function (not a leaf).
* `boot_yieldScope`: the initial state `initASt`.

Truth check (iolay gen 4, before the preservation proofs): the spec's only writer of `blockedOnReceive` is
`receiveIpcBlocked`, reached only from `receiveIpc` ← `handleRecv` with the current thread (`suspend`, `cancelIpc`,
`restart`, the fault paths and `doReplyTransfer` write `inactive` / `restart` / `running` / `blockedOnSend` /
`blockedOnReply`); `tcbYieldTo := some _` is written only by `schedContextYieldTo` on `ct`, which stays `running`;
every exit runs `activateThread` (`callKernel`, Fl4Spec/Syscall.lean:300). FL4: `yield_switches`
(schedcontext.rs:180) sets `YIELD_TO` only on the caller, `activate_thread` (sched.rs:689) and `suspend`
(sched.rs:767) clear it. No counterexample.

No premise ([J]/[P]/[W]).
-/
import Fl4Proofs.P3.SpecInvFaultTcbsT
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- The state is not `blockedOnReceive`. -/
def notRecvSt : ThreadState → Prop
  | .blockedOnReceive _ _ _ => False
  | _ => True

/-- A thread that yields to an SC is not blocked on receive. -/
def ysQ (x : Tcb) : Prop := x.tcbYieldTo ≠ none → notRecvSt x.tcbState

/-- **YieldScope**: no thread both yields to an SC and is blocked on receive. -/
abbrev YieldScopeS (σ : State Unit) : Prop := TI ysQ σ

/-- **The entry half**: the current thread does not yield. -/
def CurYieldNone (σ : State Unit) : Prop :=
  ∀ x, σ.kheap σ.curThread = some (.tcb x) → x.tcbYieldTo = none

/-- `ysQ`, and no yield for the threads of `L`. -/
def yslQ (L : List ObjRef) (p : ObjRef) (x : Tcb) : Prop := ysQ x ∧ (p ∈ L → x.tcbYieldTo = none)

/-- YieldScope, and no yield at the threads of `L`. -/
abbrev YSL (L : List ObjRef) (σ : State Unit) : Prop := TP (yslQ L) σ

theorem YSL.nil_iff (σ : State Unit) : YSL [] σ ↔ YieldScopeS σ :=
  ⟨fun h p x hp => (h p x hp).1, fun h p x hp => ⟨h p x hp, fun h => nomatch h⟩⟩

/-- **`YSL [ct]` from `YieldScopeS` and the entry half** (what `handleRecv`'s `receiveIpcBlocked` needs). -/
theorem YSL.ofCur {σ : State Unit} (h : YieldScopeS σ) (hc : CurYieldNone σ) : YSL [σ.curThread] σ := by
  intro p x hp
  refine ⟨h p x hp, fun hm => ?_⟩
  simp only [List.mem_singleton] at hm
  subst hm
  exact hc x hp

variable {L : List ObjRef}

abbrev YSK {α : Type} (L : List ObjRef) (m : NonDet (State Unit) α) : Prop := IK (YSL L) m
abbrev YSKE {ε α : Type} (L : List ObjRef) (m : NonDetE (State Unit) ε α) : Prop := IKE (YSL L) m

/-- The side conditions of the TCB-writer leaves. -/
macro "ys_side" : tactic => `(tactic| first
  | (intro _ _ h; exact h)
  | (intro t ht; cases ht; done)
  | (intro _ hx; exact hx)
  | (intro _ _ hx; exact hx)
  | (intro _ _ hx; exact ⟨hx, hx, hx, hx, hx, hx⟩)
  | (intro _ _; exact ⟨fun h => absurd rfl h, fun _ => rfl⟩)
  | (intro _; exact ⟨fun h => absurd rfl h, fun _ => rfl⟩)
  | (exact ⟨fun h => absurd rfl h, fun _ => rfl⟩)
  | (exact Or.inl trivial)
  | (exact Or.inr (by simp; done))
  | (simp [yslQ, ysQ, notRecvSt]; done)
  | (intro _ hx; simpa [yslQ, ysQ, notRecvSt] using hx)
  | (intro _ _ hx; simpa [yslQ, ysQ, notRecvSt] using hx))

syntax "ys_leaf" : tactic
macro_rules | `(tactic| ys_leaf) => `(tactic| fail "no ys_leaf")

macro "ys_auto" : tactic => `(tactic| repeat' (first | ys_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| ys_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); ys_side))
macro_rules | `(tactic| ys_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); ys_side))
macro_rules | `(tactic| ys_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| ys_leaf) => `(tactic| ((with_reducible refine tp_setObject _ _ ?_); ys_side))
macro_rules | `(tactic| ys_leaf) => `(tactic| with_reducible exact tp_setSimpleKo _ _ _)
macro_rules | `(tactic| ys_leaf) => `(tactic| ((with_reducible refine tp_threadSet _ _ ?_); ys_side))
macro_rules | `(tactic| ys_leaf) => `(tactic| ((with_reducible refine tp_archThreadSet _ _ ?_); ys_side))
macro_rules | `(tactic| ys_leaf) => `(tactic| ((with_reducible refine tp_asUser _ _ ?_); ys_side))
macro_rules | `(tactic| ys_leaf) => `(tactic| ((with_reducible refine tp_setMrs _ _ _ ?_); ys_side))
macro_rules | `(tactic| ys_leaf) => `(tactic| ((with_reducible refine tp_setCap _ _ ?_); ys_side))
macro_rules | `(tactic| ys_leaf) => `(tactic| ((with_reducible refine tp_retypeRegionWith _ _ _ _ _ _ ?_); ys_side))
macro_rules | `(tactic| ys_leaf) => `(tactic| ((with_reducible refine tp_retypeRegion _ _ _ _ _ ?_); ys_side))
macro_rules | `(tactic| ys_leaf) => `(tactic| with_reducible exact tp_deleteObjects _ _)

/-- **`set_thread_state`**: a state other than `blockedOnReceive`, or a thread known not to yield. -/
theorem ys_setThreadState (t : ObjRef) (ts : ThreadState) (h : notRecvSt ts ∨ t ∈ L) :
    YSK L (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (tp_threadSet _ _ fun x hx => ⟨fun hy => ?_, hx.2⟩) fun _ => ?_
  · rcases h with h | h
    · exact h
    · exact absurd (hx.2 h) hy
  · unfold setThreadStateAct setSchedulerAction; ys_auto
macro_rules | `(tactic| ys_leaf) => `(tactic| ((with_reducible refine ys_setThreadState _ _ ?_); ys_side))

theorem ys_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, yslQ L t x → yslQ L t (fn v x)) : YSK L (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact tp_threadSet _ _ (h _)
macro_rules | `(tactic| ys_leaf) => `(tactic| ((with_reducible refine ys_optionUpdateThread _ _ _ ?_); ys_side))

/-- **Clearing a thread's yield keeps `YSL`.** -/
theorem ys_clearYield (t : ObjRef) :
    IK (TP (yslQ L)) (threadSet (Z := Unit) (tcbYieldToUpdate fun _ => none) t) :=
  tp_threadSet _ _ fun _ _ => ⟨fun h => absurd rfl h, fun _ => rfl⟩

/-! ## Boot -/

/-- **YieldScope at boot**: the initial state `initASt`. -/
theorem boot_yieldScope : YieldScopeS (initASt (Z := Unit)) := by
  intro p x hp
  simp only [initASt, initKheap, Function.update_apply] at hp
  split_ifs at hp <;> first | (cases hp; done) | (cases hp; simp [ysQ, notRecvSt]) | simp_all [ysQ, notRecvSt]

end

end Fl4Proofs.P3.SInv
