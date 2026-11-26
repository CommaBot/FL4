/-
P3 (DESIGN.md §9), invariant line YB (iolay gen 5): **YieldBlock — a thread that yields to an SC is not blocked at
all** (receive, reply, send, notification), the strengthening of SpecInvYieldScopeT's YieldScope that vmR's `ry` needs
(its thread is `blockedOnReply`). Spec side only; the base of the preservation (definitions, leaves, boot).

* `notBlkSt`, `ybQ x := x.tcbYieldTo ≠ none → notBlkSt x.tcbState`, **`YieldBlockS := TI ybQ`**,
  `YieldBlockS.scope : YieldBlockS σ → YieldScopeS σ`; `CurYieldNone` is SpecInvYieldScopeT's.
* Exempt list as YieldScope: `yblQ L`, `YBL L := TP (yblQ L)`, `YBL.nil_iff`, `YBL.ofCur`; `yb_setThreadState`: a state
  that is not blocked, or a thread of `L`. The blocking writers (`sendIpcBlocked`, `receiveIpcBlocked`,
  `receiveSignalBlocked`, `replyPush`) block the current thread (`L = [ct]`), a thread read blocked (so not yielding:
  `replyPush`'s queued sender in `receiveIpc`, `doReplyTransfer`'s receiver), or the thread of a fault send to it.
* `boot_yieldBlock`: the initial state.

Truth check (gen 5, before the proofs): the only writers of a blocked state are the four above (Fl4Spec/Ipc.lean,
IpcCancel.lean); each blocks the current thread of the entry (whose yield is none, `CurYieldNone`, and only
`schedContextYieldTo` sets one, on the current thread, after which the entry performs no blocking call: the yield is a
non-preemptible invocation, so no preemption path, and no receive follows a first-phase-false invocation) or a thread
read in a blocked state. No counterexample.

No premise ([J]/[P]/[W]).
-/
import Fl4Proofs.P3.SpecInvYieldScopeT
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

/-- The state is not blocked (receive, reply, send, notification). -/
def notBlkSt : ThreadState → Prop
  | .blockedOnReceive _ _ _ => False
  | .blockedOnReply _ => False
  | .blockedOnSend _ _ => False
  | .blockedOnNotification _ => False
  | _ => True

/-- A thread that yields to an SC is not blocked. -/
def ybQ (x : Tcb) : Prop := x.tcbYieldTo ≠ none → notBlkSt x.tcbState

/-- **YieldBlock**: no thread both yields to an SC and is blocked. -/
abbrev YieldBlockS (σ : State Unit) : Prop := TI ybQ σ

theorem notRecv_of_notBlk {ts : ThreadState} (h : notBlkSt ts) : notRecvSt ts := by
  cases ts <;> simp_all [notBlkSt, notRecvSt]

/-- YieldBlock is the stronger invariant: it gives gen 4's YieldScope. -/
theorem YieldBlockS.scope {σ : State Unit} (h : YieldBlockS σ) : YieldScopeS σ :=
  fun p x hp hy => notRecv_of_notBlk (h p x hp hy)

/-- `ybQ`, and no yield for the threads of `L`. -/
def yblQ (L : List ObjRef) (p : ObjRef) (x : Tcb) : Prop := ybQ x ∧ (p ∈ L → x.tcbYieldTo = none)

/-- YieldScope, and no yield at the threads of `L`. -/
abbrev YBL (L : List ObjRef) (σ : State Unit) : Prop := TP (yblQ L) σ

theorem YBL.nil_iff (σ : State Unit) : YBL [] σ ↔ YieldBlockS σ :=
  ⟨fun h p x hp => (h p x hp).1, fun h p x hp => ⟨h p x hp, fun h => nomatch h⟩⟩

/-- **`YBL [ct]` from `YieldBlockS` and the entry half** (what `handleRecv`'s `receiveIpcBlocked` needs). -/
theorem YBL.ofCur {σ : State Unit} (h : YieldBlockS σ) (hc : CurYieldNone σ) : YBL [σ.curThread] σ := by
  intro p x hp
  refine ⟨h p x hp, fun hm => ?_⟩
  simp only [List.mem_singleton] at hm
  subst hm
  exact hc x hp

variable {L : List ObjRef}

abbrev YBK {α : Type} (L : List ObjRef) (m : NonDet (State Unit) α) : Prop := IK (YBL L) m
abbrev YBKE {ε α : Type} (L : List ObjRef) (m : NonDetE (State Unit) ε α) : Prop := IKE (YBL L) m

/-- The side conditions of the TCB-writer leaves. -/
macro "yb_side" : tactic => `(tactic| first
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
  | (simp [yblQ, ybQ, notBlkSt]; done)
  | (intro _ hx; simpa [yblQ, ybQ, notBlkSt] using hx)
  | (intro _ _ hx; simpa [yblQ, ybQ, notBlkSt] using hx))

syntax "yb_leaf" : tactic
macro_rules | `(tactic| yb_leaf) => `(tactic| fail "no yb_leaf")

macro "yb_auto" : tactic => `(tactic| repeat' (first | yb_leaf | ik_step0 | ik_unfold | (unfold NonDetE.whenE) | (unfold NonDetE.unlessE) | (unfold NonDet.when) | (unfold NonDet.unless)))

macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine ik_doMachineOp ?_ _); yb_side))
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine ik_doExtendedOp ?_ _); yb_side))
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact ik_getObject _)
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine tp_setObject _ _ ?_); yb_side))
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact tp_setSimpleKo _ _ _)
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine tp_threadSet _ _ ?_); yb_side))
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine tp_archThreadSet _ _ ?_); yb_side))
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine tp_asUser _ _ ?_); yb_side))
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine tp_setMrs _ _ _ ?_); yb_side))
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine tp_setCap _ _ ?_); yb_side))
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine tp_retypeRegionWith _ _ _ _ _ _ ?_); yb_side))
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine tp_retypeRegion _ _ _ _ _ ?_); yb_side))
macro_rules | `(tactic| yb_leaf) => `(tactic| with_reducible exact tp_deleteObjects _ _)

/-- **`set_thread_state`**: a state that is not blocked, or a thread known not to yield. -/
theorem yb_setThreadState (t : ObjRef) (ts : ThreadState) (h : notBlkSt ts ∨ t ∈ L) :
    YBK L (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState
  refine ik_bind (tp_threadSet _ _ fun x hx => ⟨fun hy => ?_, hx.2⟩) fun _ => ?_
  · rcases h with h | h
    · exact h
    · exact absurd (hx.2 h) hy
  · unfold setThreadStateAct setSchedulerAction; yb_auto
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine yb_setThreadState _ _ ?_); yb_side))

theorem yb_optionUpdateThread {α : Type} (t : ObjRef) (fn : α → Tcb → Tcb) (o : Option α)
    (h : ∀ v x, yblQ L t x → yblQ L t (fn v x)) : YBK L (optionUpdateThread (Z := Unit) t fn o) := by
  unfold optionUpdateThread
  split
  · exact ik_pure _
  · exact tp_threadSet _ _ (h _)
macro_rules | `(tactic| yb_leaf) => `(tactic| ((with_reducible refine yb_optionUpdateThread _ _ _ ?_); yb_side))

/-- **Clearing a thread's yield keeps `YBL`.** -/
theorem yb_clearYield (t : ObjRef) :
    IK (TP (yblQ L)) (threadSet (Z := Unit) (tcbYieldToUpdate fun _ => none) t) :=
  tp_threadSet _ _ fun _ _ => ⟨fun h => absurd rfl h, fun _ => rfl⟩

/-! ## Boot -/

/-- **YieldBlock at boot**: the initial state `initASt`. -/
theorem boot_yieldBlock : YieldBlockS (initASt (Z := Unit)) := by
  intro p x hp
  simp only [initASt, initKheap, Function.update_apply] at hp
  split_ifs at hp <;> first | (cases hp; done) | (cases hp; simp [ybQ, notBlkSt]) | simp_all [ybQ, notBlkSt]

end

end Fl4Proofs.P3.SInv
