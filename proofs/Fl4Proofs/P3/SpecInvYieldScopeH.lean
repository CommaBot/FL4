/-
P3 (DESIGN.md §9), invariant line YS (iolay gen 4): **YieldScope kept by the syscall entry and by every kernel
event** (spec side only, outside the JAtZ cone): the hand-proved functions of SpecInvYieldScopeT's skip list
(`proofs/scratch/invA/skipYS.txt`) and the tops.

* The receive: `receiveIpcBlocked` / `receiveIpc` for a thread of `L` (its `blockedOnReceive` write is allowed by
  `ys_setThreadState`'s `t ∈ L`), `handle_recv` from a state whose current thread is in `L`.
* The yield: `schedContextYieldTo` writes `ct.tcbYieldTo := some sc` with `ct` the current thread; it runs in
  `YO [] ct` = `YSL []` and the frame `OPG (fnR ct) univ (· = ct)` (SpecInvFaultTcbsG: the current thread is `ct`
  and `ct` is not `blockedOnReceive`), which every function before the write keeps (`fg_*`). `handle_invocation`
  enters the perform phase after `set_thread_state ct Restart`, so `YO [] ct` holds there (`yo_fl4HandleInvocationR`).
* The first-phase invocations (ReplyRecv, NBSendRecv, NBSendWait: `firstPhase = true`) never perform a
  scheduling-context invocation: `fl4DecodeInvocation true` throws on a SchedContext cap (`ro_decode_fp`), so they
  keep `YSL [ct]` (`ys_fl4HandleInvocationR_fp`), and the receive that follows them runs with `ct ∈ L`; the current
  thread is still `ct` there by ft3's bundle `B` (`b_fl4HandleInvocationR`).
* `activate_thread` clears the current thread's yield (`completeYieldTo`), so every kernel exit has
  `CurYieldNone` (`ys_activateThread`).
* Tops: **`kentry_yieldScope`** (`fl4KernelEntrySyscall`, from `YieldScopeS ∧ CurYieldNone` and ft3's entry facts
  `FaultTcbsS ∧ NQB`, `CtEntry`), **`kcall_yieldScope`** (`fl4CallKernel rep ev` for a non-syscall event, from
  `YieldScopeS`), `kcallF_yieldScope` (the same after the FaultIP write), `boot_curYieldNone`.

No premise ([J]/[P]/[W]): `CtEntry` and `FaultTcbsS ∧ NQB` are hypotheses of the tops, as in SpecInvFaultTcbsH10;
the J layer discharges them from `SInvX` (`SInvA.fts` / `nqb`, `SInvB.entryJ`).
-/
import Fl4Proofs.P3.SpecInvYieldScopeF4
import Fl4Proofs.P3.SpecInvFaultTcbsH10
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {L : List ObjRef}

/-! ## `YSL` lists -/

theorem ik_apply {P : State Unit → Prop} {α : Type} {m : NonDet (State Unit) α} {σ : State Unit}
    {y : α × State Unit} (hσ : P σ) (hy : y ∈ (m σ).1) (h : IK P m) : P y.2 := h σ hσ y hy

/-! ## The current thread through the generic frame -/

/-- The trivial per-thread predicate. -/
def Ftriv : FQ where
  R _ _ _ := True
  clr _ _ _ _ := trivial
  st _ _ _ _ := trivial
  dflt _ := trivial

theorem opg_triv {C : ObjRef → Prop} {σ : State Unit} (h : C σ.curThread) : OPG Ftriv Set.univ C σ := by
  refine ⟨fun p o _ => ?_, h⟩
  cases o <;> first | trivial | exact fun _ _ => trivial

/-- `set_thread_state` keeps the trivial predicate. -/
macro_rules | `(tactic| fg_leaf) => `(tactic| ((with_reducible refine fg_setThreadState _ _ ?_); intro _ _ _; trivial))

/-- A `gets curThread` read under a predicate fixing the current thread. -/
theorem ik_gets_cur_bind {P : State Unit → Prop} {ct : ObjRef} {β : Type} {k : ObjRef → NonDet (State Unit) β}
    (hc : ∀ s, P s → s.curThread = ct) (h : IK P (k ct)) :
    IK P (NonDet.gets (fun s : State Unit => s.curThread) >>= k) := by
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  dsimp only at hx
  rw [hc σ hσ] at hx
  exact h σ hσ x hx

/-! ## The receive -/

macro_rules | `(tactic| ys_leaf) => `(tactic| ((with_reducible refine ys_receiveIpcBlocked _ _ _ _ ?_); assumption))

macro_rules | `(tactic| ys_leaf) => `(tactic| ((with_reducible refine ys_receiveIpc _ _ _ _ ?_); assumption))

/-! ## The yield -/

/-! ## The decode's result in the first phase -/

/-- Every `ok` result of `m` satisfies `R`. -/
def RO {ε α : Type} (R : α → Prop) (m : NonDetE (State Unit) ε α) : Prop :=
  ∀ s y, y ∈ ((ExceptT.run m) s).1 → ∀ a, y.1 = .ok a → R a

section RO
variable {ε α β : Type} {R : β → Prop}

theorem ro_throw (e : ε) : RO R (NonDetE.throwError e : NonDetE (State Unit) ε β) := by
  intro s y hy a ha
  rw [Set.mem_singleton_iff.1 hy] at ha
  cases ha

theorem ro_returnOk {b : β} (h : R b) : RO R (NonDetE.returnOk b : NonDetE (State Unit) ε β) := by
  intro s y hy a ha
  rw [Set.mem_singleton_iff.1 hy] at ha
  cases ha
  exact h

theorem ro_liftME {f : α → β} {m : NonDetE (State Unit) ε α} (hf : ∀ x, R (f x)) :
    RO R (NonDetE.liftME f m) := by
  intro s y hy b hb
  unfold NonDetE.liftME at hy
  obtain ⟨z, -, ⟨a, -, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
  · rw [Set.mem_singleton_iff.1 hy] at hb
    cases hb
    exact hf a
  · cases hb

theorem ro_bind {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β} (hg : ∀ a, RO R (g a)) :
    RO R (m >>= g) := by
  intro s y hy b hb
  obtain ⟨z, -, ⟨a, -, hy⟩ | ⟨e, -, rfl⟩⟩ := ft_mem_bindE hy
  · exact hg a _ y hy b hb
  · cases hb

end RO

/-- **The first-phase decode never returns a scheduling-context invocation** (it throws on a SchedContext cap). -/
theorem ro_decode_fp (label : Data) (args : List Data) (ci : CapRef) (slot : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    RO (fun b => ∀ j, b ≠ Fl4Invocation.invokeSchedContext j)
      (fl4DecodeInvocation (Z := Unit) true label args ci slot cap ex buf) := by
  cases cap <;> simp only [fl4DecodeInvocation, ↓reduceIte] <;> (try split) <;>
    first
    | exact ro_throw _
    | exact ro_returnOk (by intro j h; cases h)
    | exact ro_liftME (by intro x j h; cases h)

/-! ## `handle_invocation` -/

/-! ## `handle_syscall` -/

/-! ## The events -/

/-! ## The kernel exit -/

/-- After `thread_set (tcb_yield_to := None)` on `t`, `t` has no yield. -/
theorem clearYield_post (t : ObjRef) {σ : State Unit} {y : Unit × State Unit}
    (hy : y ∈ (threadSet (Z := Unit) (tcbYieldToUpdate fun _ => none) t σ).1) :
    ∀ x, y.2.kheap t = some (.tcb x) → x.tcbYieldTo = none := by
  unfold threadSet at hy
  obtain ⟨z, hz, hy⟩ := hy
  unfold NonDet.getsThe at hz
  cases e : getTcb t σ with
  | none => rw [e] at hz; exact hz.elim
  | some a =>
    rw [e] at hz
    have hz' := Set.mem_singleton_iff.1 hz
    subst hz'
    rw [mem_setObject hy]
    intro x hx
    dsimp only at hx
    simp only [Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hx
    rw [← hx]
    rfl

/-! ## The tops -/

/-- **The entry half at boot**: the initial state's current thread does not yield. -/
theorem boot_curYieldNone : CurYieldNone (initASt (Z := Unit)) := by
  intro x hp
  simp only [initASt, initKheap, Function.update_apply] at hp
  split_ifs at hp <;> first | (cases hp; done) | (cases hp; rfl)

end

end Fl4Proofs.P3.SInv
