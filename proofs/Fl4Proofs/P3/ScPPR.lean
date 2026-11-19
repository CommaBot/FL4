/-
P3 (DESIGN.md §9), CSpace: **what a preemption point inside the CNode
Delete/Revoke loop needs of a zero consumed time** (`PPR0`, spec side only).

The preemption point updates the time (`update_time_stamp`): the consumed
time grows by the time elapsed. `JAtZ`'s `OffOK` and `CurOwnW` speak of a
positive consumed time only, so from a positive one they carry over
(XTopJointPP's `JAtZ.ppJ`); from a zero one they need what the invocation
knew at its start and the deletion keeps (l4v `cur_sc_offset_ready 0`, the
current SC released, and `ct_not_in_release_q`, the current SC's thread
outside the release queue): `PPR0`.

* `PPR0 σ`: the current thread is not the idle thread and no switch is
  pending (l4v `ct_not_idle`/`simple_sched_action` at the invocation's
  start, `Entered`; the hole after a preemption needs both, kp10), and, if
  the consumed time is `0`, the current SC's head refill is ready when the
  SC is active, and no thread bound to the current SC is in the release
  queue. Since kp12 also `CtOK σ`: the current thread is linked to the
  current SC or to none and is blocked on nothing (l4v: the current
  thread's SC is `cur_sc` at the invocation, `cur_sc_tcb_are_bound`; the
  deletion only unbinds it and donates SCs only to `BlockedOnReply` callers);
  XTopJointPreemptK reads it at a preemption hole.
* `PPK σ σ'`: a step keeping the time, the consumed time, the current SC,
  the current and idle threads, keeping no switch pending,
  shrinking the release queue, leaving every SC as it was or removing it and
  every TCB's SC link as it was (and a TCB blocked on nothing stays so). `PPR0` is kept by it (`PPR0.of_ppk`); the
  CNode steps (`CnK`), the kernel-state steps (`KsStep`) and the caller's
  restart (`PPK.restart`) are such steps.
-/
import Fl4Proofs.P3.SpecCnK
import Fl4Proofs.P3.StepSem
import Fl4Proofs.P3.NtfnSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open Fl4Spec

noncomputable section

/-- Blocked on nothing: no reply, endpoint or notification (kp12). -/
abbrev NotBlk (ts : ThreadState) : Prop := (∀ r, ts ≠ .blockedOnReply r) ∧ Notif.NotIpcBlk ts

theorem NotBlk.of_runnable {ts : ThreadState} (h : runnable ts = true) : NotBlk ts :=
  ⟨fun r e => (by rw [e] at h; cases h), Notif.NotIpcBlk.of_runnable h⟩

/-- **The current thread is linked to the current SC or to none, and is not
blocked on nothing** (kp12; module docstring). -/
def CtOK (σ : State Unit) : Prop :=
  ∀ xt, σ.kheap σ.curThread = some (.tcb xt) →
    (xt.tcbSchedContext = some σ.curSc ∨ xt.tcbSchedContext = none) ∧ NotBlk xt.tcbState

/-- **The preemption point's need at a zero consumed time** (module
docstring). -/
def PPR0 (σ : State Unit) : Prop :=
  (σ.curThread ≠ σ.idleThread ∧ (∀ u, σ.schedulerAction ≠ .switchThread u) ∧ CtOK σ) ∧ (σ.consumedTime = 0 →
    (∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → scActive y = true →
      refillReady σ.curTime (refillHd y) = true) ∧
    ∀ u xt, σ.kheap u = some (.tcb xt) → xt.tcbSchedContext = some σ.curSc → u ∉ σ.releaseQueue)

/-- A step keeping what `PPR0` reads (module docstring). -/
structure PPK (σ σ' : State Unit) : Prop where
  cons : σ'.consumedTime = σ.consumedTime
  time : σ'.curTime = σ.curTime
  csc : σ'.curSc = σ.curSc
  rel : ∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue
  sc : ∀ p y n, σ'.kheap p = some (.schedContext y n) → σ.kheap p = some (.schedContext y n)
  tcb : ∀ p y, σ'.kheap p = some (.tcb y) → ∃ x, σ.kheap p = some (.tcb x) ∧ x.tcbSchedContext = y.tcbSchedContext ∧
    (NotBlk x.tcbState → NotBlk y.tcbState)
  ct : σ'.curThread = σ.curThread
  idle : σ'.idleThread = σ.idleThread
  ns : (∀ u, σ.schedulerAction ≠ .switchThread u) → ∀ u, σ'.schedulerAction ≠ .switchThread u

theorem PPR0.of_ppk {σ σ' : State Unit} (h : PPR0 σ) (hk : PPK σ σ') : PPR0 σ' := by
  refine ⟨⟨by rw [hk.ct, hk.idle]; exact h.1.1, hk.ns h.1.2.1, fun yt hy => ?_⟩, fun h0 => ?_⟩
  · rw [hk.ct] at hy
    obtain ⟨x, hx, e, hb⟩ := hk.tcb _ yt hy
    obtain ⟨h1, h2⟩ := h.1.2.2 x hx
    rw [hk.csc, ← e]; exact ⟨h1, hb h2⟩
  rw [hk.cons] at h0
  obtain ⟨h1, h2⟩ := h.2 h0
  refine ⟨fun y n hy ha => ?_, fun u xt hu hs hr => ?_⟩
  · rw [hk.csc] at hy; rw [hk.time]
    exact h1 y n (hk.sc _ y n hy) ha
  · obtain ⟨x, hx, e, -⟩ := hk.tcb u xt hu
    rw [hk.csc, ← e] at hs
    exact h2 u x hx hs (hk.rel u hr)

theorem PPK.of_cnK {σ σ' : State Unit} (h : Ipc.CnK σ σ') : PPK σ σ' := by
  have e := h.1
  have e1 : σ'.consumedTime = σ.consumedTime := by
    have := congrArg (fun z : AbstractState => z.consumedTime) e; exact this
  have e2 : σ'.curTime = σ.curTime := by
    have := congrArg (fun z : AbstractState => z.curTime) e; exact this
  have e3 : σ'.curSc = σ.curSc := by
    have := congrArg (fun z : AbstractState => z.curSc) e; exact this
  have e4 : σ'.releaseQueue = σ.releaseQueue := by
    have := congrArg (fun z : AbstractState => z.releaseQueue) e; exact this
  have e5 : σ'.curThread = σ.curThread := by
    have := congrArg (fun z : AbstractState => z.curThread) e; exact this
  have e6 : σ'.idleThread = σ.idleThread := by
    have := congrArg (fun z : AbstractState => z.idleThread) e; exact this
  have e7 : σ'.schedulerAction = σ.schedulerAction := by
    have := congrArg (fun z : AbstractState => z.schedulerAction) e; exact this
  refine ⟨e1, e2, e3, fun u hu => ?_, fun p y n hp => ?_, fun p y hp => ?_, e5, e6, fun h => by rw [e7]; exact h⟩
  · rw [e4] at hu; exact hu
  · rcases h.2 p with h' | ⟨r, cs, cs', h1, h2⟩ | ⟨x, y', h1, h2, -⟩
    · rw [h'] at hp; exact hp
    · rw [h2] at hp; cases hp
    · rw [h2] at hp; cases hp
  · rcases h.2 p with h' | ⟨r, cs, cs', h1, h2⟩ | ⟨x, y', h1, h2, hc⟩
    · rw [h'] at hp; exact ⟨y, hp, rfl, id⟩
    · rw [h2] at hp; cases hp
    · rw [h2] at hp; cases hp
      exact ⟨x, h1, hc.2.2.2.2.2.1.symm, by rw [hc.1]; exact id⟩

theorem PPK.of_ksStep {σ σ' : State Unit} (h : KsStep σ σ') : PPK σ σ' :=
  ⟨h.cons, h.ctime, h.csc, fun u hu => by rw [h.rel] at hu; exact hu,
    fun p y n hp => by rw [h.kh] at hp; exact hp, fun p y hp => ⟨y, by rw [h.kh] at hp; exact hp, rfl, id⟩, h.ct, h.idle,
    fun hn => by rw [h.act]; exact hn⟩

/-- **The caller's restart is a `PPK` step**: its TCB's state changed, and
maybe the scheduler action. -/
theorem PPK.restart {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (ts : ThreadState)
    (hts : NotBlk ts := by exact ⟨fun _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ _ _ h => by cases h⟩) :
    PPK σ (Notif.stsAct (Notif.updK σ t (.tcb { x with tcbState := ts })) t) := by
  have e2 : ∀ σ0 : State Unit, (Notif.stsAct σ0 t).consumedTime = σ0.consumedTime ∧
      (Notif.stsAct σ0 t).curTime = σ0.curTime ∧ (Notif.stsAct σ0 t).curSc = σ0.curSc ∧
      (Notif.stsAct σ0 t).releaseQueue = σ0.releaseQueue ∧ (Notif.stsAct σ0 t).curThread = σ0.curThread ∧
      (Notif.stsAct σ0 t).idleThread = σ0.idleThread ∧
      ((Notif.stsAct σ0 t).schedulerAction = σ0.schedulerAction ∨
        (Notif.stsAct σ0 t).schedulerAction = .chooseNewThread) := fun σ0 => by
    unfold Notif.stsAct; split_ifs
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inr rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩
  obtain ⟨e1, e2', e3, e4, e5, e6, e7⟩ := e2 (Notif.updK σ t (.tcb { x with tcbState := ts }))
  refine ⟨e1, e2', e3, fun u hu => by rw [e4] at hu; exact hu, fun p y n hp => ?_, fun p y hp => ?_, e5, e6,
    fun hn u hu => ?_⟩
  rotate_right
  · rcases e7 with e | e <;> rw [e] at hu
    · exact hn u hu
    · cases hu
  · rw [Notif.stsAct_kheap] at hp
    by_cases e : p = t
    · subst e; simp [Notif.updK] at hp
    · simpa [Notif.updK, e] using hp
  · rw [Notif.stsAct_kheap] at hp
    by_cases e : p = t
    · subst e; simp [Notif.updK] at hp; subst hp; exact ⟨x, hk, rfl, fun _ => hts⟩
    · exact ⟨y, by simpa [Notif.updK, e] using hp, rfl, id⟩

end

end Fl4Proofs.P3
