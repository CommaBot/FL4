/-
P3 (DESIGN.md §9), IPC: **the spec's `reply_remove` of a thread blocked on
the reply, what `JAtZ` reads** (spec side only; for XTopJointRemove).

* `DonA`, `DonV`: the scheduler view across the call-stack part
  (`replyRemoveSc`): the current thread and the time kept, the action kept or
  a reschedule pending, every SC's refills, `REFILL_MAX` and size kept, its
  thread kept or given to the caller `t`, every TCB's SC kept, given to `t`
  (which had none) or cleared from the old holder, which is then neither the
  current thread nor the switch target unless a reschedule is pending
  (`test_reschedule`, `testReschedule_out`): `donate_donV`, `rmSc_donV`.
* `rsF`: the idle thread, the current SC, the consumed time and the time,
  kept by `reply_remove` (`rsf_replyRemove`, VsDom's generic `FK`).
* `rq_replyRemove'` (the release queue only shrinks, IpcRelQ's `RQ`),
  `yk_replyRemove'` (the yield links kept, IpcYK's `YKM`).
-/
import Fl4Proofs.P3.IpcWakeDon
import Fl4Proofs.P3.ScMidCur
import Fl4Proofs.P3.IpcRelQ
import Fl4Proofs.P3.IpcYK
import Fl4Proofs.P3.DomRecDel
import Fl4Proofs.P3.IpcRemove
open Classical

/-! ## The scalars kept (`Vs.FK rsF`) -/

namespace Fl4Proofs.P3.Vs
open Fl4Spec

noncomputable section

/-- The scalar fields `reply_remove` keeps. -/
def rsF (σ : State Unit) := (σ.idleThread, σ.curSc, σ.consumedTime, σ.curTime, σ.idleSc)

/-- An `FK rsF` lemma of a spec function. -/
syntax "rsf_leaf" : tactic
macro_rules | `(tactic| rsf_leaf) => `(tactic| fail "no rsf_leaf")

macro "rsf_auto" : tactic => `(tactic| repeat' (first | rsf_leaf | dk_step0))

theorem rsf_setObject (p : ObjRef) (o : KernelObject) : FK rsF (setObject (Z := Unit) p o) := by
  unfold setObject; dk_auto0
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_setObject _ _)

theorem rsf_threadSet (f : Tcb → Tcb) (t : ObjRef) : FK rsF (threadSet (Z := Unit) f t) := by
  unfold threadSet; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_threadSet _ _)

theorem rsf_threadGet {α : Type} (f : Tcb → α) (t : ObjRef) : FK rsF (threadGet (Z := Unit) f t) := by
  unfold threadGet; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_threadGet _ _)

theorem rsf_getThreadState (t : ObjRef) : FK rsF (getThreadState (Z := Unit) t) := by
  unfold getThreadState; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_getThreadState _)

theorem rsf_setThreadState (t : ObjRef) (ts : ThreadState) : FK rsF (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_setThreadState _ _)

theorem rsf_getSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    FK rsF (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_getSimpleKo _ _)

theorem rsf_setSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    FK rsF (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_setSimpleKo _ _ _)

theorem rsf_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef) :
    FK rsF (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_updateSkObjRef _ _ _ _)

theorem rsf_getSchedContext (q : ObjRef) : FK rsF (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_getSchedContext _)

theorem rsf_updateSchedContext (q : ObjRef) (f : SchedContext → SchedContext) :
    FK rsF (updateSchedContext (Z := Unit) q f) := by
  unfold updateSchedContext; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_updateSchedContext _ _)

theorem rsf_getScObjRef (f : SchedContext → Option ObjRef) (q : ObjRef) : FK rsF (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_getScObjRef _ _)

theorem rsf_getTcbObjRef (f : Tcb → Option ObjRef) (t : ObjRef) : FK rsF (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_getTcbObjRef _ _)

theorem rsf_getTcbQueue (d : Domain) (p : Priority) : FK rsF (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_getTcbQueue _ _)

theorem rsf_setTcbQueue (d : Domain) (p : Priority) (q : ReadyQueue) : FK rsF (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_setTcbQueue _ _ _)

theorem rsf_tcbSchedAction (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    FK rsF (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_tcbSchedAction _ _)

theorem rsf_setSchedulerAction (a : SchedulerAction) : FK rsF (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_setSchedulerAction _)

theorem rsf_getScRefillSufficient (sc : ObjRef) (u : Ticks) : FK rsF (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_getScRefillSufficient _ _)

theorem rsf_getScRefillReady (sc : ObjRef) : FK rsF (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_getScRefillReady _)

theorem rsf_tcbReleaseRemove (t : ObjRef) : FK rsF (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_tcbReleaseRemove _)

theorem rsf_rescheduleRequired : FK rsF (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_rescheduleRequired)

theorem rsf_testReschedule (t : ObjRef) : FK rsF (testReschedule (Z := Unit) t) := by
  unfold testReschedule; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_testReschedule _)

theorem rsf_replyUnlinkSc (sc r : ObjRef) : FK rsF (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_replyUnlinkSc _ _)

theorem rsf_schedContextDonate (sc t : ObjRef) : FK rsF (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_schedContextDonate _ _)

theorem rsf_replyUnlinkTcb (t r : ObjRef) : FK rsF (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; rsf_auto
macro_rules | `(tactic| rsf_leaf) => `(tactic| with_reducible exact rsf_replyUnlinkTcb _ _)

theorem rsf_replyRemove (t r : ObjRef) : FK rsF (replyRemove (Z := Unit) t r) := by
  unfold replyRemove; rsf_auto

/-- The scheduler action kept by the donation's first steps. -/
theorem fa_tcbSchedAction (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    FK (fun σ : State Unit => σ.schedulerAction) (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction threadGet getTcbQueue setTcbQueue; dk_auto0

theorem fa_tcbReleaseRemove (t : ObjRef) :
    FK (fun σ : State Unit => σ.schedulerAction) (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove setReleaseQueue; dk_auto0

end

end Fl4Proofs.P3.Vs

/-! ## The release queue and the yield links -/

namespace Fl4Proofs.P3.RelQ
open Fl4Spec

noncomputable section

theorem rq_schedContextDonate' (sc t : ObjRef) : RQ (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_schedContextDonate' _ _)

theorem rq_replyUnlinkTcb' (t r : ObjRef) : RQ (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb; rq_auto
macro_rules | `(tactic| rq_leaf) => `(tactic| with_reducible exact rq_replyUnlinkTcb' _ _)

theorem rq_replyRemove' (t r : ObjRef) : RQ (replyRemove (Z := Unit) t r) := by
  unfold replyRemove; rq_auto

end

end Fl4Proofs.P3.RelQ

namespace Fl4Proofs.P3.YK
open Fl4Spec

noncomputable section

theorem yk_getScObjRef'' (f : SchedContext → Option ObjRef) (q : ObjRef) : YKM (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; exact yk_bind (yk_getSchedContext' q) fun _ => yk_pure _
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getScObjRef'' _ _)

theorem yk_getTcbObjRef'' (f : Tcb → Option ObjRef) (t : ObjRef) : YKM (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; exact yk_threadGet' _ _
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_getTcbObjRef'' _ _)
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_tcbSchedAction _ _)
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_tcbReleaseRemove _)

theorem yk_schedContextDonate' (sc t : ObjRef) : YKM (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate testReschedule rescheduleRequired setSchedulerAction getScRefillSufficient
    getScRefillReady
  yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_schedContextDonate' _ _)

theorem yk_replyUnlinkSc' (sc r : ObjRef) : YKM (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; yk_auto
macro_rules | `(tactic| yk_leaf) => `(tactic| with_reducible exact yk_replyUnlinkSc' _ _)

theorem yk_replyRemove' (t r : ObjRef) : YKM (replyRemove (Z := Unit) t r) := by
  unfold replyRemove; yk_auto

end

end Fl4Proofs.P3.YK

/-! ## The donation -/

namespace Fl4Proofs.P3.Sched
open Fl4Spec Fl4Proofs.P3.Notif Fl4Proofs.P3.SVK

noncomputable section

/-- **A donor losing its SC** (`test_reschedule`): a reschedule pending
after, or the donor neither the current thread nor the switch target
before. -/
def DonA (σ σ' : State Unit) (f : ObjRef) : Prop :=
  σ'.schedulerAction = .chooseNewThread ∨ (f ≠ σ.curThread ∧ σ.schedulerAction ≠ .switchThread f)

/-- **The scheduler view across a donation to `t`** (module docstring). -/
structure DonV (t q : ObjRef) (σ σ' : State Unit) : Prop where
  ct : σ'.curThread = σ.curThread
  time : σ'.curTime = σ.curTime
  act : σ'.schedulerAction = σ.schedulerAction ∨ σ'.schedulerAction = .chooseNewThread
  sc : ∀ p y n, σ'.kheap p = some (.schedContext y n) → ∃ y0, σ.kheap p = some (.schedContext y0 n) ∧
    y.scRefills = y0.scRefills ∧ y.scRefillMax = y0.scRefillMax ∧
    (y.scTcb = y0.scTcb ∨ (p = q ∧ y.scTcb = some t ∧ ∀ f, y0.scTcb = some f → DonA σ σ' f))
  tcb : ∀ u x, σ.kheap u = some (.tcb x) → ∃ x', σ'.kheap u = some (.tcb x') ∧
    (x'.tcbSchedContext = x.tcbSchedContext ∨ (u = t ∧ x.tcbSchedContext = none) ∨
      (x'.tcbSchedContext = none ∧ DonA σ σ' u ∧ ∃ y0 n, σ.kheap q = some (.schedContext y0 n) ∧ y0.scTcb = some u))

/-- An SC after an `SVS` step was one before, with the same view. -/
theorem svs_scB {σ σ' : State Unit} (h : SVS σ σ') {p : ObjRef} {y : SchedContext} {n : Nat}
    (hp : σ'.kheap p = some (.schedContext y n)) :
    ∃ y0, σ.kheap p = some (.schedContext y0 n) ∧ y.scRefills = y0.scRefills ∧
      y.scRefillMax = y0.scRefillMax ∧ y.scTcb = y0.scTcb := by
  have e : sv (σ.kheap p) = (2, none, y.scRefills, y.scRefillMax, y.scTcb, n) := by rw [← h.1 p, hp]; rfl
  obtain ⟨y0, hy0, e1, e2, e3⟩ := sv_sc e
  exact ⟨y0, hy0, e1.symm, e2.symm, e3.symm⟩

theorem DonV.ofSVS {t q : ObjRef} {σ σ' : State Unit} (h : SVS σ σ') (hct : σ'.curThread = σ.curThread) :
    DonV t q σ σ' := by
  refine ⟨hct, h.2.1, h.2.2, fun p y n hp => ?_, fun u x hx => ?_⟩
  · obtain ⟨y0, hy0, e1, e2, e3⟩ := svs_scB h hp
    exact ⟨y0, hy0, e1, e2, Or.inl e3⟩
  · obtain ⟨x', hx', e⟩ := h.tcbSc hx
    exact ⟨x', hx', Or.inl e⟩

/-- `DonV` after an `SVS` step keeping the current thread. -/
theorem DonV.svs_trans {t q : ObjRef} {σ σ1 σ' : State Unit} (h1 : SVS σ σ1) (hct : σ1.curThread = σ.curThread)
    (h2 : DonV t q σ1 σ') : DonV t q σ σ' := by
  have hA : ∀ f, DonA σ1 σ' f → DonA σ σ' f := by
    rintro f (h | ⟨hf, hs⟩)
    · exact Or.inl h
    · by_cases hc : σ'.schedulerAction = .chooseNewThread
      · exact Or.inl hc
      refine Or.inr ⟨by rw [← hct]; exact hf, ?_⟩
      rcases h1.2.2 with e | e
      · rw [← e]; exact hs
      · exfalso
        rcases h2.act with e' | e'
        · exact hc (e'.trans e)
        · exact hc e'
  refine ⟨h2.ct.trans hct, h2.time.trans h1.2.1, ?_, fun p y n hp => ?_, fun u x hx => ?_⟩
  · rcases h2.act with e | e
    · rcases h1.2.2 with e' | e'
      · exact Or.inl (e.trans e')
      · exact Or.inr (e.trans e')
    · exact Or.inr e
  · obtain ⟨y1, hy1, r1, m1, c1⟩ := h2.sc p y n hp
    obtain ⟨y0, hy0, r0, m0, c0⟩ := svs_scB h1 hy1
    refine ⟨y0, hy0, r1.trans r0, m1.trans m0, ?_⟩
    rcases c1 with c1 | ⟨c1, c2, c3⟩
    · exact Or.inl (c1.trans c0)
    · exact Or.inr ⟨c1, c2, fun f hf => hA f (c3 f (c0.trans hf))⟩
  · obtain ⟨x1, hx1, e1⟩ := h1.tcbSc hx
    obtain ⟨x', hx', c⟩ := h2.tcb u x1 hx1
    refine ⟨x', hx', ?_⟩
    rcases c with c | ⟨c1, c2⟩ | ⟨c1, c2, y1, n1, hy1, ey1⟩
    · exact Or.inl (c.trans e1)
    · exact Or.inr (Or.inl ⟨c1, e1 ▸ c2⟩)
    · obtain ⟨y0, hy0, -, -, e0⟩ := svs_scB h1 hy1
      exact Or.inr (Or.inr ⟨c1, hA u c2, y0, n1, hy0, e0 ▸ ey1⟩)

/-- **`test_reschedule f`**: a reschedule pending after, or nothing done and
`f` neither the current thread nor the switch target. -/
theorem testReschedule_out {σ : State Unit} {f : ObjRef} {x : Unit × State Unit}
    (hx : x ∈ (testReschedule (Z := Unit) f σ).1) :
    x.2.schedulerAction = .chooseNewThread ∨
      (x.2 = σ ∧ f ≠ σ.curThread ∧ σ.schedulerAction ≠ .switchThread f) := by
  unfold testReschedule at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy1] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy2] at hx
  obtain ⟨y3, hy3, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy3] at hx
  dsimp only at hx
  unfold NonDet.when at hx
  split_ifs at hx with hc
  · exact Or.inl (rescheduleRequired_cn hx)
  · exact Or.inr ⟨(Prod.mk.inj (Set.mem_singleton_iff.1 hx)).2, fun e => hc (Or.inl e),
      fun e => hc (Or.inr (by simp [e]))⟩

/-- An outcome of `get_tcb_obj_ref`: the object a TCB, the state kept. -/
theorem getTcbObjRef_mem {σ : State Unit} {g : Tcb → Option ObjRef} {t : ObjRef}
    {y : Option ObjRef × State Unit} (hy : y ∈ (getTcbObjRef (Z := Unit) g t σ).1) :
    ∃ x, σ.kheap t = some (.tcb x) ∧ y = (g x, σ) := by
  unfold getTcbObjRef threadGet at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨hk, hs⟩ := wd_getTcb_mem hz
  rw [hs] at hy
  exact ⟨z.1, hk, Set.mem_singleton_iff.1 hy⟩

set_option maxHeartbeats 4000000 in
/-- **`sched_context_donate q t`** of a thread `t` with no SC (module
docstring). -/
theorem donate_donV {σ σ' : State Unit} {q t : ObjRef} {xt : Tcb} (hkt : σ.kheap t = some (.tcb xt))
    (hxt : xt.tcbSchedContext = none) (hm : ((), σ') ∈ (schedContextDonate (Z := Unit) q t σ).1) :
    DonV t q σ σ' := by
  have hct : σ'.curThread = σ.curThread := Vs.DK.ct (Vs.dk_schedContextDonate' q t) hm
  unfold schedContextDonate at hm
  obtain ⟨y1, hy1, hm⟩ := hm
  obtain ⟨yc, n, hkc, rfl⟩ := getScObjRef_mem hy1
  have hqt : q ≠ t := by rintro rfl; rw [hkt] at hkc; cases hkc
  obtain ⟨y2, hy2, hm⟩ := hm
  obtain ⟨w1, hw1, hm⟩ := hm
  obtain ⟨y0, n0, hk0, e1⟩ := MaxK.updSc_mem hw1
  have e1' : w1.2 = updK y2.2 q (.schedContext (scTcbUpdate (fun _ => some t) y0) n0) := e1
  rw [e1'] at hm
  obtain ⟨xd6, hkd6, e2⟩ := threadSet_mem hm
  have hσ' : σ' = updK (updK y2.2 q (.schedContext (scTcbUpdate (fun _ => some t) y0) n0)) t
      (.tcb (tcbSchedContextUpdate (fun _ => some q) xd6)) := e2
  have hkd6' : y2.2.kheap t = some (.tcb xd6) := by
    simpa only [updK, Function.update_of_ne (Ne.symm hqt)] using hkd6
  -- the final state's objects
  have kq : σ'.kheap q = some (.schedContext (scTcbUpdate (fun _ => some t) y0) n0) := by
    rw [hσ']; simp [updK, hqt]
  have kt : σ'.kheap t = some (.tcb (tcbSchedContextUpdate (fun _ => some q) xd6)) := by
    rw [hσ']; simp [updK]
  have ko : ∀ p, p ≠ q → p ≠ t → σ'.kheap p = y2.2.kheap p := fun p h1 h2 => by
    rw [hσ']; simp [updK, h1, h2]
  have hact : σ'.schedulerAction = y2.2.schedulerAction := by rw [hσ']; rfl
  have htime : σ'.curTime = y2.2.curTime := by rw [hσ']; rfl
  cases hyt : yc.scTcb with
  | none =>
    rw [hyt] at hy2
    simp only [NonDet.when, ne_eq, not_true_eq_false, ↓reduceIte] at hy2
    have hy2' : y2 = ((), σ) := Set.mem_singleton_iff.1 hy2
    subst hy2'
    dsimp only at hk0 hkd6' ko hact htime
    rw [hkc] at hk0; cases hk0
    rw [hkt] at hkd6'; cases hkd6'
    refine ⟨hct, htime, Or.inl hact, fun p y m hp => ?_, fun u x hx => ?_⟩
    · by_cases hpq : p = q
      · subst hpq; rw [kq] at hp; cases hp
        exact ⟨yc, hkc, rfl, rfl, Or.inr ⟨rfl, rfl, fun f hf => by rw [hyt] at hf; cases hf⟩⟩
      · have hpt : p ≠ t := by rintro rfl; rw [kt] at hp; cases hp
        rw [ko p hpq hpt] at hp
        exact ⟨y, hp, rfl, rfl, Or.inl rfl⟩
    · by_cases hut : u = t
      · subst hut; rw [hkt] at hx; cases hx
        exact ⟨_, kt, Or.inr (Or.inl ⟨rfl, hxt⟩)⟩
      · have huq : u ≠ q := by rintro rfl; rw [hkc] at hx; cases hx
        exact ⟨x, by rw [ko u huq hut]; exact hx, Or.inl rfl⟩
  | some f =>
    rw [hyt] at hy2
    simp only [NonDet.when, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte] at hy2
    obtain ⟨z1, hz1, hy2⟩ := hy2
    rw [Set.mem_singleton_iff.1 hz1] at hy2
    obtain ⟨z2, hz2, hy2⟩ := hy2
    have h2 := sv_tcbSchedAction' _ _ σ z2 hz2
    have a2 : z2.2.schedulerAction = σ.schedulerAction := Vs.fa_tcbSchedAction _ _ σ z2 hz2
    have c2 := Vs.DK.ct (Vs.dk_tcbSchedAction' _ _) hz2
    obtain ⟨z3, hz3, hy2⟩ := hy2
    have h3 := sv_tcbReleaseRemove' _ z2.2 z3 hz3
    have a3 : z3.2.schedulerAction = z2.2.schedulerAction := Vs.fa_tcbReleaseRemove _ z2.2 z3 hz3
    have c3 := Vs.DK.ct (Vs.dk_tcbReleaseRemove' _) hz3
    have h23 := h2.trans h3
    obtain ⟨z4, hz4, hy2⟩ := hy2
    obtain ⟨x3, hkt3, e4⟩ := threadSet_mem hz4
    rw [e4] at hy2
    set σf := updK z3.2 f (.tcb (tcbSchedContextUpdate (fun _ => none) x3)) with hσf
    have h5 := sv_testReschedule' f σf y2 hy2
    have T5 := testReschedule_out hy2
    have hfc : q ≠ f := by
      rintro rfl
      obtain ⟨y', hy', -⟩ := h23.scOf hkc
      rw [hkt3] at hy'; cases hy'
    have kf : σf.kheap f = some (.tcb (tcbSchedContextUpdate (fun _ => none) x3)) := by simp [hσf, updK]
    have kfo : ∀ p, p ≠ f → σf.kheap p = z3.2.kheap p := fun p hp => by simp [hσf, updK, hp]
    have hcurf : σf.curThread = σ.curThread := by
      show z3.2.curThread = σ.curThread; rw [c3, c2]
    have hactf : σf.schedulerAction = σ.schedulerAction := by
      show z3.2.schedulerAction = σ.schedulerAction; rw [a3, a2]
    have DA : DonA σ σ' f := by
      rcases T5 with e | ⟨-, e1, e2⟩
      · exact Or.inl (hact.trans e)
      · exact Or.inr ⟨by rw [← hcurf]; exact e1, by rw [← hactf]; exact e2⟩
    have h5f : σf.curTime = σ.curTime := by show z3.2.curTime = σ.curTime; exact h23.2.1
    refine ⟨hct, by rw [htime, h5.2.1, h5f], ?_, fun p y m hp => ?_, fun u x hx => ?_⟩
    · rw [hact]
      rcases h5.2.2 with e | e
      · rw [e, hactf]; exact Or.inl rfl
      · exact Or.inr e
    · by_cases hpq : p = q
      · subst hpq; rw [kq] at hp; cases hp
        obtain ⟨y5, hy5, r5, m5, t5⟩ := svs_scB h5 hk0
        rw [kfo _ hfc] at hy5
        obtain ⟨y6, hy6, r6, m6, t6⟩ := svs_scB h23 hy5
        rw [hkc] at hy6; cases hy6
        refine ⟨_, hkc, r5.trans r6, m5.trans m6, Or.inr ⟨rfl, rfl, fun f' hf' => ?_⟩⟩
        rw [hyt] at hf'; cases hf'; exact DA
      · have hpt : p ≠ t := by rintro rfl; rw [kt] at hp; cases hp
        rw [ko p hpq hpt] at hp
        obtain ⟨y5, hy5, r5, m5, t5⟩ := svs_scB h5 hp
        have hpf : p ≠ f := by rintro rfl; rw [kf] at hy5; cases hy5
        rw [kfo _ hpf] at hy5
        obtain ⟨y6, hy6, r6, m6, t6⟩ := svs_scB h23 hy5
        exact ⟨y6, hy6, r5.trans r6, m5.trans m6, Or.inl (t5.trans t6)⟩
    · by_cases hut : u = t
      · subst hut; rw [hkt] at hx; cases hx
        exact ⟨_, kt, Or.inr (Or.inl ⟨rfl, hxt⟩)⟩
      have huq : u ≠ q := by rintro rfl; rw [hkc] at hx; cases hx
      rw [ko u huq hut]
      by_cases huf : u = f
      · subst huf
        obtain ⟨x', hx', e'⟩ := h5.tcbSc kf
        exact ⟨x', hx', Or.inr (Or.inr ⟨e', DA, yc, n, hkc, hyt⟩)⟩
      · obtain ⟨x2, hx2, e2⟩ := h23.tcbSc hx
        rw [← kfo u huf] at hx2
        obtain ⟨x', hx', e'⟩ := h5.tcbSc hx2
        exact ⟨x', hx', Or.inl (e'.trans e2)⟩

/-- `reply_unlink_sc q r` cuts links only, but at `q`. -/
theorem lkm_replyUnlinkSc {W : ObjRef → Prop} {q r : ObjRef} (hq : W q) : LKM W (replyUnlinkSc (Z := Unit) q r) := by
  unfold replyUnlinkSc getReply getSimpleKo setReplyObjRef
  repeat' (first | exact lkm_getSchedContext _ | exact lk_updateSchedContextW _ hq | lkm_step0)

/-- `sched_context_donate q t` cuts links only, but at `q` and `t`. -/
theorem lkm_donate {W : ObjRef → Prop} {q t : ObjRef} (hq : W q) (ht : W t) :
    LKM W (schedContextDonate (Z := Unit) q t) := by
  unfold schedContextDonate testReschedule
  repeat' (first
    | exact lkm_getScObjRef _ _
    | exact lkm_tcbSchedAction _ _
    | exact lkm_tcbReleaseRemove _
    | exact lkm_rescheduleRequired
    | exact lk_updateSchedContextW _ hq
    | exact lk_threadSetW _ ht
    | lkm_step0)

set_option maxHeartbeats 4000000 in
/-- **The call-stack part of `reply_remove`** (module docstring). -/
theorem rmSc_donV {σ σ5 : State Unit} {t r : ObjRef} {x0 : Tcb} (hk0 : σ.kheap t = some (.tcb x0))
    (hsp : replyRemoveSc t r σ = ({((), σ5)}, False)) :
    ∃ q, (q = t ∨ ∃ y n, σ.kheap q = some (.schedContext y n)) ∧
      (∀ y n, σ.kheap q = some (.schedContext y n) → r ∈ y.scReplies) ∧ DonV t q σ σ5 ∧
      LK (fun p => p = q ∨ p = t) σ σ5 := by
  have hm : ((), σ5) ∈ (replyRemoveSc t r σ).1 := by rw [hsp]; rfl
  unfold replyRemoveSc at hm
  obtain ⟨y1, hy1, hm⟩ := hm
  rw [Set.mem_singleton_iff.1 hy1] at hm
  dsimp only at hm
  cases hw : scWithReply r σ with
  | none =>
    rw [hw] at hm
    obtain rfl : σ5 = σ := congrArg Prod.snd (Set.mem_singleton_iff.1 hm)
    exact ⟨t, Or.inl rfl, fun y n h => (by rw [hk0] at h; cases h), DonV.ofSVS (SVS.refl _) rfl, LK.refl _ _⟩
  | some q =>
    rw [hw] at hm
    obtain ⟨yq, nq, hkq, hrq⟩ := scWithReply_mem' hw
    have hQ : ∀ y n, σ.kheap q = some (.schedContext y n) → r ∈ y.scReplies := fun y n h => by
      rw [hkq] at h; cases h; exact hrq
    dsimp only at hm
    obtain ⟨y2, hy2, hm⟩ := hm
    have h2 := (sv_liftM SchedContext.scReplies (sv_getSchedContext' q)) σ y2 hy2
    have c2 := Vs.DK.ct (Vs.dk_liftM _ (Vs.dk_getSchedContext' q)) hy2
    obtain ⟨y3, hy3, hm⟩ := hm
    obtain ⟨xt, hkt, e3⟩ := getTcbObjRef_mem hy3
    rw [e3] at hm
    obtain ⟨y4, hy4, hm⟩ := hm
    have h4 := sv_replyUnlinkSc' q r y2.2 y4 hy4
    have l2 : LK (fun p => p = q ∨ p = t) σ y2.2 := (lkm_liftM _ (lkm_getSchedContext q)) σ y2 hy2
    have l4 : LK (fun p => p = q ∨ p = t) y2.2 y4.2 := lkm_replyUnlinkSc (Or.inl rfl) y2.2 y4 hy4
    have c4 := Vs.DK.ct (Vs.dk_replyUnlinkSc' q r) hy4
    have h24 := h2.trans h4
    have c24 : y4.2.curThread = σ.curThread := c4.trans c2
    unfold NonDet.when at hm
    split_ifs at hm with hc
    · obtain ⟨x4, hx4, e4⟩ := h4.tcbSc hkt
      exact ⟨q, Or.inr ⟨yq, nq, hkq⟩, hQ, DonV.svs_trans h24 c24 (donate_donV hx4 (e4.trans hc.2) hm),
        (l2.trans l4).trans (lkm_donate (Or.inl rfl) (Or.inr rfl) y4.2 _ hm)⟩
    · obtain rfl : σ5 = y4.2 := congrArg Prod.snd (Set.mem_singleton_iff.1 hm)
      exact ⟨q, Or.inr ⟨yq, nq, hkq⟩, hQ, DonV.ofSVS h24 c24, l2.trans l4⟩

end

end Fl4Proofs.P3.Sched
