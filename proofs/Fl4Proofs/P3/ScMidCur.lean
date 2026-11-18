/-
P3 (DESIGN.md §9), scheduling contexts: **Configure of the current SC**
(the SchedControl step's `MidA` case, spec side only).

* `MidKW σ σ'`: `MidK` without the current SC's refills clause and the
  no-switch clause, the release queue's new members allowed to include the
  current thread once the consumed time is cleared. `commit_time` charges the
  current SC's refills and clears the consumed time; a resume may then move
  the current thread to the release queue (the reschedule that follows is
  Configure's).
* `MidKWA P m`: every outcome of `m` from `P` is `MidKW`-related to its start;
  `MidKA` lemmas lift (`mkwa_of`).
* `mkw_configureCur`: Configure of the current SC, bound to the current
  thread, is `MidKW` with the consumed time cleared and a reschedule
  pending; `MidKW.midA`: then `MidA`.
-/
import Fl4Proofs.P3.ScMidKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

/-- **The weak current-thread step** (module docstring). -/
structure MidKW (σ σ' : State Unit) : Prop where
  ct : σ'.curThread = σ.curThread
  csc : σ'.curSc = σ.curSc
  time : σ'.curTime = σ.curTime
  idle : σ'.idleThread = σ.idleThread
  isc : σ'.idleSc = σ.idleSc
  cons : σ'.consumedTime = σ.consumedTime ∨ σ'.consumedTime = 0
  cn : σ.schedulerAction = .chooseNewThread → σ'.schedulerAction = .chooseNewThread
  ctT : MidT σ σ' σ.curThread
  idT : MidT σ σ' σ.idleThread
  cscS : ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → ∃ y', σ'.kheap σ.curSc = some (.schedContext y' n) ∧
    y'.scTcb = y.scTcb ∧ (scActive y = true → scActive y' = true)
  rq : ∀ t ∈ σ'.releaseQueue, t ∈ σ.releaseQueue ∨ (t ≠ σ.idleThread ∧ (t ≠ σ.curThread ∨ σ'.consumedTime = 0))

theorem MidKW.refl (σ : State Unit) : MidKW σ σ :=
  ⟨rfl, rfl, rfl, rfl, rfl, Or.inl rfl, id, MidT.refl _ _, MidT.refl _ _, fun y _ h => ⟨y, h, rfl, id⟩,
    fun _ h => Or.inl h⟩

theorem MidKW.cons0 {σ σ' : State Unit} (h : MidKW σ σ') (h0 : σ.consumedTime = 0) : σ'.consumedTime = 0 := by
  rcases h.cons with e | e
  · rw [e, h0]
  · exact e

theorem MidKW.trans {σ1 σ2 σ3 : State Unit} (h1 : MidKW σ1 σ2) (h2 : MidKW σ2 σ3) : MidKW σ1 σ3 := by
  refine ⟨h2.ct.trans h1.ct, h2.csc.trans h1.csc, h2.time.trans h1.time, h2.idle.trans h1.idle, h2.isc.trans h1.isc, ?_,
    fun h => h2.cn (h1.cn h), ?_, ?_, ?_, ?_⟩
  · rcases h2.cons with e | e
    · rw [e]; exact h1.cons
    · exact Or.inr e
  · have := h2.ctT; rw [h1.ct] at this; exact h1.ctT.trans this
  · have := h2.idT; rw [h1.idle] at this; exact h1.idT.trans this
  · intro y n hy
    obtain ⟨y2, hy2, e1, f1⟩ := h1.cscS y n hy
    have c2 := h2.cscS; rw [h1.csc] at c2
    obtain ⟨y3, hy3, e2, f2⟩ := c2 y2 n hy2
    exact ⟨y3, hy3, e2.trans e1, fun h => f2 (f1 h)⟩
  · intro t ht
    rcases h2.rq t ht with h | ⟨hi, hc⟩
    · rcases h1.rq t h with h' | ⟨hi', hc'⟩
      · exact Or.inl h'
      · refine Or.inr ⟨hi', ?_⟩
        rcases hc' with e | e
        · exact Or.inl e
        · exact Or.inr (h2.cons0 e)
    · rw [h1.idle] at hi; rw [h1.ct] at hc
      exact Or.inr ⟨hi, hc⟩

theorem MidK.toW {σ σ' : State Unit} (h : MidK σ σ') : MidKW σ σ' := by
  refine ⟨h.ct, h.csc, h.time, h.idle, h.isc, h.cons, h.cn, h.ctT, h.idT, fun y n hy => ?_, fun t ht => ?_⟩
  · obtain ⟨y', h1, h2, h3, -⟩ := h.cscS y n hy; exact ⟨y', h1, h2, h3⟩
  · rcases h.rq t ht with e | ⟨hi, hc⟩
    · exact Or.inl e
    · exact Or.inr ⟨hi, hc.imp id fun e => e.1⟩

theorem MidKW.of_fields {σ σ' : State Unit} (hk : σ'.kheap = σ.kheap) (h1 : σ'.curThread = σ.curThread)
    (h2 : σ'.curSc = σ.curSc) (h3 : σ'.curTime = σ.curTime) (h4 : σ'.idleThread = σ.idleThread)
    (h5 : σ'.consumedTime = σ.consumedTime) (h6 : σ'.schedulerAction = σ.schedulerAction)
    (h7 : σ'.releaseQueue = σ.releaseQueue) (h8 : σ'.idleSc = σ.idleSc := by first | rfl | assumption) :
    MidKW σ σ' :=
  (MidK.of_fields hk h1 h2 h3 h4 h5 h6 h7 h8).toW

/-! ## The monad -/

def MidKWA {α : Type} (P : State Unit → Prop) (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, P σ → ∀ x, x ∈ (m σ).1 → MidKW σ x.2

def MidKWStable (P : State Unit → Prop) : Prop := ∀ σ σ', P σ → MidKW σ σ' → P σ'

theorem mkwStable_true : MidKWStable (fun _ => True) := fun _ _ _ _ => trivial

section Comb
variable {P : State Unit → Prop}

theorem mkwa_of {α : Type} {m : NonDet (State Unit) α} (h : MidKA P m) : MidKWA P m :=
  fun σ hσ x hx => (h σ hσ x hx).toW

theorem mkwa_bind {α β : Type} (hP : MidKWStable P) {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : MidKWA P m) (hg : ∀ a, MidKWA P (g a)) : MidKWA P (m >>= g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  have h1 := hm σ hσ y hy
  exact h1.trans (hg y.1 y.2 (hP σ y.2 hσ h1) x hx)

theorem mkwa_bind' {α β : Type} (hP : MidKWStable P) {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : MidKWA P m) (hg : ∀ a, MidKWA P (g a)) : MidKWA P (NonDet.bind m g) := mkwa_bind hP hm hg

theorem mkwa_bind_rdo {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : RdO m)
    (hg : ∀ a, MidKWA P (g a)) : MidKWA P (m >>= g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  rw [hm σ y hy] at hx
  exact hg y.1 σ hσ x hx

theorem mkwa_bind_rdn {α β : Type} {Q : State Unit → α → Prop} {m : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) β} (hm : RdN Q m) (hg : ∀ a, MidKWA (fun σ => P σ ∧ Q σ a) (g a)) :
    MidKWA P (m >>= g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨e, hq⟩ := hm σ y hy
  rw [e] at hx
  exact hg y.1 σ ⟨hσ, hq⟩ x hx

theorem mkwa_mono {α : Type} {Q : State Unit → Prop} {m : NonDet (State Unit) α} (hQ : ∀ σ, P σ → Q σ)
    (h : MidKWA Q m) : MidKWA P m := fun σ hσ => h σ (hQ σ hσ)

theorem mkwa_of_rdo {α : Type} {m : NonDet (State Unit) α} (h : RdO m) : MidKWA P m :=
  fun σ _ x hx => by rw [h σ x hx]; exact MidKW.refl σ

theorem mkwa_pure {α : Type} (a : α) : MidKWA P (pure a : NonDet (State Unit) α) := mkwa_of_rdo (rdo_pure a)
theorem mkwa_pure' {α : Type} (a : α) : MidKWA P (NonDet.pure a : NonDet (State Unit) α) := mkwa_of_rdo (rdo_pure' a)
theorem mkwa_gets {α : Type} (g : State Unit → α) : MidKWA P (NonDet.gets g) := mkwa_of_rdo (rdo_gets g)
theorem mkwa_assert (Q : Prop) : MidKWA P (NonDet.assert Q : NonDet (State Unit) Unit) := mkwa_of_rdo (rdo_assert Q)
theorem mkwa_fail {α : Type} : MidKWA P (NonDet.fail : NonDet (State Unit) α) := mkwa_of_rdo rdo_fail
theorem mkwa_assertOpt {α : Type} (o : Option α) : MidKWA P (NonDet.assertOpt o : NonDet (State Unit) α) :=
  mkwa_of_rdo (rdo_assertOpt o)
theorem mkwa_getsThe {α : Type} (g : State Unit → Option α) : MidKWA P (NonDet.getsThe g) :=
  mkwa_of_rdo (rdo_getsThe g)
theorem mkwa_getObject (p : ObjRef) : MidKWA P (getObject (Z := Unit) p) := mkwa_getsThe _

theorem mkwa_ite {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDet (State Unit) α} (h1 : MidKWA P m1)
    (h2 : MidKWA P m2) : MidKWA P (if Q then m1 else m2) := by
  split <;> assumption

theorem mkwa_when (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : MidKWA P m) :
    MidKWA P (NonDet.when Q m) := by
  unfold NonDet.when; exact mkwa_ite Q h (mkwa_pure' _)

theorem mkwa_whileLoop (hP : MidKWStable P) {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, MidKWA P (B r)) (r : α) : MidKWA P (NonDet.whileLoop C B r) := by
  intro σ hσ x hx
  induction hx with
  | done _ => exact MidKW.refl _
  | step _ hm _ ih => exact (hB _ _ hσ _ hm).trans (ih (hP _ _ hσ (hB _ _ hσ _ hm)))

theorem mkwa_modify {g : State Unit → State Unit} (hg : ∀ σ, P σ → MidKW σ (g σ)) : MidKWA P (NonDet.modify g) := by
  intro σ hσ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hg σ hσ

/-- `update_sched_context` keeping the thread and activity (the refills free). -/
theorem mkwa_updateSchedContext {g : SchedContext → SchedContext} {p : ObjRef}
    (hg : ∀ y, (g y).scTcb = y.scTcb ∧ (scActive y = true → scActive (g y) = true)) :
    MidKWA P (updateSchedContext (Z := Unit) p g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getObject_mem hy
  obtain ⟨o, σ1⟩ := y
  simp only at hk hs hx; subst σ1
  cases o
  all_goals try exact hx.elim
  obtain ⟨k, hk', -, e⟩ := setObject_mem hx
  rw [hk] at hk'; cases hk'
  rw [e]
  refine ⟨rfl, rfl, rfl, rfl, rfl, Or.inl rfl, id, fun x' hx' => ?_, fun x' hx' => ?_, fun y' n' hy' => ?_,
    fun _ h => Or.inl h⟩
  · by_cases e' : σ.curThread = p
    · rw [e', hk] at hx'; cases hx'
    · exact ⟨x', by simp [Function.update_of_ne e', hx'], rfl, rfl⟩
  · by_cases e' : σ.idleThread = p
    · rw [e', hk] at hx'; cases hx'
    · exact ⟨x', by simp [Function.update_of_ne e', hx'], rfl, rfl⟩
  · by_cases e' : σ.curSc = p
    · rw [e', hk] at hy'; cases hy'
      exact ⟨_, by rw [e']; simp, (hg _).1, (hg _).2⟩
    · exact ⟨y', by simp [Function.update_of_ne e', hy'], rfl, id⟩

end Comb

macro "mkw_step" : tactic => `(tactic| first
  | with_reducible exact mkwa_pure _ | with_reducible exact mkwa_pure' _ | with_reducible exact mkwa_fail
  | with_reducible exact mkwa_gets _ | with_reducible exact mkwa_assert _ | with_reducible exact mkwa_assertOpt _
  | with_reducible exact mkwa_getObject _ | with_reducible exact mkwa_getsThe _
  | with_reducible exact mkwa_of_rdo (RdO.ofRdN (rdn_threadGet _ _))
  | with_reducible exact mkwa_of_rdo (RdO.ofRdN (rdn_getSchedContext _))
  | ((with_reducible apply mkwa_modify); intro _ _; exact MidKW.of_fields rfl rfl rfl rfl rfl rfl rfl rfl)
  | ((with_reducible apply mkwa_updateSchedContext); intro _; exact ⟨rfl, id⟩)
  | ((with_reducible apply mkwa_updateSchedContext); intro _; exact ⟨rfl, fun _ => (by assumption)⟩)
  | (with_reducible refine mkwa_bind (by assumption) ?_ (fun _ => ?_))
  | (with_reducible refine mkwa_bind' (by assumption) ?_ (fun _ => ?_))
  | (with_reducible apply mkwa_ite) | (with_reducible apply mkwa_when)
  | (with_reducible refine mkwa_whileLoop (by assumption) (fun _ => ?_) _)
  | split
  | (dsimp only))

macro "mkw_auto" : tactic => `(tactic| repeat mkw_step)

/-! ## The operations -/

section Ops

macro "unf_refills" : tactic => `(tactic| repeat (first | unfold refillNew | unfold refillUpdate | unfold updateRefillHd | unfold updateRefillTl | unfold refillAddTail | unfold refillPopHead | unfold getRefillHead | unfold getRefills | unfold getRefillTail | unfold refillFull | unfold refillSingle | unfold refillSize | unfold scheduleUsed | unfold chargeEntireHeadRefill | unfold handleOverrun | unfold headInsufficientLoop | unfold mergeNonoverlappingHeadRefill | unfold isRoundRobin | unfold getScActive | unfold getScRefillReady | unfold maybeAddEmptyTail | unfold refillBudgetCheckRoundRobin | unfold refillBudgetCheck))

/-- **`commit_time`**: `MidKW`, the consumed time cleared. -/
theorem mkw_commitTime {σ σ' : State Unit} {r : Unit} (h : (r, σ') ∈ (commitTime (Z := Unit) σ).1) :
    MidKW σ σ' ∧ σ'.consumedTime = 0 := by
  have hP := mkwStable_true
  rw [commitTime_eq] at h
  obtain ⟨y, hy, h⟩ := h
  have e := congrArg Prod.snd (Set.mem_singleton_iff.1 h)
  simp only at e
  subst e
  have k : MidKW σ y.2 := by
    refine (?_ : MidKWA (fun _ => True) commitHead) σ trivial y hy
    unfold commitHead
    unf_refills
    mkw_auto
  refine ⟨k.trans ?_, rfl⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inr rfl, id, MidT.refl _ _, MidT.refl _ _, fun y _ h => ⟨y, h, rfl, id⟩,
    fun _ h => Or.inl h⟩

theorem mkwa_refillNew (p : ObjRef) (m : Nat) (b per : Ticks) (hv : activeSc m = true) :
    MidKWA (fun _ => True) (refillNew (Z := Unit) p m b per) := by
  have hP := mkwStable_true
  unf_refills
  mkw_auto

theorem mkwa_refillUpdate (p : ObjRef) (per b : Ticks) (m : Nat) (hv : activeSc m = true) :
    MidKWA (fun _ => True) (refillUpdate (Z := Unit) p per b m) := by
  have hP := mkwStable_true
  unf_refills
  mkw_auto

/-- `tcb_release_enqueue` of a thread not idle, and not the current one
unless the consumed time is cleared. -/
theorem mkwa_tcbReleaseEnqueue (t : ObjRef) :
    MidKWA (fun σ => t ≠ σ.idleThread ∧ (t ≠ σ.curThread ∨ σ.consumedTime = 0)) (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue readyTimesAppend setReleaseQueue
  refine mkwa_bind_rdn (rdn_gets _) fun q => mkwa_bind_rdn (rdn_orderedInsert _ _ _ _) fun q' => ?_
  intro σ ⟨⟨⟨hti, htc⟩, hq⟩, hq'⟩ x hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hx
  have h1 : MidKW σ { σ with releaseQueue := q' } :=
    ⟨rfl, rfl, rfl, rfl, rfl, Or.inl rfl, id, MidT.refl _ _, MidT.refl _ _, fun y _ h => ⟨y, h, rfl, id⟩,
      fun u hu => by
        rcases hq' u hu with rfl | h
        · exact Or.inr ⟨hti, htc⟩
        · exact Or.inl (hq ▸ h)⟩
  unfold NonDet.when at hx
  split at hx
  · rw [Set.mem_singleton_iff.1 hx]
    exact h1.trans (MidKW.of_fields rfl rfl rfl rfl rfl rfl rfl rfl)
  · rw [Set.mem_singleton_iff.1 hx]; exact h1

theorem mkwa_postpone (p : ObjRef) :
    MidKWA (fun σ => ∀ y n t, σ.kheap p = some (.schedContext y n) → y.scTcb = some t →
      t ≠ σ.idleThread ∧ (t ≠ σ.curThread ∨ σ.consumedTime = 0)) (postpone (Z := Unit) p) := by
  unfold postpone
  refine mkwa_bind_rdn (rdn_getScObjRef _ _) fun o => mkwa_bind_rdn (rdn_assertOpt _) fun t => ?_
  have hst : MidKWStable (fun σ => t ≠ σ.idleThread ∧ (t ≠ σ.curThread ∨ σ.consumedTime = 0)) := fun σ σ' h k => by
    simp only at h ⊢; rw [k.idle, k.ct]
    exact ⟨h.1, h.2.imp id fun e => k.cons0 e⟩
  refine mkwa_mono (Q := fun σ => t ≠ σ.idleThread ∧ (t ≠ σ.curThread ∨ σ.consumedTime = 0)) ?_ ?_
  · rintro σ ⟨⟨h, y, n, hk, rfl⟩, ht⟩; exact h y n t hk ht
  · exact mkwa_bind hst (mkwa_of (mka_tcbSchedAction _ _)) fun _ => mkwa_bind hst (mkwa_tcbReleaseEnqueue _) fun _ =>
      mkwa_modify fun σ _ => MidKW.of_fields rfl rfl rfl rfl rfl rfl rfl rfl

theorem mkwa_schedContextResume (p : ObjRef) :
    MidKWA (fun σ => ∀ y n t, σ.kheap p = some (.schedContext y n) → y.scTcb = some t →
      t ≠ σ.idleThread ∧ (t ≠ σ.curThread ∨ σ.consumedTime = 0)) (schedContextResume (Z := Unit) p) := by
  unfold schedContextResume getScRefillReady getScRefillSufficient getTcbQueue
  refine mkwa_bind_rdo (RdO.ofRdN (rdn_getSchedContext _)) fun _ => mkwa_bind_rdo (rdo_assertOpt _) fun _ =>
    mkwa_bind_rdo (rdo_gets _) fun _ => mkwa_when _ ?_
  refine mkwa_bind_rdo (RdO.ofRdN (rdn_threadGet _ _)) fun _ => mkwa_bind_rdo (rdo_getsThe _) fun _ =>
    mkwa_bind_rdo (rdo_getsThe _) fun _ => mkwa_when _ ?_
  refine mkwa_bind_rdo (RdO.ofRdN (rdn_threadGet _ _)) fun _ => mkwa_bind_rdo (RdO.ofRdN (rdn_threadGet _ _)) fun _ =>
    mkwa_bind_rdo (rdo_bind (rdo_gets _) fun _ => rdo_pure _) fun _ => mkwa_bind_rdo (rdo_assert _) fun _ =>
    mkwa_postpone _

/-- `reschedule_required` leaves a reschedule pending. -/
theorem rescheduleRequired_cn {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (rescheduleRequired (Z := Unit) σ).1) : x.2.schedulerAction = .chooseNewThread := by
  unfold rescheduleRequired setSchedulerAction at hx
  obtain ⟨y, -, hx⟩ := hx
  generalize y.1 = act at hx
  cases act with
  | switchThread t =>
    obtain ⟨z, -, hx⟩ := hx
    obtain ⟨w, -, hx⟩ := hx
    rw [Set.mem_singleton_iff.1 hx]
  | resumeCurThread =>
    first | (rw [Set.mem_singleton_iff.1 hx]) | (obtain ⟨w, -, hx⟩ := hx; rw [Set.mem_singleton_iff.1 hx])
  | chooseNewThread =>
    first | (rw [Set.mem_singleton_iff.1 hx]) | (obtain ⟨w, -, hx⟩ := hx; rw [Set.mem_singleton_iff.1 hx])

/-- A `MidK` step keeps a pending reschedule and a cleared consumed time. -/
theorem MidK.keep0 {σ σ' : State Unit} (h : MidK σ σ') (h0 : σ.consumedTime = 0)
    (hc : σ.schedulerAction = .chooseNewThread) :
    σ'.consumedTime = 0 ∧ σ'.schedulerAction = .chooseNewThread := ⟨h.cons0 h0, h.cn hc⟩

set_option maxHeartbeats 4000000 in
/-- **Configure of the current SC, bound to the current thread**: `MidKW`,
the consumed time cleared (`commit_time`), a reschedule pending. -/
theorem mkw_configureCur {σ : State Unit} {p : ObjRef} {b per : Ticks} {mr : Nat} {badge : Badge} {flag : Data}
    {y0 : SchedContext} {n0 : Nat} (hk : σ.kheap p = some (.schedContext y0 n0)) (hp : p = σ.curSc)
    (hyt : y0.scTcb = some σ.curThread) (hci : σ.curThread ≠ σ.idleThread) (hv : activeSc mr = true) :
    ∀ x ∈ (invokeSchedControlConfigureFlags (Z := Unit) (.invokeSchedControlConfigureFlags p b per mr badge flag) σ).1,
      MidKW σ x.2 ∧ x.2.consumedTime = 0 ∧ x.2.schedulerAction = .chooseNewThread := by
  intro x hx
  have hP := mkwStable_true
  -- the tail after the refills
  have rest : ∀ (σ3 : State Unit) (x : Unit × State Unit), MidKW σ σ3 → SKa σ σ3 → σ3.consumedTime = 0 →
      x ∈ ((do
        NonDet.when (y0.scTcb ≠ none) (do
          schedContextResume p
          let tcbPtr ← NonDet.assertOpt y0.scTcb
          let st ← getThreadState tcbPtr
          let ct ← NonDet.gets fun s : State Unit => s.curThread
          if tcbPtr = ct then rescheduleRequired else NonDet.when (runnable st = true) (possibleSwitchTo tcbPtr))
        setScObjRef scBadgeUpdate p badge
        setScObjRef scSporadicUpdate p (testBit flag scSporadicFlag) : SMonad Unit Unit) σ3).1 →
      MidKW σ3 x.2 ∧ x.2.consumedTime = 0 ∧ x.2.schedulerAction = .chooseNewThread := by
    intro σ3 x k3 s3 h03 hx
    obtain ⟨y4, hy4, hx⟩ := hx
    have k4 : MidKW σ3 y4.2 ∧ y4.2.consumedTime = 0 ∧ y4.2.schedulerAction = .chooseNewThread := by
      unfold NonDet.when at hy4
      rw [if_pos (by rw [hyt]; simp)] at hy4
      obtain ⟨z1, hz1, hy4⟩ := hy4
      have kz : MidKW σ3 z1.2 := mkwa_schedContextResume p σ3 (fun y n t' hy ht' => by
        obtain ⟨y0', hy0', e, -⟩ := s3 p y n hy
        rw [hk] at hy0'; cases hy0'
        rcases e with e | e
        · rw [e, hyt] at ht'; cases ht'; rw [k3.idle, k3.ct]; exact ⟨hci, Or.inr h03⟩
        · rw [e] at ht'; cases ht') z1 hz1
      have hz0 : z1.2.consumedTime = 0 := kz.cons0 h03
      obtain ⟨z2, hz2, hy4⟩ := hy4
      rw [hyt] at hz2
      rw [Set.mem_singleton_iff.1 hz2] at hy4
      obtain ⟨z3, hz3, hy4⟩ := hy4
      rw [RdO.ofRdN (rdn_threadGet _ _) _ z3 hz3] at hy4
      obtain ⟨z4, hz4, hy4⟩ := hy4
      obtain ⟨e4, hv4⟩ := rdn_gets (fun s : State Unit => s.curThread) _ z4 hz4
      rw [e4, hv4] at hy4
      have hct : σ.curThread = z1.2.curThread := by rw [kz.ct, k3.ct]
      dsimp only at hy4
      rw [if_pos hct] at hy4
      have kr := mka_rescheduleRequired (P := fun _ => True) midkStable_true z1.2 trivial _ hy4
      exact ⟨kz.trans kr.toW, kr.cons0 hz0, rescheduleRequired_cn hy4⟩
    obtain ⟨k4, h04, hc4⟩ := k4
    obtain ⟨y5, hy5, hx⟩ := hx
    have k5 : MidK y4.2 y5.2 :=
      mka_updateSchedContext (P := fun _ => True) (g := scBadgeUpdate fun _ => badge) (p := p)
        (fun _ _ _ _ => ⟨rfl, id, fun _ => rfl⟩) _ trivial _ hy5
    have k6 : MidK y5.2 x.2 :=
      mka_updateSchedContext (P := fun _ => True) (g := scSporadicUpdate fun _ => testBit flag scSporadicFlag) (p := p)
        (fun _ _ _ _ => ⟨rfl, id, fun _ => rfl⟩) _ trivial _ hx
    obtain ⟨h05, hc5⟩ := k5.keep0 h04 hc4
    obtain ⟨h06, hc6⟩ := k6.keep0 h05 hc5
    exact ⟨k4.trans (k5.toW.trans k6.toW), h06, hc6⟩
  unfold invokeSchedControlConfigureFlags at hx
  dsimp only at hx
  rw [nd_bind_one (getSchedContext_eq hk)] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  have s2 : SKa σ y2.2 := by
    refine (?_ : SKaM _) σ y2 hy2
    repeat' skm_step
  -- the bound branch: the release remove, the dequeue, `commit_time`
  have k2 : MidKW σ y2.2 ∧ y2.2.consumedTime = 0 := by
    unfold NonDet.when at hy2
    rw [if_pos (by rw [hyt]; simp)] at hy2
    obtain ⟨z1, hz1, hy2⟩ := hy2
    rw [hyt] at hz1
    rw [Set.mem_singleton_iff.1 hz1] at hy2
    obtain ⟨z2, hz2, hy2⟩ := hy2
    have kz2 := mka_tcbReleaseRemove (P := fun _ => True) _ σ trivial _ hz2
    obtain ⟨z3, hz3, hy2⟩ := hy2
    have kz3 := mka_tcbSchedAction (P := fun _ => True) _ _ z2.2 trivial _ hz3
    obtain ⟨z4, hz4, hy2⟩ := hy2
    obtain ⟨e4, hv4⟩ := rdn_gets (fun s : State Unit => s.curSc) _ z4 hz4
    rw [e4, hv4] at hy2
    dsimp only at hy2
    rw [if_pos (by rw [kz3.csc, kz2.csc, hp])] at hy2
    obtain ⟨kc, hc0⟩ := mkw_commitTime hy2
    exact ⟨(kz2.trans kz3).toW.trans kc, hc0⟩
  obtain ⟨k2, h02⟩ := k2
  dsimp only at hx
  have tail : ∀ {m : SMonad Unit Unit}, MidKWA (fun _ => True) m → SKaM m →
      ∀ σ2 x, MidKW σ σ2 → SKa σ σ2 → σ2.consumedTime = 0 → x ∈ ((m >>= fun _ => (do
        NonDet.when (y0.scTcb ≠ none) (do
          schedContextResume p
          let tcbPtr ← NonDet.assertOpt y0.scTcb
          let st ← getThreadState tcbPtr
          let ct ← NonDet.gets fun s : State Unit => s.curThread
          if tcbPtr = ct then rescheduleRequired else NonDet.when (runnable st = true) (possibleSwitchTo tcbPtr))
        setScObjRef scBadgeUpdate p badge
        setScObjRef scSporadicUpdate p (testBit flag scSporadicFlag) : SMonad Unit Unit)) σ2).1 →
      MidKW σ2 x.2 ∧ x.2.consumedTime = 0 ∧ x.2.schedulerAction = .chooseNewThread := by
    intro m hm hs σ2 x k s h0 hx
    obtain ⟨y3, hy3, hx⟩ := hx
    have k3 := hm σ2 trivial y3 hy3
    obtain ⟨r1, r2, r3⟩ := rest y3.2 x (k.trans k3) (s.trans (hs σ2 y3 hy3)) (k3.cons0 h0) hx
    exact ⟨k3.trans r1, r2, r3⟩
  obtain ⟨r1, r2, r3⟩ : MidKW y2.2 x.2 ∧ x.2.consumedTime = 0 ∧ x.2.schedulerAction = .chooseNewThread := by
    split at hx
    · exact tail (mkwa_refillNew _ _ _ _ (by decide)) (skm_refillNew _ _ _ _ (by decide)) y2.2 x k2 s2 h02 hx
    · obtain ⟨y3, hy3, hx⟩ := hx
      rw [rdo_getsThe _ _ y3 hy3] at hx
      dsimp only at hx
      split at hx
      · obtain ⟨y4, hy4, hx⟩ := hx
        rw [rdo_assertOpt _ _ y4 hy4] at hx
        obtain ⟨y5, hy5, hx⟩ := hx
        rw [RdO.ofRdN (rdn_threadGet _ _) _ y5 hy5] at hx
        dsimp only at hx
        split at hx
        · exact tail (mkwa_refillUpdate _ _ _ _ hv) (skm_refillUpdate _ _ _ _ hv) y2.2 x k2 s2 h02 hx
        · exact tail (mkwa_refillNew _ _ _ _ hv) (skm_refillNew _ _ _ _ hv) y2.2 x k2 s2 h02 hx
      · exact tail (mkwa_refillNew _ _ _ _ hv) (skm_refillNew _ _ _ _ hv) y2.2 x k2 s2 h02 hx
  exact ⟨k2.trans r1, r2, r3⟩

/-- **`MidA` after a `MidKW` step** ending with the consumed time cleared and
a reschedule pending. -/
theorem MidKW.midA {T : Set U64} {σ σ' : State Unit} (hK : MidKW σ σ') (h0 : σ'.consumedTime = 0)
    (hcn : σ'.schedulerAction = .chooseNewThread) (hC : CurInv σ) (hI : Inv σ)
    (hcT : ∃ u ∈ T, u.bv = σ.curThread) : MidA T σ' := by
  obtain ⟨xt, hkt, hsc, -⟩ := hC.tcb
  obtain ⟨y0, n0, hy0⟩ := hC.sc
  obtain ⟨xt', hkt', e1, -⟩ := hK.ctT xt hkt
  obtain ⟨y0', hy0', f1, -⟩ := hK.cscS y0 n0 hy0
  refine ⟨Or.inl hcn, fun _ => ?_, fun hpos => ?_⟩
  · obtain ⟨u, hu, hub⟩ := hcT
    obtain ⟨y1, n1, hy1, hy1t⟩ := hI.back _ xt σ.curSc hkt hsc
    rw [hy0] at hy1; cases hy1
    refine ⟨u, hu, xt', by rw [hub]; exact hkt', by rw [e1, hK.csc]; exact hsc, fun x n hx => ?_, fun hpos _ => ?_⟩
    · rw [hK.csc, hy0'] at hx; cases hx; rw [f1, hy1t, hub]
    · rw [h0] at hpos; simp at hpos
  · rw [h0] at hpos; simp at hpos

end Ops

end

end Fl4Proofs.P3.Sched
