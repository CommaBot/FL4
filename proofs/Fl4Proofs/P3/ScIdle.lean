/-
P3 (DESIGN.md §9), scheduler: **the switch-thread and idle-thread
invariant `ActIdle`**: l4v `valid_sched_action`'s switch-thread clause
(`ActSched`: the thread to switch to is schedulable) and the idle thread's
facts (`IdleOK`: bound to the idle SC, in the idle state, not released),
and their preservation by the scheduler's spec steps.

* `TKeep`: TCBs kept and SCs kept as active (`ActIdle.keep`, with a release
  queue that does not grow and no new switch target);
* the notification code's steps: `ActIdle.stable` (`NtfnStep`, `NoBlock`),
  `ActIdle.block` (a thread that is neither the switch target nor idle);
* `Calm`, `possibleSwitchTo_calm`, `possibleSwitchTo_actSched`.
-/
import Fl4Proofs.P3.ScInvR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- What `awaken` keeps: the heap and the current thread, SC, time,
consumed time, idle thread, domain and domain time. -/
def Calm (σ σ' : State Unit) : Prop :=
  σ'.kheap = σ.kheap ∧ σ'.curThread = σ.curThread ∧ σ'.curSc = σ.curSc ∧ σ'.curTime = σ.curTime ∧
    σ'.consumedTime = σ.consumedTime ∧ σ'.idleThread = σ.idleThread ∧ σ'.curDomain = σ.curDomain ∧
    σ'.domainTime = σ.domainTime

theorem Calm.refl (σ : State Unit) : Calm σ σ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Calm.trans {σ₁ σ₂ σ₃ : State Unit} (h₁ : Calm σ₁ σ₂) (h₂ : Calm σ₂ σ₃) : Calm σ₁ σ₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1,
    h₂.2.2.2.2.1.trans h₁.2.2.2.2.1, h₂.2.2.2.2.2.1.trans h₁.2.2.2.2.2.1,
    h₂.2.2.2.2.2.2.1.trans h₁.2.2.2.2.2.2.1, h₂.2.2.2.2.2.2.2.trans h₁.2.2.2.2.2.2.2⟩

theorem rescheduleRequired_calm {σ : State Unit} (hA : ActReady σ) :
    ∃ σ1, rescheduleRequired (Z := Unit) σ = ({((), σ1)}, False) ∧ QChange σ σ1 ∧ Calm σ σ1 := by
  cases ha : σ.schedulerAction with
  | switchThread t =>
    by_cases hs : schedulable t σ = true
    · obtain ⟨x, -, -, -, hk, -⟩ := schedulable_inv hs
      have he := tcbSchedAction_gen hk tcbSchedEnqueue
      exact ⟨_, rescheduleRequired_sched ha hs hA he, (qchange_enqueue hk hs).trans (qchange_action _ _),
        Calm.refl _⟩
    · exact ⟨_, rescheduleRequired_notsched ha (by simpa using hs), qchange_action _ _, Calm.refl _⟩
  | resumeCurThread =>
    exact ⟨_, rescheduleRequired_noswitch (fun t h => by rw [ha] at h; cases h), qchange_action _ _, Calm.refl _⟩
  | chooseNewThread =>
    exact ⟨_, rescheduleRequired_noswitch (fun t h => by rw [ha] at h; cases h), qchange_action _ _, Calm.refl _⟩

/-- **`possible_switch_to` of a schedulable thread keeps `Calm`.** -/
theorem possibleSwitchTo_calm {σ σ' : State Unit} (h : Inv σ) {t : ObjRef} (hs : schedulable t σ = true)
    (he : possibleSwitchTo (Z := Unit) t σ = ({((), σ')}, False)) : Calm σ σ' := by
  obtain ⟨x, -, -, -, hk, -⟩ := schedulable_inv hs
  rw [possibleSwitchTo_unfold hk] at he
  split_ifs at he
  · rw [tcbSchedAction_gen hk] at he
    rw [pair_eq he]; exact Calm.refl _
  · obtain ⟨σ1, h1, hq1, hc1⟩ := rescheduleRequired_calm h.actReady
    rw [nd_bind_one h1] at he
    have hk1 : σ1.kheap t = some (.tcb x) := by rw [hq1.1]; exact hk
    rw [tcbSchedAction_gen hk1] at he
    rw [pair_eq he]
    exact hc1.trans (Calm.refl _)
  · rw [setAction_eq] at he
    rw [pair_eq he]; exact Calm.refl _
  · rw [pair_eq he]; exact Calm.refl σ

/-- l4v `valid_sched_action`'s switch-thread clause: the thread to switch to
is schedulable. -/
def ActSched (σ : State Unit) : Prop :=
  ∀ t, σ.schedulerAction = .switchThread t → schedulable t σ = true

/-- The idle thread: bound to the idle SC, in the idle state, not released. -/
def IdleOK (σ : State Unit) : Prop :=
  ∃ x, σ.kheap σ.idleThread = some (.tcb x) ∧ x.tcbSchedContext = some idleScPtr ∧
    x.tcbState = .idleThreadState ∧ σ.idleThread ∉ σ.releaseQueue

/-- `schedulable` survives a smaller release queue on the same heap. -/
theorem schedulable_sub {σ σ' : State Unit} {t : ObjRef} (h : schedulable t σ = true)
    (hk : σ'.kheap = σ.kheap) (hsub : ∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue) : schedulable t σ' = true := by
  obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv h
  exact schedulable_of (σ := σ') (by rw [hk]; exact h1) h2 h3 (by rw [hk]; exact h4) h5 (fun hm => h6 (hsub t hm))

theorem ActSched.sub {σ σ' : State Unit} (h : ActSched σ) (hk : σ'.kheap = σ.kheap)
    (hsub : ∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue) (ha : σ'.schedulerAction = σ.schedulerAction) :
    ActSched σ' := fun t ht => schedulable_sub (h t (ha ▸ ht)) hk hsub

/-- **`possible_switch_to` of a schedulable thread keeps `ActSched`.** -/
theorem possibleSwitchTo_actSched {σ σ' : State Unit} (h : Inv σ) {t : ObjRef} (hs : schedulable t σ = true)
    (hA : ActSched σ) (he : possibleSwitchTo (Z := Unit) t σ = ({((), σ')}, False)) : ActSched σ' := by
  obtain ⟨x, -, -, -, hk, -⟩ := schedulable_inv hs
  rw [possibleSwitchTo_unfold hk] at he
  split_ifs at he
  · rw [tcbSchedAction_gen hk] at he
    rw [pair_eq he]; exact hA.sub rfl (fun _ h => h) rfl
  · obtain ⟨σ1, h1, hq1, -⟩ := rescheduleRequired_calm h.actReady
    rw [nd_bind_one h1] at he
    have hk1 : σ1.kheap t = some (.tcb x) := by rw [hq1.1]; exact hk
    rw [tcbSchedAction_gen hk1] at he
    rw [pair_eq he]
    have hc : σ1.schedulerAction = .chooseNewThread := by
      revert h1
      cases ha : σ.schedulerAction with
      | switchThread u =>
        intro h1
        by_cases hsu : schedulable u σ = true
        · obtain ⟨xu, -, -, -, hku, -⟩ := schedulable_inv hsu
          rw [rescheduleRequired_sched ha hsu h.actReady (tcbSchedAction_gen hku tcbSchedEnqueue)] at h1
          rw [pair_eq h1]
        · rw [rescheduleRequired_notsched ha (by simpa using hsu)] at h1
          rw [pair_eq h1]
      | resumeCurThread =>
        intro h1
        rw [rescheduleRequired_noswitch (fun t h => by rw [ha] at h; cases h)] at h1; rw [pair_eq h1]
      | chooseNewThread =>
        intro h1
        rw [rescheduleRequired_noswitch (fun t h => by rw [ha] at h; cases h)] at h1; rw [pair_eq h1]
    intro u hu
    simp only [setQ] at hu
    rw [hc] at hu; cases hu
  · rw [setAction_eq] at he
    rw [pair_eq he]
    intro u hu
    cases hu
    rw [schedulable_heap (σ' := { σ with schedulerAction := .switchThread t }) rfl rfl]; exact hs
  · rw [pair_eq he]; exact hA


theorem IdleOK.sub {σ σ' : State Unit} (h : IdleOK σ) (hc : Calm σ σ')
    (hsub : ∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue) : IdleOK σ' := by
  obtain ⟨hk, -, -, -, -, h5, -⟩ := hc
  obtain ⟨x, h1, h2, h3, h4⟩ := h
  exact ⟨x, by rw [hk, h5]; exact h1, h2, h3, fun hm => h4 (by rw [← h5]; exact hsub _ hm)⟩


/-- **The switch-thread and idle-thread invariant.** -/
def ActIdle (σ : State Unit) : Prop := ActSched σ ∧ IdleOK σ

/-- TCBs other than those in `E` kept, and SCs kept as active. -/
def TKeepE (E : ObjRef → Prop) (σ σ' : State Unit) : Prop :=
  (∀ p x, ¬ E p → σ.kheap p = some (.tcb x) → σ'.kheap p = some (.tcb x)) ∧
  (∀ p y n, σ.kheap p = some (.schedContext y n) → ∃ y', σ'.kheap p = some (.schedContext y' n) ∧
    scActive y' = scActive y)

/-- TCBs kept, and SCs kept as active. -/
abbrev TKeep (σ σ' : State Unit) : Prop := TKeepE (fun _ => False) σ σ'

theorem TKeepE.refl (E : ObjRef → Prop) (σ : State Unit) : TKeepE E σ σ :=
  ⟨fun _ _ _ h => h, fun _ y _ h => ⟨y, h, rfl⟩⟩

theorem TKeepE.of_kheap (E : ObjRef → Prop) {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) : TKeepE E σ σ' :=
  ⟨fun _ _ _ hp => by rw [h]; exact hp, fun _ y _ hp => ⟨y, by rw [h]; exact hp, rfl⟩⟩

theorem TKeepE.trans {E : ObjRef → Prop} {σ₁ σ₂ σ₃ : State Unit} (h₁ : TKeepE E σ₁ σ₂) (h₂ : TKeepE E σ₂ σ₃) :
    TKeepE E σ₁ σ₃ :=
  ⟨fun p x hp hx => h₂.1 p x hp (h₁.1 p x hp hx), fun p y n hy => by
    obtain ⟨y1, h1, e1⟩ := h₁.2 p y n hy
    obtain ⟨y2, h2, e2⟩ := h₂.2 p y1 n h1
    exact ⟨y2, h2, e2.trans e1⟩⟩

theorem TKeepE.congr {E : ObjRef → Prop} {σ σ1 σ2 : State Unit} (h : TKeepE E σ σ1) (hk : σ2.kheap = σ1.kheap) :
    TKeepE E σ σ2 := h.trans (TKeepE.of_kheap E hk)

theorem TKeepE.mono {E E' : ObjRef → Prop} {σ σ' : State Unit} (h : TKeepE E σ σ') (hE : ∀ p, E p → E' p) :
    TKeepE E' σ σ' := ⟨fun p x hp hx => h.1 p x (fun e => hp (hE p e)) hx, h.2⟩

/-- An SC replaced by one as active. -/
theorem TKeepE.updSc (E : ObjRef → Prop) {σ : State Unit} {p : ObjRef} {y z : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (hz : scActive z = scActive y) :
    TKeepE E σ (updK σ p (.schedContext z n)) := by
  refine ⟨fun q x _ hx => ?_, fun q w m hw => ?_⟩
  · have : q ≠ p := by rintro rfl; rw [hk] at hx; cases hx
    simp [updK, this, hx]
  · by_cases e : q = p
    · subst e; rw [hk] at hw; cases hw; exact ⟨z, by simp [updK], hz⟩
    · exact ⟨w, by simp [updK, e, hw], rfl⟩

/-- A TCB of `E` replaced. -/
theorem TKeepE.updTcb {E : ObjRef → Prop} {σ : State Unit} {p : ObjRef} {x : Tcb}
    (hk : σ.kheap p = some (.tcb x)) (hp : E p) (x' : Tcb) : TKeepE E σ (updK σ p (.tcb x')) := by
  refine ⟨fun q w hq hw => ?_, fun q w m hw => ?_⟩
  · have : q ≠ p := by rintro rfl; exact hq hp
    simp [updK, this, hw]
  · have : q ≠ p := by rintro rfl; rw [hk] at hw; cases hw
    exact ⟨w, by simp [updK, this, hw], rfl⟩

theorem schedulable_keep {E : ObjRef → Prop} {σ σ' : State Unit} {t : ObjRef} (h : schedulable t σ = true)
    (hk : TKeepE E σ σ') (ht : ¬ E t) (hr : t ∈ σ'.releaseQueue → t ∈ σ.releaseQueue) :
    schedulable t σ' = true := by
  obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv h
  obtain ⟨y', h4', e⟩ := hk.2 scp y n h4
  exact schedulable_of (σ := σ') (hk.1 t x ht h1) h2 h3 h4' (e.trans h5) (fun hm => h6 (hr hm))

/-- **`ActIdle` under `TKeepE`**: TCBs other than those of `E` kept (none of
them the idle thread or the switch target), SCs kept as active, the release
queue grown at most by members of `E`, and no new switch target. -/
theorem ActIdle.keepE {E : ObjRef → Prop} {σ σ' : State Unit} (h : ActIdle σ) (hk : TKeepE E σ σ')
    (hr : ∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue ∨ E u)
    (ha : σ'.schedulerAction = σ.schedulerAction ∨ ∀ t, σ'.schedulerAction ≠ .switchThread t)
    (hid : σ'.idleThread = σ.idleThread) (hEa : ∀ t, σ.schedulerAction = .switchThread t → ¬ E t)
    (hEi : ¬ E σ.idleThread) : ActIdle σ' := by
  obtain ⟨hA, x, h1, h2, h3, h4⟩ := h
  refine ⟨fun t ht => ?_, x, by rw [hid]; exact hk.1 _ x hEi h1, h2, h3, fun hm => ?_⟩
  · rcases ha with e | e
    · rw [e] at ht
      exact schedulable_keep (hA t ht) hk (hEa t ht) fun hm => (hr t hm).resolve_right (hEa t ht)
    · exact absurd ht (e t)
  · rw [hid] at hm
    rcases hr _ hm with hm | hm
    · exact h4 hm
    · exact hEi hm

/-- **`ActIdle` under `TKeep`.** -/
theorem ActIdle.keep {σ σ' : State Unit} (h : ActIdle σ) (hk : TKeep σ σ')
    (hr : ∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue)
    (ha : σ'.schedulerAction = σ.schedulerAction ∨ ∀ t, σ'.schedulerAction ≠ .switchThread t)
    (hid : σ'.idleThread = σ.idleThread) : ActIdle σ' :=
  h.keepE hk (fun u hu => Or.inl (hr u hu)) ha hid (fun _ _ h => h) (fun h => h)

theorem ActIdle.calm {σ σ' : State Unit} (h : ActIdle σ) (hc : Calm σ σ')
    (hr : ∀ u ∈ σ'.releaseQueue, u ∈ σ.releaseQueue)
    (ha : σ'.schedulerAction = σ.schedulerAction ∨ ∀ t, σ'.schedulerAction ≠ .switchThread t) : ActIdle σ' :=
  h.keep (TKeepE.of_kheap _ hc.1) hr ha hc.2.2.2.2.2.1

/-! ## The notification code's steps -/

/-- **A notification step that blocks no thread keeps `ActIdle`.** -/
theorem ActIdle.stable {σ σ' : State Unit} (h : ActIdle σ) (hn : NtfnStep σ σ') (hb : NoBlock σ σ') :
    ActIdle σ' := by
  obtain ⟨-, e2, -, e4, -, -, -, -, -⟩ := NtfnStep.abs hn
  obtain ⟨hA, xi, hi1, hi2, hi3, hi4⟩ := h
  have eid := NtfnStep.idleThread hn
  refine ⟨fun t ht => ?_, ?_⟩
  · rw [e4] at ht
    obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv (hA t ht)
    obtain ⟨x', hk', -, hsc', -⟩ := NtfnStep.tcbSched hn h1
    refine schedulable_of (σ := σ') hk' (hsc'.trans h2) ?_ (NtfnStep.sc hn h4) h5 (by rw [e2]; exact h6)
    rcases hb t x x' h1 hk' with e | ⟨hr, -⟩
    · rw [e]; exact h3
    · exact hr
  · obtain ⟨x', hk', -, hsc', -⟩ := NtfnStep.tcbSched hn hi1
    refine ⟨x', by rw [eid]; exact hk', hsc'.trans hi2, ?_, by rw [eid, e2]; exact hi4⟩
    rcases hb _ xi x' hi1 hk' with e | ⟨-, hne, -⟩
    · rw [e]; exact hi3
    · exact absurd hi3 hne

/-- **Blocking a thread that is neither the switch target nor idle keeps
`ActIdle`.** -/
theorem ActIdle.block {σ σ' : State Unit} {t : ObjRef} (h : ActIdle σ) (hn : NtfnStep σ σ')
    (hoth : ∀ p x y, σ.kheap p = some (.tcb x) → σ'.kheap p = some (.tcb y) → p ≠ t → y.tcbState = x.tcbState)
    (hta : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t) (hti : t ≠ σ.idleThread) : ActIdle σ' := by
  obtain ⟨-, e2, -, e4, -, -, -, -, -⟩ := NtfnStep.abs hn
  obtain ⟨hA, xi, hi1, hi2, hi3, hi4⟩ := h
  have eid := NtfnStep.idleThread hn
  refine ⟨fun u hu => ?_, ?_⟩
  · rw [e4] at hu
    obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv (hA u hu)
    obtain ⟨x', hk', -, hsc', -⟩ := NtfnStep.tcbSched hn h1
    exact schedulable_of (σ := σ') hk' (hsc'.trans h2) (by rw [hoth u x x' h1 hk' (hta u hu)]; exact h3)
      (NtfnStep.sc hn h4) h5 (by rw [e2]; exact h6)
  · obtain ⟨x', hk', -, hsc', -⟩ := NtfnStep.tcbSched hn hi1
    exact ⟨x', by rw [eid]; exact hk', hsc'.trans hi2, by rw [hoth _ xi x' hi1 hk' (Ne.symm hti)]; exact hi3,
      by rw [eid, e2]; exact hi4⟩

theorem ActIdle.ofSts {σ : State Unit} (h : ActIdle σ) (t : ObjRef) : ActIdle (stsAct σ t) := by
  unfold stsAct; split_ifs
  · exact h.keep (TKeepE.of_kheap _ rfl) (fun _ hu => hu) (Or.inr fun _ e => by cases e) rfl
  · exact h

/-- **`possible_switch_to` of a schedulable thread keeps `ActIdle`.** -/
theorem ActIdle.possibleSwitchTo {σ σ' : State Unit} (h : ActIdle σ) (hI : Inv σ) {t : ObjRef}
    (hs : schedulable t σ = true) (he : possibleSwitchTo (Z := Unit) t σ = ({((), σ')}, False)) : ActIdle σ' := by
  have hq := possibleSwitchTo_qchange hI hs he
  have hc := possibleSwitchTo_calm hI hs he
  obtain ⟨x, h1, h2, h3, h4⟩ := h.2
  exact ⟨possibleSwitchTo_actSched hI hs h.1 he, x, by rw [hc.2.2.2.2.2.1, hc.1]; exact h1, h2, h3,
    by rw [hc.2.2.2.2.2.1, hq.2.1]; exact h4⟩

/-- **`refill_unblock_check` keeps `ActIdle`.** -/
theorem ActIdle.unblock {σ σ' : State Unit} (h : ActIdle σ) {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills ≠ [])
    {r : Unit} (hm : (r, σ') ∈ (refillUnblockCheck (Z := Unit) p σ).1) : ActIdle σ' := by
  rcases unblock_result hk hne hm with ⟨rfl, -⟩ | ⟨z, rfl, -, -, hzy, -⟩
  · exact h
  · exact h.keep (TKeepE.updSc _ (σ := { σ with reprogramTimer := true }) hk (by rw [hzy]))
      (fun _ hu => hu) (Or.inl rfl) rfl


/-- **The sporadic check after a wake-up keeps `ActIdle`.** -/
theorem ActIdle.unblockTail {σ σ' : State Unit} (h : ActIdle σ) (hI : Inv σ) {t : ObjRef} {x : Tcb}
    (hkt : σ.kheap t = some (.tcb x))
    (hsa : ∀ p y n, x.tcbSchedContext = some p → σ.kheap p = some (.schedContext y n) → y.scSporadic = true →
      scActive y = true)
    (hm : ((), σ') ∈ (specUnblock t σ).1) : ActIdle σ' := by
  unfold specUnblock getTcbObjRef at hm
  rw [nd_bind_one (threadGet_eq _ hkt)] at hm
  cases hsc : x.tcbSchedContext with
  | none =>
    rw [hsc, ifSporadic_none, Set.mem_singleton_iff] at hm; cases hm; exact h
  | some p =>
    rw [hsc] at hm
    obtain ⟨y, n, hkp, -⟩ := hI.back t x p hkt hsc
    rw [ifSporadic_some hkp] at hm
    split_ifs at hm with hg
    · exact h.unblock hkp (hI.ne p y n hkp (hsa p y n hsc hkp hg.1)) hm
    · rw [Set.mem_singleton_iff] at hm; cases hm; exact h

/-- **The sporadic check after `complete_signal`'s donation keeps
`ActIdle`.** -/
theorem ActIdle.completeCheck {σ σ' : State Unit} (h : ActIdle σ) (hI : Inv σ) {t m : ObjRef} {x : Tcb}
    {xn : Notification} (hkt : σ.kheap t = some (.tcb x)) (hkn : σ.kheap m = some (.notification xn))
    (hsa : ∀ p y n, x.tcbSchedContext = some p → σ.kheap p = some (.schedContext y n) → y.scSporadic = true →
      scActive y = true)
    (hm : ((), σ') ∈ (specCompleteCheck t m σ).1) : ActIdle σ' := by
  unfold specCompleteCheck getTcbObjRef at hm
  rw [nd_bind_one (threadGet_eq _ hkt)] at hm
  cases hsc : x.tcbSchedContext with
  | none =>
    rw [hsc] at hm; simp only [NonDet.maybeM] at hm
    rw [mem_pure hm]; exact h
  | some p =>
    rw [hsc] at hm
    obtain ⟨y, n, hkp, -⟩ := hI.back t x p hkt hsc
    simp only [NonDet.maybeM] at hm
    rw [nd_bind_one (getSchedContext_eq hkp)] at hm
    simp only [NonDet.when] at hm
    split_ifs at hm with hg
    · rw [nd_bind_one (getNtfnSc_eq hkn), nd_gets_bind] at hm
      split_ifs at hm
      · exact h.unblock hkp (hI.ne p y n hkp (hsa p y n hsc hkp hg)) hm
      · rw [mem_pure hm]; exact h
    · rw [mem_pure hm]; exact h

/-- **`maybe_donate_sc` keeps `ActIdle`**, for a runnable thread in no
queue: a donation goes to a thread with no SC, which is neither the switch
target nor idle; it may be postponed. -/
theorem ActIdle.donate {σ σ' : State Unit} (h : ActIdle σ) (hI : Inv σ) {t n : ObjRef} {xt : Tcb}
    {xn : Notification} (hkt : σ.kheap t = some (.tcb xt)) (hkn : σ.kheap n = some (.notification xn))
    (hnq : NotQueued σ t) (he : maybeDonateSc (Z := Unit) t n σ = ({((), σ')}, False)) : ActIdle σ' := by
  unfold maybeDonateSc getTcbObjRef at he
  rw [nd_bind_one (threadGet_eq _ hkt)] at he
  simp only [NonDet.when] at he
  split_ifs at he with h0
  swap
  · rw [pair_eq he]; exact h
  rw [nd_bind_one' (getNtfnSc_eq hkn)] at he
  cases hsc : xn.ntfnSc with
  | none => rw [hsc] at he; rw [pair_eq he]; exact h
  | some p =>
    rw [hsc] at he
    obtain ⟨ys, ns, hks⟩ := hI.ntfnSc n xn p hkn hsc
    have hpt : p ≠ t := by rintro rfl; rw [hkt] at hks; cases hks
    simp only [NonDet.maybeM] at he
    have hg : getScObjRef (Z := Unit) SchedContext.scTcb p σ = ({(ys.scTcb, σ)}, False) := by
      unfold getScObjRef; rw [nd_bind_one (getSchedContext_eq hks)]; rfl
    rw [nd_bind_one hg] at he
    cases hst : ys.scTcb with
    | some u => rw [hst] at he; simp only [reduceCtorEq, ↓reduceIte] at he; rw [pair_eq he]; exact h
    | none =>
      rw [hst] at he
      simp only [↓reduceIte] at he
      rw [nd_bind_one (schedContextDonate_eq hks hst hkt hpt)] at he
      have hb := hI.donated hks hst hkt hpt hnq
      set σd := donSt σ p t ys ns xt
      set xt' : Tcb := { xt with tcbSchedContext := some p }
      set ys' : SchedContext := { ys with scTcb := some t }
      have kt : σd.kheap t = some (.tcb xt') := by simp [σd, donSt, updK] <;> rfl
      have kp : σd.kheap p = some (.schedContext ys' ns) := by simp [σd, donSt, updK, hpt] <;> rfl
      have hne : scActive ys' = true → ys'.scRefills ≠ [] := hI.ne p ys ns hks
      have hnr : t ∉ σd.releaseQueue := hnq.2
      -- `t` has no SC, so it is neither the switch target nor idle
      have hEa : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t := by
        rintro u hu rfl
        obtain ⟨x, scp, -, -, h1, h2, -⟩ := schedulable_inv (h.1 _ hu)
        rw [hkt] at h1; cases h1; rw [h0] at h2; cases h2
      have hEi : σ.idleThread ≠ t := by
        rintro e
        obtain ⟨x, h1, h2, -⟩ := h.2
        rw [e, hkt] at h1; cases h1; rw [h0] at h2; cases h2
      have hk : TKeepE (· = t) σ σd :=
        (TKeepE.updSc (· = t) hks (z := ys') rfl).trans (TKeepE.updTcb (E := (· = t)) (x := xt) (by simp [updK, Ne.symm hpt, hkt]) rfl xt')
      have hd : ActIdle σd := h.keepE hk (fun u hu => Or.inl hu) (Or.inl rfl) rfl
        (fun u hu e => hEa u hu e) hEi
      rw [resume_spec_eq kp rfl kt hne
        (fun hs => by
          obtain ⟨x, scp, y, m, h1, h2, h3, h4, h5, -⟩ := schedulable_inv hs
          rw [kt] at h1; cases h1; cases h2; rw [kp] at h4; cases h4; exact ⟨h3, h5⟩)
        (fun _ => hnq.1 _ _)] at he
      split_ifs at he with hc
      · have hact : scActive ys' = true := by
          obtain ⟨x, scp, y, m, h1, h2, -, h4, h5, -⟩ := schedulable_inv hc.1
          rw [kt] at h1; cases h1; cases h2; rw [kp] at h4; cases h4; exact h5
        obtain ⟨b, hp⟩ := postpone_eq kp rfl kt (specRt σd) (fun u hu => by
          rcases hu with rfl | hu
          · exact ⟨xt', p, ys', ns, kt, rfl, kp, hne hact, specRt_eq kt rfl kp (hne hact)⟩
          · obtain ⟨xu, scp, yu, nu, h1, h2, -, h4, h5⟩ := hb.rel u hu
            exact ⟨xu, scp, yu, nu, h1, h2, h4, hb.ne _ _ _ h4 h5, specRt_eq h1 h2 h4 (hb.ne _ _ _ h4 h5)⟩)
        rw [hp] at he
        rw [pair_eq he]
        exact hd.keepE (E := (· = t)) (TKeepE.of_kheap _ rfl)
          (fun u hu => by
            have := mem_specInsT.1 hu
            rcases this with e | e
            · exact Or.inr e
            · exact Or.inl e) (Or.inl rfl) rfl (fun u hu e => hEa u hu e) hEi
      · rw [pair_eq he]; exact hd

/-- **`maybe_return_sc` keeps `ActIdle`**, for a thread that is not runnable
and not idle. -/
theorem ActIdle.ret {σ σ' : State Unit} (h : ActIdle σ) (hI : Inv σ) {n t : ObjRef} {xt : Tcb}
    {xn : Notification} (hkt : σ.kheap t = some (.tcb xt)) (hkn : σ.kheap n = some (.notification xn))
    (hnr : runnable xt.tcbState = false) (hti : t ≠ σ.idleThread)
    (he : ((), σ') ∈ (maybeReturnSc (Z := Unit) n t σ).1) : ActIdle σ' := by
  have hnq := hI.notQueued hkt hnr
  unfold maybeReturnSc getTcbObjRef at he
  rw [nd_bind_one (getNtfnSc_eq hkn), nd_bind_one (threadGet_eq _ hkt)] at he
  simp only [NonDet.when] at he
  split_ifs at he with hc
  swap
  · rw [mem_pure he]; exact h
  obtain ⟨e1, e2⟩ := hc
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 e2
  rw [hp] at he
  have hsc : xt.tcbSchedContext = some p := e1 ▸ hp
  obtain ⟨ys, ns, hks, -⟩ := hI.back t xt p hkt hsc
  have hpt : p ≠ t := by rintro rfl; rw [hkt] at hks; cases hks
  rw [nd_bind_one (show NonDet.assertOpt (σ := State Unit) (some p) σ = ({(p, σ)}, False) from rfl),
    nd_bind_one (threadSet_eq _ hkt)] at he
  have hks1 : (updK σ t (.tcb (tcbSchedContextUpdate (fun _ => none) xt))).kheap p =
      some (.schedContext ys ns) := by simp [updK, hpt, hks]
  change ((), σ') ∈ ((updateSchedContext p _ >>= _) _).1 at he
  rw [nd_bind_one (updateSchedContext_eq hks1 _), nd_gets_bind] at he
  have hI1 := hI.unbound hkt hsc hks hnq
  have e3 : (updSc (updK σ t (.tcb (tcbSchedContextUpdate (fun _ => none) xt))) p
      (scTcbUpdate (fun _ => none) ys) ns) =
      updSc (updK σ t (.tcb { xt with tcbSchedContext := none })) p { ys with scTcb := none } ns := rfl
  rw [e3] at he
  -- `t` is not runnable, so not the switch target
  have hEa : ∀ u, σ.schedulerAction = .switchThread u → u ≠ t := by
    rintro u hu rfl
    obtain ⟨x, -, -, -, h1, -, h3, -⟩ := schedulable_inv (h.1 _ hu)
    rw [hkt] at h1; cases h1; rw [hnr] at h3; cases h3
  set σu := updSc (updK σ t (.tcb { xt with tcbSchedContext := none })) p { ys with scTcb := none } ns
  have hk : TKeepE (· = t) σ σu :=
    (TKeepE.updTcb (E := (· = t)) hkt rfl _).trans (TKeepE.updSc (· = t) hks1 (z := { ys with scTcb := none }) rfl)
  have hu : ActIdle σu := h.keepE hk (fun u hu => Or.inl hu) (Or.inl rfl) rfl (fun u hu e => hEa u hu e)
    (fun e => hti e.symm)
  split_ifs at he
  · obtain ⟨σ3, h3, hq3, hc3⟩ := rescheduleRequired_calm hI1.actReady
    rw [h3, Set.mem_singleton_iff] at he; cases he
    have ha3 : σ'.schedulerAction = .chooseNewThread := by
      revert h3
      cases ha : σu.schedulerAction with
      | switchThread u =>
        intro h3
        by_cases hsu : schedulable u σu = true
        · obtain ⟨xu, -, -, -, hku, -⟩ := schedulable_inv hsu
          rw [rescheduleRequired_sched ha hsu hI1.actReady (tcbSchedAction_gen hku tcbSchedEnqueue)] at h3
          rw [pair_eq h3]
        · rw [rescheduleRequired_notsched ha (by simpa using hsu)] at h3
          rw [pair_eq h3]
      | resumeCurThread =>
        intro h3
        rw [rescheduleRequired_noswitch (fun t h => by rw [ha] at h; cases h)] at h3; rw [pair_eq h3]
      | chooseNewThread =>
        intro h3
        rw [rescheduleRequired_noswitch (fun t h => by rw [ha] at h; cases h)] at h3; rw [pair_eq h3]
    exact hu.calm hc3 (fun u h => by rw [hq3.2.1] at h; exact h) (Or.inr fun t e => by rw [ha3] at e; cases e)
  · rw [mem_pure he]; exact hu


/-- `IdleOK` when the idle TCB is kept and the idle thread is not released. -/
theorem IdleOK.of {σ σ' : State Unit} (h : IdleOK σ) (hid : σ'.idleThread = σ.idleThread)
    (hk : σ'.kheap σ.idleThread = σ.kheap σ.idleThread)
    (hr : σ.idleThread ∈ σ'.releaseQueue → σ.idleThread ∈ σ.releaseQueue) : IdleOK σ' := by
  obtain ⟨x, h1, h2, h3, h4⟩ := h
  exact ⟨x, by rw [hid, hk]; exact h1, h2, h3, fun hm => h4 (hr (hid ▸ hm))⟩

/-- The idle thread is not schedulable. -/
theorem IdleOK.not_sched {σ : State Unit} (h : IdleOK σ) : schedulable σ.idleThread σ = false := by
  obtain ⟨x, h1, -, h3, -⟩ := h
  by_contra hne
  obtain ⟨x', -, -, -, hk', -, hr', -⟩ := schedulable_inv (by simpa using hne)
  rw [h1] at hk'; cases hk'
  rw [h3] at hr'; cases hr'

theorem IdleOK.ne_of_sched {σ : State Unit} (h : IdleOK σ) {t : ObjRef} (hs : schedulable t σ = true) :
    t ≠ σ.idleThread := by
  rintro rfl; rw [h.not_sched] at hs; cases hs

/-- `ActIdle` when the action becomes `choose_new_thread` (or another
non-switch action) and `IdleOK` holds. -/
theorem ActIdle.of_noswitch {σ : State Unit} (h : IdleOK σ) (ha : ∀ t, σ.schedulerAction ≠ .switchThread t) :
    ActIdle σ := ⟨fun t ht => absurd ht (ha t), h⟩


/-- **A runnable thread's state set to a runnable state keeps `ActIdle`.** -/
theorem ActIdle.updState {σ : State Unit} (h : ActIdle σ) {p : ObjRef} {x : Tcb}
    (hk : σ.kheap p = some (.tcb x)) (hr0 : runnable x.tcbState = true) (ts : ThreadState)
    (hrun : runnable ts = true) : ActIdle (updK σ p (.tcb { x with tcbState := ts })) := by
  have hpi : p ≠ σ.idleThread := by
    rintro rfl; obtain ⟨xi, h1, -, h3, -⟩ := h.2; rw [hk] at h1; cases h1; rw [h3] at hr0; cases hr0
  refine ⟨fun u hu => ?_, ?_⟩
  · obtain ⟨xu, scp, y, n, h1, h2, h3, h4, h5, h6⟩ := schedulable_inv (h.1 u hu)
    have hscp : scp ≠ p := by rintro rfl; rw [hk] at h4; cases h4
    by_cases e : u = p
    · rw [e] at h1 h6 ⊢; rw [hk] at h1
      have ex : xu = x := by cases h1; rfl
      rw [ex] at h2
      exact schedulable_of (σ := updK σ p (.tcb { x with tcbState := ts })) (x := { x with tcbState := ts })
        (y := y) (n := n) (by simp [updK]) h2 hrun (by simp [updK, hscp, h4]) h5 h6
    · exact schedulable_of (σ := updK σ p (.tcb { x with tcbState := ts })) (x := xu) (y := y) (n := n)
        (by simp [updK, e, h1]) h2 h3 (by simp [updK, hscp, h4]) h5 h6
  · obtain ⟨xi, h1, h2, h3, h4⟩ := h.2
    exact ⟨xi, by simp [updK, Ne.symm hpi, h1], h2, h3, h4⟩


end Spec

end

end Fl4Proofs.P3.Sched
