/-
P3 (DESIGN.md §9), CSpace: **the spec's finalisation of a final
notification cap has an outcome** (`finNtfn_out`, `specFinOut_ntfn`: the
Notification case of `SpecFinOut`), from `NtfnPre`: the notification and
its bound TCB and SC exist, its queue is a duplicate-free list of TCBs whose
SCs are ready and sufficient (l4v's `released_ipc_queues`), the SCs are
bound back (`ScBack`, part of the Sc side's `Inv`) and refill-valid when
active and periodic (`Inv.refills`), and `ActReady` (the refill part of l4v's
`valid_sched_action`).

The scheduler steps are the Sc side's (`rescheduleRequired_some`,
`possibleSwitchTo_some`, `refillUnblockCheck_some`, `unblock_result`);
`ActReady` is kept along the loop of `cancel_all_signals`: a restarted
thread that becomes the switch target is ready and sufficient (`RdyAt`).
-/
import Fl4Proofs.P3.ScSchedOut
import Fl4Proofs.P3.ScBindSpec
import Fl4Proofs.P3.DelObjK
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- Thread `u` has an SC with a ready and sufficient head refill. -/
def RdyAt (σ : State Unit) (u : ObjRef) : Prop :=
  ∃ x c y k, σ.kheap u = some (.tcb x) ∧ x.tcbSchedContext = some c ∧ σ.kheap c = some (.schedContext y k) ∧
    y.scRefills ≠ [] ∧ refillReady σ.curTime (refillHd y) = true ∧ refillSufficient 0 (refillHd y) = true

theorem actReady_iff {σ : State Unit} :
    ActReady σ ↔ ∀ u, σ.schedulerAction = .switchThread u → schedulable u σ = true → RdyAt σ u := by
  constructor
  · intro h u hu hs
    obtain ⟨x, c, hk, hc, h1, h2⟩ := h u hu hs
    obtain ⟨y, k, hky, hne, hsuff⟩ := suff_inv h1
    exact ⟨x, c, y, k, hk, hc, hky, hne, ready_inv h2 hky hne, hsuff⟩
  · intro h u hu hs
    obtain ⟨x, c, y, k, hk, hc, hky, hne, hr, hsf⟩ := h u hu hs
    exact ⟨x, c, hk, hc, by rw [getScRefillSufficient_eq hky hne, hsf], by rw [getScRefillReady_eq hky hne, hr]⟩

/-- Every TCB's SC exists, with refills, bound back to it. -/
def ScBack (σ : State Unit) : Prop :=
  ∀ u xu c, σ.kheap u = some (.tcb xu) → xu.tcbSchedContext = some c →
    ∃ y k, σ.kheap c = some (.schedContext y k) ∧ y.scTcb = some u ∧ y.scRefills ≠ []

/-- The scheduling-relevant parts kept: every TCB with its state's
runnability and SC; every SC with its size, refills, refill maximum and
TCB; no new TCB or SC; the time and the release queue. -/
structure SFr (σ σ' : State Unit) : Prop where
  tcb : ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧
    runnable y.tcbState = runnable x.tcbState ∧ y.tcbSchedContext = x.tcbSchedContext
  tcb' : ∀ p y, σ'.kheap p = some (.tcb y) → ∃ x, σ.kheap p = some (.tcb x)
  sc : ∀ p y n, σ.kheap p = some (.schedContext y n) → ∃ y', σ'.kheap p = some (.schedContext y' n) ∧
    y'.scRefills = y.scRefills ∧ y'.scRefillMax = y.scRefillMax ∧ y'.scTcb = y.scTcb ∧ y'.scPeriod = y.scPeriod
  sc' : ∀ p y n, σ'.kheap p = some (.schedContext y n) → ∃ y0, σ.kheap p = some (.schedContext y0 n)
  tm : σ'.curTime = σ.curTime
  rq : σ'.releaseQueue = σ.releaseQueue

theorem SFr.schedulable {σ σ' : State Unit} (h : SFr σ σ') (u : ObjRef) :
    schedulable u σ' = schedulable u σ := by
  have ht : (tcbsOf σ' u).map (fun z => (runnable z.tcbState, z.tcbSchedContext)) =
      (tcbsOf σ u).map (fun z => (runnable z.tcbState, z.tcbSchedContext)) := by
    rw [tcbsOf_eq, tcbsOf_eq]
    cases hk : σ.kheap u with
    | some o =>
      cases o with
      | tcb x => obtain ⟨y, hy, e1, e2⟩ := h.tcb u x hk; rw [hy]; simp [e1, e2]
      | _ =>
        cases hk' : σ'.kheap u with
        | none => rfl
        | some o' => cases o' with
          | tcb y => obtain ⟨x, hx⟩ := h.tcb' u y hk'; rw [hk] at hx; cases hx
          | _ => rfl
    | none =>
      cases hk' : σ'.kheap u with
      | none => rfl
      | some o' => cases o' with
        | tcb y => obtain ⟨x, hx⟩ := h.tcb' u y hk'; rw [hk] at hx; cases hx
        | _ => rfl
  have hs : ∀ p, Option.map scActive (scsOf σ' p) = Option.map scActive (scsOf σ p) := by
    intro p
    rw [scsOf_eq, scsOf_eq]
    cases hk : σ.kheap p with
    | some o =>
      cases o with
      | schedContext y n => obtain ⟨y', hy, -, e2, -, -⟩ := h.sc p y n hk; rw [hy]; simp [scActive, e2]
      | _ =>
        cases hk' : σ'.kheap p with
        | none => rfl
        | some o' => cases o' with
          | schedContext y n => obtain ⟨y0, hx⟩ := h.sc' p y n hk'; rw [hk] at hx; cases hx
          | _ => rfl
    | none =>
      cases hk' : σ'.kheap p with
      | none => rfl
      | some o' => cases o' with
        | schedContext y n => obtain ⟨y0, hx⟩ := h.sc' p y n hk'; rw [hk] at hx; cases hx
        | _ => rfl
  exact schedulable_upd ht hs h.rq

theorem SFr.rdyAt {σ σ' : State Unit} (h : SFr σ σ') {u : ObjRef} (hr : RdyAt σ u) : RdyAt σ' u := by
  obtain ⟨x, c, y, k, hk, hc, hky, hne, h1, h2⟩ := hr
  obtain ⟨x', hx', -, hsc⟩ := h.tcb u x hk
  obtain ⟨y', hy', e1, -, -, -⟩ := h.sc c y k hky
  refine ⟨x', c, y', k, hx', by rw [hsc, hc], hy', by rw [e1]; exact hne, ?_, ?_⟩
  · rw [h.tm, show refillHd y' = refillHd y by simp [refillHd, e1]]; exact h1
  · rw [show refillHd y' = refillHd y by simp [refillHd, e1]]; exact h2

/-- **`ActReady` across an `SFr` step** with the scheduler action kept or
made `choose_new_thread`. -/
theorem SFr.actReady {σ σ' : State Unit} (h : SFr σ σ') (hA : ActReady σ)
    (hact : σ'.schedulerAction = σ.schedulerAction ∨ σ'.schedulerAction = .chooseNewThread) : ActReady σ' := by
  rw [actReady_iff] at hA ⊢
  intro u hu hs
  have hu' : σ.schedulerAction = .switchThread u := by
    rcases hact with e | e
    · rw [← e]; exact hu
    · rw [e] at hu; cases hu
  exact h.rdyAt (hA u hu' (by rw [← h.schedulable]; exact hs))

theorem SFr.refl (σ : State Unit) : SFr σ σ :=
  ⟨fun _ x h => ⟨x, h, rfl, rfl⟩, fun _ y h => ⟨y, h⟩, fun _ y _ h => ⟨y, h, rfl, rfl, rfl, rfl⟩,
    fun _ y _ h => ⟨y, h⟩, rfl, rfl⟩

theorem SFr.trans {σ1 σ2 σ3 : State Unit} (h1 : SFr σ1 σ2) (h2 : SFr σ2 σ3) : SFr σ1 σ3 := by
  refine ⟨fun p x hx => ?_, fun p y hy => ?_, fun p y n hy => ?_, fun p y n hy => ?_, h2.tm.trans h1.tm,
    h2.rq.trans h1.rq⟩
  · obtain ⟨y, hy, e1, e2⟩ := h1.tcb p x hx
    obtain ⟨z, hz, f1, f2⟩ := h2.tcb p y hy
    exact ⟨z, hz, f1.trans e1, f2.trans e2⟩
  · obtain ⟨x, hx⟩ := h2.tcb' p y hy; exact h1.tcb' p x hx
  · obtain ⟨y', hy', e1, e2, e3, e4⟩ := h1.sc p y n hy
    obtain ⟨z, hz, f1, f2, f3, f4⟩ := h2.sc p y' n hy'
    exact ⟨z, hz, f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4⟩
  · obtain ⟨y0, hy0⟩ := h2.sc' p y n hy; exact h1.sc' p y0 n hy0

theorem SFr.scBack {σ σ' : State Unit} (h : SFr σ σ') (hB : ScBack σ) : ScBack σ' := by
  intro u xu c hk hc
  obtain ⟨x0, hx0⟩ := h.tcb' u xu hk
  obtain ⟨y1, hy1, -, hsc⟩ := h.tcb u x0 hx0
  rw [hk] at hy1; cases hy1
  obtain ⟨y, k, hky, hyt, hne⟩ := hB u x0 c hx0 (by rw [← hsc, hc])
  obtain ⟨y', hy', e1, -, e3, -⟩ := h.sc c y k hky
  exact ⟨y', k, hy', by rw [e3, hyt], by rw [e1]; exact hne⟩

/-- An update of an object that is neither a TCB nor an SC, to another such. -/
theorem SFr.updOther {σ : State Unit} {p : ObjRef} {o o' : KernelObject} (hk : σ.kheap p = some o)
    (h1 : ∀ x, o ≠ .tcb x) (h2 : ∀ y n, o ≠ .schedContext y n) (h1' : ∀ x, o' ≠ .tcb x)
    (h2' : ∀ y n, o' ≠ .schedContext y n) : SFr σ (updK σ p o') := by
  refine ⟨fun q x hq => ?_, fun q y hq => ?_, fun q y n hq => ?_, fun q y n hq => ?_, rfl, rfl⟩
  · have hne : q ≠ p := by rintro rfl; rw [hk] at hq; exact h1 x (Option.some.inj hq)
    exact ⟨x, by simp only [updK, Function.update_of_ne hne]; exact hq, rfl, rfl⟩
  · by_cases e : q = p
    · subst e; simp only [updK, Function.update_self, Option.some.injEq] at hq; exact absurd hq (h1' y)
    · exact ⟨y, by simp only [updK, Function.update_of_ne e] at hq; exact hq⟩
  · have hne : q ≠ p := by rintro rfl; rw [hk] at hq; exact h2 y n (Option.some.inj hq)
    exact ⟨y, by simp only [updK, Function.update_of_ne hne]; exact hq, rfl, rfl, rfl, rfl⟩
  · by_cases e : q = p
    · subst e; simp only [updK, Function.update_self, Option.some.injEq] at hq; exact absurd hq (h2' y n)
    · exact ⟨y, by simp only [updK, Function.update_of_ne e] at hq; exact hq⟩

/-- A TCB update keeping its state's runnability and its SC. -/
theorem SFr.updTcb {σ : State Unit} {p : ObjRef} {x y : Tcb} (hk : σ.kheap p = some (.tcb x))
    (hst : runnable y.tcbState = runnable x.tcbState) (hsc : y.tcbSchedContext = x.tcbSchedContext) :
    SFr σ (updK σ p (.tcb y)) := by
  refine ⟨fun q x' hq => ?_, fun q y' hq => ?_, fun q y' n hq => ?_, fun q y' n hq => ?_, rfl, rfl⟩
  · by_cases e : q = p
    · subst e; rw [hk] at hq; cases hq; exact ⟨y, by simp [updK], hst, hsc⟩
    · exact ⟨x', by simp only [updK, Function.update_of_ne e]; exact hq, rfl, rfl⟩
  · by_cases e : q = p
    · subst e; exact ⟨x, hk⟩
    · exact ⟨y', by simp only [updK, Function.update_of_ne e] at hq; exact hq⟩
  · have hne : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    exact ⟨y', by simp only [updK, Function.update_of_ne hne]; exact hq, rfl, rfl, rfl, rfl⟩
  · by_cases e : q = p
    · subst e; simp [updK] at hq
    · exact ⟨y', by simp only [updK, Function.update_of_ne e] at hq; exact hq⟩

/-- An SC update keeping its refills, refill maximum and TCB. -/
theorem SFr.updSc {σ : State Unit} {p : ObjRef} {y z : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (e1 : z.scRefills = y.scRefills)
    (e2 : z.scRefillMax = y.scRefillMax) (e3 : z.scTcb = y.scTcb) (e4 : z.scPeriod = y.scPeriod) :
    SFr σ (updK σ p (.schedContext z n)) := by
  refine ⟨fun q x hq => ?_, fun q x hq => ?_, fun q y' n' hq => ?_, fun q y' n' hq => ?_, rfl, rfl⟩
  · have hne : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    exact ⟨x, by simp only [updK, Function.update_of_ne hne]; exact hq, rfl, rfl⟩
  · by_cases e : q = p
    · subst e; simp [updK] at hq
    · exact ⟨x, by simp only [updK, Function.update_of_ne e] at hq; exact hq⟩
  · by_cases e : q = p
    · subst e; rw [hk] at hq; cases hq; exact ⟨z, by simp [updK], e1, e2, e3, e4⟩
    · exact ⟨y', by simp only [updK, Function.update_of_ne e]; exact hq, rfl, rfl, rfl, rfl⟩
  · by_cases e : q = p
    · subst e; simp only [updK, Function.update_self, Option.some.injEq, KernelObject.schedContext.injEq] at hq
      obtain ⟨-, rfl⟩ := hq; exact ⟨y, hk⟩
    · exact ⟨y', by simp only [updK, Function.update_of_ne e] at hq; exact hq⟩


/-- A queued thread's facts: a TCB whose SC, if any, has refills, with a
ready and sufficient head when active (l4v `released_ipc_queues`), valid
when active and periodic. -/
def MemOK (σ : State Unit) (t : ObjRef) : Prop :=
  ∃ x, σ.kheap t = some (.tcb x) ∧ ∀ c, x.tcbSchedContext = some c → ∃ y k, σ.kheap c = some (.schedContext y k) ∧
    y.scRefills ≠ [] ∧
    (scActive y = true → refillReady σ.curTime (refillHd y) = true ∧ refillSufficient 0 (refillHd y) = true) ∧
    (scActive y = true → y.scPeriod ≠ 0 → RefOK y)

theorem SFr.memOK {σ σ' : State Unit} (h : SFr σ σ') {t : ObjRef} (hm : MemOK σ t) : MemOK σ' t := by
  obtain ⟨x, hk, hc⟩ := hm
  obtain ⟨x', hx', -, hsc⟩ := h.tcb t x hk
  refine ⟨x', hx', fun c e => ?_⟩
  obtain ⟨y, k, hky, hne, h12, h3⟩ := hc c (by rw [← hsc, e])
  obtain ⟨y', hy', e1, e2, -, e4⟩ := h.sc c y k hky
  have hh : refillHd y' = refillHd y := by simp [refillHd, e1]
  have hact : scActive y' = true → scActive y = true := fun ha => by simpa [scActive, e2] using ha
  refine ⟨y', k, hy', by rw [e1]; exact hne, fun ha => by rw [h.tm, hh]; exact h12 (hact ha), fun ha hp => ?_⟩
  have ha' : scActive y = true := hact ha
  have hR := h3 ha' (by rw [← e4]; exact hp)
  obtain ⟨r1, r2, r3, r4⟩ := hR
  exact ⟨by rw [e1]; exact r1, by rw [e1]; exact r2, by rw [e1]; exact r3, by rw [hh]; exact r4⟩

/-- A state change keeping the heap, the time and the release queue. -/
theorem SFr.of_heap {σ σ' : State Unit} (hk : σ'.kheap = σ.kheap) (ht : σ'.curTime = σ.curTime)
    (hr : σ'.releaseQueue = σ.releaseQueue) : SFr σ σ' :=
  ⟨fun _ x h => ⟨x, by rw [hk]; exact h, rfl, rfl⟩, fun _ y h => ⟨y, by rw [← hk]; exact h⟩,
    fun _ y _ h => ⟨y, by rw [hk]; exact h, rfl, rfl, rfl, rfl⟩, fun _ y _ h => ⟨y, by rw [← hk]; exact h⟩, ht, hr⟩

/-! ### The notification's links -/

theorem getSkObjRef_ntfn_eq {σ : State Unit} {r : ObjRef} {n : Notification} (hk : σ.kheap r = some (.notification n))
    (f : Notification → Option ObjRef) :
    getSkObjRef (Z := Unit) KernelObject.notification f r σ = ({(f n, σ)}, False) := by
  unfold getSkObjRef
  rw [nd_bind_one (getNotification_eq hk)]; rfl

theorem updateSkObjRef_ntfn_eq {σ : State Unit} {r : ObjRef} {n : Notification}
    (hk : σ.kheap r = some (.notification n)) (f : (Option ObjRef → Option ObjRef) → Notification → Notification)
    (new : Option ObjRef) :
    updateSkObjRef (Z := Unit) KernelObject.notification f r new σ =
      ({((), updK σ r (.notification (f (fun _ => new) n)))}, False) := by
  unfold updateSkObjRef
  rw [nd_bind_one (getNotification_eq hk)]
  exact setNotification_eq _ hk

/-- **`sched_context_maybe_unbind_ntfn` has one outcome**, keeping the
scheduling parts and every TCB; the notification keeps its queue and bound
TCB. -/
theorem smun_eq {σ : State Unit} {r : ObjRef} {n : Notification} (hk : σ.kheap r = some (.notification n))
    (hsc : ∀ c, n.ntfnSc = some c → ∃ y k, σ.kheap c = some (.schedContext y k)) :
    ∃ σ', schedContextMaybeUnbindNtfn (Z := Unit) r σ = ({((), σ')}, False) ∧ SFr σ σ' ∧
      (∃ n', σ'.kheap r = some (.notification n') ∧ n'.ntfnObj = n.ntfnObj ∧ n'.ntfnBoundTcb = n.ntfnBoundTcb) ∧
      (∀ p x, σ.kheap p = some (.tcb x) → σ'.kheap p = some (.tcb x)) ∧
      σ'.schedulerAction = σ.schedulerAction := by
  unfold schedContextMaybeUnbindNtfn
  rw [nd_bind_one (getSkObjRef_ntfn_eq hk _)]
  cases hn : n.ntfnSc with
  | none => exact ⟨σ, rfl, SFr.refl σ, ⟨n, hk, rfl, rfl⟩, fun _ _ h => h, rfl⟩
  | some c =>
    obtain ⟨y, k, hky⟩ := hsc c hn
    have hrc : r ≠ c := by rintro rfl; rw [hk] at hky; cases hky
    simp only [NonDet.maybeM]
    unfold doUnbindNtfnSc setNtfnObjRef
    rw [nd_bind_one (updateSkObjRef_ntfn_eq hk _ _)]
    set σ1 := updK σ r (.notification (ntfnScUpdate (fun _ => none) n)) with hσ1
    have hky1 : σ1.kheap c = some (.schedContext y k) := by
      simp only [hσ1, updK, Function.update_of_ne (Ne.symm hrc)]; exact hky
    refine ⟨_, updateSchedContext_eq hky1 _, ?_, ⟨ntfnScUpdate (fun _ => none) n, ?_, rfl, rfl⟩, ?_, rfl⟩
    · exact (SFr.updOther hk (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ h => by cases h)
        (fun _ _ h => by cases h)).trans (SFr.updSc hky1 rfl rfl rfl rfl)
    · simp [hσ1, updK, Function.update_of_ne hrc]
    · intro p x hp
      have h1 : p ≠ r := by rintro rfl; rw [hk] at hp; cases hp
      have h2 : p ≠ c := by rintro rfl; rw [hky] at hp; cases hp
      simp [hσ1, updK, Function.update_of_ne h1, Function.update_of_ne h2, hp]

/-- **`unbind_maybe_notification` has one outcome**, keeping the scheduling
parts; the notification keeps its queue. -/
theorem umn_eq {σ : State Unit} {r : ObjRef} {n : Notification} (hk : σ.kheap r = some (.notification n))
    (hb : ∀ t, n.ntfnBoundTcb = some t → ∃ x, σ.kheap t = some (.tcb x)) :
    ∃ σ', unbindMaybeNotification (Z := Unit) r σ = ({((), σ')}, False) ∧ SFr σ σ' ∧
      (∃ n', σ'.kheap r = some (.notification n') ∧ n'.ntfnObj = n.ntfnObj) ∧
      σ'.schedulerAction = σ.schedulerAction := by
  unfold unbindMaybeNotification
  rw [nd_bind_one (getSkObjRef_ntfn_eq hk _)]
  cases hn : n.ntfnBoundTcb with
  | none => exact ⟨σ, rfl, SFr.refl σ, ⟨n, hk, rfl⟩, rfl⟩
  | some t =>
    obtain ⟨x, hkt⟩ := hb t hn
    have hrt : r ≠ t := by rintro rfl; rw [hk] at hkt; cases hkt
    simp only [NonDet.maybeM]
    unfold doUnbindNotification setNtfnObjRef
    rw [nd_bind_one (updateSkObjRef_ntfn_eq hk _ _)]
    set σ1 := updK σ r (.notification (ntfnBoundTcbUpdate (fun _ => none) n)) with hσ1
    have hkt1 : σ1.kheap t = some (.tcb x) := by
      simp only [hσ1, updK, Function.update_of_ne (Ne.symm hrt)]; exact hkt
    refine ⟨_, threadSet_eq _ hkt1, ?_, ⟨ntfnBoundTcbUpdate (fun _ => none) n, ?_, rfl⟩, rfl⟩
    · exact (SFr.updOther hk (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ h => by cases h)
        (fun _ _ h => by cases h)).trans (SFr.updTcb hkt1 rfl rfl)
    · simp [hσ1, updK, Function.update_of_ne hrt]


/-! ### The scheduler steps -/

theorem stsAct_heap (σ : State Unit) (t : ObjRef) : (stsAct σ t).kheap = σ.kheap ∧
    (stsAct σ t).curTime = σ.curTime ∧ (stsAct σ t).releaseQueue = σ.releaseQueue ∧
    ((stsAct σ t).schedulerAction = σ.schedulerAction ∨ (stsAct σ t).schedulerAction = .chooseNewThread) := by
  unfold stsAct; split
  · exact ⟨rfl, rfl, rfl, Or.inr rfl⟩
  · exact ⟨rfl, rfl, rfl, Or.inl rfl⟩

/-- **`reschedule_required`'s outcome** under `ActReady`: the heap, the time
and the release queue kept, the action `choose_new_thread`. -/
theorem resched_ok {σ : State Unit} (hA : ActReady σ) :
    ∃ σ', rescheduleRequired (Z := Unit) σ = ({((), σ')}, False) ∧ σ'.kheap = σ.kheap ∧
      σ'.curTime = σ.curTime ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.schedulerAction = .chooseNewThread := by
  cases ha : σ.schedulerAction with
  | switchThread t =>
    by_cases hs : schedulable t σ = true
    · obtain ⟨x, -, -, -, hk, -⟩ := schedulable_inv hs
      have he := tcbSchedAction_gen hk tcbSchedEnqueue
      exact ⟨_, rescheduleRequired_sched ha hs hA he, rfl, rfl, rfl, rfl⟩
    · exact ⟨_, rescheduleRequired_notsched ha (by simpa using hs), rfl, rfl, rfl, rfl⟩
  | _ => exact ⟨_, rescheduleRequired_noswitch (fun t h => by rw [ha] at h; cases h), rfl, rfl, rfl, rfl⟩

/-- **`possible_switch_to`'s outcome** under `ActReady`: the heap, the time
and the release queue kept; the action kept, `choose_new_thread`, or a
switch to the target. -/
theorem pst_ok {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (hA : ActReady σ) :
    ∃ σ', possibleSwitchTo (Z := Unit) t σ = ({((), σ')}, False) ∧ σ'.kheap = σ.kheap ∧
      σ'.curTime = σ.curTime ∧ σ'.releaseQueue = σ.releaseQueue ∧
      (σ'.schedulerAction = σ.schedulerAction ∨ σ'.schedulerAction = .chooseNewThread ∨
        σ'.schedulerAction = .switchThread t) := by
  rw [possibleSwitchTo_unfold hk]
  split_ifs
  · exact ⟨_, tcbSchedAction_gen hk _, rfl, rfl, rfl, Or.inl rfl⟩
  · obtain ⟨σ1, he, hk1, ht1, hr1, ha1⟩ := resched_ok hA
    have hk' : σ1.kheap t = some (.tcb x) := by rw [hk1]; exact hk
    refine ⟨setQ σ1 x.tcbDomain x.tcbPriority (tcbSchedEnqueue t (σ1.readyQueues x.tcbDomain x.tcbPriority)), ?_,
      hk1, ht1, hr1, Or.inr (Or.inl ha1)⟩
    rw [nd_bind_one he, tcbSchedAction_gen hk' _]
  · exact ⟨_, setAction_eq σ _, rfl, rfl, rfl, Or.inr (Or.inr rfl)⟩
  · exact ⟨σ, rfl, rfl, rfl, rfl, Or.inl rfl⟩

/-- `ActReady` after `possible_switch_to t`, the target ready when
schedulable. -/
theorem pst_actReady {σ σ' : State Unit} {t : ObjRef} (hA : ActReady σ) (hT : schedulable t σ = true → RdyAt σ t)
    (hk : σ'.kheap = σ.kheap) (ht : σ'.curTime = σ.curTime) (hr : σ'.releaseQueue = σ.releaseQueue)
    (ha : σ'.schedulerAction = σ.schedulerAction ∨ σ'.schedulerAction = .chooseNewThread ∨
      σ'.schedulerAction = .switchThread t) : ActReady σ' := by
  have hF := SFr.of_heap hk ht hr
  rcases ha with e | e | e
  · exact hF.actReady hA (Or.inl e)
  · exact hF.actReady hA (Or.inr e)
  · rw [actReady_iff]
    intro u hu hs
    rw [e] at hu; cases hu
    exact hF.rdyAt (hT (by rw [← hF.schedulable]; exact hs))

/-- **The refill unblock check of a restarted thread's SC** (Sc side's
`refillUnblockCheck_some`, `unblock_result`): an outcome, the state kept or
the SC's refills changed, its head now at the current time. -/
theorem unblockCur_some {σ : State Unit} {c : ObjRef} {y : SchedContext} {k : Nat}
    (hk : σ.kheap c = some (.schedContext y k)) (hne : y.scRefills ≠ []) :
    ∃ σ', ((), σ') ∈ (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) (some c) σ).1 ∧
      (σ' = σ ∨ ∃ z, σ' = updSc { σ with reprogramTimer := true } c z k ∧ (RefOK y → RefOK z) ∧
        (refillHd z).rTime = σ.curTime ∧ z = { y with scRefills := z.scRefills } ∧ z.scRefills ≠ [] ∧
        y.scPeriod ≠ 0) := by
  unfold ifSporadicCurScAssertRefillUnblockCheck ifCondRefillUnblockCheck
  simp only [NonDet.maybeM]
  rw [nd_bind_one (getSchedContext_eq hk), nd_gets_bind, nd_pure_bind']
  simp only [NonDet.when]
  split_ifs
  · obtain ⟨σ3, h3⟩ := refillUnblockCheck_some hk hne
    refine ⟨σ3, h3, ?_⟩
    rcases unblock_result hk hne h3 with ⟨rfl, -⟩ | ⟨z, rfl, h1, h2, h3', -, h5, h6⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨z, rfl, h1, h2, h3', h5, h6⟩
  · exact ⟨σ, Set.mem_singleton _, Or.inl rfl⟩
  · exact ⟨σ, Set.mem_singleton _, Or.inl rfl⟩


/-! ### `cancel_all_signals` -/

theorem dequeue_eq {σ : State Unit} {t r : ObjRef} {l : List ObjRef} {n : Notification}
    (hk : σ.kheap r = some (.notification n)) (hq : ntfnQueueOf n = t :: l) (hnd : (t :: l).Nodup) :
    ∃ n', tcbNtfnDequeue (Z := Unit) t r σ = ({((), updK σ r (.notification n'))}, False) ∧ ntfnQueueOf n' = l := by
  unfold tcbNtfnDequeue
  rw [nd_bind_one (getNotification_eq hk), nd_pure_bind', hq]
  rw [nd_bind_one (show NonDet.assert (σ := State Unit) (t ∈ t :: l) σ = ({((), σ)}, False) by
    simp [NonDet.assert])]
  have hr : removeAll t (t :: l) = l := by
    have ht : t ∉ l := (List.nodup_cons.1 hnd).1
    unfold removeAll
    simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact List.filter_eq_self.2 fun a ha => by
      simp only [ne_eq, decide_eq_true_eq]; rintro rfl; exact ht ha
  rw [nd_pure_bind', hr, nd_pure_bind']
  refine ⟨_, setNotification_eq _ hk, ?_⟩
  cases l <;> rfl

/-- Thread `u` (not `t`) keeps what `RdyAt`, `MemOK` and `schedulable` read
when only the TCB `t` changes, keeping its SC. -/
theorem tcbUpd_keeps {σ : State Unit} {t : ObjRef} {x x' : Tcb} (hkt : σ.kheap t = some (.tcb x))
    (hsc : x'.tcbSchedContext = x.tcbSchedContext) {u : ObjRef} (hu : u ≠ t) :
    let σ' := updK σ t (.tcb x')
    (RdyAt σ u → RdyAt σ' u) ∧ (MemOK σ u → MemOK σ' u) ∧ schedulable u σ' = schedulable u σ := by
  intro σ'
  have hkp : ∀ p, p ≠ t → σ'.kheap p = σ.kheap p := fun p hp => by
    simp only [σ', updK, Function.update_of_ne hp]
  refine ⟨fun ⟨x0, c, y, k, h1, h2, h3, h4, h5, h6⟩ => ?_, fun ⟨x0, h1, h2⟩ => ?_, ?_⟩
  · have hc : c ≠ t := by rintro rfl; rw [hkt] at h3; cases h3
    exact ⟨x0, c, y, k, by rw [hkp u hu]; exact h1, h2, by rw [hkp c hc]; exact h3, h4, h5, h6⟩
  · refine ⟨x0, by rw [hkp u hu]; exact h1, fun c e => ?_⟩
    obtain ⟨y, k, h3, h4⟩ := h2 c e
    have hc : c ≠ t := by rintro rfl; rw [hkt] at h3; cases h3
    exact ⟨y, k, by rw [hkp c hc]; exact h3, h4⟩
  · apply schedulable_upd
    · rw [tcbsOf_eq, tcbsOf_eq, hkp u hu]
    · intro p
      rw [scsOf_eq, scsOf_eq]
      by_cases e : p = t
      · subst e; simp [σ', updK, hkt]
      · rw [hkp p e]
    · rfl

/-- **One thread of `cancel_all_signals`** (`remove_and_restart_ntfn_queued_thread`):
an outcome, with the notification's queue its tail, the other queued
threads' facts, `ScBack` and `ActReady` kept. -/
theorem ntfn_iter {σ : State Unit} {r t : ObjRef} {l : List ObjRef} {n : Notification}
    (hk : σ.kheap r = some (.notification n)) (hq : ntfnQueueOf n = t :: l) (hnd : (t :: l).Nodup)
    (hm : ∀ u ∈ t :: l, MemOK σ u) (hB : ScBack σ) (hA : ActReady σ) :
    ∃ σ5, ((), σ5) ∈ (removeAndRestartNtfnQueuedThread (Z := Unit) t r σ).1 ∧
      (∃ n5, σ5.kheap r = some (.notification n5) ∧ ntfnQueueOf n5 = l) ∧
      (∀ u ∈ l, MemOK σ5 u) ∧ ScBack σ5 ∧ ActReady σ5 := by
  have htl : t ∉ l := (List.nodup_cons.1 hnd).1
  -- the dequeue
  obtain ⟨n1, hdq, hq1⟩ := dequeue_eq hk hq hnd
  set σ1 := updK σ r (.notification n1) with hσ1
  have hF1 : SFr σ σ1 := SFr.updOther hk (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ h => by cases h)
    (fun _ _ h => by cases h)
  have hm1 : ∀ u ∈ t :: l, MemOK σ1 u := fun u hu => hF1.memOK (hm u hu)
  have hB1 := hF1.scBack hB
  have hA1 := hF1.actReady hA (Or.inl rfl)
  have hk1 : σ1.kheap r = some (.notification n1) := by simp [hσ1, updK]
  obtain ⟨x, hkt, hxs⟩ := hm1 t (List.mem_cons_self ..)
  have hrt : r ≠ t := by rintro rfl; rw [hk1] at hkt; cases hkt
  -- the restart
  set x' : Tcb := { x with tcbState := .restart } with hx'
  set σ2' := updK σ1 t (.tcb x') with hσ2'
  have hkp2 : ∀ p, p ≠ t → σ2'.kheap p = σ1.kheap p := fun p hp => by
    simp only [hσ2', updK, Function.update_of_ne hp]
  have hkt2 : σ2'.kheap t = some (.tcb x') := by simp [hσ2', updK]
  have hT2 : schedulable t σ2' = true → RdyAt σ2' t := by
    intro hs
    obtain ⟨x0, c, y0, k0, hk0, hsc0, -, hky0, hact0, -⟩ := schedulable_inv hs
    rw [hkt2] at hk0; cases hk0
    obtain ⟨y, k, hky, hne, h12, -⟩ := hxs c hsc0
    have hct : c ≠ t := by rintro rfl; rw [hkt] at hky; cases hky
    rw [hkp2 c hct, hky] at hky0; cases hky0
    obtain ⟨h1, h2⟩ := h12 hact0
    exact ⟨x', c, _, _, hkt2, hsc0, by rw [hkp2 c hct]; exact hky, hne, h1, h2⟩
  have hA2' : ActReady σ2' := by
    rw [actReady_iff] at hA1 ⊢
    intro u hu hs
    by_cases e : u = t
    · subst e; exact hT2 hs
    · have hK := tcbUpd_keeps (x' := x') hkt rfl e
      exact hK.1 (hA1 u hu (by rw [← hK.2.2]; exact hs))
  have hst := setThreadState_eq' hkt .restart
  set σ2 := stsAct σ2' t with hσ2
  obtain ⟨hk2, ht2, hr2, ha2⟩ := stsAct_heap σ2' t
  have hF2 : SFr σ2' σ2 := SFr.of_heap hk2 ht2 hr2
  have hA2 : ActReady σ2 := hF2.actReady hA2' ha2
  have hT2'' : schedulable t σ2 = true → RdyAt σ2 t := fun hs =>
    hF2.rdyAt (hT2 (by rw [← hF2.schedulable]; exact hs))
  have hm2 : ∀ u ∈ l, MemOK σ2 u := fun u hu =>
    hF2.memOK ((tcbUpd_keeps (x' := x') hkt rfl (fun e => htl (e ▸ hu))).2.1 (hm1 u (List.mem_cons_of_mem _ hu)))
  have hB2' : ScBack σ2' := by
    intro u xu c hku hc
    by_cases e : u = t
    · subst e; rw [hkt2] at hku; cases hku
      obtain ⟨y, k, hky, hyt, hne⟩ := hB1 u x c hkt hc
      have hct : c ≠ u := by rintro rfl; rw [hkt] at hky; cases hky
      exact ⟨y, k, by rw [hkp2 c hct]; exact hky, hyt, hne⟩
    · rw [hkp2 u e] at hku
      obtain ⟨y, k, hky, hyt, hne⟩ := hB1 u xu c hku hc
      have hct : c ≠ t := by rintro rfl; rw [hkt] at hky; cases hky
      exact ⟨y, k, by rw [hkp2 c hct]; exact hky, hyt, hne⟩
  have hB2 := hF2.scBack hB2'
  have hkt2' : σ2.kheap t = some (.tcb x') := by rw [hk2]; exact hkt2
  have hkr2 : σ2.kheap r = some (.notification n1) := by rw [hk2, hkp2 r hrt]; exact hk1
  -- the steps to the refill check
  unfold removeAndRestartNtfnQueuedThread
  rw [nd_bind_one hdq, nd_bind_one hst,
    nd_bind_one (show getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t σ2 = _ from threadGet_eq _ hkt2')]
  -- the refill check, then the switch
  suffices hS : ∃ σ3, ((), σ3) ∈ (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) x'.tcbSchedContext σ2).1 ∧
      σ3.kheap t = some (.tcb x') ∧ σ3.kheap r = some (.notification n1) ∧ (∀ u ∈ l, MemOK σ3 u) ∧
      ScBack σ3 ∧ ActReady σ3 ∧ (schedulable t σ3 = true → RdyAt σ3 t) by
    obtain ⟨σ3, hm3, hkt3, hkr3, hmm3, hB3, hA3, hT3⟩ := hS
    obtain ⟨σ4, he4, hk4, ht4, hr4, ha4⟩ := pst_ok hkt3 hA3
    have hF4 := SFr.of_heap hk4 ht4 hr4
    refine ⟨σ4, mem_bind_nd hm3 (by rw [he4]; exact Set.mem_singleton _), ⟨n1, by rw [hk4]; exact hkr3, hq1⟩,
      fun u hu => hF4.memOK (hmm3 u hu), hF4.scBack hB3, pst_actReady hA3 hT3 hk4 ht4 hr4 ha4⟩
  cases hxc : x'.tcbSchedContext with
  | none =>
    exact ⟨σ2, Set.mem_singleton _, hkt2', hkr2, hm2, hB2, hA2, hT2''⟩
  | some c =>
    have hxc' : x.tcbSchedContext = some c := hxc
    obtain ⟨y, k, hky1, hne, -, hrf⟩ := hxs c hxc'
    have hct : c ≠ t := by rintro rfl; rw [hkt] at hky1; cases hky1
    have hky2 : σ2.kheap c = some (.schedContext y k) := by rw [hk2, hkp2 c hct]; exact hky1
    obtain ⟨σ3, hm3, hcase⟩ := unblockCur_some hky2 hne
    rcases hcase with rfl | ⟨z, rfl, hRz, hrt3, hz, hzne, hper⟩
    · exact ⟨σ2, hm3, hkt2', hkr2, hm2, hB2, hA2, hT2''⟩
    · -- the SC's refills changed
      obtain ⟨yb, kb, hkyb, hybt, -⟩ := hB2 t x' c hkt2' hxc
      rw [hky2] at hkyb; cases hkyb
      set σ3 := updSc { σ2 with reprogramTimer := true } c z k with hσ3
      have hkp3 : ∀ p, p ≠ c → σ3.kheap p = σ2.kheap p := fun p hp => by
        simp only [hσ3, updSc, updK, Function.update_of_ne hp]
      have hkc3 : σ3.kheap c = some (.schedContext z k) := by simp [hσ3, updSc, updK]
      have hrc : r ≠ c := by rintro rfl; rw [hkr2] at hky2; cases hky2
      have hzact : scActive z = scActive y := by rw [hz]
      have hzt : z.scTcb = y.scTcb := by rw [hz]
      have hsch : ∀ u, schedulable u σ3 = schedulable u σ2 := by
        intro u
        apply schedulable_upd
        · rw [tcbsOf_eq, tcbsOf_eq]
          by_cases e : u = c
          · subst e; rw [hkc3, hky2]
          · rw [hkp3 u e]
        · intro p
          rw [scsOf_eq, scsOf_eq]
          by_cases e : p = c
          · subst e; rw [hkc3, hky2]; simp [hzact]
          · rw [hkp3 p e]
        · rfl
      have ht3 : σ3.curTime = σ2.curTime := rfl
      -- the restarted thread: ready and sufficient when schedulable
      have hT3 : schedulable t σ3 = true → RdyAt σ3 t := by
        intro hs
        obtain ⟨x0, c0, y0, k0, hk0, hsc0, -, hky0, hact0, -⟩ := schedulable_inv hs
        rw [hkp3 t (Ne.symm hct), hkt2'] at hk0; cases hk0
        rw [hxc] at hsc0; cases hsc0
        rw [hkc3] at hky0; cases hky0
        have hRy : RefOK y := hrf (by rw [← hzact]; exact hact0) hper
        have hR := hRz hRy
        refine ⟨x', c, z, k, by rw [hkp3 t (Ne.symm hct)]; exact hkt2', hxc, hkc3, hzne, ?_, suff_of_min hR.2.2.2⟩
        rw [ht3]
        simp only [refillReady, refillReady', hrt3, decide_eq_true_eq]
        exact BitVec.le_of_eq (by simp)
      -- a thread other than `t` has an SC other than `c`
      have hother : ∀ u xu cu, σ2.kheap u = some (.tcb xu) → xu.tcbSchedContext = some cu → u ≠ t → cu ≠ c := by
        intro u xu cu hku hcu hut e
        subst e
        obtain ⟨yu, ku, hkyu, hyut, -⟩ := hB2 u xu cu hku hcu
        rw [hky2] at hkyu; cases hkyu
        rw [hybt] at hyut; cases hyut; exact hut rfl
      refine ⟨σ3, hm3, by rw [hkp3 t (Ne.symm hct)]; exact hkt2', by rw [hkp3 r hrc]; exact hkr2, fun u hu => ?_, ?_, ?_, hT3⟩
      · obtain ⟨xu, hku, hcu⟩ := hm2 u hu
        have hut : u ≠ t := fun e => htl (e ▸ hu)
        have huc : u ≠ c := by rintro rfl; rw [hky2] at hku; cases hku
        refine ⟨xu, by rw [hkp3 u huc]; exact hku, fun cu e => ?_⟩
        have hcc := hother u xu cu hku e hut
        obtain ⟨yu, ku, h1, h2⟩ := hcu cu e
        exact ⟨yu, ku, by rw [hkp3 cu hcc]; exact h1, h2⟩
      · intro u xu cu hku hcu
        by_cases e : u = c
        · subst e; rw [hkc3] at hku; cases hku
        rw [hkp3 u e] at hku
        obtain ⟨yu, ku, h1, h2, h3⟩ := hB2 u xu cu hku hcu
        by_cases e2 : cu = c
        · subst e2; rw [hky2] at h1; cases h1
          exact ⟨z, _, hkc3, by rw [hzt]; exact h2, hzne⟩
        · exact ⟨yu, ku, by rw [hkp3 cu e2]; exact h1, h2, h3⟩
      · rw [actReady_iff] at hA2 ⊢
        intro u hu hs
        by_cases e : u = t
        · subst e; exact hT3 hs
        · have hu2 : σ2.schedulerAction = .switchThread u := hu
          obtain ⟨xu, cu, yu, ku, h1, h2, h3, h4, h5, h6⟩ := hA2 u hu2 (by rw [← hsch]; exact hs)
          have huc : u ≠ c := by rintro rfl; rw [hky2] at h1; cases h1
          have hcc := hother u xu cu h1 h2 e
          exact ⟨xu, cu, yu, ku, by rw [hkp3 u huc]; exact h1, h2, by rw [hkp3 cu hcc]; exact h3, h4, by rw [ht3]; exact h5, h6⟩


/-- **The loop of `cancel_all_signals`** over the notification's queue. -/
theorem ntfn_loop {r : ObjRef} :
    ∀ (l : List ObjRef) (σ : State Unit), (∃ n, σ.kheap r = some (.notification n) ∧ ntfnQueueOf n = l) →
      l.Nodup → (∀ u ∈ l, MemOK σ u) → ScBack σ → ActReady σ →
      ∃ σ', ((), σ') ∈ (NonDet.mapMx (fun t => removeAndRestartNtfnQueuedThread (Z := Unit) t r) l σ).1 ∧
        ActReady σ'
  | [], σ, _, _, _, _, hA => ⟨σ, Set.mem_singleton _, hA⟩
  | t :: l, σ, ⟨n, hk, hq⟩, hnd, hm, hB, hA => by
    obtain ⟨σ5, h5, hq5, hm5, hB5, hA5⟩ := ntfn_iter hk hq hnd hm hB hA
    obtain ⟨σ', h', hA'⟩ := ntfn_loop l σ5 hq5 (List.nodup_cons.1 hnd).2 hm5 hB5 hA5
    exact ⟨σ', mem_bind_nd h5 h', hA'⟩

/-- **`cancel_all_signals` has an outcome.** -/
theorem cas_out {σ : State Unit} {r : ObjRef} {n : Notification} (hk : σ.kheap r = some (.notification n))
    (hnd : (ntfnQueueOf n).Nodup) (hm : ∀ u ∈ ntfnQueueOf n, MemOK σ u) (hB : ScBack σ) (hA : ActReady σ) :
    ∃ σ', ((), σ') ∈ (cancelAllSignals (Z := Unit) r σ).1 := by
  unfold cancelAllSignals
  rw [nd_bind_one (getNotification_eq hk)]
  cases ho : n.ntfnObj with
  | waitingNtfn q =>
    have hq : ntfnQueueOf n = q := by simp [ntfnQueueOf, ho, Ntfn.ntfnQueue]
    rw [hq] at hnd hm
    obtain ⟨σ', h', hA'⟩ := ntfn_loop q σ ⟨n, hk, hq⟩ hnd hm hB hA
    obtain ⟨σ'', he, -⟩ := resched_ok hA'
    exact ⟨σ'', mem_bind_nd h' (by rw [he]; exact Set.mem_singleton _)⟩
  | _ => exact ⟨σ, Set.mem_singleton _⟩

/-- **What the finalisation of a notification cap needs of the spec state**:
the notification, its SC and bound TCB exist; its queue is a duplicate-free
list of queued threads' facts (`MemOK`); `ScBack`; `ActReady`. -/
def NtfnPre (σ : State Unit) (r : ObjRef) : Prop :=
  ∃ n, σ.kheap r = some (.notification n) ∧ (∀ c, n.ntfnSc = some c → ∃ y k, σ.kheap c = some (.schedContext y k)) ∧
    (∀ t, n.ntfnBoundTcb = some t → ∃ x, σ.kheap t = some (.tcb x)) ∧ (ntfnQueueOf n).Nodup ∧
    (∀ u ∈ ntfnQueueOf n, MemOK σ u) ∧ ScBack σ ∧ ActReady σ

/-- `NtfnPre` from the Sc side's `Inv` and `ActReady`, the bound TCB, and the
queued threads: distinct TCBs with ready and sufficient SCs (l4v's
`released_ipc_queues`). -/
theorem ntfnPre_of_inv {σ : State Unit} {r : ObjRef} {n : Notification} (hI : Inv σ) (hA : ActReady σ)
    (hk : σ.kheap r = some (.notification n)) (hb : ∀ t, n.ntfnBoundTcb = some t → ∃ x, σ.kheap t = some (.tcb x))
    (hnd : (ntfnQueueOf n).Nodup)
    (hq : ∀ u ∈ ntfnQueueOf n, ∃ x, σ.kheap u = some (.tcb x) ∧ ∀ c, x.tcbSchedContext = some c →
      ∀ y k, σ.kheap c = some (.schedContext y k) → scActive y = true →
        refillReady σ.curTime (refillHd y) = true ∧ refillSufficient 0 (refillHd y) = true) :
    NtfnPre σ r := by
  refine ⟨n, hk, fun c hc => hI.ntfnSc r n c hk hc, hb, hnd, fun u hu => ?_, fun u xu c hku hc => ?_, hA⟩
  · obtain ⟨x, hku, hc⟩ := hq u hu
    refine ⟨x, hku, fun c e => ?_⟩
    obtain ⟨y, k, hky, -⟩ := hI.back u x c hku e
    exact ⟨y, k, hky, hI.ne c y k hky, hc c e y k hky, fun ha hp => hI.refills c y k hky ha hp⟩
  · obtain ⟨y, k, hky, hyt⟩ := hI.back u xu c hku hc
    exact ⟨y, k, hky, hyt, hI.ne c y k hky⟩

/-- **The spec's finalisation of a final notification cap has an outcome.** -/
theorem finNtfn_out {σ : State Unit} {r : ObjRef} (b : Badge) (R : CapRights) (h : NtfnPre σ r) :
    ∃ σ', ((Cap.nullCap, Cap.nullCap), σ') ∈ (finaliseCap (Z := Unit) (.notificationCap r b R) true σ).1 := by
  obtain ⟨n, hk, hsc, hb, hnd, hm, hB, hA⟩ := h
  obtain ⟨σA, hA1, hFA, ⟨nA, hkA, hoA, hbA⟩, htA, haA⟩ := smun_eq hk hsc
  have hbA' : ∀ t, nA.ntfnBoundTcb = some t → ∃ x, σA.kheap t = some (.tcb x) := fun t e => by
    obtain ⟨x, hx⟩ := hb t (by rw [← hbA]; exact e); exact ⟨x, htA t x hx⟩
  obtain ⟨σB, hB1, hFB, ⟨nB, hkB, hoB⟩, haB⟩ := umn_eq hkA hbA'
  have hF := hFA.trans hFB
  have hqB : ntfnQueueOf nB = ntfnQueueOf n := by simp [ntfnQueueOf, hoB, hoA]
  obtain ⟨σC, hC⟩ := cas_out hkB (by rw [hqB]; exact hnd) (fun u hu => hF.memOK (hm u (by rw [← hqB]; exact hu)))
    (hF.scBack hB) (hF.actReady hA (Or.inl (by rw [haB, haA])))
  refine ⟨σC, ?_⟩
  unfold finaliseCap
  simp only [NonDet.liftM, NonDet.when, ↓reduceIte]
  refine mem_bind_nd (x := ((), σC)) ?_ (Set.mem_singleton _)
  rw [nd_bind_one hA1, nd_bind_one hB1]
  exact hC

end Spec

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The spec's side of a final notification cap's finalisation**: the
spec state meets `NtfnPre` at the notification. -/
def NtfnSpecHyp (th : TypedHeap) : Prop :=
  ∀ (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost) (sl : Fl4Spec.CslotPtr) (n b0 : U64) (b1 b2 : Bool),
    DState (L := L) th s σ G → AbsSlot th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Notification n b0 b1 b2) →
    Fl4Spec.isFinalCap' (absCap (.Notification n b0 b1 b2)) σ → NtfnPre σ n.bv

/-- **`SpecFinOut` for the notification caps.** -/
theorem specFinOut_ntfn (th : TypedHeap) (h : NtfnSpecHyp (L := L) th) : SpecFinOut (L := L) FinNtfnK th := by
  intro s σ G sl c hk hDS hA hc hfin
  obtain ⟨n, b0, b1, b2, rfl⟩ := hk
  exact finNtfn_out _ _ (h s σ G sl n b0 b1 b2 hDS hA hc hfin)

end

end Fl4Proofs.P3.Sched
