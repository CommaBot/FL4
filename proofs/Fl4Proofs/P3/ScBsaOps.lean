/-
P3 (DESIGN.md §9), scheduling contexts: **`BlockedScActive` ([J]) across the
SC operations** (plan §5.1: the per-operation SC conditions).

* `BK σ σ'`: every IPC-blocked thread of `σ'` was IPC-blocked in `σ`, and
  every inactive SC of `σ'` was an inactive SC of `σ` (same size) whose new
  bound thread, if any, is not IPC-blocked in `σ'`. Reflexive and
  transitive; with the call stacks kept (`SOK (_, true)`), it keeps
  `BlockedScActive` (`BlockedScActive.bk`).
* `BKM m`: every outcome of `m` is `BK`-related to its start; `BKA P m` the
  same from the states satisfying `P`. Combinators as for `MK`; `bkm_of`
  from `NKT` and `MK`.
* The operations: `bkm_refillMaxSet` (`REFILL_MAX` set to an active value),
  `bka_setScTcb` (an SC's bound thread set, the SC active or the thread not
  IPC-blocked).
-/
import Fl4Proofs.P3.ScJointKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

/-- The TCB half of `BK`. -/
def TB (σ σ' : State Unit) : Prop :=
  ∀ t x, σ'.kheap t = some (.tcb x) → ipcQueuedThreadState x.tcbState = true →
    ∃ x0, σ.kheap t = some (.tcb x0) ∧ ipcQueuedThreadState x0.tcbState = true

/-- **The SC-activity step** (module docstring). -/
def BK (σ σ' : State Unit) : Prop :=
  TB σ σ' ∧
  ∀ p y n, σ'.kheap p = some (.schedContext y n) → scActive y = false →
    ∃ y0, σ.kheap p = some (.schedContext y0 n) ∧ scActive y0 = false ∧
      ∀ t, y.scTcb = some t → y0.scTcb = some t ∨
        ∀ x, σ'.kheap t = some (.tcb x) → ipcQueuedThreadState x.tcbState = false

theorem BK.refl (σ : State Unit) : BK σ σ :=
  ⟨fun _ x h hq => ⟨x, h, hq⟩, fun _ y _ h ha => ⟨y, h, ha, fun _ e => Or.inl e⟩⟩

theorem BK.trans {σ1 σ2 σ3 : State Unit} (h1 : BK σ1 σ2) (h2 : BK σ2 σ3) : BK σ1 σ3 := by
  refine ⟨fun t x hx hq => ?_, fun p y n hp ha => ?_⟩
  · obtain ⟨x2, hx2, hq2⟩ := h2.1 t x hx hq
    exact h1.1 t x2 hx2 hq2
  · obtain ⟨y2, hp2, ha2, ht2⟩ := h2.2 p y n hp ha
    obtain ⟨y1, hp1, ha1, ht1⟩ := h1.2 p y2 n hp2 ha2
    refine ⟨y1, hp1, ha1, fun t e => ?_⟩
    rcases ht2 t e with e2 | hn
    · rcases ht1 t e2 with e1 | hn1
      · exact Or.inl e1
      · refine Or.inr fun x hx => ?_
        by_contra hq
        obtain ⟨x2, hx2, hq2⟩ := h2.1 t x hx (by simpa using hq)
        rw [hn1 x2 hx2] at hq2; cases hq2
    · exact Or.inr hn

/-- **`BK` with the call stacks kept keeps `BlockedScActive`.** -/
theorem BlockedScActive.bk {σ σ' : State Unit} {f1 : Bool} (h : BlockedScActive σ) (hK : BK σ σ')
    (hS : SOK (f1, true) σ σ') : BlockedScActive σ' := by
  refine ⟨fun p y n t x hp hyt hx hq => ?_, fun p y n hp hr => ?_⟩
  · by_contra ha
    obtain ⟨y0, hp0, ha0, ht0⟩ := hK.2 p y n hp (by simpa using ha)
    rcases ht0 t hyt with e | hn
    · obtain ⟨x0, hx0, hq0⟩ := hK.1 t x hx hq
      have := h.tcb p y0 n t x0 hp0 e hx0 hq0
      rw [ha0] at this; cases this
    · rw [hn x hx] at hq; cases hq
  · by_contra ha
    obtain ⟨y0, hp0, ha0, -⟩ := hK.2 p y n hp (by simpa using ha)
    have hk := hS.kh p
    rw [hp0, hp] at hk
    obtain ⟨-, -, hrep⟩ := hk
    have := h.replies p y0 n hp0 (by rw [← hrep rfl]; exact hr)
    rw [ha0] at this; cases this

/-- Every outcome of `m` is `BK`-related to its start. -/
def BKM {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → BK σ x.2

/-- `BKM` from the start states satisfying `P`. -/
def BKA {α : Type} (P : State Unit → Prop) (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, P σ → ∀ x, x ∈ (m σ).1 → BK σ x.2

/-- **An `NKT` and `MK` operation is `BKM`.** -/
theorem bkm_of {α : Type} {m : NonDet (State Unit) α} (hn : NKT m) (hm : MaxK.MK m) : BKM m := by
  intro σ x hx
  refine ⟨(hn σ x hx).tcb_back, fun p y n hp ha => ?_⟩
  obtain ⟨y0, hp0, e1, e2⟩ := hm σ x hx p y n hp
  exact ⟨y0, hp0, by simpa [scActive, e1] using ha, fun t e => Or.inl (e2 ▸ e)⟩

theorem BKM.toA {α : Type} {m : NonDet (State Unit) α} (h : BKM m) (P : State Unit → Prop) : BKA P m :=
  fun σ _ => h σ

theorem bkm_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : BKM m)
    (hg : ∀ a, BKM (g a)) : BKM (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

/-- A bind whose first part runs from `P` and ends in `Q`, the rest from `Q`. -/
theorem bka_bind {α β : Type} {P : State Unit → Prop} {Q : α → State Unit → Prop} {m : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) β} (hm : BKA P m) (hq : ∀ σ, P σ → ∀ y, y ∈ (m σ).1 → Q y.1 y.2)
    (hg : ∀ a, BKA (Q a) (g a)) : BKA P (m >>= g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  exact (hm σ hσ y hy).trans (hg y.1 y.2 (hq σ hσ y hy) x hx)

theorem bka_when (P : State Unit → Prop) (C : Prop) [Decidable C] {m : NonDet (State Unit) Unit} (h : BKA P m) :
    BKA P (NonDet.when C m) := by
  unfold NonDet.when; split
  · exact h
  · intro σ _ x hx; rw [Set.mem_singleton_iff.1 hx]; exact BK.refl _

/-- **`update_sched_context` keeping the bound thread and making no SC
inactive.** -/
theorem bkm_updSc (q : ObjRef) (f : SchedContext → SchedContext) (ht : ∀ y, (f y).scTcb = y.scTcb)
    (ha : ∀ y, scActive (f y) = false → scActive y = false) : BKM (updateSchedContext (Z := Unit) q f) := by
  intro σ x hx
  obtain ⟨y0, n0, hk, e⟩ := MaxK.updSc_mem hx
  rw [e]
  refine ⟨fun t x' hx' hq => ?_, fun p y n hp hya => ?_⟩
  · have : t ≠ q := by rintro rfl; simp at hx'
    simp only [Function.update_of_ne this] at hx'; exact ⟨x', hx', hq⟩
  · by_cases hpq : p = q
    · subst hpq
      simp only [Function.update_self, Option.some.injEq, KernelObject.schedContext.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨y0, hk, ha y0 hya, fun t e' => Or.inl (by rw [← ht y0]; exact e')⟩
    · simp only [Function.update_of_ne hpq] at hp; exact ⟨y, hp, hya, fun t e' => Or.inl e'⟩

/-- **`REFILL_MAX` set to an active value** (Configure's `refill_new`,
`refill_update`). -/
theorem bkm_refillMaxSet (q : ObjRef) (v : Nat) (hv : activeSc v = true) :
    BKM (setScObjRef (Z := Unit) scRefillMaxUpdate q v) :=
  bkm_updSc q _ (fun _ => rfl) (fun y h => by simp [scRefillMaxUpdate, scActive, hv] at h)

/-- **An SC's bound thread set** (Bind's, a donation's): from a state where
the SC is active or the thread is not IPC-blocked. -/
theorem bka_setScTcb (q t : ObjRef) :
    BKA (fun σ => ∀ y n, σ.kheap q = some (.schedContext y n) → scActive y = true ∨
        ∀ x, σ.kheap t = some (.tcb x) → ipcQueuedThreadState x.tcbState = false)
      (setScObjRef (Z := Unit) scTcbUpdate q (some t)) := by
  intro σ hP x hx
  obtain ⟨y0, n0, hk, e⟩ := MaxK.updSc_mem hx
  rw [e]
  refine ⟨fun t' x' hx' hq => ?_, fun p y n hp hya => ?_⟩
  · have : t' ≠ q := by rintro rfl; simp at hx'
    simp only [Function.update_of_ne this] at hx'; exact ⟨x', hx', hq⟩
  · by_cases hpq : p = q
    · rw [hpq] at hp
      simp only [Function.update_self, Option.some.injEq, KernelObject.schedContext.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨y0, by rw [hpq]; exact hk, by simpa [scActive, scTcbUpdate] using hya, fun t' e' => ?_⟩
      have e'' : t' = t := by simpa [scTcbUpdate] using e'.symm
      rw [e'']
      rcases hP y0 n0 hk with h1 | h1
      · exfalso; simp_all [scActive, scTcbUpdate]
      · refine Or.inr fun x' hx' => ?_
        by_cases e2 : t = q
        · rw [e2] at hx'; simp at hx'
        · simp only [Function.update_of_ne e2] at hx'; exact h1 x' hx'
    · simp only [Function.update_of_ne hpq] at hp; exact ⟨y, hp, hya, fun t' e' => Or.inl e'⟩

/-! ## SC steps keeping the bound threads and making no SC inactive -/

/-- Every SC of `σ'` was one of `σ` with the same size and bound thread (or
none), and inactive only if it was. -/
def SKa (σ σ' : State Unit) : Prop :=
  ∀ p y n, σ'.kheap p = some (.schedContext y n) →
    ∃ y0, σ.kheap p = some (.schedContext y0 n) ∧ (y.scTcb = y0.scTcb ∨ y.scTcb = none) ∧
      (scActive y = false → scActive y0 = false)

theorem SKa.refl (σ : State Unit) : SKa σ σ := fun _ y _ h => ⟨y, h, Or.inl rfl, id⟩

theorem SKa.trans {σ1 σ2 σ3 : State Unit} (h1 : SKa σ1 σ2) (h2 : SKa σ2 σ3) : SKa σ1 σ3 := by
  intro p y n h
  obtain ⟨y2, h2', e1, f1⟩ := h2 p y n h
  obtain ⟨y1, h1', e2, f2⟩ := h1 p y2 n h2'
  refine ⟨y1, h1', ?_, fun ha => f2 (f1 ha)⟩
  rcases e1 with e1 | e1
  · rcases e2 with e2 | e2
    · exact Or.inl (e1.trans e2)
    · exact Or.inr (e1.trans e2)
  · exact Or.inr e1

def SKaM {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → SKa σ x.2

theorem skm_of {α : Type} {m : NonDet (State Unit) α} (hm : MaxK.MK m) : SKaM m := by
  intro σ x hx p y n hp
  obtain ⟨y0, hp0, e1, e2⟩ := hm σ x hx p y n hp
  exact ⟨y0, hp0, Or.inl e2, fun ha => by simpa [scActive, e1] using ha⟩

theorem skm_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : SKaM m)
    (hg : ∀ a, SKaM (g a)) : SKaM (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem skm_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : SKaM m1)
    (h2 : SKaM m2) : SKaM (if P then m1 else m2) := by
  split <;> assumption

theorem skm_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : SKaM m) :
    SKaM (NonDet.when P m) := by
  unfold NonDet.when; exact skm_ite P h (skm_of (MaxK.mk_pure' _))

/-- **`REFILL_MAX` set to an active value** (`SKaM`). -/
theorem skm_refillMaxSet (q : ObjRef) (v : Nat) (hv : activeSc v = true) :
    SKaM (setScObjRef (Z := Unit) scRefillMaxUpdate q v) := by
  intro σ x hx
  obtain ⟨y0, n0, hk, e⟩ := MaxK.updSc_mem hx
  rw [e]
  intro p y n hp
  by_cases hpq : p = q
  · subst hpq
    simp only [Function.update_self, Option.some.injEq, KernelObject.schedContext.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨y0, hk, Or.inl rfl, fun h => by simp [scRefillMaxUpdate, scActive, hv] at h⟩
  · simp only [Function.update_of_ne hpq] at hp; exact ⟨y, hp, Or.inl rfl, id⟩

/-- **`NKT` and `SKaM` give `BKM`.** -/
theorem bkm_of_sk {α : Type} {m : NonDet (State Unit) α} (hn : NKT m) (hs : SKaM m) : BKM m := by
  intro σ x hx
  refine ⟨(hn σ x hx).tcb_back, fun p y n hp ha => ?_⟩
  obtain ⟨y0, hp0, e1, e2⟩ := hs σ x hx p y n hp
  refine ⟨y0, hp0, e2 ha, fun t e => ?_⟩
  rcases e1 with e1 | e1
  · exact Or.inl (e1 ▸ e)
  · rw [e1] at e; cases e

/-- **An SC's bound thread cleared** (`SKaM`). -/
theorem skm_setScTcbNone (q : ObjRef) : SKaM (setScObjRef (Z := Unit) scTcbUpdate q none) := by
  intro σ x hx
  obtain ⟨y0, n0, hk, e⟩ := MaxK.updSc_mem hx
  rw [e]
  intro p y n hp
  by_cases hpq : p = q
  · subst hpq
    simp only [Function.update_self, Option.some.injEq, KernelObject.schedContext.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨y0, hk, Or.inr rfl, fun h => by simpa [scTcbUpdate, scActive] using h⟩
  · simp only [Function.update_of_ne hpq] at hp; exact ⟨y, hp, Or.inl rfl, id⟩

/-! ## Configure -/

/-- The refill operations' unfoldings (for `mk_auto`). -/
macro "unf_ref" : tactic => `(tactic| repeat (first | unfold updateRefillHd | unfold updateRefillTl | unfold refillAddTail | unfold refillPopHead | unfold getRefillHead | unfold getRefills | unfold getRefillTail | unfold refillFull | unfold refillSingle | unfold refillSize | unfold scheduleUsed | unfold chargeEntireHeadRefill | unfold handleOverrun | unfold headInsufficientLoop | unfold mergeNonoverlappingHeadRefill | unfold isRoundRobin | unfold getScActive | unfold getScRefillReady | unfold maybeAddEmptyTail | unfold refillBudgetCheck | unfold refillBudgetCheckRoundRobin | unfold commitTime | unfold postpone | unfold tcbReleaseEnqueue | unfold readyTimesAppend | unfold setReleaseQueue | unfold orderedInsert | unfold schedContextResume | unfold getThreadState))
theorem skm_refillNew (p : ObjRef) (m : Nat) (b per : Ticks) (hv : activeSc m = true) :
    SKaM (refillNew (Z := Unit) p m b per) := by
  unfold refillNew
  refine skm_bind (skm_of (MaxK.mk_gets _)) fun _ => skm_bind (skm_of (by mk_auto)) fun _ =>
    skm_bind (skm_of (by mk_auto)) fun _ => skm_bind (skm_refillMaxSet p m hv) fun _ =>
    skm_bind (skm_of (MaxK.mk_pure _)) fun _ => skm_bind (skm_of (by mk_auto)) fun _ =>
    skm_of (by unf_ref; mk_auto)
theorem skm_refillUpdate (p : ObjRef) (per b : Ticks) (m : Nat) (hv : activeSc m = true) :
    SKaM (refillUpdate (Z := Unit) p per b m) := by
  unfold refillUpdate
  refine skm_bind (skm_of (by mk_auto)) fun _ => skm_bind (skm_refillMaxSet p m hv) fun _ =>
    skm_of (by unf_ref; mk_auto)
macro "skm_step" : tactic => `(tactic| first
  | (with_reducible exact skm_refillNew _ _ _ _ (by assumption))
  | (with_reducible exact skm_refillNew _ _ _ _ (by decide))
  | (with_reducible exact skm_refillUpdate _ _ _ _ (by assumption))
  | (with_reducible exact skm_setScTcbNone _)
  | (with_reducible refine skm_bind ?_ (fun _ => ?_))
  | (with_reducible apply skm_when)
  | (with_reducible apply skm_ite)
  | (apply skm_of; unf_ref; mk_auto; done))
set_option maxHeartbeats 1000000 in
theorem skm_configure (p : ObjRef) (b per : Ticks) (mr : Nat) (badge : Badge) (flag : Data) (hv : activeSc mr = true) :
    SKaM (invokeSchedControlConfigureFlags (Z := Unit) (.invokeSchedControlConfigureFlags p b per mr badge flag)) := by
  unfold invokeSchedControlConfigureFlags
  dsimp only
  repeat' skm_step

/-- **Configure is `BKM`** (its `REFILL_MAX` an active value, as the decode's
`extra_refills + MIN_REFILLS`). -/
theorem bkm_configure (p : ObjRef) (b per : Ticks) (k : Nat) (badge : Badge) (flag : Data) :
    BKM (invokeSchedControlConfigureFlags (Z := Unit)
      (.invokeSchedControlConfigureFlags p b per (k + MIN_REFILLS) badge flag)) :=
  bkm_of_sk (nkt_invokeSchedControlConfigureFlags _) (skm_configure p b per _ badge flag (by simp [activeSc, MIN_REFILLS]))

/-! ## The bound thread set from a state allowing it -/

/-- An SC `q` may be bound to `t`: it is active, or `t` is not IPC-blocked. -/
def ScBindOK (q t : ObjRef) (σ : State Unit) : Prop :=
  ∀ y n, σ.kheap q = some (.schedContext y n) → scActive y = true ∨
    ∀ x, σ.kheap t = some (.tcb x) → ipcQueuedThreadState x.tcbState = false

theorem ScBindOK.bk {q t : ObjRef} {σ σ' : State Unit} (h : ScBindOK q t σ) (hK : BK σ σ') : ScBindOK q t σ' := by
  intro y n hy
  by_cases ha : scActive y = true
  · exact Or.inl ha
  obtain ⟨y0, hy0, ha0, -⟩ := hK.2 q y n hy (by simpa using ha)
  rcases h y0 n hy0 with h1 | h1
  · rw [ha0] at h1; cases h1
  · refine Or.inr fun x hx => ?_
    by_contra hq
    obtain ⟨x0, hx0, hq0⟩ := hK.1 t x hx (by simpa using hq)
    rw [h1 x0 hx0] at hq0; cases hq0

/-- A `BKM` prefix keeps `ScBindOK`, so the rest may run from it. -/
theorem bka_bkm_bind {α β : Type} {q t : ObjRef} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : BKM m) (hg : ∀ a, BKA (ScBindOK q t) (g a)) : BKA (ScBindOK q t) (m >>= g) :=
  bka_bind (Q := fun _ => ScBindOK q t) (hm.toA _) (fun σ h y hy => h.bk (hm σ y hy)) hg

/-- **Bind of a TCB** (`sched_context_bind_tcb`) from a state allowing it
(the decode's `sc_released` check for an IPC-blocked thread). -/
theorem bka_schedContextBindTcb (q t : ObjRef) : BKA (ScBindOK q t) (schedContextBindTcb (Z := Unit) q t) := by
  unfold schedContextBindTcb
  refine bka_bkm_bind (bkm_of (by nkt_auto) (by mk_auto)) fun _ => ?_
  refine bka_bind (Q := fun _ _ => True) (bka_setScTcb q t) (fun _ _ _ _ => trivial) fun _ => ?_
  exact (bkm_of_sk (nkt_bind (nkt_ifCondRefillUnblockCheck _ _ _) fun _ => nkt_bind (nkt_schedContextResume _) fun _ =>
      nkt_bind (nkt_gets _) fun _ => nkt_when _ (nkt_bind (nkt_tcbSchedAction _ _) fun _ => nkt_rescheduleRequired))
    (by repeat' skm_step)).toA _

/-- **A donation** (`sched_context_donate`) from a state allowing it: the SC
active, or its new thread not IPC-blocked (each donation site's fact). -/
theorem bka_schedContextDonate (q t : ObjRef) : BKA (ScBindOK q t) (schedContextDonate (Z := Unit) q t) := by
  unfold schedContextDonate
  refine bka_bkm_bind (bkm_of (by nkt_auto) (by mk_auto)) fun fromOpt => ?_
  refine bka_bkm_bind (bkm_of ?_ (by unfold testReschedule; mk_auto)) fun _ => ?_
  · unfold testReschedule
    repeat' (first | exact nkt_rescheduleRequired | exact nkt_tcbReleaseRemove _ | nkt_step | (unfold NonDet.when; split))
  refine bka_bind (Q := fun _ _ => True) (bka_setScTcb q t) (fun _ _ _ _ => trivial) fun _ => ?_
  exact (bkm_of (by nkt_auto) (by mk_auto)).toA _

/-! ## The decode's facts at the invocation -/


/-- A read-only operation: every outcome keeps the state, its value `P`. -/
def RdN {α : Type} (P : State Unit → α → Prop) (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, x ∈ (m σ).1 → x.2 = σ ∧ P σ x.1

def RdP {α : Type} (P : State Unit → α → Prop) (m : SEMonad Unit α) : Prop :=
  ∀ σ x, x ∈ (m.run σ).1 → x.2 = σ ∧ ∀ v, x.1 = .ok v → P σ v

theorem rdp_bind {α β : Type} {Q : State Unit → α → Prop} {P : State Unit → β → Prop} {m : SEMonad Unit α}
    {f : α → SEMonad Unit β} (hm : RdP Q m) (hf : ∀ a, RdP (fun σ v => Q σ a → P σ v) (f a)) : RdP P (m >>= f) := by
  intro σ x hx
  rw [ExceptT.run_bind] at hx
  obtain ⟨⟨e, σ1⟩, hy, hx⟩ := hx
  obtain ⟨e1, hq⟩ := hm σ _ hy
  have e1' : σ1 = σ := e1
  subst σ1
  cases e with
  | error e => rw [Set.mem_singleton_iff.1 hx]; exact ⟨rfl, fun v h => by cases h⟩
  | ok a =>
    obtain ⟨e2, hp⟩ := hf a σ x hx
    exact ⟨e2, fun v hv => hp v hv (hq a rfl)⟩

theorem rdp_pure {α : Type} {P : State Unit → α → Prop} {a : α} (h : ∀ σ, P σ a) :
    RdP P (pure a : SEMonad Unit α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ⟨rfl, fun v hv => by cases hv; exact h σ⟩

theorem rdp_returnOk {α : Type} {P : State Unit → α → Prop} {a : α} (h : ∀ σ, P σ a) :
    RdP P (NonDetE.returnOk a : SEMonad Unit α) := rdp_pure h

theorem rdp_throw {α : Type} {P : State Unit → α → Prop} (e : SyscallError) :
    RdP P (NonDetE.throwError e : SEMonad Unit α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ⟨rfl, fun v hv => by cases hv⟩

theorem rdp_whenE_throw (C : Prop) [Decidable C] (e : SyscallError) :
    RdP (fun _ _ => ¬ C) (NonDetE.whenE C (NonDetE.throwError e) : SEMonad Unit Unit) := by
  unfold NonDetE.whenE; split
  · exact rdp_throw e
  · rename_i h; exact rdp_pure fun _ => h

theorem rdp_liftE {α : Type} {P : State Unit → α → Prop} {m : NonDet (State Unit) α} (h : RdN P m) :
    RdP P (NonDetE.liftE m) := by
  intro σ x hx
  unfold NonDetE.liftE at hx; rw [ExceptT.run_lift] at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hx]
  obtain ⟨e1, hp⟩ := h σ y hy
  exact ⟨e1, fun v hv => by cases hv; exact hp⟩

theorem rdn_getThreadState (t : ObjRef) :
    RdN (fun σ v => ∃ x, σ.kheap t = some (.tcb x) ∧ x.tcbState = v) (getThreadState (Z := Unit) t) := by
  intro σ x hx
  unfold getThreadState threadGet NonDet.getsThe getTcb readObject at hx
  obtain ⟨y, hy, hx⟩ := hx
  cases h : σ.kheap t with
  | none => simp [h] at hy; exact hy.elim
  | some o =>
    cases o <;> simp [h, NonDet.assertOpt] at hy <;> try exact hy.elim
    rename_i tc
    simp [NonDet.pure] at hy
    subst hy
    rw [Set.mem_singleton_iff.1 hx]
    exact ⟨rfl, tc, h, rfl⟩

theorem rdn_getSchedContext (p : ObjRef) :
    RdN (fun σ v => ∃ n, σ.kheap p = some (.schedContext v n)) (getSchedContext (Z := Unit) p) := by
  intro σ x hx
  unfold getSchedContext getObject NonDet.getsThe readObject at hx
  obtain ⟨y, hy, hx⟩ := hx
  cases h : σ.kheap p with
  | none => simp [h, NonDet.assertOpt] at hy; exact hy.elim
  | some o =>
    simp [h, NonDet.assertOpt, NonDet.pure] at hy
    subst hy
    cases o <;> simp at hx <;> try exact hx.elim
    rename_i y0 n0
    rw [Set.mem_singleton_iff.1 hx]
    exact ⟨rfl, n0, h⟩

theorem rdn_threadGet {α : Type} (g : Tcb → α) (t : ObjRef) :
    RdN (fun _ _ => True) (threadGet (Z := Unit) g t) := by
  intro σ x hx
  unfold threadGet NonDet.getsThe getTcb readObject at hx
  obtain ⟨y, hy, hx⟩ := hx
  cases h : σ.kheap t with
  | none => simp [h, NonDet.assertOpt] at hy; exact hy.elim
  | some o =>
    cases o <;> simp [h, NonDet.assertOpt] at hy <;> try exact hy.elim
    simp [NonDet.pure] at hy
    subst hy
    rw [Set.mem_singleton_iff.1 hx]
    exact ⟨rfl, trivial⟩

theorem rdn_getScReleased (p : ObjRef) :
    RdN (fun σ v => v = true → ∃ y n, σ.kheap p = some (.schedContext y n) ∧ scActive y = true)
      (getScReleased (Z := Unit) p) := by
  intro σ x hx
  unfold getScReleased NonDet.getsThe at hx
  cases h : readScReleased (Z := Unit) p σ with
  | none => rw [h] at hx; simp [NonDet.assertOpt] at hx; exact hx.elim
  | some b =>
    rw [h] at hx; simp [NonDet.assertOpt, NonDet.pure] at hx
    subst hx
    refine ⟨rfl, fun hb => ?_⟩
    simp only at hb; subst hb
    unfold readScReleased readScActive readSchedContext readObject at h
    cases hk : σ.kheap p with
    | none => simp [hk, Bind.bind, ReaderT.bind, Lookup.ofail, Lookup.oreturn, Option.bind] at h
    | some o =>
      cases o <;> simp [hk, Bind.bind, ReaderT.bind, Lookup.ofail, Lookup.oreturn, Option.bind] at h
      rename_i y n
      refine ⟨y, n, rfl, ?_⟩
      by_contra ha
      simp [ha, Lookup.oreturn] at h

theorem rdn_getNtfnObjRef (g : Notification → Option ObjRef) (p : ObjRef) :
    RdN (fun _ _ => True) (getNtfnObjRef (Z := Unit) g p) := by
  intro σ x hx
  unfold getNtfnObjRef getSkObjRef getSimpleKo getObject NonDet.getsThe readObject at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨z, hz, hy⟩ := hy
  cases h : σ.kheap p with
  | none => simp [h, NonDet.assertOpt] at hz; exact hz.elim
  | some o =>
    simp [h, NonDet.assertOpt, NonDet.pure] at hz
    subst hz
    obtain ⟨w, hw, hy⟩ := hy
    obtain ⟨-, rfl⟩ := hw
    split at hy
    · rw [Set.mem_singleton_iff.1 hy] at hx; rw [Set.mem_singleton_iff.1 hx]; exact ⟨rfl, trivial⟩
    · exact hy.elim

theorem RdP.mono {α : Type} {P Q : State Unit → α → Prop} {m : SEMonad Unit α} (h : RdP Q m)
    (hq : ∀ σ v, Q σ v → P σ v) : RdP P m :=
  fun σ x hx => ⟨(h σ x hx).1, fun v hv => hq σ v ((h σ x hx).2 v hv)⟩

theorem rdp_decodeBind (sc : ObjRef) (excaps : List Cap) :
    RdP (fun σ v => ∀ t, v = .invokeSchedContextBind sc (.threadCap t) → ScBindOK sc t σ)
      (decodeSchedContextBind (Z := Unit) sc excaps) := by
  unfold decodeSchedContextBind
  refine rdp_bind (rdp_whenE_throw _ _) fun _ => ?_
  refine rdp_bind (Q := fun _ _ => True) (rdp_returnOk fun _ => trivial) fun cap => ?_
  refine rdp_bind (rdp_liftE (rdn_getSchedContext sc)) fun sc0 => ?_
  dsimp only
  cases cap
  case threadCap t0 =>
    refine rdp_bind (rdp_whenE_throw _ _) fun _ => rdp_bind (rdp_liftE (rdn_threadGet _ _)) fun _ =>
      rdp_bind (rdp_whenE_throw _ _) fun _ => rdp_bind (rdp_liftE (rdn_getThreadState t0)) fun st =>
      rdp_bind (rdp_liftE (rdn_getScReleased sc)) fun rel => rdp_bind (rdp_whenE_throw _ _) fun _ =>
      rdp_returnOk fun σ => ?_
    intro hn hrel hst _ _ _ _ _ _ t e y n hy
    simp only [SchedContextInvocation.invokeSchedContextBind.injEq, Cap.threadCap.injEq, true_and] at e
    subst e
    by_cases hq : ipcQueuedThreadState st = true
    · left
      have hr : rel = true := by by_contra h; exact hn ⟨hq, by simpa using h⟩
      obtain ⟨y1, n1, hy1, ha⟩ := hrel hr
      rw [hy] at hy1; cases hy1; exact ha
    · right
      intro x hx
      obtain ⟨x1, hx1, e1⟩ := hst
      rw [hx] at hx1; cases hx1; simpa [e1] using hq
  case notificationCap n b r =>
    refine rdp_bind (rdp_whenE_throw _ _) fun _ => rdp_bind (rdp_liftE (rdn_getNtfnObjRef _ _)) fun _ =>
      rdp_bind (rdp_whenE_throw _ _) fun _ => rdp_returnOk fun σ => ?_
    intro _ _ _ _ _ _ t e; cases e
  all_goals exact rdp_bind (Q := fun _ _ => True) (rdp_throw _) fun _ => rdp_returnOk fun σ => by intro _ _ _ _ t e; cases e

/-- **Configure's decoded `REFILL_MAX` is `extra_refills + MIN_REFILLS`.** -/
theorem retP_configureDec (label : Data) (args : List Data) (excaps : List Cap) :
    RetP (fun v => ∃ p b per k badge flag, v = .invokeSchedControlConfigureFlags p b per (k + MIN_REFILLS) badge flag)
      (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags
  repeat (first
    | exact retP_pure ⟨_, _, _, _, _, _, rfl⟩ | exact retP_throw _
    | (refine retP_bind _ fun _ => ?_) | split | (dsimp only))

/-! ## `BlockedScActive` across the SC steps -/

/-- **The restart of a runnable thread** is a `BK` step. -/
theorem bk_restart {σ σ0 : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hr : runnable x.tcbState = true) (h : ((), σ0) ∈ (setThreadState (Z := Unit) t .restart σ).1) : BK σ σ0 := by
  have hK := tk_setThreadState hk (ipcFree_of_runnable hr) ipcFree_restart _ h
  refine ⟨hK.tcb_back, fun p y n hp ha => ?_⟩
  obtain ⟨y0, hp0, e1, e2⟩ := MaxK.mk_setThreadState' t .restart σ _ h p y n hp
  exact ⟨y0, hp0, by simpa [scActive, e1] using ha, fun t e => Or.inl (e2 ▸ e)⟩

/-- **`BlockedScActive` across Configure** (after the caller's restart). -/
theorem bsa_configure {σ σ0 σ' : State Unit} {ct : ObjRef} {xc : Tcb} (hB : BlockedScActive σ)
    (hkc : σ.kheap ct = some (.tcb xc)) (hrun : runnable xc.tcbState = true)
    (h0 : ((), σ0) ∈ (setThreadState (Z := Unit) ct .restart σ).1)
    {p : ObjRef} {b per : Ticks} {k : Nat} {badge : Badge} {flag : Data}
    (h1 : ((), σ') ∈ (invokeSchedControlConfigureFlags (Z := Unit)
      (.invokeSchedControlConfigureFlags p b per (k + MIN_REFILLS) badge flag) σ0).1) :
    BlockedScActive σ' := by
  have hB0 := hB.bk (bk_restart hkc hrun h0) (f1 := true) (pres_setThreadState (f := (true, true)) _ _ σ _ h0)
  exact hB0.bk (bkm_configure p b per k badge flag σ0 _ h1)
    (pres_invokeSchedControlConfigureFlags (true, true) _ σ0 _ h1)

/-- **`BlockedScActive` across Bind of a TCB** (after the caller's restart),
from the decode's state allowing it (`rdp_decodeBind`: the `sc_released`
check). -/
theorem bsa_bindTcb {σ σ0 σ' : State Unit} {ct : ObjRef} {xc : Tcb} (hB : BlockedScActive σ)
    (hkc : σ.kheap ct = some (.tcb xc)) (hrun : runnable xc.tcbState = true)
    (h0 : ((), σ0) ∈ (setThreadState (Z := Unit) ct .restart σ).1) {q t : ObjRef} (hok : ScBindOK q t σ)
    (h1 : ((), σ') ∈ (schedContextBindTcb (Z := Unit) q t σ0).1) : BlockedScActive σ' := by
  have hK0 := bk_restart hkc hrun h0
  have hB0 := hB.bk hK0 (f1 := true) (pres_setThreadState (f := (true, true)) _ _ σ _ h0)
  exact hB0.bk (bka_schedContextBindTcb q t σ0 (hok.bk hK0) _ h1)
    (pres_schedContextBindTcb (f := (true, true)) _ _ σ0 _ h1)

/-- **`BlockedScActive` across a donation** from a state allowing it (each
site: the SC active or the new thread not IPC-blocked). -/
theorem pres_schedContextDonate (f : Bool × Bool) (q t : ObjRef) : Pres f (schedContextDonate (Z := Unit) q t) := by
  unfold schedContextDonate testReschedule
  repeat' (first | exact pres_rescheduleRequired _ | exact pres_tcbReleaseRemove _ _ | exact pres_tcbSchedAction _ _ _ | pres_step | (unfold NonDet.when; split))

theorem bsa_donate {σ σ' : State Unit} (hB : BlockedScActive σ) {q t : ObjRef} (hok : ScBindOK q t σ)
    (h : ((), σ') ∈ (schedContextDonate (Z := Unit) q t σ).1) : BlockedScActive σ' :=
  hB.bk (bka_schedContextDonate q t σ hok _ h) (f1 := true) (pres_schedContextDonate (true, true) _ _ σ _ h)

/-! ## The SchedContext invocations -/

theorem bk_of_tk_sk {P : ObjRef → Prop} {σ σ' : State Unit} (hK : ScTKw P σ σ') (hs : SKa σ σ') : BK σ σ' := by
  refine ⟨hK.tcb_back, fun p y n hp ha => ?_⟩
  obtain ⟨y0, hp0, e1, e2⟩ := hs p y n hp
  refine ⟨y0, hp0, e2 ha, fun t e => ?_⟩
  rcases e1 with e1 | e1
  · exact Or.inl (e1 ▸ e)
  · rw [e1] at e; cases e

set_option maxHeartbeats 1000000 in
theorem skm_unbindTcb (q : ObjRef) : SKaM (schedContextUnbindTcb (Z := Unit) q) := by
  unfold schedContextUnbindTcb; repeat' skm_step
theorem skm_bindNtfn (q n : ObjRef) : SKaM (schedContextBindNtfn (Z := Unit) q n) := by
  unfold schedContextBindNtfn; repeat' skm_step
theorem skm_unbindNtfn (q : ObjRef) : SKaM (schedContextUnbindNtfn (Z := Unit) q) := by
  unfold schedContextUnbindNtfn; repeat' skm_step
set_option maxHeartbeats 2000000 in
theorem skm_yieldTo (q : ObjRef) : SKaM (schedContextYieldTo (Z := Unit) q) := by
  unfold schedContextYieldTo completeYieldTo setConsumed schedContextCancelYieldTo returnConsumed replyFromKernel
  repeat' skm_step

/-- **`BK` across a SchedContext invocation** of Bind, UnbindObject or
YieldTo (an `ScTKw` step), Bind of a TCB from a state allowing it. -/
theorem bk_invokeSchedContext {P : ObjRef → Prop} {σ0 σ1 : State Unit} {inv : SchedContextInvocation}
    {data : List Data} (hm : (data, σ1) ∈ (invokeSchedContext (Z := Unit) inv σ0).1) (hK : ScTKw P σ0 σ1)
    (hinv : (∃ q cap, inv = .invokeSchedContextBind q cap) ∨ (∃ q cap, inv = .invokeSchedContextUnbindObject q cap) ∨
      (∃ q, inv = .invokeSchedContextYieldTo q))
    (hbind : ∀ q t, inv = .invokeSchedContextBind q (.threadCap t) → ScBindOK q t σ0) : BK σ0 σ1 := by
  have sk : ∀ {m : NonDet (State Unit) Unit}, SKaM m → (data, σ1) ∈ ((m >>= fun _ => pure ([] : List Data)) σ0).1 →
      BK σ0 σ1 := fun h hx => by
    obtain ⟨y, hy, hx⟩ := hx
    have e : σ1 = y.2 := congrArg Prod.snd (Set.mem_singleton_iff.1 hx)
    subst e
    exact bk_of_tk_sk hK (h σ0 y hy)
  rcases hinv with ⟨q, cap, rfl⟩ | ⟨q, cap, rfl⟩ | ⟨q, rfl⟩
  · unfold invokeSchedContext at hm
    cases cap
    case threadCap t =>
      obtain ⟨y, hy, hx⟩ := hm
      have e : σ1 = y.2 := congrArg Prod.snd (Set.mem_singleton_iff.1 hx)
      subst e
      exact bka_schedContextBindTcb q t σ0 (hbind q t rfl) y hy
    case notificationCap n b r => exact sk (skm_bindNtfn q n) hm
    all_goals exact hm.elim
  · unfold invokeSchedContext at hm
    cases cap
    case threadCap t => exact sk (skm_unbindTcb q) hm
    case notificationCap n b r => exact sk (skm_unbindNtfn q) hm
    all_goals exact hm.elim
  · exact bk_of_tk_sk hK (skm_yieldTo q σ0 _ hm)

end

end Fl4Proofs.P3.Sched
