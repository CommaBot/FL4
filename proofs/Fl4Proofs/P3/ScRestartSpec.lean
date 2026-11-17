/-
P3 (DESIGN.md §9), scheduling contexts: **the spec facts of `restart`'s
first steps** (`RestartSpecOK`, IpcResumeJ; spec side only).

* `IK t σ σ'`: every object keeps its kind among TCBs, SCs and
  notifications; a TCB keeps its SC and (but at `t`) its state; an SC keeps
  its refills, `REFILL_MAX`, period and thread; a notification its SC; the
  ready and release queues and the time are kept. With `t` in no queue,
  `InvBut _ t` is kept (`InvBut.ik`).
* `IKM t m`: every outcome of `m` is `IK t`-related to its start;
  `cancel_ipc t` and `set_thread_state t` are (`ikm_cancelIpc`,
  `ikm_setThreadState`).
* `restartSpecOK_of`: from `Inv` and a stopped thread, `RestartSpecOK`
  (`InvBut.unblock` for the sporadic unblock check, `InvBut.resume` for the
  SC's resume).
-/
import Fl4Proofs.P3.IpcResumeJ
import Fl4Proofs.P3.ScMidKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical Fl4Proofs.P3.Notif

noncomputable section

/-! ## The relation -/

/-- The SC fields `Inv` reads. -/
def ScIK (y y' : SchedContext) : Prop :=
  y'.scRefills = y.scRefills ∧ y'.scRefillMax = y.scRefillMax ∧ y'.scPeriod = y.scPeriod ∧ y'.scTcb = y.scTcb ∧
    y'.scSporadic = y.scSporadic

theorem ScIK.refl (y : SchedContext) : ScIK y y := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ScIK.trans {a b c : SchedContext} (h1 : ScIK a b) (h2 : ScIK b c) : ScIK a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.trans h1.2.2.2.2⟩

/-- An object step of `cancel_ipc` (module docstring); `k`: the state kept. -/
def IKObj (k : Prop) (o o' : KernelObject) : Prop :=
  (∀ x, o = .tcb x → ∃ y, o' = .tcb y ∧ y.tcbSchedContext = x.tcbSchedContext ∧ (k → y.tcbState = x.tcbState)) ∧
  (∀ y n, o = .schedContext y n → ∃ y', o' = .schedContext y' n ∧ ScIK y y') ∧
  (∀ x, o = .notification x → ∃ y, o' = .notification y ∧ y.ntfnSc = x.ntfnSc) ∧
  (∀ y, o' = .tcb y → ∃ x, o = .tcb x) ∧ (∀ y n, o' = .schedContext y n → ∃ x m, o = .schedContext x m) ∧
  (∀ y, o' = .notification y → ∃ x, o = .notification x)

theorem IKObj.refl (k : Prop) (o : KernelObject) : IKObj k o o :=
  ⟨fun x e => ⟨x, e, rfl, fun _ => rfl⟩, fun y n e => ⟨y, e, ScIK.refl y⟩, fun x e => ⟨x, e, rfl⟩,
    fun y e => ⟨y, e⟩, fun y n e => ⟨y, n, e⟩, fun y e => ⟨y, e⟩⟩

theorem IKObj.trans {k : Prop} {a b c : KernelObject} (h1 : IKObj k a b) (h2 : IKObj k b c) : IKObj k a c := by
  refine ⟨fun x e => ?_, fun y n e => ?_, fun x e => ?_, fun y e => ?_, fun y n e => ?_, fun y e => ?_⟩
  · obtain ⟨y, rfl, e1, f1⟩ := h1.1 x e
    obtain ⟨z, rfl, e2, f2⟩ := h2.1 y rfl
    exact ⟨z, rfl, e2.trans e1, fun hk => (f2 hk).trans (f1 hk)⟩
  · obtain ⟨y', rfl, e1⟩ := h1.2.1 y n e
    obtain ⟨z, rfl, e2⟩ := h2.2.1 y' n rfl
    exact ⟨z, rfl, e1.trans e2⟩
  · obtain ⟨y, rfl, e1⟩ := h1.2.2.1 x e
    obtain ⟨z, rfl, e2⟩ := h2.2.2.1 y rfl
    exact ⟨z, rfl, e2.trans e1⟩
  · obtain ⟨x, rfl⟩ := h2.2.2.2.1 y e; exact h1.2.2.2.1 x rfl
  · obtain ⟨x, m, rfl⟩ := h2.2.2.2.2.1 y n e; exact h1.2.2.2.2.1 x m rfl
  · obtain ⟨x, rfl⟩ := h2.2.2.2.2.2 y e; exact h1.2.2.2.2.2 x rfl

/-- An object of none of the three kinds steps to one of none of them. -/
theorem IKObj.other {k : Prop} {o o' : KernelObject} (h : ∀ o0, o0 = o ∨ o0 = o' →
    (∀ x, o0 ≠ .tcb x) ∧ (∀ y n, o0 ≠ .schedContext y n) ∧ (∀ x, o0 ≠ .notification x)) : IKObj k o o' := by
  obtain ⟨a1, a2, a3⟩ := h o (Or.inl rfl)
  obtain ⟨b1, b2, b3⟩ := h o' (Or.inr rfl)
  exact ⟨fun x e => absurd e (a1 x), fun y n e => absurd e (a2 y n), fun x e => absurd e (a3 x),
    fun y e => absurd e (b1 y), fun y n e => absurd e (b2 y n), fun y e => absurd e (b3 y)⟩

def OIK (k : Prop) : Option KernelObject → Option KernelObject → Prop
  | none, none => True
  | some a, some b => IKObj k a b
  | _, _ => False

theorem OIK.refl (k : Prop) (o : Option KernelObject) : OIK k o o := by
  cases o
  · trivial
  · exact IKObj.refl _ _

theorem OIK.trans {k : Prop} {a b c : Option KernelObject} (h1 : OIK k a b) (h2 : OIK k b c) : OIK k a c := by
  cases a <;> cases b <;> cases c <;> simp only [OIK] at h1 h2 ⊢
  exact h1.trans h2

/-- **The `cancel_ipc` step** (module docstring). -/
def IK (t : ObjRef) (σ σ' : State Unit) : Prop :=
  (∀ p, OIK (p ≠ t) (σ.kheap p) (σ'.kheap p)) ∧ σ'.readyQueues = σ.readyQueues ∧
    σ'.releaseQueue = σ.releaseQueue ∧ σ'.curTime = σ.curTime

theorem IK.refl (t : ObjRef) (σ : State Unit) : IK t σ σ := ⟨fun _ => OIK.refl _ _, rfl, rfl, rfl⟩

theorem IK.trans {t : ObjRef} {σ1 σ2 σ3 : State Unit} (h1 : IK t σ1 σ2) (h2 : IK t σ2 σ3) : IK t σ1 σ3 :=
  ⟨fun p => (h1.1 p).trans (h2.1 p), h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

/-- An update at `p` with an `IKObj`-related object. -/
theorem IK.upd {t : ObjRef} {σ : State Unit} {p : ObjRef} {o o' : KernelObject} (hk : σ.kheap p = some o)
    (h : IKObj (p ≠ t) o o') : IK t σ { σ with kheap := Function.update σ.kheap p (some o') } := by
  refine ⟨fun q => ?_, rfl, rfl, rfl⟩
  by_cases e : q = p
  · subst e; simp only [Function.update_self, hk, OIK]; exact h
  · simp only [Function.update_of_ne e]; exact OIK.refl _ _

section Look
variable {t : ObjRef} {σ σ' : State Unit}

theorem IK.obj (h : IK t σ σ') (p : ObjRef) {o' : KernelObject} (ho : σ'.kheap p = some o') :
    ∃ o, σ.kheap p = some o ∧ IKObj (p ≠ t) o o' := by
  have := h.1 p
  rw [ho] at this
  cases e : σ.kheap p with
  | none => rw [e] at this; exact this.elim
  | some o => rw [e] at this; exact ⟨o, rfl, this⟩

theorem IK.objF (h : IK t σ σ') (p : ObjRef) {o : KernelObject} (ho : σ.kheap p = some o) :
    ∃ o', σ'.kheap p = some o' ∧ IKObj (p ≠ t) o o' := by
  have := h.1 p
  rw [ho] at this
  cases e : σ'.kheap p with
  | none => rw [e] at this; exact this.elim
  | some o' => rw [e] at this; exact ⟨o', rfl, this⟩

theorem IK.tcbF (h : IK t σ σ') {p : ObjRef} {x : Tcb} (hk : σ.kheap p = some (.tcb x)) :
    ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbSchedContext = x.tcbSchedContext ∧ (p ≠ t → y.tcbState = x.tcbState) := by
  obtain ⟨o', ho', hr⟩ := h.objF p hk
  obtain ⟨y, rfl, h1, h2⟩ := hr.1 x rfl
  exact ⟨y, ho', h1, h2⟩

theorem IK.tcbB (h : IK t σ σ') {p : ObjRef} {y : Tcb} (hk : σ'.kheap p = some (.tcb y)) :
    ∃ x, σ.kheap p = some (.tcb x) ∧ y.tcbSchedContext = x.tcbSchedContext ∧ (p ≠ t → y.tcbState = x.tcbState) := by
  obtain ⟨o, ho, hr⟩ := h.obj p hk
  obtain ⟨x, rfl⟩ := hr.2.2.2.1 y rfl
  obtain ⟨y', e, h1, h2⟩ := hr.1 x rfl
  cases e
  exact ⟨x, ho, h1, h2⟩

theorem IK.scF (h : IK t σ σ') {p : ObjRef} {y : SchedContext} {n : Nat} (hk : σ.kheap p = some (.schedContext y n)) :
    ∃ y', σ'.kheap p = some (.schedContext y' n) ∧ ScIK y y' := by
  obtain ⟨o', ho', hr⟩ := h.objF p hk
  obtain ⟨y', rfl, h1⟩ := hr.2.1 y n rfl
  exact ⟨y', ho', h1⟩

theorem IK.scB (h : IK t σ σ') {p : ObjRef} {y' : SchedContext} {n : Nat} (hk : σ'.kheap p = some (.schedContext y' n)) :
    ∃ y, σ.kheap p = some (.schedContext y n) ∧ ScIK y y' := by
  obtain ⟨o, ho, hr⟩ := h.obj p hk
  obtain ⟨x, m, rfl⟩ := hr.2.2.2.2.1 y' n rfl
  obtain ⟨z, e, h1⟩ := hr.2.1 x m rfl
  cases e
  exact ⟨x, ho, h1⟩

theorem IK.ntfnB (h : IK t σ σ') {p : ObjRef} {y : Notification} (hk : σ'.kheap p = some (.notification y)) :
    ∃ x, σ.kheap p = some (.notification x) ∧ y.ntfnSc = x.ntfnSc := by
  obtain ⟨o, ho, hr⟩ := h.obj p hk
  obtain ⟨x, rfl⟩ := hr.2.2.2.2.2 y rfl
  obtain ⟨z, e, h1⟩ := hr.2.2.1 x rfl
  cases e
  exact ⟨x, ho, h1⟩

end Look

theorem ScIK.active {y y' : SchedContext} (h : ScIK y y') : scActive y' = scActive y := by
  unfold scActive; rw [h.2.1]

theorem ScIK.hd {y y' : SchedContext} (h : ScIK y y') : refillHd y' = refillHd y := by
  unfold refillHd; rw [h.1]

/-- **`InvBut` across an `IK` step**, the thread in no queue. -/
theorem InvBut.ik {t : ObjRef} {σ σ' : State Unit} (h : InvBut σ t) (hq : NotQueued σ t) (hk : IK t σ σ') :
    InvBut σ' t ∧ NotQueued σ' t := by
  have hrq := hk.2.1
  have hrl := hk.2.2.1
  have htm := hk.2.2.2
  have hnq : NotQueued σ' t := ⟨fun d p => by rw [hrq]; exact hq.1 d p, by rw [hrl]; exact hq.2⟩
  -- a queued thread's facts
  have qd : ∀ u, u ≠ t → ∀ x scp y n, σ.kheap u = some (.tcb x) → x.tcbSchedContext = some scp →
      runnable x.tcbState = true → σ.kheap scp = some (.schedContext y n) → scActive y = true →
      ∃ x scp y n, σ'.kheap u = some (.tcb x) ∧ x.tcbSchedContext = some scp ∧
        runnable x.tcbState = true ∧ σ'.kheap scp = some (.schedContext y n) ∧ scActive y = true := by
    intro u hu x scp y n h1 h2 h3 h4 h5
    obtain ⟨x', k1, e1, f1⟩ := hk.tcbF h1
    obtain ⟨y', k2, e2⟩ := hk.scF h4
    exact ⟨x', scp, y', n, k1, by rw [e1]; exact h2, by rw [f1 hu]; exact h3, k2, by rw [e2.active]; exact h5⟩
  refine ⟨⟨fun d p u hu => ?_, fun u hu => ?_, ?_, fun u x hut hx hc => ?_, fun p y n hy => ?_,
    fun u x p hx hp => ?_, fun q x p hx hp => ?_, fun p y n hy => ?_, fun p y n hy => ?_⟩, hnq⟩
  · rw [hrq] at hu
    obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5⟩ := h.rq d p u hu
    exact qd u (fun e => hq.1 d p (e ▸ hu)) x scp y n h1 h2 h3 h4 h5
  · rw [hrl] at hu
    obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5⟩ := h.rel u hu
    exact qd u (fun e => hq.2 (e ▸ hu)) x scp y n h1 h2 h3 h4 h5
  · rw [hrl]
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    have rt : ∀ u ∈ σ.releaseQueue, specRt σ' u = specRt σ u := by
      intro u hu
      obtain ⟨x, scp, y, n, h1, h2, -, h4, h5⟩ := h.rel u hu
      obtain ⟨x', k1, e1, -⟩ := hk.tcbF h1
      obtain ⟨y', k2, e2⟩ := hk.scF h4
      have hne := h.ne _ _ _ h4 h5
      rw [specRt_eq k1 (by rw [e1]; exact h2) k2 (by rw [e2.1]; exact hne), specRt_eq h1 h2 h4 hne, e2.hd]
    rw [rt a ha, rt b hb]; exact hab
  · obtain ⟨x0, k0, e0, f0⟩ := hk.tcbB hx
    intro x' scp y n h1 h2 h3 h4 h5
    rw [hx] at h1; cases h1
    obtain ⟨y0, k3, e3⟩ := hk.scB h3
    rw [hrl] at h5
    rw [released_congr htm]
    unfold released; rw [e3.hd]
    exact h.rd u x0 hut k0 (by rw [← f0 hut]; exact hc) x0 scp y0 n k0 (by rw [← e0]; exact h2) k3
      (by rw [← e3.active]; exact h4) h5
  · obtain ⟨y0, k0, e0⟩ := hk.scB hy
    intro ha hp
    have r := h.refills p y0 n k0 (by rw [← e0.active]; exact ha) (by rw [← e0.2.2.1]; exact hp)
    unfold RefOK at r ⊢; rw [e0.hd, e0.1]; exact r
  · obtain ⟨x0, k0, e0, -⟩ := hk.tcbB hx
    obtain ⟨y, n, k1, e1⟩ := h.back u x0 p k0 (by rw [← e0]; exact hp)
    obtain ⟨y', k2, e2⟩ := hk.scF k1
    exact ⟨y', n, k2, by rw [e2.2.2.2.1]; exact e1⟩
  · obtain ⟨x0, k0, e0⟩ := hk.ntfnB hx
    obtain ⟨y, n, k1⟩ := h.ntfnSc q x0 p k0 (by rw [← e0]; exact hp)
    obtain ⟨y', k2, -⟩ := hk.scF k1
    exact ⟨y', n, k2⟩
  · obtain ⟨y0, k0, e0⟩ := hk.scB hy
    intro ha
    rw [e0.1]; exact h.ne p y0 n k0 (by rw [← e0.active]; exact ha)
  · obtain ⟨y0, k0, e0⟩ := hk.scB hy
    intro ha hp
    exact RRok.of_refills (h.rr p y0 n k0 (by rw [← e0.active]; exact ha) (by rw [← e0.2.2.1]; exact hp)) e0.1

/-! ## The monad -/

section Comb
variable {t : ObjRef}

def IKM (t : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → IK t σ x.2

theorem IKM.of_eq {α : Type} {m : NonDet (State Unit) α} (hP : IKM t m) {σ σ' : State Unit} {a : α} {X : Prop}
    (h : m σ = ({(a, σ')}, X)) : IK t σ σ' :=
  hP σ (a, σ') (by rw [h]; exact Set.mem_singleton _)

theorem ikm_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : IKM t m)
    (hg : ∀ a, IKM t (g a)) : IKM t (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem ikm_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : IKM t m)
    (hg : ∀ a, IKM t (g a)) : IKM t (NonDet.bind m g) := ikm_bind hm hg

theorem ikm_of_rdo {α : Type} {m : NonDet (State Unit) α} (h : RdO m) : IKM t m :=
  fun σ x hx => by rw [h σ x hx]; exact IK.refl t σ

theorem ikm_pure {α : Type} (a : α) : IKM t (pure a : NonDet (State Unit) α) := ikm_of_rdo (rdo_pure a)
theorem ikm_pure' {α : Type} (a : α) : IKM t (NonDet.pure a : NonDet (State Unit) α) := ikm_of_rdo (rdo_pure' a)
theorem ikm_gets {α : Type} (g : State Unit → α) : IKM t (NonDet.gets g) := ikm_of_rdo (rdo_gets g)
theorem ikm_assert (P : Prop) : IKM t (NonDet.assert P : NonDet (State Unit) Unit) := ikm_of_rdo (rdo_assert P)
theorem ikm_fail {α : Type} : IKM t (NonDet.fail : NonDet (State Unit) α) := ikm_of_rdo rdo_fail
theorem ikm_assertOpt {α : Type} (o : Option α) : IKM t (NonDet.assertOpt o : NonDet (State Unit) α) :=
  ikm_of_rdo (rdo_assertOpt o)
theorem ikm_getsThe {α : Type} (g : State Unit → Option α) : IKM t (NonDet.getsThe g) := ikm_of_rdo (rdo_getsThe g)
theorem ikm_getObject (p : ObjRef) : IKM t (getObject (Z := Unit) p) := ikm_getsThe _

theorem ikm_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : IKM t m1)
    (h2 : IKM t m2) : IKM t (if P then m1 else m2) := by
  split <;> assumption

theorem ikm_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : IKM t m) : IKM t (NonDet.when P m) := by
  unfold NonDet.when; exact ikm_ite P h (ikm_pure' _)

theorem ikm_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : IKM t m) : IKM t (NonDet.liftM g m) :=
  ikm_bind' h fun _ => ikm_pure' _

theorem ikm_modify {g : State Unit → State Unit}
    (hg : ∀ σ, (g σ).kheap = σ.kheap ∧ (g σ).readyQueues = σ.readyQueues ∧ (g σ).releaseQueue = σ.releaseQueue ∧
      (g σ).curTime = σ.curTime) : IKM t (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]
  obtain ⟨e1, e2, e3, e4⟩ := hg σ
  exact ⟨fun p => by rw [e1]; exact OIK.refl _ _, e2, e3, e4⟩

theorem ikm_threadSet {g : Tcb → Tcb} {p : ObjRef}
    (hg : ∀ x, (g x).tcbSchedContext = x.tcbSchedContext ∧ (p ≠ t → (g x).tcbState = x.tcbState)) :
    IKM t (threadSet (Z := Unit) g p) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getsThe_getTcb_mem hy
  rw [hs] at hx
  obtain ⟨k, hk', -, e⟩ := setObject_mem hx
  rw [hk] at hk'; cases hk'
  rw [e]
  refine IK.upd hk ⟨fun x' e' => ?_, fun _ _ e' => (by cases e'), fun _ e' => (by cases e'), fun _ _ => ⟨_, rfl⟩,
    fun _ _ e' => (by cases e'), fun _ e' => by cases e'⟩
  cases e'
  exact ⟨_, rfl, (hg _).1, (hg _).2⟩

theorem ikm_updateSchedContext {g : SchedContext → SchedContext} (hg : ∀ y, ScIK y (g y)) (p : ObjRef) :
    IKM t (updateSchedContext (Z := Unit) p g) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getObject_mem hy
  obtain ⟨o, σ1⟩ := y
  simp only at hk hs hx; subst σ1
  cases o
  all_goals try exact hx.elim
  obtain ⟨k, hk', -, e⟩ := setObject_mem hx
  rw [hk] at hk'; cases hk'
  rw [e]
  exact IK.upd hk ⟨fun _ e' => (by cases e'), fun y' n' e' => by cases e'; exact ⟨_, rfl, hg _⟩, fun _ e' => (by cases e'),
    fun _ e' => (by cases e'), fun _ _ _ => ⟨_, _, rfl⟩, fun _ e' => by cases e'⟩

/-- The kinds the relation constrains. -/
def NotTSN (o : KernelObject) : Prop := (∀ x, o ≠ .tcb x) ∧ (∀ y n, o ≠ .schedContext y n) ∧ ∀ x, o ≠ .notification x

theorem ikm_setSimpleKo {α : Type} [Nonempty α] {C : α → KernelObject} (hC : ∀ a, NotTSN (C a)) (p : ObjRef) (e : α) :
    IKM t (setSimpleKo (Z := Unit) C p e) := by
  intro σ x hx
  unfold setSimpleKo at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨hk, hs⟩ := getObject_mem hy1
  rw [hs] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hy2
  obtain ⟨y3, hy3, hx⟩ := hx
  obtain ⟨hne, rfl⟩ := hy3
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hne
  have hC0 := partialInv_eq ha
  obtain ⟨k, hk', -, e'⟩ := setObject_mem hx
  rw [e']
  refine IK.upd hk (IKObj.other fun o0 h0 => ?_)
  rcases h0 with rfl | rfl
  · rw [← hC0]; exact hC a
  · exact hC e

theorem ikm_updateSkObjRef {α : Type} [Nonempty α] {C : α → KernelObject} (hC : ∀ a, NotTSN (C a))
    (g : (Option ObjRef → Option ObjRef) → α → α) (ref : ObjRef) (new : Option ObjRef) :
    IKM t (updateSkObjRef (Z := Unit) C g ref new) := by
  unfold updateSkObjRef getSimpleKo
  refine ikm_bind (ikm_bind (ikm_getObject _) fun _ => ikm_bind (ikm_assert _) fun _ => ?_) fun _ =>
    ikm_setSimpleKo hC _ _
  split
  · exact ikm_pure _
  · exact ikm_fail

theorem notTSN_ep (x : Endpoint) : NotTSN (.endpoint x) :=
  ⟨fun _ e => (by cases e), fun _ _ e => (by cases e), fun _ e => by cases e⟩
theorem notTSN_reply (x : Reply) : NotTSN (.reply x) :=
  ⟨fun _ e => (by cases e), fun _ _ e => (by cases e), fun _ e => by cases e⟩

end Comb

macro "ikm_step0" : tactic => `(tactic| first
  | with_reducible exact ikm_pure _ | with_reducible exact ikm_pure' _ | with_reducible exact ikm_fail
  | with_reducible exact ikm_gets _ | with_reducible exact ikm_assert _ | with_reducible exact ikm_assertOpt _
  | with_reducible exact ikm_getObject _ | with_reducible exact ikm_getsThe _
  | ((with_reducible apply ikm_modify); intro _; exact ⟨rfl, rfl, rfl, rfl⟩)
  | ((with_reducible apply ikm_threadSet); intro _; exact ⟨rfl, fun _ => rfl⟩)
  | ((with_reducible apply ikm_threadSet); intro _; exact ⟨rfl, fun h => absurd rfl h⟩)
  | ((with_reducible apply ikm_updateSchedContext); intro _; exact ScIK.refl _)
  | (with_reducible exact ikm_setSimpleKo notTSN_ep _ _)
  | (with_reducible exact ikm_updateSkObjRef notTSN_reply _ _ _)
  | (with_reducible refine ikm_bind ?_ (fun _ => ?_))
  | (with_reducible refine ikm_bind' ?_ (fun _ => ?_))
  | (with_reducible apply ikm_ite) | (with_reducible apply ikm_when) | (with_reducible apply ikm_liftM)
  | split
  | (dsimp only))

section Ops
variable {t : ObjRef}

theorem ikm_threadGet {α : Type} (g : Tcb → α) (p : ObjRef) : IKM t (threadGet (Z := Unit) g p) :=
  ikm_of_rdo (RdO.ofRdN (rdn_threadGet g p))

theorem ikm_getSchedContext (p : ObjRef) : IKM t (getSchedContext (Z := Unit) p) :=
  ikm_of_rdo (RdO.ofRdN (rdn_getSchedContext p))

/-- `get_simple_ko`'s value is the object there. -/
theorem rdn_getSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (p : ObjRef) :
    RdN (fun σ v => σ.kheap p = some (C v)) (getSimpleKo (Z := Unit) C p) := by
  intro σ x hx
  unfold getSimpleKo at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨hk, hs⟩ := getObject_mem hy1
  rw [hs] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hy2
  cases he : partialInv C y1.1 with
  | none => simp only [he] at hx; exact hx.elim
  | some e =>
    simp only [he] at hx
    rw [Set.mem_singleton_iff.1 hx]
    exact ⟨rfl, by show σ.kheap p = some (C e); rw [hk, partialInv_eq he]⟩

theorem rdo_getSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (p : ObjRef) :
    RdO (getSimpleKo (Z := Unit) C p) := RdO.ofRdN (rdn_getSimpleKo C p)

macro "ikm_step" : tactic => `(tactic| first
  | with_reducible exact ikm_threadGet _ _ | with_reducible exact ikm_getSchedContext _
  | with_reducible exact ikm_of_rdo (rdo_getSimpleKo _ _) | ikm_step0)

theorem ikm_setThreadState (ts : ThreadState) : IKM t (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction
  repeat ikm_step

/-- `tcb_ntfn_dequeue` keeps the notification's SC. -/
theorem ikm_tcbNtfnDequeue (u n : ObjRef) : IKM t (tcbNtfnDequeue (Z := Unit) u n) := by
  intro σ x hx
  unfold tcbNtfnDequeue at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨e1, hk⟩ := rdn_getSimpleKo _ _ σ y1 hy1
  rw [e1] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  rw [rdo_pure _ σ y2 hy2] at hx
  obtain ⟨y3, hy3, hx⟩ := hx
  rw [rdo_assert _ σ y3 hy3] at hx
  obtain ⟨y4, hy4, hx⟩ := hx
  rw [rdo_pure _ σ y4 hy4] at hx
  obtain ⟨y5, hy5, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy5] at hx
  dsimp only [setSimpleKo] at hx
  obtain ⟨z1, hz1, hx⟩ := hx
  obtain ⟨hk1, hs1⟩ := getObject_mem hz1
  rw [hs1] at hx
  obtain ⟨z2, hz2, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hz2
  obtain ⟨z3, hz3, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hz3
  obtain ⟨k, hk', -, e'⟩ := setObject_mem hx
  rw [e']
  refine IK.upd hk ⟨fun _ e => (by cases e), fun _ _ e => (by cases e), fun x0 e => ?_, fun _ e => (by cases e),
    fun _ _ e => (by cases e), fun _ _ => ⟨_, rfl⟩⟩
  cases e
  exact ⟨_, rfl, rfl⟩

theorem ikm_replyUnlinkTcb (r : ObjRef) : IKM t (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState
  repeat (first | exact ikm_setThreadState _ | ikm_step)

theorem ikm_cancelSignal (n : ObjRef) : IKM t (cancelSignal (Z := Unit) t n) := by
  unfold cancelSignal
  exact ikm_bind (ikm_tcbNtfnDequeue _ _) fun _ => ikm_setThreadState _

theorem ikm_blockedCancelIpc (ts : ThreadState) (o : Option ObjRef) :
    IKM t (blockedCancelIpc (Z := Unit) ts t o) := by
  unfold blockedCancelIpc getBlockingObject tcbEpDequeue
  repeat (first | exact ikm_setThreadState _ | exact ikm_replyUnlinkTcb _ | ikm_step)

theorem ikm_replyRemoveTcb (r : ObjRef) : IKM t (replyRemoveTcb (Z := Unit) t r) := by
  unfold replyRemoveTcb getThreadState getReplyObjRef getSkObjRef
  repeat (first | exact ikm_replyUnlinkTcb _ | ikm_step)

/-- **`cancel_ipc t` is an `IK t` step.** -/
theorem ikm_cancelIpc : IKM t (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState
  repeat (first | exact ikm_blockedCancelIpc _ _ | exact ikm_cancelSignal _ | exact ikm_replyRemoveTcb _ | ikm_step)

end Ops

/-! ## `RestartSpecOK` -/

/-- The sporadic unblock check of `restart`: nothing, or the SC is sporadic
and `refill_unblock_check` ran. -/
theorem unblockTest_cases {σ σ' : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) {r : Unit}
    (hm : (r, σ') ∈ (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) (some p) σ).1) :
    σ' = σ ∨ (y.scSporadic = true ∧ (r, σ') ∈ (refillUnblockCheck (Z := Unit) p σ).1) := by
  change (r, σ') ∈ (ifCondRefillUnblockCheck (Z := Unit) (some p) (some false) (some false) σ).1 at hm
  unfold ifCondRefillUnblockCheck NonDet.maybeM at hm
  dsimp only at hm
  rw [nd_bind_one (getSchedContext_eq hk), Notif.nd_gets_bind, Notif.nd_pure_bind'] at hm
  unfold NonDet.when at hm
  split at hm
  · rename_i hc
    split at hm
    · exact Or.inr ⟨by simpa using hc.1, hm⟩
    · left; exact congrArg Prod.snd (Set.mem_singleton_iff.1 hm)
  · left; exact congrArg Prod.snd (Set.mem_singleton_iff.1 hm)

/-- **`RestartSpecOK` from `Inv`** and sporadic SCs active (`ScLinkHyp.scSpor`). -/
theorem restartSpecOK_of {t : ObjRef} {σ : State Unit} (hI : Inv σ)
    (hsp : ∀ p y n, σ.kheap p = some (.schedContext y n) → y.scSporadic = true → scActive y = true) :
    Ipc.RestartSpecOK t σ := by
  intro x σa σb σc hk hnr hca hstb hu
  have hnq : NotQueued σ t := by
    refine ⟨fun d p hm => ?_, fun hm => ?_⟩
    · obtain ⟨x', -, -, -, h1, -, h3, -⟩ := hI.rq d p t hm; rw [hk] at h1; cases h1; rw [hnr] at h3; cases h3
    · obtain ⟨x', -, -, -, h1, -, h3, -⟩ := hI.rel t hm; rw [hk] at h1; cases h1; rw [hnr] at h3; cases h3
  have ha : IK t σ σa := ikm_cancelIpc.of_eq hca
  have hb : IK t σa σb := (ikm_setThreadState .restart).of_eq hstb
  have hab := ha.trans hb
  obtain ⟨hIb, hnqb⟩ := (hI.toBut t).ik hnq hab
  have hspb : ∀ p y n, σb.kheap p = some (.schedContext y n) → y.scSporadic = true → scActive y = true := by
    intro p y n hy hs
    obtain ⟨y0, k0, e0⟩ := hab.scB hy
    rw [e0.active]; exact hsp p y0 n k0 (by rw [← e0.2.2.2.2]; exact hs)
  -- the thread at `σb`: restarted, its SC kept
  obtain ⟨xb, hkb, hxb, -⟩ := hab.tcbF hk
  have hrunb : runnable xb.tcbState = true := by
    obtain ⟨xa, hka, -, -⟩ := ha.tcbF hk
    have e := the_result (Notif.setThreadState_eq .restart hka) hstb
    rw [e, stsAct_kheap] at hkb; simp [updK] at hkb; rw [← hkb]; rfl
  have hm : ((), σc) ∈ (ifSporadicCurScTestRefillUnblockCheck (Z := Unit) x.tcbSchedContext σb).1 := by
    rw [hu]; exact Set.mem_singleton _
  -- the unblock check: `InvBut`, the queues and the thread kept
  have hc : InvBut σc t ∧ NotQueued σc t ∧ σc.kheap t = σb.kheap t := by
    cases hxs : x.tcbSchedContext with
    | none =>
      rw [hxs] at hm
      change ((), σc) ∈ (ifCondRefillUnblockCheck (Z := Unit) none (some false) (some false) σb).1 at hm
      unfold ifCondRefillUnblockCheck NonDet.maybeM at hm
      have e := congrArg Prod.snd (Set.mem_singleton_iff.1 hm)
      simp only at e
      rw [e]; exact ⟨hIb, hnqb, rfl⟩
    | some p =>
      rw [hxs] at hm
      obtain ⟨y, n, hky, hyt⟩ := hIb.back t xb p hkb (by rw [hxb, hxs])
      rcases unblockTest_cases hky hm with e | ⟨hsy, hm'⟩
      · rw [e]; exact ⟨hIb, hnqb, rfl⟩
      have hne : y.scRefills ≠ [] := hIb.ne p y n hky (hspb p y n hky hsy)
      refine ⟨hIb.unblock hky hne (fun _ _ u hu xu hku hsu => ?_) hm', ?_⟩
      · obtain ⟨y', n', hky', hyu⟩ := hIb.back u xu p hku hsu
        rw [hky] at hky'; cases hky'
        rw [hyt] at hyu; cases hyu
        exact hnqb.2 hu
      have hpt : p ≠ t := fun e => by rw [e, hkb] at hky; cases hky
      rcases unblock_result hky hne hm' with ⟨e, -⟩ | ⟨z, e, -⟩
      · rw [e]; exact ⟨hnqb, rfl⟩
      · rw [e]
        exact ⟨⟨fun d q => hnqb.1 d q, hnqb.2⟩, by simp [updSc, updK, Ne.symm hpt]⟩
  obtain ⟨hIc, hnqc, hktc⟩ := hc
  have hkc : σc.kheap t = some (.tcb xb) := by rw [hktc]; exact hkb
  refine ⟨⟨fun u hu => ?_, hIc.sorted, fun u hu xu p hku hsu => ?_⟩, fun xc p hkc' hsc => ?_, fun σd hd => ?_⟩
  · obtain ⟨xu, p, -, -, h1, h2, -⟩ := hIc.rel u hu; exact ⟨xu, p, h1, h2⟩
  · obtain ⟨xu', p', y, n, h1, h2, -, h4, h5⟩ := hIc.rel u hu
    rw [hku] at h1; cases h1; rw [hsu] at h2; cases h2; exact ⟨y, n, h4, h5⟩
  · exact hIc.back t xc p hkc' hsc
  · cases hxs : x.tcbSchedContext with
    | none =>
      rw [hxs] at hd
      unfold NonDet.maybeM at hd
      have e : σc = σd := congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hd))
      subst e
      refine hIc.inv fun xc hxc _ => ?_
      intro x' scp y n h1 h2
      rw [hkc] at h1; cases h1; rw [hxb, hxs] at h2; cases h2
    | some p =>
      rw [hxs] at hd
      obtain ⟨y, n, hky, hyt⟩ := hIc.back t xb p hkc (by rw [hxb, hxs])
      exact hIc.resume hky hyt hkc (by rw [hxb, hxs]) hnqc (fun h => by rw [hrunb] at h; cases h) hd

end

end Fl4Proofs.P3.Sched
