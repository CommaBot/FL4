/-
P3 (DESIGN.md §9), scheduling contexts: **the spec's SC step of
SetSchedParams** (`ScSpecHyp`, ScTcbHyp.lean).

* `VK σ σ'`: what the scheduler-view of `ActReady` reads is kept: every TCB
  stays a TCB with its state and SC, the SC objects, the current thread and
  time and the release queue are unchanged, and the scheduler action is kept
  or becomes `choose_new_thread`. `PresV`: every outcome of a step is `VK`;
  `VK.actReady`: `ActReady` carries over.
* `presV_setMcpriority`, `presV_setPriority`: `set_mcpriority` and
  `set_priority` are `PresV`.
* `scStep_some_none`, `scStep_some_unbind`: the SC step with no SC change or
  with the unbind (l4v `sched_context_unbind_tcb`) has an outcome, from
  `ActReady` and the thread's SC back-link.
* `scSpecHyp_of`: `ScSpecHyp` from the facts after the install for an unbind
  (`hS2`: the target's TCB with its SC, the SC's back-link, `ActReady`) and
  the spec's SC bind (`BindSpecHyp`).
-/
import Fl4Proofs.P3.ScTcbHyp
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Classical

noncomputable section

section Spec
open Fl4Spec

/-- **What `ActReady` reads, kept** (module docstring). -/
structure VK (σ σ' : State Unit) : Prop where
  tcb : ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbState = x.tcbState ∧
    y.tcbSchedContext = x.tcbSchedContext
  tcb' : ∀ p y, σ'.kheap p = some (.tcb y) → ∃ x, σ.kheap p = some (.tcb x)
  sc : ∀ p y n, σ'.kheap p = some (.schedContext y n) ↔ σ.kheap p = some (.schedContext y n)
  ct : σ'.curThread = σ.curThread
  tm : σ'.curTime = σ.curTime
  rq : σ'.releaseQueue = σ.releaseQueue
  act : σ'.schedulerAction = σ.schedulerAction ∨ σ'.schedulerAction = .chooseNewThread

theorem VK.refl (σ : State Unit) : VK σ σ :=
  ⟨fun _ x h => ⟨x, h, rfl, rfl⟩, fun _ y h => ⟨y, h⟩, fun _ _ _ => Iff.rfl, rfl, rfl, rfl, Or.inl rfl⟩

theorem VK.trans {σ1 σ2 σ3 : State Unit} (h1 : VK σ1 σ2) (h2 : VK σ2 σ3) : VK σ1 σ3 := by
  refine ⟨fun p x hx => ?_, fun p y hy => ?_, fun p y n => (h2.sc p y n).trans (h1.sc p y n),
    h2.ct.trans h1.ct, h2.tm.trans h1.tm, h2.rq.trans h1.rq, ?_⟩
  · obtain ⟨y, hy, e1, e2⟩ := h1.tcb p x hx
    obtain ⟨z, hz, f1, f2⟩ := h2.tcb p y hy
    exact ⟨z, hz, f1.trans e1, f2.trans e2⟩
  · obtain ⟨x, hx⟩ := h2.tcb' p y hy
    exact h1.tcb' p x hx
  · rcases h2.act with e | e
    · rw [e]; exact h1.act
    · exact Or.inr e

/-- An object update that is neither a TCB nor an SC, to another such. -/
theorem VK.updOther {σ : State Unit} {p : ObjRef} {o o' : KernelObject} (hk : σ.kheap p = some o)
    (h1 : ∀ x, o ≠ .tcb x) (h2 : ∀ y n, o ≠ .schedContext y n) (h1' : ∀ x, o' ≠ .tcb x)
    (h2' : ∀ y n, o' ≠ .schedContext y n) : VK σ (Notif.updK σ p o') := by
  refine ⟨fun q x hq => ?_, fun q y hq => ?_, fun q y n => ?_, rfl, rfl, rfl, Or.inl rfl⟩
  · have hne : q ≠ p := by rintro rfl; rw [hk] at hq; exact h1 x (Option.some.inj hq)
    exact ⟨x, by simp only [Notif.updK, Function.update_of_ne hne]; exact hq, rfl, rfl⟩
  · by_cases e : q = p
    · subst e; simp only [Notif.updK, Function.update_self, Option.some.injEq] at hq; exact absurd hq (h1' y)
    · exact ⟨y, by simp only [Notif.updK, Function.update_of_ne e] at hq; exact hq⟩
  · by_cases e : q = p
    · subst e
      simp only [Notif.updK, Function.update_self, Option.some.injEq, hk]
      exact ⟨fun h => absurd h (h2' y n), fun h => absurd h (h2 y n)⟩
    · simp only [Notif.updK, Function.update_of_ne e]

/-- A TCB update keeping the state and the SC. -/
theorem VK.updTcb {σ : State Unit} {p : ObjRef} {x y : Tcb} (hk : σ.kheap p = some (.tcb x))
    (hst : y.tcbState = x.tcbState) (hsc : y.tcbSchedContext = x.tcbSchedContext) :
    VK σ (Notif.updK σ p (.tcb y)) := by
  refine ⟨fun q x' hq => ?_, fun q y' hq => ?_, fun q y' n => ?_, rfl, rfl, rfl, Or.inl rfl⟩
  · by_cases e : q = p
    · subst e; rw [hk] at hq; cases hq; exact ⟨y, by simp [Notif.updK], hst, hsc⟩
    · exact ⟨x', by simp only [Notif.updK, Function.update_of_ne e]; exact hq, rfl, rfl⟩
  · by_cases e : q = p
    · subst e; exact ⟨x, hk⟩
    · exact ⟨y', by simp only [Notif.updK, Function.update_of_ne e] at hq; exact hq⟩
  · by_cases e : q = p
    · subst e; simp [Notif.updK, hk]
    · simp only [Notif.updK, Function.update_of_ne e]

/-- **`ActReady` across a `VK` step.** -/
theorem VK.actReady {σ σ' : State Unit} (h : Notif.ActReady σ) (hv : VK σ σ') : Notif.ActReady σ' := by
  intro u hu hs
  have hu' : σ.schedulerAction = .switchThread u := by
    rcases hv.act with e | e
    · rw [← e]; exact hu
    · rw [e] at hu; cases hu
  have htc : (tcbsOf σ' u).map (fun z => (runnable z.tcbState, z.tcbSchedContext)) =
      (tcbsOf σ u).map (fun z => (runnable z.tcbState, z.tcbSchedContext)) := by
    rw [tcbsOf_eq, tcbsOf_eq]
    cases hk : σ.kheap u with
    | some o =>
      cases o with
      | tcb x =>
        obtain ⟨y, hy, e1, e2⟩ := hv.tcb u x hk
        rw [hy]; simp [e1, e2]
      | _ =>
        cases hk' : σ'.kheap u with
        | none => rfl
        | some o' =>
          cases o' with
          | tcb y => obtain ⟨x, hx⟩ := hv.tcb' u y hk'; rw [hk] at hx; cases hx
          | _ => rfl
    | none =>
      cases hk' : σ'.kheap u with
      | none => rfl
      | some o' =>
        cases o' with
        | tcb y => obtain ⟨x, hx⟩ := hv.tcb' u y hk'; rw [hk] at hx; cases hx
        | _ => rfl
  have hscs : ∀ p, Option.map scActive (scsOf σ' p) = Option.map scActive (scsOf σ p) := by
    intro p
    rw [scsOf_eq, scsOf_eq]
    cases hk' : σ'.kheap p with
    | some o' =>
      cases o' with
      | schedContext y n => rw [(hv.sc p y n).1 hk']
      | _ =>
        cases hk : σ.kheap p with
        | none => rfl
        | some o =>
          cases o with
          | schedContext y n => have := (hv.sc p y n).2 hk; rw [hk'] at this; cases this
          | _ => rfl
    | none =>
      cases hk : σ.kheap p with
      | none => rfl
      | some o =>
        cases o with
        | schedContext y n => have := (hv.sc p y n).2 hk; rw [hk'] at this; cases this
        | _ => rfl
  have hs0 : schedulable u σ = true := by rw [← schedulable_upd htc hscs hv.rq]; exact hs
  obtain ⟨x0, scp, hk1, hsc1, h1, h2⟩ := h u hu' hs0
  obtain ⟨yy, n, hky, hne, hsuff⟩ := suff_inv h1
  have hrdy := ready_inv h2 hky hne
  have hky' := (hv.sc scp yy n).2 hky
  obtain ⟨x', hx', -, hsx'⟩ := hv.tcb u x0 hk1
  refine ⟨x', scp, hx', by rw [hsx', hsc1], ?_, ?_⟩
  · rw [getScRefillSufficient_eq hky' hne, hsuff]
  · rw [getScRefillReady_eq hky' hne, hv.tm, hrdy]

/-! ### `PresV` -/

/-- Every outcome is `VK`. -/
def PresV {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → VK σ x.2

theorem presV_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : PresV m)
    (hg : ∀ a, PresV (g a)) : PresV (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem presV_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : PresV m)
    (hg : ∀ a, PresV (g a)) : PresV (NonDet.bind m g) := presV_bind hm hg

theorem presV_pure {α : Type} (a : α) : PresV (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact VK.refl σ

theorem presV_pure' {α : Type} (a : α) : PresV (NonDet.pure a : NonDet (State Unit) α) := presV_pure a

theorem presV_gets {α : Type} (g : State Unit → α) : PresV (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact VK.refl σ

theorem presV_assert (P : Prop) : PresV (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact VK.refl σ

theorem presV_fail {α : Type} : PresV (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem presV_assertOpt {α : Type} (o : Option α) : PresV (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact presV_fail
  · exact presV_pure' _

theorem presV_getsThe {α : Type} (g : State Unit → Option α) : PresV (NonDet.getsThe g) := by
  intro σ x hx; exact presV_assertOpt (g σ) σ x hx

theorem presV_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : PresV m1)
    (h2 : PresV m2) : PresV (if P then m1 else m2) := by
  split <;> assumption

theorem presV_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : PresV m) :
    PresV (NonDet.when P m) := by
  unfold NonDet.when; exact presV_ite P h (presV_pure' _)

theorem presV_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, PresV (g a)) (o : Option α) :
    PresV (NonDet.maybeM g o) := by
  cases o
  · exact presV_pure' _
  · exact h _

theorem presV_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, PresV (g a)) (xs : List α) :
    PresV (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact presV_pure' _
  | cons a xs' ih => exact presV_bind' (h a) fun _ => presV_bind' ih fun _ => presV_pure' _

theorem presV_modify {g : State Unit → State Unit}
    (hg : ∀ σ, (g σ).kheap = σ.kheap ∧ (g σ).curThread = σ.curThread ∧ (g σ).curTime = σ.curTime ∧
      (g σ).releaseQueue = σ.releaseQueue ∧
      ((g σ).schedulerAction = σ.schedulerAction ∨ (g σ).schedulerAction = .chooseNewThread)) :
    PresV (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]
  obtain ⟨e1, e2, e3, e4, e5⟩ := hg σ
  exact ⟨fun p x h => ⟨x, by rw [e1]; exact h, rfl, rfl⟩, fun p y h => ⟨y, by rw [e1] at h; exact h⟩,
    fun p y n => by rw [e1], e2, e3, e4, e5⟩

theorem presV_threadSet {g : Tcb → Tcb} (hg1 : ∀ x, (g x).tcbState = x.tcbState)
    (hg2 : ∀ x, (g x).tcbSchedContext = x.tcbSchedContext) (t : ObjRef) : PresV (threadSet (Z := Unit) g t) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getsThe_getTcb_mem hy
  rw [hs] at hx
  obtain ⟨k, hk', -, e⟩ := setObject_mem hx
  rw [hk] at hk'; cases hk'
  rw [e]; exact VK.updTcb hk (hg1 _) (hg2 _)

/-- `set_object` of an endpoint or a notification (over one of the same type). -/
theorem presV_setObject_ep (p : ObjRef) (ep : Endpoint) : PresV (setObject (Z := Unit) p (.endpoint ep)) := by
  intro σ x hx
  obtain ⟨k, hk, hty, e⟩ := setObject_mem hx
  rw [e]
  cases k <;> simp only [aType, reduceCtorEq] at hty
  all_goals first | (split_ifs at hty) | skip
  exact VK.updOther hk (fun _ => by simp) (fun _ _ => by simp) (fun _ => by simp) (fun _ _ => by simp)

theorem presV_setObject_ntfn (p : ObjRef) (n : Notification) :
    PresV (setObject (Z := Unit) p (.notification n)) := by
  intro σ x hx
  obtain ⟨k, hk, hty, e⟩ := setObject_mem hx
  rw [e]
  cases k <;> simp only [aType, reduceCtorEq] at hty
  all_goals first | (split_ifs at hty) | skip
  exact VK.updOther hk (fun _ => by simp) (fun _ _ => by simp) (fun _ => by simp) (fun _ _ => by simp)

theorem presV_getObject (p : ObjRef) : PresV (getObject (Z := Unit) p) := presV_getsThe _

theorem presV_threadGet {α : Type} (g : Tcb → α) (p : ObjRef) : PresV (threadGet (Z := Unit) g p) := by
  unfold threadGet; exact presV_bind (presV_getsThe _) fun _ => presV_pure _

theorem presV_getSimpleKo {α : Type} [Nonempty α] (C : α → KernelObject) (p : ObjRef) :
    PresV (getSimpleKo (Z := Unit) C p) := by
  unfold getSimpleKo
  refine presV_bind (presV_getObject _) fun _ => presV_bind (presV_assert _) fun _ => ?_
  split
  · exact presV_pure _
  · exact presV_fail

theorem presV_tcbSchedAction (a : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    PresV (tcbSchedAction (Z := Unit) a t) := by
  unfold tcbSchedAction getTcbQueue setTcbQueue
  refine presV_bind (presV_threadGet _ _) fun _ => presV_bind (presV_threadGet _ _) fun _ =>
    presV_bind (presV_bind (presV_gets _) fun _ => presV_pure _) fun _ => presV_bind (presV_pure _) fun _ => ?_
  exact presV_modify fun σ => ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩

theorem presV_rescheduleRequired : PresV (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired setSchedulerAction getScRefillSufficient getScRefillReady
  repeat (first
    | exact presV_pure _ | exact presV_pure' _ | exact presV_gets _ | exact presV_getsThe _
    | exact presV_assert _ | exact presV_assertOpt _ | exact presV_threadGet _ _ | exact presV_tcbSchedAction _ _
    | (apply presV_modify; intro σ; exact ⟨rfl, rfl, rfl, rfl, Or.inr rfl⟩)
    | (refine presV_bind ?_ (fun _ => ?_)) | (refine presV_bind' ?_ (fun _ => ?_))
    | (apply presV_when) | split | (dsimp only))

theorem presV_tcbAppend (t : ObjRef) (qs : List ObjRef) : PresV (tcbAppend (Z := Unit) t qs) := by
  unfold tcbAppend orderedInsert
  exact presV_bind (presV_getsThe _) fun _ => presV_bind (presV_mapM (fun _ => presV_getsThe _) _) fun _ =>
    presV_bind (presV_pure _) fun _ => presV_bind (presV_pure _) fun _ => presV_pure _

theorem presV_reorderEp (e t : ObjRef) : PresV (reorderEp (Z := Unit) e t) := by
  unfold reorderEp
  refine presV_bind (presV_getSimpleKo _ _) fun _ => presV_bind (presV_assert _) fun _ =>
    presV_bind (presV_pure _) fun _ => presV_bind (presV_assert _) fun _ =>
    presV_bind (presV_pure _) fun _ => presV_bind (presV_tcbAppend _ _) fun _ => ?_
  show PresV (setSimpleKo (Z := Unit) KernelObject.endpoint e _)
  unfold setSimpleKo
  exact presV_bind (presV_getObject _) fun _ => presV_bind (presV_assert _) fun _ =>
    presV_bind (presV_assert _) fun _ => presV_setObject_ep _ _

theorem presV_reorderNtfn (n t : ObjRef) : PresV (reorderNtfn (Z := Unit) n t) := by
  unfold reorderNtfn
  refine presV_bind (presV_getSimpleKo _ _) fun _ => presV_bind (presV_assert _) fun _ =>
    presV_bind (presV_pure _) fun _ => presV_bind (presV_assert _) fun _ =>
    presV_bind (presV_pure _) fun _ => presV_bind (presV_tcbAppend _ _) fun _ => ?_
  show PresV (setSimpleKo (Z := Unit) KernelObject.notification n _)
  unfold setSimpleKo
  exact presV_bind (presV_getObject _) fun _ => presV_bind (presV_assert _) fun _ =>
    presV_bind (presV_assert _) fun _ => presV_setObject_ntfn _ _

theorem presV_setMcpriority (t : ObjRef) (m : Priority) : PresV (setMcpriority (Z := Unit) t m) :=
  presV_threadSet (g := fun tcb => { tcb with tcbMcpriority := m }) (fun _ => rfl) (fun _ => rfl) t

theorem presV_threadSetPriority (t : ObjRef) (pr : Priority) : PresV (threadSetPriority (Z := Unit) t pr) :=
  presV_threadSet (g := fun tcb => { tcb with tcbPriority := pr }) (fun _ => rfl) (fun _ => rfl) t

/-- **`set_priority` keeps what `ActReady` reads.** -/
theorem presV_setPriority (t : ObjRef) (pr : Priority) : PresV (setPriority (Z := Unit) t pr) := by
  unfold setPriority getThreadState
  refine presV_bind (presV_threadGet _ _) fun ts => ?_
  split
  · refine presV_bind (presV_threadGet _ _) fun _ => presV_bind (presV_threadGet _ _) fun _ => ?_
    unfold getTcbQueue
    refine presV_bind (presV_bind (presV_gets _) fun _ => presV_pure _) fun _ => presV_bind (presV_gets _) fun _ => ?_
    split
    · exact presV_bind (presV_tcbSchedAction _ _) fun _ => presV_bind (presV_threadSetPriority _ _) fun _ =>
        presV_bind (presV_tcbSchedAction _ _) fun _ => presV_rescheduleRequired
    · exact presV_threadSetPriority _ _
  · exact presV_bind (presV_threadSetPriority _ _) fun _ =>
      presV_bind (presV_maybeM (fun e => presV_reorderEp e t) _) fun _ =>
      presV_maybeM (fun n => presV_reorderNtfn n t) _

/-! ### The SC step -/

theorem tcbReleaseRemove_one (σ : State Unit) (t : ObjRef) :
    ∃ σ', tcbReleaseRemove (Z := Unit) t σ = ({((), σ')}, False) ∧ σ'.kheap = σ.kheap := by
  unfold tcbReleaseRemove
  rw [Notif.nd_gets_bind]
  unfold NonDet.when
  split
  · rw [nd_bind_one (show NonDet.modify (fun s : State Unit => { s with reprogramTimer := true }) σ =
      ({((), { σ with reprogramTimer := true })}, False) from rfl), Notif.nd_pure_bind']
    exact ⟨_, rfl, rfl⟩
  · rw [nd_bind_one (show NonDet.pure (σ := State Unit) () σ = ({((), σ)}, False) from rfl), Notif.nd_pure_bind']
    exact ⟨_, rfl, rfl⟩

/-- **The spec's SC unbind has an outcome**, from `ActReady` and the SC's
back-link to the thread. -/
theorem schedContextUnbindTcb_some {σ : State Unit} {t c : ObjRef} {x : Tcb} {y : SchedContext} {n : Nat}
    (hA : Notif.ActReady σ) (hkt : σ.kheap t = some (.tcb x)) (hks : σ.kheap c = some (.schedContext y n))
    (hy : y.scTcb = some t) : ∃ σ', ((), σ') ∈ (schedContextUnbindTcb (Z := Unit) c σ).1 := by
  unfold schedContextUnbindTcb
  rw [nd_bind_one (getSchedContext_eq hks), hy,
    nd_bind_one (show NonDet.assertOpt (σ := State Unit) (some t) σ = ({(t, σ)}, False) from rfl),
    Notif.nd_gets_bind]
  have hct : t ≠ c := by rintro rfl; rw [hkt] at hks; cases hks
  have tail : ∀ σr : State Unit, σr.kheap = σ.kheap → ∃ σ', ((), σ') ∈ ((do
      tcbSchedAction tcbSchedDequeue t
      tcbReleaseRemove t
      setTcbObjRef tcbSchedContextUpdate t none
      setScObjRef scTcbUpdate c none : SMonad Unit Unit) σr).1 := by
    intro σr hkr
    have hkt' : σr.kheap t = some (.tcb x) := by rw [hkr]; exact hkt
    rw [nd_bind_one (tcbSchedAction_gen hkt' _)]
    obtain ⟨σ2, h2, hk2⟩ := tcbReleaseRemove_one (setQ σr x.tcbDomain x.tcbPriority
      (tcbSchedDequeue t (σr.readyQueues x.tcbDomain x.tcbPriority))) t
    rw [nd_bind_one h2]
    have hkt2 : σ2.kheap t = some (.tcb x) := by rw [hk2]; exact hkt'
    rw [nd_bind_one (Notif.threadSet_eq _ hkt2)]
    have hks3 : (Notif.updK σ2 t (.tcb (tcbSchedContextUpdate (fun _ => none) x))).kheap c =
        some (.schedContext y n) := by
      simp only [Notif.updK, Function.update_of_ne (Ne.symm hct)]; rw [hk2]; simp [setQ, hkr, hks]
    exact ⟨_, by
      show _ ∈ (updateSchedContext (Z := Unit) c _ _).1
      rw [updateSchedContext_eq hks3]; exact Set.mem_singleton _⟩
  unfold NonDet.when
  split
  · obtain ⟨σr, hr, hq⟩ := rescheduleRequired_qchange hA
    rw [nd_bind_one hr]
    exact tail σr hq.1
  · rw [nd_bind_one (show NonDet.pure (σ := State Unit) () σ = ({((), σ)}, False) from rfl)]
    exact tail σ rfl

theorem scStep_some_none (t : ObjRef) (σ : State Unit) : ∃ σc, ((), σc) ∈ (scStep t none σ).1 :=
  ⟨σ, Set.mem_singleton _⟩

/-- **The SC step with the unbind has an outcome.** -/
theorem scStep_some_unbind {σ : State Unit} {t c : ObjRef} {x : Tcb} {y : SchedContext} {n : Nat}
    (hA : Notif.ActReady σ) (hkt : σ.kheap t = some (.tcb x)) (hsc : x.tcbSchedContext = some c)
    (hks : σ.kheap c = some (.schedContext y n)) (hy : y.scTcb = some t) :
    ∃ σc, ((), σc) ∈ (scStep t (some none) σ).1 := by
  show ∃ σc, _ ∈ ((getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t >>= fun o =>
    NonDet.assertOpt o >>= fun c => schedContextUnbindTcb c) σ).1
  rw [nd_bind_one (m := getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t) (Notif.threadGet_eq _ hkt), hsc,
    nd_bind_one (show NonDet.assertOpt (σ := State Unit) (some c) σ = ({(c, σ)}, False) from rfl)]
  exact schedContextUnbindTcb_some hA hkt hks hy

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The spec's SC bind of SetSchedParams** (for the SC bind's spec
outcome): `ScSpecHyp` at a bind. -/
def BindSpecHyp (s : S) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  ∀ (s1 : S) (σ1 : Fl4Spec.State Unit) (a : A) (p mcp prio scv x2 : U64) (scf : Bool) (ssl : Fl4Spec.CslotPtr)
    (fh : Fl4Spec.Cap × Fl4Spec.CslotPtr) (v : Fl4Spec.ObjRef)
    (s2 : S) (a1 : A) (σ2 σa σb : Fl4Spec.State Unit),
    sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
    scf = true → v = scv.bv → scv ≠ 0#u64 →
    tcb.install_tcb_cap st arI s1 a p (cslotAddr ssl) layout.tcb.SLOT_FAULT_HANDLER (capV (L.mem s) x2) x2 =
      ok (.Ok (), s2, a1) →
    (.ok (), σ2) ∈ ((Fl4Spec.installTcbCap (Z := Unit) p.bv ssl 3 (some fh)).run σ1).1 →
    ((), σa) ∈ (Fl4Spec.setMcpriority (Z := Unit) p.bv (Fl4Spec.ucast 8 mcp.bv) σ2).1 →
    ((), σb) ∈ (Fl4Spec.setPriority (Z := Unit) p.bv (Fl4Spec.ucast 8 prio.bv) σa).1 →
    ∃ σc, ((), σc) ∈ (scStep p.bv (some (some v)) σb).1

/-- **`ScSpecHyp` from the facts after the install and the SC bind**: no SC
change, or the unbind (`scStep_some_unbind`, its facts carried from the
install's state across `set_mcpriority` and `set_priority` by `PresV`);
the bind is `BindSpecHyp`. -/
theorem scSpecHyp_of (s : S) (σ : Fl4Spec.State Unit) (ct : U64)
    (hS2 : ∀ (s1 : S) (σ1 : Fl4Spec.State Unit) (a : A) (p x2 : U64) (ssl : Fl4Spec.CslotPtr)
      (fh : Fl4Spec.Cap × Fl4Spec.CslotPtr) (sco : Option (Option Fl4Spec.ObjRef)) (s2 : S) (a1 : A)
      (σ2 : Fl4Spec.State Unit),
      sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
      tcb.install_tcb_cap st arI s1 a p (cslotAddr ssl) layout.tcb.SLOT_FAULT_HANDLER (capV (L.mem s) x2) x2 =
        ok (.Ok (), s2, a1) →
      (.ok (), σ2) ∈ ((Fl4Spec.installTcbCap (Z := Unit) p.bv ssl 3 (some fh)).run σ1).1 →
      sco = some none →
      ∃ x c y n, σ2.kheap p.bv = some (.tcb x) ∧ Notif.ActReady σ2 ∧ x.tcbSchedContext = some c ∧
        σ2.kheap c = some (.schedContext y n) ∧ y.scTcb = some p.bv)
    (hBind : BindSpecHyp (L := L) arI s σ ct) :
    ScSpecHyp (L := L) arI s σ ct := by
  intro s1 σ1 a p mcp prio scv x2 scf ssl fh sco s2 a1 σ2 σa σb hs1 hst1 h1 h2 h3 hins hx ha hb
  cases sco with
  | none => exact scStep_some_none _ _
  | some o =>
    cases o with
    | some v =>
      have hscf : scf = true := by
        cases scf
        · exact absurd (h1.2 rfl) (by simp)
        · rfl
      obtain ⟨e1, e2⟩ := h3 v rfl
      exact hBind s1 σ1 a p mcp prio scv x2 scf ssl fh v s2 a1 σ2 σa σb hs1 hst1 hscf e1 e2 hins hx ha hb
    | none =>
      obtain ⟨x, c, y, n, hk2, hA2, hc, hks, hy⟩ := hS2 s1 σ1 a p x2 ssl fh (some none) s2 a1 σ2 hs1 hst1 hins hx rfl
      have hv : VK σ2 σb := (presV_setMcpriority _ _ σ2 _ ha).trans (presV_setPriority _ _ σa _ hb)
      obtain ⟨xb, hkb, -, hscb⟩ := hv.tcb _ x hk2
      exact scStep_some_unbind (hv.actReady hA2) hkb (by rw [hscb, hc]) ((hv.sc c y n).2 hks) hy

end

end

end Fl4Proofs.P3.Sched
