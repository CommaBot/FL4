/-
P3 (DESIGN.md §9), scheduling contexts: **the current thread's facts across
an SC invocation** (the SC steps' mid-entry facts, spec side only).

* `MidK σ σ'`: the current thread, SC, time and idle thread kept; the
  consumed time kept or cleared; a pending reschedule kept pending, no new
  switch-thread action; the current and the idle thread's SC and state kept;
  the current SC an SC of the same size with the same thread, active if it
  was, its refills kept while the consumed time is not cleared; the release
  queue's new members neither the idle thread nor the current one (unless
  the consumed time is cleared and a reschedule is pending). Reflexive,
  transitive.
* `MidKA P m`: every outcome of `m` from a state satisfying `P` is `MidK`-related
  to its start; `P` is `MidK`-stable along a `bind` (`MidKStable`). The object
  updates: `mka_threadSet`, `mka_updateSchedContext`, `mka_updateSkObjRef`.
* `MidK.mid`: from `MidK σ σ'` and the current thread's invariants at `σ`
  (`CurInv`, `OffOK`, `ActIdle`, `Inv`'s back-pointer, a resume action): the
  mid-entry facts at `σ'` (`CurInvW`, `CurOwn` under a pending reschedule,
  `OffOK`, `ActIdle`).
-/
import Fl4Proofs.P3.ScCurKeep
import Fl4Proofs.P3.ScLinkKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

/-! ## The relation -/

/-- The thread at `p`: its SC and state kept. -/
def MidT (σ σ' : State Unit) (p : ObjRef) : Prop :=
  ∀ x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbSchedContext = x.tcbSchedContext ∧
    y.tcbState = x.tcbState

theorem MidT.refl (σ : State Unit) (p : ObjRef) : MidT σ σ p := fun x h => ⟨x, h, rfl, rfl⟩

theorem MidT.trans {σ1 σ2 σ3 : State Unit} {p : ObjRef} (h1 : MidT σ1 σ2 p) (h2 : MidT σ2 σ3 p) : MidT σ1 σ3 p := by
  intro x hx
  obtain ⟨y, hy, e1, f1⟩ := h1 x hx
  obtain ⟨z, hz, e2, f2⟩ := h2 y hy
  exact ⟨z, hz, e2.trans e1, f2.trans f1⟩

/-- **The current thread's step** (module docstring). -/
structure MidK (σ σ' : State Unit) : Prop where
  ct : σ'.curThread = σ.curThread
  csc : σ'.curSc = σ.curSc
  time : σ'.curTime = σ.curTime
  idle : σ'.idleThread = σ.idleThread
  cons : σ'.consumedTime = σ.consumedTime ∨ σ'.consumedTime = 0
  cn : σ.schedulerAction = .chooseNewThread → σ'.schedulerAction = .chooseNewThread
  sw : ∀ t, σ'.schedulerAction = .switchThread t → σ.schedulerAction = .switchThread t
  ctT : MidT σ σ' σ.curThread
  idT : MidT σ σ' σ.idleThread
  cscS : ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → ∃ y', σ'.kheap σ.curSc = some (.schedContext y' n) ∧
    y'.scTcb = y.scTcb ∧ (scActive y = true → scActive y' = true) ∧
    (σ'.consumedTime ≠ 0 → y'.scRefills = y.scRefills)
  rq : ∀ t ∈ σ'.releaseQueue, t ∈ σ.releaseQueue ∨
    (t ≠ σ.idleThread ∧ (t ≠ σ.curThread ∨ (σ'.consumedTime = 0 ∧ σ'.schedulerAction = .chooseNewThread)))

theorem MidK.refl (σ : State Unit) : MidK σ σ :=
  ⟨rfl, rfl, rfl, rfl, Or.inl rfl, id, fun _ h => h, MidT.refl _ _, MidT.refl _ _,
    fun y _ h => ⟨y, h, rfl, id, fun _ => rfl⟩, fun _ h => Or.inl h⟩

theorem MidK.cons0 {σ σ' : State Unit} (h : MidK σ σ') (h0 : σ.consumedTime = 0) : σ'.consumedTime = 0 := by
  rcases h.cons with e | e
  · rw [e, h0]
  · exact e

theorem MidK.consNe {σ σ' : State Unit} (h : MidK σ σ') (h0 : σ'.consumedTime ≠ 0) :
    σ'.consumedTime = σ.consumedTime :=
  h.cons.resolve_right h0

theorem MidK.trans {σ1 σ2 σ3 : State Unit} (h1 : MidK σ1 σ2) (h2 : MidK σ2 σ3) : MidK σ1 σ3 := by
  refine ⟨h2.ct.trans h1.ct, h2.csc.trans h1.csc, h2.time.trans h1.time, h2.idle.trans h1.idle, ?_,
    fun h => h2.cn (h1.cn h), fun t h => h1.sw t (h2.sw t h), ?_, ?_, ?_, ?_⟩
  · rcases h2.cons with e | e
    · rw [e]; exact h1.cons
    · exact Or.inr e
  · have := h2.ctT; rw [h1.ct] at this; exact h1.ctT.trans this
  · have := h2.idT; rw [h1.idle] at this; exact h1.idT.trans this
  · intro y n hy
    obtain ⟨y2, hy2, e1, f1, g1⟩ := h1.cscS y n hy
    have c2 := h2.cscS; rw [h1.csc] at c2
    obtain ⟨y3, hy3, e2, f2, g2⟩ := c2 y2 n hy2
    exact ⟨y3, hy3, e2.trans e1, fun h => f2 (f1 h), fun h => (g2 h).trans (g1 (fun e => h (h2.cons0 e)))⟩
  · intro t ht
    rcases h2.rq t ht with h | ⟨hi, hc⟩
    · rcases h1.rq t h with h' | ⟨hi', hc'⟩
      · exact Or.inl h'
      · refine Or.inr ⟨hi', ?_⟩
        rcases hc' with e | ⟨e1, e2⟩
        · exact Or.inl e
        · exact Or.inr ⟨h2.cons0 e1, h2.cn e2⟩
    · rw [h1.idle] at hi; rw [h1.ct] at hc
      exact Or.inr ⟨hi, hc⟩

/-- An object update: the current and idle threads' SC and state kept, the
current SC's thread, activity and (with consumed time) refills kept. -/
theorem MidK.upd {σ : State Unit} {p : ObjRef} {o o' : KernelObject} (hk : σ.kheap p = some o)
    (ht : ∀ x, o = .tcb x → (p = σ.curThread ∨ p = σ.idleThread) →
      ∃ y, o' = .tcb y ∧ y.tcbSchedContext = x.tcbSchedContext ∧ y.tcbState = x.tcbState)
    (hs : ∀ y n, o = .schedContext y n → p = σ.curSc → ∃ y', o' = .schedContext y' n ∧ y'.scTcb = y.scTcb ∧
      (scActive y = true → scActive y' = true) ∧ (σ.consumedTime ≠ 0 → y'.scRefills = y.scRefills)) :
    MidK σ { σ with kheap := Function.update σ.kheap p (some o') } := by
  have tk : ∀ q, (q = σ.curThread ∨ q = σ.idleThread) → MidT σ { σ with kheap := Function.update σ.kheap p (some o') } q := by
    intro q hq x hx
    by_cases e : q = p
    · subst e
      rw [hk] at hx; cases hx
      obtain ⟨y, rfl, h1, h2⟩ := ht x rfl hq
      exact ⟨y, by simp, h1, h2⟩
    · exact ⟨x, by simp [Function.update_of_ne e, hx], rfl, rfl⟩
  refine ⟨rfl, rfl, rfl, rfl, Or.inl rfl, id, fun _ h => h, tk _ (Or.inl rfl), tk _ (Or.inr rfl), fun y n hy => ?_,
    fun _ h => Or.inl h⟩
  by_cases e : σ.curSc = p
  · rw [e] at hy ⊢
    rw [hk] at hy; cases hy
    obtain ⟨y', rfl, h1, h2, h3⟩ := hs y n rfl e.symm
    exact ⟨y', by simp, h1, h2, h3⟩
  · exact ⟨y, by simp [Function.update_of_ne e, hy], rfl, id, fun _ => rfl⟩

/-! ## The monad -/

/-- `MidK` from the states satisfying `P`. -/
def MidKA {α : Type} (P : State Unit → Prop) (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, P σ → ∀ x, x ∈ (m σ).1 → MidK σ x.2

/-- `P` survives `MidK` steps. -/
def MidKStable (P : State Unit → Prop) : Prop := ∀ σ σ', P σ → MidK σ σ' → P σ'

theorem midkStable_true : MidKStable (fun _ => True) := fun _ _ _ _ => trivial

section Comb
variable {P : State Unit → Prop}

theorem mka_bind {α β : Type} (hP : MidKStable P) {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : MidKA P m) (hg : ∀ a, MidKA P (g a)) : MidKA P (m >>= g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  have h1 := hm σ hσ y hy
  exact h1.trans (hg y.1 y.2 (hP σ y.2 hσ h1) x hx)

theorem mka_bind' {α β : Type} (hP : MidKStable P) {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : MidKA P m) (hg : ∀ a, MidKA P (g a)) : MidKA P (NonDet.bind m g) := mka_bind hP hm hg

theorem mka_of_eq {α : Type} {m : NonDet (State Unit) α} (h : ∀ σ x, x ∈ (m σ).1 → x.2 = σ) : MidKA P m :=
  fun σ _ x hx => by rw [h σ x hx]; exact MidK.refl σ

theorem mka_pure {α : Type} (a : α) : MidKA P (pure a : NonDet (State Unit) α) :=
  mka_of_eq fun _ _ hx => by rw [Set.mem_singleton_iff.1 hx]

theorem mka_pure' {α : Type} (a : α) : MidKA P (NonDet.pure a : NonDet (State Unit) α) := mka_pure a

theorem mka_gets {α : Type} (g : State Unit → α) : MidKA P (NonDet.gets g) :=
  mka_of_eq fun _ _ hx => by rw [Set.mem_singleton_iff.1 hx]

theorem mka_get : MidKA P (NonDet.get : NonDet (State Unit) (State Unit)) :=
  mka_of_eq fun _ _ hx => by rw [Set.mem_singleton_iff.1 hx]

theorem mka_assert (Q : Prop) : MidKA P (NonDet.assert Q : NonDet (State Unit) Unit) :=
  mka_of_eq fun _ _ hx => by obtain ⟨-, rfl⟩ := hx; rfl

theorem mka_fail {α : Type} : MidKA P (NonDet.fail : NonDet (State Unit) α) := fun _ _ _ hx => hx.elim

theorem mka_assertOpt {α : Type} (o : Option α) : MidKA P (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact mka_fail
  · exact mka_pure' _

theorem mka_getsThe {α : Type} (g : State Unit → Option α) : MidKA P (NonDet.getsThe g) :=
  fun σ hσ x hx => mka_assertOpt (g σ) σ hσ x hx

theorem mka_selectF {α : Type} (S : Set α × Prop) : MidKA P (NonDet.selectF S : NonDet (State Unit) α) :=
  mka_of_eq fun _ _ hx => by obtain ⟨-, h⟩ := hx; exact h

theorem mka_ite {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDet (State Unit) α} (h1 : MidKA P m1)
    (h2 : MidKA P m2) : MidKA P (if Q then m1 else m2) := by
  split <;> assumption

theorem mka_when (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : MidKA P m) :
    MidKA P (NonDet.when Q m) := by
  unfold NonDet.when; exact mka_ite Q h (mka_pure' _)

theorem mka_unless (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : MidKA P m) :
    MidKA P (NonDet.unless Q m) := by
  unfold NonDet.unless; exact mka_ite Q (mka_pure' _) h

theorem mka_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, MidKA P (g a)) (o : Option α) :
    MidKA P (NonDet.maybeM g o) := by
  cases o
  · exact mka_pure' _
  · exact h _

theorem mka_whileLoop (hP : MidKStable P) {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, MidKA P (B r)) (r : α) : MidKA P (NonDet.whileLoop C B r) := by
  intro σ hσ x hx
  induction hx with
  | done _ => exact MidK.refl _
  | step _ hm _ ih => exact (hB _ _ hσ _ hm).trans (ih (hP _ _ hσ (hB _ _ hσ _ hm)))

theorem mka_mapM (hP : MidKStable P) {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, MidKA P (g a))
    (xs : List α) : MidKA P (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact mka_pure' _
  | cons a xs' ih => exact mka_bind' hP (h a) fun _ => mka_bind' hP ih fun _ => mka_pure' _

theorem mka_modify {g : State Unit → State Unit} (hg : ∀ σ, P σ → MidK σ (g σ)) : MidKA P (NonDet.modify g) := by
  intro σ hσ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hg σ hσ

theorem mka_bind_ret {α β : Type} {m : NonDet (State Unit) α} (hm : MidKA P m) (b : β) :
    MidKA P (m >>= fun _ => pure b) := by
  intro σ hσ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hx]; exact hm σ hσ y hy

theorem mka_mono {α : Type} {Q : State Unit → Prop} {m : NonDet (State Unit) α} (hQ : ∀ σ, P σ → Q σ)
    (h : MidKA Q m) : MidKA P m := fun σ hσ => h σ (hQ σ hσ)

theorem mka_getObject (p : ObjRef) : MidKA P (getObject (Z := Unit) p) := mka_getsThe _

/-- A state update touching no field `MidK` reads. -/
theorem MidK.of_fields {σ σ' : State Unit} (hk : σ'.kheap = σ.kheap) (h1 : σ'.curThread = σ.curThread)
    (h2 : σ'.curSc = σ.curSc) (h3 : σ'.curTime = σ.curTime) (h4 : σ'.idleThread = σ.idleThread)
    (h5 : σ'.consumedTime = σ.consumedTime) (h6 : σ'.schedulerAction = σ.schedulerAction)
    (h7 : σ'.releaseQueue = σ.releaseQueue) : MidK σ σ' := by
  refine ⟨h1, h2, h3, h4, Or.inl h5, fun h => by rw [h6]; exact h, fun t h => by rw [← h6]; exact h,
    fun x hx => ⟨x, by rw [hk]; exact hx, rfl, rfl⟩, fun x hx => ⟨x, by rw [hk]; exact hx, rfl, rfl⟩,
    fun y n hy => ⟨y, by rw [hk]; exact hy, rfl, id, fun _ => rfl⟩, fun t ht => Or.inl (by rw [← h7]; exact ht)⟩

end Comb

/-! ## Object updates -/

section Obj
variable {P : State Unit → Prop}

theorem mka_threadSet {g : Tcb → Tcb} {p : ObjRef}
    (hg : ∀ σ, P σ → (p = σ.curThread ∨ p = σ.idleThread) → ∀ x,
      (g x).tcbSchedContext = x.tcbSchedContext ∧ (g x).tcbState = x.tcbState) :
    MidKA P (threadSet (Z := Unit) g p) := by
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getsThe_getTcb_mem hy
  rw [hs] at hx
  obtain ⟨k, hk', -, e⟩ := setObject_mem hx
  rw [hk] at hk'; cases hk'
  rw [e]
  refine MidK.upd hk (fun x' e' hq => ?_) (fun _ _ e' => by cases e')
  cases e'
  exact ⟨_, rfl, (hg σ hσ hq _).1, (hg σ hσ hq _).2⟩

theorem mka_updateSchedContext {g : SchedContext → SchedContext} {p : ObjRef}
    (hg : ∀ σ, P σ → p = σ.curSc → ∀ y, (g y).scTcb = y.scTcb ∧ (scActive y = true → scActive (g y) = true) ∧
      (σ.consumedTime ≠ 0 → (g y).scRefills = y.scRefills)) :
    MidKA P (updateSchedContext (Z := Unit) p g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getObject_mem hy
  obtain ⟨o, σ1⟩ := y
  simp only at hk hs hx; subst σ1
  cases o
  all_goals try exact hx.elim
  obtain ⟨k, hk', -, e⟩ := setObject_mem hx
  rw [hk] at hk'; cases hk'
  rw [e]
  refine MidK.upd hk (fun _ e' => by cases e') (fun y' n' e' hq => ?_)
  cases e'
  exact ⟨_, rfl, hg σ hσ hq _⟩

theorem mka_updateSkObjRef {α : Type} [Nonempty α] {C : α → KernelObject}
    {g : (Option ObjRef → Option ObjRef) → α → α} {new : Option ObjRef}
    (hC : ∀ a, (∀ x, C a ≠ .tcb x) ∧ ∀ y n, C a ≠ .schedContext y n) (ref : ObjRef) :
    MidKA P (updateSkObjRef (Z := Unit) C g ref new) := by
  intro σ _ x ⟨y, hy, hx⟩
  obtain ⟨⟨o, σ1⟩, hy1, hy⟩ := hy
  obtain ⟨hk, hs⟩ := getObject_mem hy1
  simp only at hk hs; subst hs
  obtain ⟨y2, hy2, hy⟩ := hy
  obtain ⟨-, rfl⟩ := hy2
  cases he : partialInv C o with
  | none => simp only [he] at hy; exact hy.elim
  | some e =>
    simp only [he] at hy
    rw [Set.mem_singleton_iff.1 hy] at hx
    have hCe := partialInv_eq he
    subst hCe
    obtain ⟨z1, hz1, hx⟩ := hx
    obtain ⟨hk1, hs1⟩ := getObject_mem hz1
    obtain ⟨z2, hz2, hx⟩ := hx
    obtain ⟨-, rfl⟩ := hz2
    obtain ⟨z3, hz3, hx⟩ := hx
    obtain ⟨-, rfl⟩ := hz3
    simp only at hx
    rw [hs1] at hx
    obtain ⟨k, hk', -, e'⟩ := setObject_mem hx
    rw [e']
    exact MidK.upd hk (fun x' e'' => absurd e'' ((hC e).1 x')) (fun y' n' e'' => absurd e'' ((hC e).2 y' n'))

end Obj

/-! ## Specific state updates -/

theorem MidK.choose (σ : State Unit) : MidK σ { σ with schedulerAction := .chooseNewThread } :=
  ⟨rfl, rfl, rfl, rfl, Or.inl rfl, fun _ => rfl, fun _ h => (by cases h), MidT.refl _ _, MidT.refl _ _,
    fun y _ h => ⟨y, h, rfl, id, fun _ => rfl⟩, fun _ h => Or.inl h⟩

/-- A release queue whose new members are neither the idle nor the current thread. -/
theorem MidK.relq (σ : State Unit) (q : List ObjRef)
    (hq : ∀ u ∈ q, u ∈ σ.releaseQueue ∨ (u ≠ σ.idleThread ∧ u ≠ σ.curThread)) (b : Bool) :
    MidK σ { σ with releaseQueue := q, reprogramTimer := b } :=
  ⟨rfl, rfl, rfl, rfl, Or.inl rfl, id, fun _ h => h, MidT.refl _ _, MidT.refl _ _,
    fun y _ h => ⟨y, h, rfl, id, fun _ => rfl⟩, fun u hu => (hq u hu).imp id fun h => ⟨h.1, Or.inl h.2⟩⟩

/-! ## Read-only operations -/

/-- Every outcome keeps the state. -/
def RdO {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → x.2 = σ

theorem rdo_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : RdO m)
    (hg : ∀ a, RdO (g a)) : RdO (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  rw [hg y.1 y.2 x hx, hm σ y hy]

theorem rdo_pure {α : Type} (a : α) : RdO (pure a : NonDet (State Unit) α) := fun _ _ hx => by
  rw [Set.mem_singleton_iff.1 hx]
theorem rdo_pure' {α : Type} (a : α) : RdO (NonDet.pure a : NonDet (State Unit) α) := rdo_pure a
theorem rdo_gets {α : Type} (g : State Unit → α) : RdO (NonDet.gets g) := fun _ _ hx => by
  rw [Set.mem_singleton_iff.1 hx]
theorem rdo_assert (Q : Prop) : RdO (NonDet.assert Q : NonDet (State Unit) Unit) := fun _ _ hx => by
  obtain ⟨-, rfl⟩ := hx; rfl
theorem rdo_fail {α : Type} : RdO (NonDet.fail : NonDet (State Unit) α) := fun _ _ hx => hx.elim
theorem rdo_assertOpt {α : Type} (o : Option α) : RdO (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact rdo_fail
  · exact rdo_pure' _
theorem rdo_getsThe {α : Type} (g : State Unit → Option α) : RdO (NonDet.getsThe g) :=
  fun σ x hx => rdo_assertOpt (g σ) σ x hx
theorem rdo_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, RdO (g a)) (xs : List α) :
    RdO (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact rdo_pure' _
  | cons a xs' ih => exact rdo_bind (h a) fun _ => rdo_bind ih fun _ => rdo_pure' _
theorem rdo_ite {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDet (State Unit) α} (h1 : RdO m1) (h2 : RdO m2) :
    RdO (if Q then m1 else m2) := by
  split <;> assumption

theorem RdO.ofRdN {α : Type} {Q : State Unit → α → Prop} {m : NonDet (State Unit) α} (h : RdN Q m) : RdO m :=
  fun σ x hx => (h σ x hx).1

theorem mka_bind_rdn {P : State Unit → Prop} {α β : Type} {Q : State Unit → α → Prop} {m : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) β} (hm : RdN Q m) (hg : ∀ a, MidKA (fun σ => P σ ∧ Q σ a) (g a)) :
    MidKA P (m >>= g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  obtain ⟨e, hq⟩ := hm σ y hy
  rw [e] at hx
  exact hg y.1 σ ⟨hσ, hq⟩ x hx

theorem mka_bind_rdo {P : State Unit → Prop} {α β : Type} {m : NonDet (State Unit) α}
    {g : α → NonDet (State Unit) β} (hm : RdO m) (hg : ∀ a, MidKA P (g a)) : MidKA P (m >>= g) := by
  intro σ hσ x ⟨y, hy, hx⟩
  rw [hm σ y hy] at hx
  exact hg y.1 σ hσ x hx

theorem rdn_gets {α : Type} (g : State Unit → α) : RdN (fun σ v => v = g σ) (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ⟨rfl, rfl⟩

theorem rdn_assertOpt {α : Type} (o : Option α) : RdN (fun _ v => o = some v) (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · intro σ x hx; exact hx.elim
  · intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ⟨rfl, rfl⟩

theorem rdn_getScObjRef (f : SchedContext → Option ObjRef) (p : ObjRef) :
    RdN (fun σ v => ∃ y n, σ.kheap p = some (.schedContext y n) ∧ v = f y) (getScObjRef (Z := Unit) f p) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨e, n, hk⟩ := rdn_getSchedContext p σ y hy
  rw [Set.mem_singleton_iff.1 hx]
  exact ⟨e, y.1, n, hk, rfl⟩

/-- `ordered_insert` reads only, its list the old one with `t`. -/
theorem rdn_orderedInsert {α β : Type} [Nonempty β] (t : α) (ts : List α) (f : α → RMonad Unit β)
    (R : β → β → Prop) [DecidableRel R] :
    RdN (fun _ v => ∀ u ∈ v, u = t ∨ u ∈ ts) (orderedInsert (Z := Unit) t ts f R) := by
  intro σ x hx
  unfold orderedInsert at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨y2, hy2, hx⟩ := hx
  have e1 := rdo_getsThe _ σ y1 hy1
  rw [e1] at hy2
  have e2 := rdo_mapM (fun _ => rdo_getsThe _) ts σ y2 hy2
  rw [e2] at hx
  obtain ⟨y3, hy3, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy3] at hx
  obtain ⟨y4, hy4, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy4] at hx
  rw [Set.mem_singleton_iff.1 hx]
  refine ⟨rfl, fun u hu => ?_⟩
  simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hu
  rcases hu with (hu | hu) | hu
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.1 hu
    exact Or.inr (List.of_mem_zip ((List.takeWhile_sublist _).subset hab)).1
  · exact Or.inl hu
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.1 hu
    exact Or.inr (List.of_mem_zip ((List.dropWhile_sublist _).subset hab)).1

/-! ## The operations -/

section Ops
variable {P : State Unit → Prop}

theorem mka_tcbSchedAction (a : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    MidKA P (tcbSchedAction (Z := Unit) a t) := by
  unfold tcbSchedAction getTcbQueue setTcbQueue
  refine mka_bind_rdo (RdO.ofRdN (rdn_threadGet _ _)) fun _ => mka_bind_rdo (RdO.ofRdN (rdn_threadGet _ _)) fun _ =>
    mka_bind_rdo (rdo_bind (rdo_gets _) fun _ => rdo_pure _) fun _ => mka_bind_rdo (rdo_pure _) fun _ =>
    mka_modify fun σ _ => MidK.of_fields rfl rfl rfl rfl rfl rfl rfl rfl

theorem mka_setChoose : MidKA P (setSchedulerAction (Z := Unit) .chooseNewThread) := by
  unfold setSchedulerAction; exact mka_modify fun σ _ => MidK.choose σ

theorem mka_rescheduleRequired (hP : MidKStable P) : MidKA P (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired
  refine mka_bind_rdo (rdo_gets _) fun act => ?_
  dsimp only
  split
  · refine mka_bind_rdo (rdo_gets _) fun _ => mka_bind hP (mka_when _ ?_) fun _ => mka_setChoose
    refine mka_bind_rdo (RdO.ofRdN (rdn_threadGet _ _)) fun _ => mka_bind_rdo (rdo_assertOpt _) fun _ =>
      mka_bind_rdo (rdo_getsThe _) fun _ => mka_bind_rdo (rdo_getsThe _) fun _ => mka_bind_rdo (rdo_assert _) fun _ =>
      mka_tcbSchedAction _ _
  · exact mka_setChoose

theorem mka_tcbReleaseRemove (t : ObjRef) : MidKA P (tcbReleaseRemove (Z := Unit) t) := by
  intro σ _ x hx
  unfold tcbReleaseRemove at hx
  rw [Notif.nd_gets_bind] at hx
  have key : ∀ σ1 : State Unit, σ1.releaseQueue = σ.releaseQueue → MidK σ σ1 →
      x ∈ ((pure (tcbSchedDequeue t σ.releaseQueue) >>= fun qs' => setReleaseQueue qs') σ1).1 → MidK σ x.2 := by
    intro σ1 hq1 hk1 hx1
    rw [Notif.nd_pure_bind'] at hx1
    unfold setReleaseQueue at hx1
    rw [Set.mem_singleton_iff.1 hx1]
    refine hk1.trans (MidK.relq σ1 _ (fun u hu => Or.inl ?_) σ1.reprogramTimer)
    rw [hq1]; unfold tcbSchedDequeue at hu; exact (List.mem_filter.1 hu).1
  unfold NonDet.when at hx
  split at hx
  · rw [nd_bind_one (show NonDet.modify (fun s : State Unit => { s with reprogramTimer := true }) σ =
      ({((), { σ with reprogramTimer := true })}, False) from rfl)] at hx
    exact key { σ with reprogramTimer := true } rfl (MidK.of_fields rfl rfl rfl rfl rfl rfl rfl rfl) hx
  · rw [nd_bind_one (show NonDet.pure (σ := State Unit) () σ = ({((), σ)}, False) from rfl)] at hx
    exact key σ rfl (MidK.refl σ) hx

/-- **`tcb_release_enqueue`** of a thread neither idle nor current. -/
theorem mka_tcbReleaseEnqueue (t : ObjRef) :
    MidKA (fun σ => t ≠ σ.idleThread ∧ t ≠ σ.curThread) (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue readyTimesAppend setReleaseQueue
  refine mka_bind_rdn (rdn_gets _) fun q => mka_bind_rdn (rdn_orderedInsert _ _ _ _) fun q' => ?_
  intro σ ⟨⟨⟨hti, htc⟩, hq⟩, hq'⟩ x hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hx
  have h1 : MidK σ { σ with releaseQueue := q' } := by
    refine MidK.relq σ q' (fun u hu => ?_) σ.reprogramTimer
    rcases hq' u hu with rfl | h
    · exact Or.inr ⟨hti, htc⟩
    · exact Or.inl (hq ▸ h)
  unfold NonDet.when at hx
  split at hx
  · rw [Set.mem_singleton_iff.1 hx]
    exact h1.trans (MidK.of_fields rfl rfl rfl rfl rfl rfl rfl rfl)
  · rw [Set.mem_singleton_iff.1 hx]; exact h1

/-- **`postpone`** of an SC whose thread is neither idle nor current. -/
theorem mka_postpone (p : ObjRef) :
    MidKA (fun σ => ∀ y n t, σ.kheap p = some (.schedContext y n) → y.scTcb = some t →
      t ≠ σ.idleThread ∧ t ≠ σ.curThread) (postpone (Z := Unit) p) := by
  unfold postpone
  refine mka_bind_rdn (rdn_getScObjRef _ _) fun o => mka_bind_rdn (rdn_assertOpt _) fun t => ?_
  have hst : MidKStable (fun σ => t ≠ σ.idleThread ∧ t ≠ σ.curThread) := fun σ σ' h k => by
    simp only at h ⊢; rw [k.idle, k.ct]; exact h
  refine mka_mono (Q := fun σ => t ≠ σ.idleThread ∧ t ≠ σ.curThread) ?_ ?_
  · rintro σ ⟨⟨h, y, n, hk, rfl⟩, ht⟩; exact h y n t hk ht
  · exact mka_bind hst (mka_tcbSchedAction _ _) fun _ => mka_bind hst (mka_tcbReleaseEnqueue _) fun _ =>
      mka_modify fun σ _ => MidK.of_fields rfl rfl rfl rfl rfl rfl rfl rfl

end Ops

macro "mka_step0" : tactic => `(tactic| first
  | with_reducible exact mka_pure _ | with_reducible exact mka_pure' _ | with_reducible exact mka_fail
  | with_reducible exact mka_gets _ | with_reducible exact mka_get
  | with_reducible exact mka_assert _ | with_reducible exact mka_assertOpt _
  | with_reducible exact mka_getObject _ | with_reducible exact mka_getsThe _
  | with_reducible exact mka_selectF _
  | with_reducible exact mka_tcbSchedAction _ _ | (with_reducible exact mka_rescheduleRequired (by assumption))
  | with_reducible exact mka_tcbReleaseRemove _ | with_reducible exact mka_setChoose
  | ((with_reducible apply mka_modify); intro _ _; exact MidK.of_fields rfl rfl rfl rfl rfl rfl rfl rfl)
  | ((with_reducible apply mka_threadSet); intro _ _ _ _; exact ⟨rfl, rfl⟩)
  | ((with_reducible apply mka_updateSchedContext); intro _ _ _ _; exact ⟨rfl, id, fun _ => rfl⟩)
  | ((with_reducible apply mka_updateSchedContext); intro _ h e; exact absurd e h)
  | ((with_reducible apply mka_updateSkObjRef); intro _; exact ⟨fun _ e => (by cases e), fun _ _ e => (by cases e)⟩)
  | (with_reducible refine mka_bind (by assumption) ?_ (fun _ => ?_))
  | (with_reducible refine mka_bind' (by assumption) ?_ (fun _ => ?_))
  | (with_reducible apply mka_ite) | (with_reducible apply mka_when) | (with_reducible apply mka_unless)
  | (with_reducible refine mka_maybeM (fun _ => ?_) _)
  | (with_reducible refine mka_whileLoop (by assumption) (fun _ => ?_) _)
  | (with_reducible refine mka_mapM (by assumption) (fun _ => ?_) _)
  | split
  | (dsimp only))

macro "mka_auto" : tactic => `(tactic| repeat mka_step0)

section Ops2

theorem mka_getSchedContext {P : State Unit → Prop} (p : ObjRef) : MidKA P (getSchedContext (Z := Unit) p) :=
  mka_of_eq (RdO.ofRdN (rdn_getSchedContext p))

theorem mka_threadGet {P : State Unit → Prop} {α : Type} (g : Tcb → α) (p : ObjRef) :
    MidKA P (threadGet (Z := Unit) g p) := mka_of_eq (RdO.ofRdN (rdn_threadGet g p))

theorem mka_getScObjRef {P : State Unit → Prop} (g : SchedContext → Option ObjRef) (p : ObjRef) :
    MidKA P (getScObjRef (Z := Unit) g p) := mka_of_eq (RdO.ofRdN (rdn_getScObjRef g p))

/-- **The unblock check** of an SC other than the current one. -/
theorem mka_refillUnblockCheck (p : ObjRef) :
    MidKA (fun σ => p ≠ σ.curSc) (refillUnblockCheck (Z := Unit) p) := by
  have hP : MidKStable (fun σ => p ≠ σ.curSc) := fun σ σ' h k => by simp only at h ⊢; rw [k.csc]; exact h
  unfold refillUnblockCheck isRoundRobin getScRefillReady refillHeadOverlappingLoop mergeOverlappingRefills
    refillPopHead updateRefillHd getRefillHead
  refine mka_bind hP (mka_bind hP (mka_getSchedContext _) fun _ => mka_pure _) fun _ => ?_
  mka_auto

theorem mka_ifCondRefillUnblockCheck (p : ObjRef) (a b : Option Bool) :
    MidKA (fun σ => p ≠ σ.curSc) (ifCondRefillUnblockCheck (Z := Unit) (some p) a b) := by
  have hP : MidKStable (fun σ => p ≠ σ.curSc) := fun σ σ' h k => by simp only at h ⊢; rw [k.csc]; exact h
  unfold ifCondRefillUnblockCheck NonDet.maybeM
  exact mka_bind hP (mka_getSchedContext _) fun _ => mka_bind hP (mka_gets _) fun _ =>
    mka_bind hP (mka_pure _) fun _ => mka_when _ (mka_when _ (mka_refillUnblockCheck _))

/-- **`sched_context_resume`** of an SC whose thread is neither idle nor
current. -/
theorem mka_schedContextResume (p : ObjRef) :
    MidKA (fun σ => ∀ y n t, σ.kheap p = some (.schedContext y n) → y.scTcb = some t →
      t ≠ σ.idleThread ∧ t ≠ σ.curThread) (schedContextResume (Z := Unit) p) := by
  unfold schedContextResume getScRefillReady getScRefillSufficient getTcbQueue
  refine mka_bind_rdo (RdO.ofRdN (rdn_getSchedContext _)) fun _ => mka_bind_rdo (rdo_assertOpt _) fun _ =>
    mka_bind_rdo (rdo_gets _) fun _ => mka_when _ ?_
  refine mka_bind_rdo (RdO.ofRdN (rdn_threadGet _ _)) fun _ => mka_bind_rdo (rdo_getsThe _) fun _ =>
    mka_bind_rdo (rdo_getsThe _) fun _ => mka_when _ ?_
  refine mka_bind_rdo (RdO.ofRdN (rdn_threadGet _ _)) fun _ => mka_bind_rdo (RdO.ofRdN (rdn_threadGet _ _)) fun _ =>
    mka_bind_rdo (rdo_bind (rdo_gets _) fun _ => rdo_pure _) fun _ => mka_bind_rdo (rdo_assert _) fun _ =>
    mka_postpone _

theorem mka_schedContextUnbindNtfn (p : ObjRef) : MidKA (fun _ => True) (schedContextUnbindNtfn (Z := Unit) p) := by
  have hP := midkStable_true
  unfold schedContextUnbindNtfn
  refine mka_bind hP (mka_getScObjRef _ _) fun _ => ?_
  mka_auto

theorem mka_schedContextBindNtfn (sc n : ObjRef) : MidKA (fun _ => True) (schedContextBindNtfn (Z := Unit) sc n) := by
  have hP := midkStable_true
  unfold schedContextBindNtfn
  mka_auto

theorem mka_returnConsumed (p : ObjRef) : MidKA (fun _ => True) (returnConsumed (Z := Unit) p) := by
  have hP := midkStable_true
  unfold returnConsumed schedContextUpdateConsumed
  refine mka_bind hP ?_ fun _ => mka_pure _
  refine mka_bind hP (mka_getSchedContext _) fun _ => ?_
  mka_auto

end Ops2

macro "mka_step" : tactic => `(tactic| first
  | with_reducible exact mka_threadGet _ _ | with_reducible exact mka_getSchedContext _
  | with_reducible exact mka_getScObjRef _ _ | mka_step0)

macro "mka_auto2" : tactic => `(tactic| repeat mka_step)

section Ops3

/-- The precondition of the binds and unbinds: an SC other than the current
one, a thread neither current nor idle. -/
def BindPre (sc t : ObjRef) (σ : State Unit) : Prop :=
  sc ≠ σ.curSc ∧ t ≠ σ.curThread ∧ t ≠ σ.idleThread

theorem bindPre_stable (sc t : ObjRef) : MidKStable (BindPre sc t) := fun σ σ' h k => by
  unfold BindPre at h ⊢; rw [k.csc, k.ct, k.idle]; exact h

/-- **`sched_context_unbind_tcb`** of an SC other than the current one,
whose thread is neither current nor idle. -/
theorem mka_schedContextUnbindTcb (sc : ObjRef) :
    MidKA (fun σ => sc ≠ σ.curSc ∧ ∀ y n t, σ.kheap sc = some (.schedContext y n) → y.scTcb = some t →
      t ≠ σ.curThread ∧ t ≠ σ.idleThread) (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb
  refine mka_bind_rdn (rdn_getSchedContext _) fun y => mka_bind_rdn (rdn_assertOpt _) fun t => ?_
  refine mka_mono (Q := BindPre sc t) (fun σ ⟨⟨⟨h1, h2⟩, n, hk⟩, ht⟩ => ⟨h1, h2 y n t hk ht⟩) ?_
  have hP := bindPre_stable sc t
  refine mka_bind hP (mka_gets _) fun _ => mka_bind hP (mka_when _ (mka_rescheduleRequired hP)) fun _ =>
    mka_bind hP (mka_tcbSchedAction _ _) fun _ => mka_bind hP (mka_tcbReleaseRemove _) fun _ => mka_bind hP ?_ fun _ => ?_
  · exact mka_threadSet fun σ h hq _ => absurd hq (by rintro (e | e); exacts [h.2.1 e, h.2.2 e])
  · exact mka_updateSchedContext fun σ h e _ => absurd e h.1

/-- **`sched_context_bind_tcb`** of an SC other than the current one to a
thread neither current nor idle. -/
theorem mka_schedContextBindTcb (sc t : ObjRef) : MidKA (BindPre sc t) (schedContextBindTcb (Z := Unit) sc t) := by
  have hP := bindPre_stable sc t
  intro σ hσ x hx
  unfold schedContextBindTcb at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨y2, hy2, hx⟩ := hx
  obtain ⟨y3, hy3, hx⟩ := hx
  obtain ⟨y4, hy4, hx⟩ := hx
  have k1 : MidK σ y1.2 :=
    mka_threadSet (P := BindPre sc t) (fun σ h hq _ => absurd hq (by rintro (e | e); exacts [h.2.1 e, h.2.2 e])) σ hσ _ hy1
  have h1 := hP _ _ hσ k1
  have k2 : MidK y1.2 y2.2 := mka_updateSchedContext (P := BindPre sc t) (fun σ h e _ => absurd e h.1) _ h1 _ hy2
  have h2 := hP _ _ h1 k2
  have k3 : MidK y2.2 y3.2 := mka_mono (fun σ h => h.1) (mka_ifCondRefillUnblockCheck sc _ _) _ h2 _ hy3
  have h3 := hP _ _ h2 k3
  -- the SC's thread at the resume is `t`
  obtain ⟨y0, n0, hk2, e2⟩ := MaxK.updSc_mem hy2
  have hsc3 : ∀ y n, y3.2.kheap sc = some (.schedContext y n) → y.scTcb = some t := by
    intro y n hy
    obtain ⟨y', hy', -, ht⟩ := MaxK.mk_ifCondRefillUnblockCheck' _ _ _ y2.2 y3 hy3 sc y n hy
    rw [e2] at hy'; simp only [Function.update_self, Option.some.injEq, KernelObject.schedContext.injEq] at hy'
    rw [ht, ← hy'.1]; rfl
  have k4 : MidK y3.2 y4.2 := mka_schedContextResume sc y3.2 (fun y n t' hy ht' => by
    rw [hsc3 y n hy] at ht'; cases ht'; exact ⟨h3.2.2, h3.2.1⟩) _ hy4
  have h4 := hP _ _ h3 k4
  have k5 : MidK y4.2 x.2 := by
    refine (mka_bind hP (mka_gets _) fun _ => mka_when _ (mka_bind hP (mka_tcbSchedAction _ _) fun _ =>
      mka_rescheduleRequired hP)) _ h4 _ hx
  exact k1.trans (k2.trans (k3.trans (k4.trans k5)))

/-- **A YieldTo from an SC yielded to by none** whose thread is neither
current nor idle. -/
theorem mka_schedContextYieldTo {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (hyf : x.scYieldFrom = none)
    (ht : ∀ t, x.scTcb = some t → t ≠ σ.idleThread ∧ t ≠ σ.curThread) :
    ∀ y ∈ (schedContextYieldTo (Z := Unit) p σ).1, MidK σ y.2 := by
  have hP := midkStable_true
  intro y hy
  unfold schedContextYieldTo at hy
  rw [nd_bind_one (getScObjRef_eq hk _), hyf] at hy
  obtain ⟨y1, hy1, hy⟩ := hy
  have e1 : y1.2 = σ := by
    unfold NonDet.when at hy1; simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hy1
    rw [Set.mem_singleton_iff.1 hy1]
  rw [e1] at hy
  obtain ⟨y2, hy2, hy⟩ := hy
  have k2 : MidK σ y2.2 := mka_schedContextResume p σ (fun y' n' t hy' ht' => by
    rw [hk] at hy'; cases hy'; exact ht t ht') _ hy2
  refine k2.trans ((show MidKA (fun _ => True) _ from ?_) y2.2 trivial y hy)
  unfold returnConsumed schedContextUpdateConsumed
  refine mka_bind hP ?_ fun _ => ?_
  · refine mka_bind hP (mka_getScObjRef _ _) fun _ => ?_
    mka_auto2
  · refine mka_ite _ (mka_bind hP ?_ fun _ => mka_pure _) (mka_pure _)
    refine mka_bind hP (mka_getSchedContext _) fun _ => ?_
    mka_auto2

end Ops3

/-- **The restart keeps the current thread's invariants and the resume
action** (the current thread schedulable). -/
theorem restart_mid {σ : State Unit} {xc : Tcb} {t : ObjRef} (hct : σ.curThread = t)
    (hkc : σ.kheap t = some (.tcb xc))
    (hcs : schedulable t σ = true) (hres : σ.schedulerAction = .resumeCurThread) (hC : CurInv σ)
    (hO : OffOK σ) (hA : ActIdle σ) (hI : Inv σ) :
    let σ0 := Notif.stsAct (Notif.updK σ t (.tcb { xc with tcbState := .restart })) t
    σ0.schedulerAction = .resumeCurThread ∧ CurInv σ0 ∧ OffOK σ0 ∧ ActIdle σ0 ∧ Inv σ0 := by
  subst hct
  intro σ0
  obtain ⟨xc', scp, y, n, hk', hsc, hrun, hky, hact, hnr⟩ := schedulable_inv hcs
  rw [hkc] at hk'; cases hk'
  have hne : scp ≠ σ.curThread := fun e => by rw [e, hkc] at hky; cases hky
  refine ⟨?_, ?_, hO.restart .restart, (ActIdle.updState hA hkc hrun .restart rfl).ofSts _, hI.restart hkc hrun⟩
  · show (Notif.stsAct _ _).schedulerAction = _
    unfold Notif.stsAct
    rw [if_neg]
    · exact hres
    rintro ⟨-, -, h⟩
    refine h (schedulable_of (x := { xc with tcbState := .restart }) (y := y) (n := n) (by simp [Notif.updK]) hsc rfl
      (by simp [Notif.updK, hne, hky]) hact hnr)
  · have := hC.restart hkc; exact this

/-! ## Without the no-switch clause (Configure's `possible_switch_to`) -/

/-- `MidK` without the no-switch clause. -/
structure MidKn (σ σ' : State Unit) : Prop where
  ct : σ'.curThread = σ.curThread
  csc : σ'.curSc = σ.curSc
  time : σ'.curTime = σ.curTime
  idle : σ'.idleThread = σ.idleThread
  cons : σ'.consumedTime = σ.consumedTime ∨ σ'.consumedTime = 0
  cn : σ.schedulerAction = .chooseNewThread → σ'.schedulerAction = .chooseNewThread
  ctT : MidT σ σ' σ.curThread
  idT : MidT σ σ' σ.idleThread
  cscS : ∀ y n, σ.kheap σ.curSc = some (.schedContext y n) → ∃ y', σ'.kheap σ.curSc = some (.schedContext y' n) ∧
    y'.scTcb = y.scTcb ∧ (scActive y = true → scActive y' = true) ∧
    (σ'.consumedTime ≠ 0 → y'.scRefills = y.scRefills)
  rq : ∀ t ∈ σ'.releaseQueue, t ∈ σ.releaseQueue ∨
    (t ≠ σ.idleThread ∧ (t ≠ σ.curThread ∨ (σ'.consumedTime = 0 ∧ σ'.schedulerAction = .chooseNewThread)))

theorem MidK.toN {σ σ' : State Unit} (h : MidK σ σ') : MidKn σ σ' :=
  ⟨h.ct, h.csc, h.time, h.idle, h.cons, h.cn, h.ctT, h.idT, h.cscS, h.rq⟩

theorem MidKn.cons0 {σ σ' : State Unit} (h : MidKn σ σ') (h0 : σ.consumedTime = 0) : σ'.consumedTime = 0 := by
  rcases h.cons with e | e
  · rw [e, h0]
  · exact e

theorem MidKn.trans {σ1 σ2 σ3 : State Unit} (h1 : MidKn σ1 σ2) (h2 : MidKn σ2 σ3) : MidKn σ1 σ3 := by
  refine ⟨h2.ct.trans h1.ct, h2.csc.trans h1.csc, h2.time.trans h1.time, h2.idle.trans h1.idle, ?_,
    fun h => h2.cn (h1.cn h), ?_, ?_, ?_, ?_⟩
  · rcases h2.cons with e | e
    · rw [e]; exact h1.cons
    · exact Or.inr e
  · have := h2.ctT; rw [h1.ct] at this; exact h1.ctT.trans this
  · have := h2.idT; rw [h1.idle] at this; exact h1.idT.trans this
  · intro y n hy
    obtain ⟨y2, hy2, e1, f1, g1⟩ := h1.cscS y n hy
    have c2 := h2.cscS; rw [h1.csc] at c2
    obtain ⟨y3, hy3, e2, f2, g2⟩ := c2 y2 n hy2
    exact ⟨y3, hy3, e2.trans e1, fun h => f2 (f1 h), fun h => (g2 h).trans (g1 (fun e => h (h2.cons0 e)))⟩
  · intro t ht
    rcases h2.rq t ht with h | ⟨hi, hc⟩
    · rcases h1.rq t h with h' | ⟨hi', hc'⟩
      · exact Or.inl h'
      · refine Or.inr ⟨hi', ?_⟩
        rcases hc' with e | ⟨e1, e2⟩
        · exact Or.inl e
        · exact Or.inr ⟨h2.cons0 e1, h2.cn e2⟩
    · rw [h1.idle] at hi; rw [h1.ct] at hc
      exact Or.inr ⟨hi, hc⟩

/-- **The mid-entry facts after a `MidKn` step** but `ActIdle`. -/
theorem MidKn.mid3 {T : Set U64} {σ σ' : State Unit} (hK : MidKn σ σ') (hC : CurInv σ) (hO : OffOK σ) (hI : Inv σ)
    (hcT : ∃ u ∈ T, u.bv = σ.curThread) :
    (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧
      (σ'.schedulerAction = .chooseNewThread → CurOwn T σ') ∧ OffOK σ' := by
  obtain ⟨xt, hkt, hsc, hnb⟩ := hC.tcb
  obtain ⟨y0, n0, hy0⟩ := hC.sc
  obtain ⟨xt', hkt', e1, e2⟩ := hK.ctT xt hkt
  obtain ⟨y0', hy0', f1, f2, f3⟩ := hK.cscS y0 n0 hy0
  have hnr' : ∀ hcn : σ'.schedulerAction ≠ .chooseNewThread ∨ 0 < σ'.consumedTime,
      σ.curThread ∉ σ'.releaseQueue := by
    intro hc hm
    rcases hK.rq _ hm with h | ⟨-, h | ⟨h0, hcn⟩⟩
    · exact hC.notRel h
    · exact h rfl
    · rcases hc with hc | hc
      · exact hc hcn
      · rw [h0] at hc; simp at hc
  refine ⟨?_, fun hcn => ?_, fun hpos y n hy _ => ?_⟩
  · by_cases hcn : σ'.schedulerAction = .chooseNewThread
    · exact Or.inl hcn
    right
    refine ⟨⟨xt', by rw [hK.ct]; exact hkt', by rw [e1, hK.csc]; exact hsc, by rw [e2]; exact hnb⟩,
      ⟨y0', n0, by rw [hK.csc]; exact hy0'⟩, fun hid y m hy => ?_, fun hm => hnr' (Or.inl hcn) (by rw [← hK.ct]; exact hm)⟩
    rw [hK.csc] at hid hy
    rw [hy0'] at hy; cases hy
    exact f2 (hC.active hid y0 n0 hy0)
  · obtain ⟨u, hu, hub⟩ := hcT
    obtain ⟨y1, n1, hy1, hy1t⟩ := hI.back _ xt σ.curSc hkt hsc
    rw [hy0] at hy1; cases hy1
    refine ⟨u, hu, xt', by rw [hub]; exact hkt', by rw [e1, hK.csc]; exact hsc, fun x n hx => ?_, fun hpos hm => ?_⟩
    · rw [hK.csc, hy0'] at hx; cases hx; rw [f1, hy1t, hub]
    · exact hnr' (Or.inr hpos) (by rw [← hub]; exact hm)
  · have hne : σ'.consumedTime ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
    have hc : σ'.consumedTime = σ.consumedTime := hK.cons.resolve_right hne
    rw [hK.csc, hy0'] at hy; cases hy
    have hpos0 : 0 < σ.consumedTime := by rw [← hc]; exact hpos
    obtain ⟨g1, g2, g3⟩ := hO hpos0 y0 n0 hy0 (fun hid => hC.active hid y0 n0 hy0)
    have hr : refillHd y0' = refillHd y0 := by unfold refillHd; rw [f3 hne]
    rw [hr, hc, hK.time]
    exact ⟨g1, g2, g3⟩

/-- **`possible_switch_to`** of a thread neither idle nor current: `MidKn`. -/
theorem mkn_possibleSwitchTo {t : ObjRef} {σ : State Unit} (ht : t ≠ σ.idleThread ∧ t ≠ σ.curThread) :
    ∀ x ∈ (possibleSwitchTo (Z := Unit) t σ).1, MidKn σ x.2 := by
  intro x hx
  unfold possibleSwitchTo getTcbObjRef setSchedulerAction at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  rw [RdO.ofRdN (rdn_threadGet _ _) σ y1 hy1] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  rw [rdo_gets _ σ y2 hy2] at hx
  unfold NonDet.when at hx
  dsimp only at hx
  split at hx
  · obtain ⟨y3, hy3, hx⟩ := hx
    rw [rdo_gets _ σ y3 hy3] at hx
    obtain ⟨y4, hy4, hx⟩ := hx
    rw [RdO.ofRdN (rdn_threadGet _ _) σ y4 hy4] at hx
    obtain ⟨y5, hy5, hx⟩ := hx
    obtain ⟨e5, hv5⟩ := rdn_gets (fun s : State Unit => s.schedulerAction) σ y5 hy5
    rw [e5] at hx
    dsimp only at hx
    split at hx
    · exact (mka_tcbSchedAction (P := fun _ => True) _ _ σ trivial x hx).toN
    · split at hx
      · exact ((mka_bind midkStable_true (mka_rescheduleRequired midkStable_true) fun _ => mka_tcbSchedAction _ _)
          σ trivial x hx).toN
      · rename_i hres
        rw [Set.mem_singleton_iff.1 hx]
        have hr : σ.schedulerAction = .resumeCurThread := by rw [← hv5]; simpa using hres
        refine ⟨rfl, rfl, rfl, rfl, Or.inl rfl, fun h => (by rw [hr] at h; cases h), MidT.refl _ _, MidT.refl _ _,
          fun y _ h => ⟨y, h, rfl, id, fun _ => rfl⟩, fun _ h => Or.inl h⟩
  · rw [Set.mem_singleton_iff.1 hx]; exact (MidK.refl σ).toN

theorem mka_refillNew (p : ObjRef) (m : Nat) (b per : Ticks) :
    MidKA (fun σ => p ≠ σ.curSc) (refillNew (Z := Unit) p m b per) := by
  have hP : MidKStable (fun σ => p ≠ σ.curSc) := fun σ σ' h k => by simp only at h ⊢; rw [k.csc]; exact h
  unfold refillNew
  repeat (first | unfold updateRefillHd | unfold updateRefillTl | unfold refillAddTail | unfold refillPopHead | unfold getRefillHead | unfold getRefills | unfold getRefillTail | unfold refillFull | unfold refillSingle | unfold refillSize | unfold scheduleUsed | unfold chargeEntireHeadRefill | unfold handleOverrun | unfold headInsufficientLoop | unfold mergeNonoverlappingHeadRefill | unfold isRoundRobin | unfold getScActive | unfold getScRefillReady | unfold maybeAddEmptyTail)
  mka_auto2

theorem mka_refillUpdate (p : ObjRef) (per b : Ticks) (m : Nat) :
    MidKA (fun σ => p ≠ σ.curSc) (refillUpdate (Z := Unit) p per b m) := by
  have hP : MidKStable (fun σ => p ≠ σ.curSc) := fun σ σ' h k => by simp only at h ⊢; rw [k.csc]; exact h
  unfold refillUpdate
  repeat (first | unfold updateRefillHd | unfold updateRefillTl | unfold refillAddTail | unfold refillPopHead | unfold getRefillHead | unfold getRefills | unfold getRefillTail | unfold refillFull | unfold refillSingle | unfold refillSize | unfold scheduleUsed | unfold chargeEntireHeadRefill | unfold handleOverrun | unfold headInsufficientLoop | unfold mergeNonoverlappingHeadRefill | unfold isRoundRobin | unfold getScActive | unfold getScRefillReady | unfold maybeAddEmptyTail)
  mka_auto2

set_option maxHeartbeats 4000000 in
/-- **Configure of an SC other than the current one**, whose thread (if any)
is neither idle nor current: `MidKn` (its `possible_switch_to` may switch). -/
theorem mkn_configure {σ : State Unit} {p : ObjRef} {b per : Ticks} {mr : Nat} {badge : Badge} {flag : Data}
    {y0 : SchedContext} {n0 : Nat} (hk : σ.kheap p = some (.schedContext y0 n0)) (hp : p ≠ σ.curSc)
    (ht : ∀ t, y0.scTcb = some t → t ≠ σ.idleThread ∧ t ≠ σ.curThread) (hv : activeSc mr = true) :
    ∀ x ∈ (invokeSchedControlConfigureFlags (Z := Unit) (.invokeSchedControlConfigureFlags p b per mr badge flag) σ).1,
      MidKn σ x.2 := by
  intro x hx
  have hP : MidKStable (fun σ => p ≠ σ.curSc) := fun σ σ' h k => by simp only at h ⊢; rw [k.csc]; exact h
  -- the tail after the refills
  have rest : ∀ (σ3 : State Unit) (x : Unit × State Unit), MidK σ σ3 → SKa σ σ3 →
      x ∈ ((do
        NonDet.when (y0.scTcb ≠ none) (do
          schedContextResume p
          let tcbPtr ← NonDet.assertOpt y0.scTcb
          let st ← getThreadState tcbPtr
          let ct ← NonDet.gets fun s : State Unit => s.curThread
          if tcbPtr = ct then rescheduleRequired else NonDet.when (runnable st = true) (possibleSwitchTo tcbPtr))
        setScObjRef scBadgeUpdate p badge
        setScObjRef scSporadicUpdate p (testBit flag scSporadicFlag) : SMonad Unit Unit) σ3).1 → MidKn σ3 x.2 := by
    intro σ3 x k23 s23 hx
    obtain ⟨y4, hy4, hx⟩ := hx
    have k4 : MidKn σ3 y4.2 := by
      unfold NonDet.when at hy4
      split at hy4
      · rename_i hb
        obtain ⟨t, hyt⟩ := Option.ne_none_iff_exists'.1 hb
        obtain ⟨hti, htc⟩ := ht t hyt
        obtain ⟨z1, hz1, hy4⟩ := hy4
        have kz : MidK σ3 z1.2 := mka_schedContextResume p σ3 (fun y n t' hy ht' => by
          obtain ⟨y0', hy0', e, -⟩ := s23 p y n hy
          rw [hk] at hy0'; cases hy0'
          rcases e with e | e
          · rw [e, hyt] at ht'; cases ht'; rw [k23.idle, k23.ct]; exact ⟨hti, htc⟩
          · rw [e] at ht'; cases ht') z1 hz1
        obtain ⟨z2, hz2, hy4⟩ := hy4
        rw [hyt] at hz2
        rw [Set.mem_singleton_iff.1 hz2] at hy4
        obtain ⟨z3, hz3, hy4⟩ := hy4
        rw [RdO.ofRdN (rdn_threadGet _ _) _ z3 hz3] at hy4
        obtain ⟨z4, hz4, hy4⟩ := hy4
        obtain ⟨e4, hv4⟩ := rdn_gets (fun s : State Unit => s.curThread) _ z4 hz4
        rw [e4, hv4] at hy4
        have hkk := k23.trans kz
        have htc' : t ≠ z1.2.curThread := by rw [hkk.ct]; exact htc
        have hti' : t ≠ z1.2.idleThread := by rw [hkk.idle]; exact hti
        dsimp only at hy4
        rw [if_neg htc'] at hy4
        split at hy4
        · exact kz.toN.trans (mkn_possibleSwitchTo ⟨hti', htc'⟩ _ hy4)
        · rw [Set.mem_singleton_iff.1 hy4]; exact kz.toN
      · rw [Set.mem_singleton_iff.1 hy4]; exact (MidK.refl _).toN
    obtain ⟨y5, hy5, hx⟩ := hx
    have k5 : MidK y4.2 y5.2 :=
      mka_updateSchedContext (P := fun _ => True) (g := scBadgeUpdate fun _ => badge) (p := p)
        (fun _ _ _ _ => ⟨rfl, id, fun _ => rfl⟩) _ trivial _ hy5
    have k6 : MidK y5.2 x.2 :=
      mka_updateSchedContext (P := fun _ => True) (g := scSporadicUpdate fun _ => testBit flag scSporadicFlag) (p := p)
        (fun _ _ _ _ => ⟨rfl, id, fun _ => rfl⟩) _ trivial _ hx
    exact k4.trans (k5.toN.trans k6.toN)
  unfold invokeSchedControlConfigureFlags at hx
  dsimp only at hx
  rw [nd_bind_one (getSchedContext_eq hk)] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  have k2 : MidK σ y2.2 := by
    refine (?_ : MidKA (fun σ => p ≠ σ.curSc) _) σ hp y2 hy2
    refine mka_when _ ?_
    refine mka_bind_rdo (rdo_assertOpt _) fun _ => mka_bind hP (mka_tcbReleaseRemove _) fun _ =>
      mka_bind hP (mka_tcbSchedAction _ _) fun _ => mka_bind_rdn (rdn_gets _) fun c => ?_
    intro σ' ⟨h1, h2⟩ z hz
    unfold NonDet.when at hz
    rw [if_neg (show ¬ (c = p) from fun e => h1 (e ▸ h2))] at hz
    rw [Set.mem_singleton_iff.1 hz]; exact MidK.refl _
  have s2 : SKa σ y2.2 := by
    refine (?_ : SKaM _) σ y2 hy2
    repeat' skm_step
  have hp2 : p ≠ y2.2.curSc := hP _ _ hp k2
  dsimp only at hx
  -- the refills, then the tail
  have tail : ∀ {m : SMonad Unit Unit}, MidKA (fun σ => p ≠ σ.curSc) m → SKaM m →
      ∀ σ2 x, MidK σ σ2 → SKa σ σ2 → x ∈ ((m >>= fun _ => (do
        NonDet.when (y0.scTcb ≠ none) (do
          schedContextResume p
          let tcbPtr ← NonDet.assertOpt y0.scTcb
          let st ← getThreadState tcbPtr
          let ct ← NonDet.gets fun s : State Unit => s.curThread
          if tcbPtr = ct then rescheduleRequired else NonDet.when (runnable st = true) (possibleSwitchTo tcbPtr))
        setScObjRef scBadgeUpdate p badge
        setScObjRef scSporadicUpdate p (testBit flag scSporadicFlag) : SMonad Unit Unit)) σ2).1 → MidKn σ2 x.2 := by
    intro m hm hs σ2 x k s hx
    obtain ⟨y3, hy3, hx⟩ := hx
    have k3 := hm σ2 (hP _ _ hp k) y3 hy3
    exact k3.toN.trans (rest y3.2 x (k.trans k3) (s.trans (hs σ2 y3 hy3)) hx)
  refine k2.toN.trans ?_
  split at hx
  · exact tail (mka_refillNew _ _ _ _) (skm_refillNew _ _ _ _ (by decide)) y2.2 x k2 s2 hx
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
      · exact tail (mka_refillUpdate _ _ _ _) (skm_refillUpdate _ _ _ _ hv) y2.2 x k2 s2 hx
      · exact tail (mka_refillNew _ _ _ _) (skm_refillNew _ _ _ _ hv) y2.2 x k2 s2 hx
    · exact tail (mka_refillNew _ _ _ _) (skm_refillNew _ _ _ _ hv) y2.2 x k2 s2 hx

/-- **The current thread is schedulable** under `CurInv`, `ActIdle` and
`Inv` when runnable (the current SC is not the idle SC: the idle thread
owns it). -/
theorem ct_schedulable {σ : State Unit} (hC : CurInv σ) (hA : ActIdle σ) (hI : Inv σ) {x : Tcb}
    (hk : σ.kheap σ.curThread = some (.tcb x)) (hr : runnable x.tcbState = true) : schedulable σ.curThread σ = true := by
  obtain ⟨xt, hkt, hsc, -⟩ := hC.tcb
  rw [hk] at hkt; cases hkt
  obtain ⟨y, n, hy⟩ := hC.sc
  have hni : σ.curSc ≠ idleScPtr := by
    intro e
    obtain ⟨xi, hki, hsi, hti, -⟩ := hA.2
    obtain ⟨y1, n1, hy1, h1⟩ := hI.back _ _ _ hk hsc
    obtain ⟨y2, n2, hy2, h2⟩ := hI.back _ _ _ hki hsi
    rw [← e, hy1] at hy2; cases hy2
    have e2 : σ.curThread = σ.idleThread := Option.some.inj (h1.symm.trans h2)
    rw [← e2, hk] at hki; cases hki; rw [hti] at hr; cases hr
  exact schedulable_of hk hsc hr hy (hC.active hni y n hy) hC.notRel

/-- The mid-entry facts but `ActIdle` (`CurInvW`, `CurOwn` under a pending
reschedule, `OffOK`). -/
def MidA (T : Set U64) (σ : State Unit) : Prop :=
  (σ.schedulerAction = .chooseNewThread ∨ CurInv σ) ∧ (σ.schedulerAction = .chooseNewThread → CurOwn T σ) ∧ OffOK σ

/-! ## The decodes' facts -/

theorem rdn_threadGetV {α : Type} (g : Tcb → α) (t : ObjRef) :
    RdN (fun σ v => ∃ x, σ.kheap t = some (.tcb x) ∧ v = g x) (threadGet (Z := Unit) g t) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getsThe_getTcb_mem hy
  rw [Set.mem_singleton_iff.1 hx]
  exact ⟨hs, y.1, hk, rfl⟩

theorem rdn_getsV {α : Type} (g : State Unit → α) : RdN (fun σ v => v = g σ) (NonDet.gets g) := rdn_gets g

/-- Bind's decode: the SC bound to no thread, the thread to no SC. -/
theorem rdp_decodeBindPre (sc : ObjRef) (excaps : List Cap) :
    RdP (fun σ v => ∀ t, v = .invokeSchedContextBind sc (.threadCap t) →
      (∃ y n, σ.kheap sc = some (.schedContext y n) ∧ y.scTcb = none) ∧
      ∃ x, σ.kheap t = some (.tcb x) ∧ x.tcbSchedContext = none)
      (decodeSchedContextBind (Z := Unit) sc excaps) := by
  unfold decodeSchedContextBind
  refine rdp_bind (rdp_whenE_throw _ _) fun _ => ?_
  refine rdp_bind (Q := fun _ _ => True) (rdp_returnOk fun _ => trivial) fun cap => ?_
  refine rdp_bind (rdp_liftE (rdn_getSchedContext sc)) fun sc0 => ?_
  dsimp only
  cases cap
  case threadCap t0 =>
    refine rdp_bind (rdp_whenE_throw _ _) fun _ => rdp_bind (rdp_liftE (rdn_threadGetV _ _)) fun _ =>
      rdp_bind (rdp_whenE_throw _ _) fun _ => rdp_bind (rdp_liftE (rdn_getThreadState t0)) fun _ =>
      rdp_bind (rdp_liftE (rdn_getScReleased sc)) fun _ => rdp_bind (rdp_whenE_throw _ _) fun _ =>
      rdp_returnOk fun σ => ?_
    intro _ _ _ hn0 ⟨x, hkx, hv⟩ hn1 ⟨n, hk⟩ _ _ t e
    simp only [SchedContextInvocation.invokeSchedContextBind.injEq, Cap.threadCap.injEq, true_and] at e
    subst e
    refine ⟨⟨sc0, n, hk, by simpa using hn1⟩, x, hkx, ?_⟩
    rw [← hv]; simpa using hn0
  case notificationCap n b r =>
    refine rdp_bind (rdp_whenE_throw _ _) fun _ => rdp_bind (rdp_liftE (rdn_getNtfnObjRef _ _)) fun _ =>
      rdp_bind (rdp_whenE_throw _ _) fun _ => rdp_returnOk fun σ => ?_
    intro _ _ _ _ _ _ t e; cases e
  all_goals exact rdp_bind (Q := fun _ _ => True) (rdp_throw _) fun _ => rdp_returnOk fun σ => by intro _ _ _ _ t e; cases e

/-- UnbindObject's decode of a thread cap: the SC's thread, not the caller. -/
theorem rdp_decodeUnbindObjPre (sc : ObjRef) (excaps : List Cap) :
    RdP (fun σ v => ∀ t, v = .invokeSchedContextUnbindObject sc (.threadCap t) →
      (∃ y n, σ.kheap sc = some (.schedContext y n) ∧ y.scTcb = some t) ∧ t ≠ σ.curThread)
      (decodeSchedContextUnbindObject (Z := Unit) sc excaps) := by
  unfold decodeSchedContextUnbindObject
  refine rdp_bind (rdp_whenE_throw _ _) fun _ => ?_
  refine rdp_bind (Q := fun _ _ => True) (rdp_returnOk fun _ => trivial) fun cap => ?_
  dsimp only
  cases cap
  case threadCap t0 =>
    refine rdp_bind (rdp_liftE (rdn_getScObjRef _ _)) fun _ => rdp_bind (rdp_whenE_throw _ _) fun _ =>
      rdp_bind (rdp_liftE (rdn_getsV _)) fun _ => rdp_bind (rdp_whenE_throw _ _) fun _ => rdp_returnOk fun σ => ?_
    intro hne hc hne2 ⟨y, n, hk, hv⟩ _ _ t e
    simp only [SchedContextInvocation.invokeSchedContextUnbindObject.injEq, Cap.threadCap.injEq, true_and] at e
    subst e
    refine ⟨⟨y, n, hk, ?_⟩, ?_⟩
    · rw [← hv]; simpa using hne2
    · rw [← hc]; exact hne
  case notificationCap n b r =>
    refine rdp_bind (rdp_liftE (rdn_getScObjRef _ _)) fun _ => rdp_bind (rdp_whenE_throw _ _) fun _ =>
      rdp_returnOk fun σ => ?_
    intro _ _ _ _ t e; cases e
  all_goals exact rdp_bind (Q := fun _ _ => True) (rdp_throw _) fun _ => rdp_returnOk fun σ => by intro _ _ _ t e; cases e

/-- YieldTo's decode: the SC's thread, not the caller. -/
theorem rdp_decodeYieldToPre (sc : ObjRef) :
    RdP (fun σ _ => ∃ y n t, σ.kheap sc = some (.schedContext y n) ∧ y.scTcb = some t ∧ t ≠ σ.curThread)
      (decodeSchedContextYieldTo (Z := Unit) sc) := by
  unfold decodeSchedContextYieldTo
  refine rdp_bind (rdp_liftE (rdn_getScObjRef _ _)) fun o => rdp_bind (rdp_whenE_throw _ _) fun _ =>
    rdp_bind (rdp_liftE (rdn_getsV _)) fun c => rdp_bind (rdp_whenE_throw _ _) fun _ =>
    rdp_bind (rdp_liftE (rdn_threadGet _ _)) fun _ => rdp_bind (rdp_liftE (rdn_threadGet _ _)) fun _ =>
    rdp_bind (rdp_whenE_throw _ _) fun _ => rdp_bind (rdp_liftE (rdn_threadGet _ _)) fun _ =>
    rdp_bind (rdp_whenE_throw _ _) fun _ => rdp_returnOk fun σ => ?_
  intro _ _ _ _ _ hsome hc hnone ⟨y, n, hk, hv⟩
  cases o with
  | none => exact absurd rfl hnone
  | some t =>
    refine ⟨y, n, t, hk, hv.symm, fun e => hsome ?_⟩
    rw [hc, e]

theorem rdp_unlessE_throw (C : Prop) [Decidable C] (e : SyscallError) :
    RdP (fun _ _ => C) (NonDetE.unlessE C (NonDetE.throwError e) : SEMonad Unit Unit) := by
  unfold NonDetE.unlessE; split
  · rename_i h; exact rdp_pure fun _ => h
  · exact rdp_throw e

theorem rdp_assertE (C : Prop) : RdP (fun _ _ => C) (NonDetE.assertE C : SEMonad Unit Unit) := by
  unfold NonDetE.assertE
  refine rdp_liftE fun σ x hx => ?_
  obtain ⟨hc, rfl⟩ := hx
  exact ⟨rfl, hc⟩

theorem the_some' {α : Type} [Nonempty α] (a : α) : the (some a) = a := rfl

/-- Configure's decoded SC is the first extra cap's. -/
theorem rdp_decodeCfgHead (label : Data) (args : List Data) (excaps : List Cap) :
    RdP (fun _ v => ∃ a rest, excaps = a :: rest ∧ ∃ q sz, a = .schedContextCap q sz ∧
      ∃ b per k bd fl, v = .invokeSchedControlConfigureFlags q b per (k + MIN_REFILLS) bd fl)
      (decodeSchedControlInvocationFlags (Z := Unit) label args excaps) := by
  unfold decodeSchedControlInvocationFlags
  simp only [retOk_bind]
  cases excaps with
  | nil =>
    refine rdp_bind (rdp_unlessE_throw _ _) fun _ => rdp_bind (rdp_whenE_throw _ _) fun _ => ?_
    repeat (first | (refine rdp_bind (rdp_whenE_throw _ _) fun _ => ?_) | (refine rdp_bind (rdp_assertE _) fun _ => ?_) | (refine rdp_returnOk fun σ => ?_))
    intros
    exact absurd rfl (by assumption : ¬ ([] : List Cap).length = 0)
  | cons a rest =>
    simp only [List.head?_cons, the_some']
    repeat (first | (refine rdp_bind (rdp_whenE_throw _ _) fun _ => ?_) | (refine rdp_bind (rdp_assertE _) fun _ => ?_) | (refine rdp_bind (rdp_unlessE_throw _ _) fun _ => ?_) | (refine rdp_returnOk fun σ => ?_))
    intros
    have h : ¬¬isSchedContextCap a = true := by assumption
    refine ⟨a, rest, rfl, ?_⟩
    cases a <;> simp [isSchedContextCap] at h
    exact ⟨_, _, rfl, _, _, _, _, _, rfl⟩

/-! ## The mid-entry facts after -/

/-- **The mid-entry facts after an `MidK` step** from a state with the
current thread's invariants and a resume action (module docstring). -/
theorem MidK.mid {T : Set U64} {σ σ' : State Unit} (hK : MidK σ σ')
    (hres : σ.schedulerAction = .resumeCurThread) (hC : CurInv σ) (hO : OffOK σ) (hA : ActIdle σ) (hI : Inv σ)
    (hcT : ∃ u ∈ T, u.bv = σ.curThread) :
    (σ'.schedulerAction = .chooseNewThread ∨ CurInv σ') ∧
      (σ'.schedulerAction = .chooseNewThread → CurOwn T σ') ∧ OffOK σ' ∧ ActIdle σ' := by
  obtain ⟨xt, hkt, hsc, hnb⟩ := hC.tcb
  obtain ⟨y0, n0, hy0⟩ := hC.sc
  obtain ⟨xt', hkt', e1, e2⟩ := hK.ctT xt hkt
  obtain ⟨y0', hy0', f1, f2, f3⟩ := hK.cscS y0 n0 hy0
  have hnr' : ∀ hcn : σ'.schedulerAction ≠ .chooseNewThread ∨ 0 < σ'.consumedTime,
      σ.curThread ∉ σ'.releaseQueue := by
    intro hc hm
    rcases hK.rq _ hm with h | ⟨-, h | ⟨h0, hcn⟩⟩
    · exact hC.notRel h
    · exact h rfl
    · rcases hc with hc | hc
      · exact hc hcn
      · rw [h0] at hc; simp at hc
  refine ⟨?_, fun hcn => ?_, fun hpos y n hy _ => ?_, ⟨fun t ht => ?_, ?_⟩⟩
  · by_cases hcn : σ'.schedulerAction = .chooseNewThread
    · exact Or.inl hcn
    right
    refine ⟨⟨xt', by rw [hK.ct]; exact hkt', by rw [e1, hK.csc]; exact hsc, by rw [e2]; exact hnb⟩,
      ⟨y0', n0, by rw [hK.csc]; exact hy0'⟩, fun hid y m hy => ?_, fun hm => hnr' (Or.inl hcn) (by rw [← hK.ct]; exact hm)⟩
    rw [hK.csc] at hid hy
    rw [hy0'] at hy; cases hy
    exact f2 (hC.active hid y0 n0 hy0)
  · obtain ⟨u, hu, hub⟩ := hcT
    obtain ⟨y1, n1, hy1, hy1t⟩ := hI.back _ xt σ.curSc hkt hsc
    rw [hy0] at hy1; cases hy1
    refine ⟨u, hu, xt', by rw [hub]; exact hkt', by rw [e1, hK.csc]; exact hsc, fun x n hx => ?_, fun hpos hm => ?_⟩
    · rw [hK.csc, hy0'] at hx; cases hx; rw [f1, hy1t, hub]
    · exact hnr' (Or.inr hpos) (by rw [← hub]; exact hm)
  · have hne : σ'.consumedTime ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
    have hc := hK.consNe hne
    rw [hK.csc, hy0'] at hy; cases hy
    have hpos0 : 0 < σ.consumedTime := by rw [← hc]; exact hpos
    obtain ⟨g1, g2, g3⟩ := hO hpos0 y0 n0 hy0 (fun hid => hC.active hid y0 n0 hy0)
    have hr : refillHd y0' = refillHd y0 := by unfold refillHd; rw [f3 hne]
    rw [hr, hc, hK.time]
    exact ⟨g1, g2, g3⟩
  · rw [hK.sw t ht] at hres; cases hres
  · obtain ⟨xi, hki, hsi, hti, hri⟩ := hA.2
    obtain ⟨xi', hki', g1, g2⟩ := hK.idT xi hki
    refine ⟨xi', by rw [hK.idle]; exact hki', by rw [g1]; exact hsi, by rw [g2]; exact hti, fun hm => ?_⟩
    rw [hK.idle] at hm
    rcases hK.rq _ hm with h | ⟨h, -⟩
    · exact hri h
    · exact h rfl

end

end Fl4Proofs.P3.Sched
