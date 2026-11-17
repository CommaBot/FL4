/-
P3, scheduling contexts: **the SC operations only cut links** (spec side
only; for the dead set across an SC step, ScDeadStep).

* `LObj o o'`: a TCB stays a TCB whose SC is kept or cleared; an SC stays an
  SC of the same size whose bound thread and notification are kept or
  cleared; a notification stays one whose SC is kept or cleared.
* `LK W σ σ'`: every object outside `W` `LObj`-steps (none stays none).
  Reflexive, transitive, monotone in `W`.
* `LKM W m`: every outcome of `m` is `LK W`-related to its start. The
  combinators mirror `NKT` (ScTK); the object updates take the `LObj` fact
  of the update (`lk_threadSet`, `lk_updateSchedContext`,
  `lk_updateSkObjRef`) or an address in `W` (`lk_threadSetW`,
  `lk_updateSchedContextW`, `lk_updateSkObjRefW`).
* The operations: Configure (`lkm_configure`), UnbindObject's two unbinds,
  a YieldTo from an SC yielded to by none, `set_thread_state` (with `W = ∅`),
  and the two binds (`W` the SC and its new thread or notification):
  `lk_invokeSchedContext`.
-/
import Fl4Proofs.P3.ScXProd
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

/-! ## The relations -/

section Rel

/-- **An object step cutting links only** (module docstring). -/
def LObj (o o' : KernelObject) : Prop :=
  (∀ x, o = .tcb x → ∃ y, o' = .tcb y ∧ (y.tcbSchedContext = x.tcbSchedContext ∨ y.tcbSchedContext = none)) ∧
  (∀ x n, o = .schedContext x n → ∃ y, o' = .schedContext y n ∧ (y.scTcb = x.scTcb ∨ y.scTcb = none) ∧
    (y.scNtfn = x.scNtfn ∨ y.scNtfn = none)) ∧
  (∀ x, o = .notification x → ∃ y, o' = .notification y ∧ (y.ntfnSc = x.ntfnSc ∨ y.ntfnSc = none))

theorem LObj.refl (o : KernelObject) : LObj o o :=
  ⟨fun x e => ⟨x, e, Or.inl rfl⟩, fun x n e => ⟨x, e, Or.inl rfl, Or.inl rfl⟩, fun x e => ⟨x, e, Or.inl rfl⟩⟩

theorem orNone_trans {α : Type} {a b c : Option α} (h1 : b = a ∨ b = none) (h2 : c = b ∨ c = none) :
    c = a ∨ c = none := by
  rcases h2 with rfl | rfl
  · exact h1
  · exact Or.inr rfl

theorem LObj.trans {a b c : KernelObject} (h1 : LObj a b) (h2 : LObj b c) : LObj a c := by
  refine ⟨fun x e => ?_, fun x n e => ?_, fun x e => ?_⟩
  · obtain ⟨y, rfl, hy⟩ := h1.1 x e
    obtain ⟨z, rfl, hz⟩ := h2.1 y rfl
    exact ⟨z, rfl, orNone_trans hy hz⟩
  · obtain ⟨y, rfl, hy1, hy2⟩ := h1.2.1 x n e
    obtain ⟨z, rfl, hz1, hz2⟩ := h2.2.1 y n rfl
    exact ⟨z, rfl, orNone_trans hy1 hz1, orNone_trans hy2 hz2⟩
  · obtain ⟨y, rfl, hy⟩ := h1.2.2 x e
    obtain ⟨z, rfl, hz⟩ := h2.2.2 y rfl
    exact ⟨z, rfl, orNone_trans hy hz⟩

theorem LObj.tcb {x y : Tcb} (h : y.tcbSchedContext = x.tcbSchedContext ∨ y.tcbSchedContext = none) :
    LObj (.tcb x) (.tcb y) :=
  ⟨fun _ e => (by cases e; exact ⟨y, rfl, h⟩), fun _ _ e => (by cases e), fun _ e => (by cases e)⟩

theorem LObj.sc {x y : SchedContext} {n : Nat} (h1 : y.scTcb = x.scTcb ∨ y.scTcb = none)
    (h2 : y.scNtfn = x.scNtfn ∨ y.scNtfn = none) : LObj (.schedContext x n) (.schedContext y n) :=
  ⟨fun _ e => (by cases e), fun _ _ e => (by cases e; exact ⟨y, rfl, h1, h2⟩), fun _ e => (by cases e)⟩

theorem LObj.ntfn {x y : Notification} (h : y.ntfnSc = x.ntfnSc ∨ y.ntfnSc = none) :
    LObj (.notification x) (.notification y) :=
  ⟨fun _ e => (by cases e), fun _ _ e => (by cases e), fun _ e => (by cases e; exact ⟨y, rfl, h⟩)⟩

/-- An object of none of the three kinds steps anywhere. -/
theorem LObj.other {o o' : KernelObject} (h1 : ∀ x, o ≠ .tcb x) (h2 : ∀ x n, o ≠ .schedContext x n)
    (h3 : ∀ x, o ≠ .notification x) : LObj o o' :=
  ⟨fun x e => absurd e (h1 x), fun x n e => absurd e (h2 x n), fun x e => absurd e (h3 x)⟩

/-- `LObj` on optional objects: none stays none. -/
def OL : Option KernelObject → Option KernelObject → Prop
  | none, none => True
  | some a, some b => LObj a b
  | _, _ => False

theorem OL.refl (o : Option KernelObject) : OL o o := by
  cases o
  · trivial
  · exact LObj.refl _

theorem OL.trans {a b c : Option KernelObject} (h1 : OL a b) (h2 : OL b c) : OL a c := by
  cases a <;> cases b <;> cases c <;> simp only [OL] at h1 h2 ⊢
  exact h1.trans h2

/-- **The link-cutting step** outside `W` (module docstring). -/
def LK (W : ObjRef → Prop) (σ σ' : State Unit) : Prop := ∀ p, W p ∨ OL (σ.kheap p) (σ'.kheap p)

theorem LK.refl (W : ObjRef → Prop) (σ : State Unit) : LK W σ σ := fun _ => Or.inr (OL.refl _)

theorem LK.trans {W : ObjRef → Prop} {σ1 σ2 σ3 : State Unit} (h1 : LK W σ1 σ2) (h2 : LK W σ2 σ3) : LK W σ1 σ3 :=
  fun p => (h1 p).elim Or.inl fun a => (h2 p).elim Or.inl fun b => Or.inr (a.trans b)

theorem LK.mono {W W' : ObjRef → Prop} {σ σ' : State Unit} (h : LK W σ σ') (hW : ∀ p, W p → W' p) : LK W' σ σ' :=
  fun p => (h p).imp (hW p) id

theorem LK.of_kheap {W : ObjRef → Prop} {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) : LK W σ σ' :=
  fun p => Or.inr (by rw [h]; exact OL.refl _)

/-- An update of `σ` at `p` with `o'`, `LObj`-related to the object there. -/
theorem LK.upd {W : ObjRef → Prop} {σ : State Unit} {p : ObjRef} {o o' : KernelObject} (hk : σ.kheap p = some o)
    (h : W p ∨ LObj o o') : LK W σ { σ with kheap := Function.update σ.kheap p (some o') } := by
  intro q
  by_cases e : q = p
  · subst e
    rcases h with h | h
    · exact Or.inl h
    · right; simp only [Function.update_self, hk, OL]; exact h
  · right; simp only [Function.update_of_ne e]; exact OL.refl _

/-- Read off an SC of `σ'` outside `W`. -/
theorem LK.sc {W : ObjRef → Prop} {σ σ' : State Unit} (h : LK W σ σ') {p : ObjRef} (hp : ¬ W p)
    {x : SchedContext} {n : Nat} (hk : σ.kheap p = some (.schedContext x n)) :
    ∃ y, σ'.kheap p = some (.schedContext y n) ∧ (y.scTcb = x.scTcb ∨ y.scTcb = none) ∧
      (y.scNtfn = x.scNtfn ∨ y.scNtfn = none) := by
  have h1 := (h p).resolve_left hp
  rw [hk] at h1
  cases h2 : σ'.kheap p with
  | none => rw [h2] at h1; exact h1.elim
  | some o =>
    rw [h2] at h1
    obtain ⟨y, rfl, hy⟩ := h1.2.1 x n rfl
    exact ⟨y, rfl, hy⟩

/-- Read off a TCB of `σ'` outside `W`. -/
theorem LK.tcb {W : ObjRef → Prop} {σ σ' : State Unit} (h : LK W σ σ') {p : ObjRef} (hp : ¬ W p)
    {x : Tcb} (hk : σ.kheap p = some (.tcb x)) :
    ∃ y, σ'.kheap p = some (.tcb y) ∧ (y.tcbSchedContext = x.tcbSchedContext ∨ y.tcbSchedContext = none) := by
  have h1 := (h p).resolve_left hp
  rw [hk] at h1
  cases h2 : σ'.kheap p with
  | none => rw [h2] at h1; exact h1.elim
  | some o =>
    rw [h2] at h1
    obtain ⟨y, rfl, hy⟩ := h1.1 x rfl
    exact ⟨y, rfl, hy⟩

/-- Read off a notification of `σ'` outside `W`. -/
theorem LK.ntfn {W : ObjRef → Prop} {σ σ' : State Unit} (h : LK W σ σ') {p : ObjRef} (hp : ¬ W p)
    {x : Notification} (hk : σ.kheap p = some (.notification x)) :
    ∃ y, σ'.kheap p = some (.notification y) ∧ (y.ntfnSc = x.ntfnSc ∨ y.ntfnSc = none) := by
  have h1 := (h p).resolve_left hp
  rw [hk] at h1
  cases h2 : σ'.kheap p with
  | none => rw [h2] at h1; exact h1.elim
  | some o =>
    rw [h2] at h1
    obtain ⟨y, rfl, hy⟩ := h1.2.2 x rfl
    exact ⟨y, rfl, hy⟩

end Rel

/-! ## The combinators -/

section Comb
variable {W : ObjRef → Prop}

/-- Every outcome cuts links only, outside `W`. -/
def LKM (W : ObjRef → Prop) {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → LK W σ x.2

theorem LKM.of_eq {α : Type} {m : NonDet (State Unit) α} (hP : LKM W m) {σ σ' : State Unit} {a : α} {X : Prop}
    (h : m σ = ({(a, σ')}, X)) : LK W σ σ' :=
  hP σ (a, σ') (by rw [h]; exact Set.mem_singleton _)

theorem LKM.mono {W' : ObjRef → Prop} {α : Type} {m : NonDet (State Unit) α} (h : LKM W m) (hW : ∀ p, W p → W' p) :
    LKM W' m := fun σ x hx => (h σ x hx).mono hW

theorem lkm_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : LKM W m)
    (hg : ∀ a, LKM W (g a)) : LKM W (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem lkm_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : LKM W m)
    (hg : ∀ a, LKM W (g a)) : LKM W (NonDet.bind m g) := lkm_bind hm hg

theorem lkm_pure {α : Type} (a : α) : LKM W (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact LK.refl _ σ

theorem lkm_pure' {α : Type} (a : α) : LKM W (NonDet.pure a : NonDet (State Unit) α) := lkm_pure a

theorem lkm_gets {α : Type} (g : State Unit → α) : LKM W (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact LK.refl _ σ

theorem lkm_get : LKM W (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact LK.refl _ σ

theorem lkm_assert (P : Prop) : LKM W (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact LK.refl _ σ

theorem lkm_fail {α : Type} : LKM W (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem lkm_assertOpt {α : Type} (o : Option α) : LKM W (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact lkm_fail
  · exact lkm_pure' _

theorem lkm_getsThe {α : Type} (g : State Unit → Option α) : LKM W (NonDet.getsThe g) := by
  intro σ x hx; exact lkm_assertOpt (g σ) σ x hx

theorem lkm_selectF {α : Type} (S : Set α × Prop) : LKM W (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact LK.refl _ σ

theorem lkm_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : LKM W m1)
    (h2 : LKM W m2) : LKM W (if P then m1 else m2) := by
  split <;> assumption

theorem lkm_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : LKM W m) :
    LKM W (NonDet.when P m) := by
  unfold NonDet.when; exact lkm_ite P h (lkm_pure' _)

theorem lkm_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : LKM W m) :
    LKM W (NonDet.unless P m) := by
  unfold NonDet.unless; exact lkm_ite P (lkm_pure' _) h

theorem lkm_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, LKM W (g a)) (o : Option α) :
    LKM W (NonDet.maybeM g o) := by
  cases o
  · exact lkm_pure' _
  · exact h _

theorem lkm_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : LKM W m) :
    LKM W (NonDet.liftM g m) := lkm_bind' h fun _ => lkm_pure' _

theorem lkm_modify {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap) : LKM W (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact LK.of_kheap (hg σ)

theorem lkm_get_put {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap) :
    LKM W (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact LK.of_kheap (hg σ)

theorem lkm_getObject (p : ObjRef) : LKM W (getObject (Z := Unit) p) := lkm_getsThe _

theorem lkm_doExtendedOp (eop : DetExtMonad Unit) : LKM W (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine lkm_bind lkm_get (fun _ => lkm_bind (lkm_selectF _) (fun _ => ?_))
  split
  exact lkm_modify (fun σ => rfl)

theorem lkm_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, LKM W (B r)) (r : α) : LKM W (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => exact LK.refl _ _
  | step _ hm _ ih => exact (hB _ _ _ hm).trans ih

theorem lkm_mapMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, LKM W (g a)) (xs : List α) :
    LKM W (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact lkm_pure' _
  | cons a xs' ih => exact lkm_bind' (h a) fun _ => ih

theorem lkm_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, LKM W (g a)) (xs : List α) :
    LKM W (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact lkm_pure' _
  | cons a xs' ih => exact lkm_bind' (h a) fun _ => lkm_bind' ih fun _ => lkm_pure' _

end Comb

/-! ## Object updates -/

section Obj
variable {W : ObjRef → Prop}

theorem lk_tcb_rw {p : ObjRef} {g : Tcb → Tcb} (hg : W p ∨ ∀ x, LObj (.tcb x) (.tcb (g x))) :
    LKM W (NonDet.getsThe (getTcb (Z := Unit) p) >>= fun tcb => setObject p (.tcb (g tcb))) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getsThe_getTcb_mem hy
  rw [hs] at hx
  obtain ⟨k, hk', -, e⟩ := setObject_mem hx
  rw [hk] at hk'; cases hk'
  rw [e]; exact LK.upd hk (hg.imp id fun h => h _)

theorem lk_threadSet {g : Tcb → Tcb} (hg : ∀ x, LObj (.tcb x) (.tcb (g x))) (p : ObjRef) :
    LKM W (threadSet (Z := Unit) g p) := lk_tcb_rw (Or.inr hg)

theorem lk_threadSetW (g : Tcb → Tcb) {p : ObjRef} (hp : W p) : LKM W (threadSet (Z := Unit) g p) :=
  lk_tcb_rw (Or.inl hp)

theorem lk_updateSchedContext' {g : SchedContext → SchedContext} {p : ObjRef}
    (hg : W p ∨ ∀ x n, LObj (.schedContext x n) (.schedContext (g x) n)) :
    LKM W (updateSchedContext (Z := Unit) p g) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getObject_mem hy
  obtain ⟨o, σ1⟩ := y
  simp only at hk hs hx; subst hs
  cases o
  all_goals try exact hx.elim
  obtain ⟨k, hk', -, e⟩ := setObject_mem hx
  rw [hk] at hk'; cases hk'
  rw [e]; exact LK.upd hk (hg.imp id fun h => h _ _)

theorem lk_updateSchedContext {g : SchedContext → SchedContext}
    (hg : ∀ x n, LObj (.schedContext x n) (.schedContext (g x) n)) (p : ObjRef) :
    LKM W (updateSchedContext (Z := Unit) p g) := lk_updateSchedContext' (Or.inr hg)

theorem lk_updateSchedContextW (g : SchedContext → SchedContext) {p : ObjRef} (hp : W p) :
    LKM W (updateSchedContext (Z := Unit) p g) := lk_updateSchedContext' (Or.inl hp)

theorem lk_updateSkObjRef' {α : Type} [Nonempty α] {C : α → KernelObject}
    {g : (Option ObjRef → Option ObjRef) → α → α} {new : Option ObjRef} {ref : ObjRef}
    (hg : W ref ∨ ∀ a, LObj (C a) (C (g (fun _ => new) a))) :
    LKM W (updateSkObjRef (Z := Unit) C g ref new) := by
  intro σ x ⟨y, hy, hx⟩
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
    have hC := partialInv_eq he
    subst hC
    obtain ⟨z1, hz1, hx⟩ := hx
    obtain ⟨hk1, hs1⟩ := getObject_mem hz1
    obtain ⟨z2, hz2, hx⟩ := hx
    obtain ⟨-, rfl⟩ := hz2
    obtain ⟨z3, hz3, hx⟩ := hx
    obtain ⟨-, rfl⟩ := hz3
    simp only at hx
    rw [hs1] at hx
    obtain ⟨k, hk', -, e'⟩ := setObject_mem hx
    rw [e']; exact LK.upd hk (hg.imp id fun h => h e)

theorem lk_updateSkObjRef {α : Type} [Nonempty α] {C : α → KernelObject}
    {g : (Option ObjRef → Option ObjRef) → α → α} {new : Option ObjRef}
    (hg : ∀ a, LObj (C a) (C (g (fun _ => new) a))) (ref : ObjRef) :
    LKM W (updateSkObjRef (Z := Unit) C g ref new) := lk_updateSkObjRef' (Or.inr hg)

theorem lk_updateSkObjRefW {α : Type} [Nonempty α] (C : α → KernelObject)
    (g : (Option ObjRef → Option ObjRef) → α → α) (new : Option ObjRef) {ref : ObjRef} (hp : W ref) :
    LKM W (updateSkObjRef (Z := Unit) C g ref new) := lk_updateSkObjRef' (Or.inl hp)

end Obj

/-! ## The operations -/

/-- The `LObj` side goals of the object updates: a field other than the links,
or a link cleared. -/
macro "lobj_tac" : tactic => `(tactic| first
  | exact LObj.tcb (Or.inl rfl) | exact LObj.tcb (Or.inr rfl)
  | exact LObj.sc (Or.inl rfl) (Or.inl rfl) | exact LObj.sc (Or.inr rfl) (Or.inl rfl)
  | exact LObj.sc (Or.inl rfl) (Or.inr rfl)
  | exact LObj.ntfn (Or.inl rfl) | exact LObj.ntfn (Or.inr rfl)
  | (exact LObj.other (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)))

macro "lkm_step0" : tactic => `(tactic| first
  | with_reducible exact lkm_pure _ | with_reducible exact lkm_pure' _ | with_reducible exact lkm_fail
  | with_reducible exact lkm_gets _ | with_reducible exact lkm_get
  | with_reducible exact lkm_assert _ | with_reducible exact lkm_assertOpt _
  | with_reducible exact lkm_getObject _ | with_reducible exact lkm_getsThe _
  | with_reducible exact lkm_selectF _
  | ((with_reducible apply lkm_modify); intro _; rfl)
  | ((with_reducible apply lkm_get_put); intro _; rfl)
  | with_reducible exact lkm_doExtendedOp _
  | ((with_reducible apply lk_threadSet); intro _; lobj_tac)
  | ((with_reducible apply lk_updateSchedContext); intro _ _; lobj_tac)
  | ((with_reducible apply lk_updateSkObjRef); intro _; lobj_tac)
  | (with_reducible refine lkm_bind ?_ (fun _ => ?_))
  | (with_reducible refine lkm_bind' ?_ (fun _ => ?_))
  | (with_reducible apply lkm_ite) | (with_reducible apply lkm_when) | (with_reducible apply lkm_unless)
  | (with_reducible refine lkm_maybeM (fun _ => ?_) _) | (with_reducible apply lkm_liftM)
  | (with_reducible refine lkm_whileLoop (fun _ => ?_) _)
  | (with_reducible refine lkm_mapMx (fun _ => ?_) _)
  | (with_reducible refine lkm_mapM (fun _ => ?_) _)
  | split
  | (dsimp only))

section Ops
variable {W : ObjRef → Prop}

theorem lkm_getSchedContext (p : ObjRef) : LKM W (getSchedContext (Z := Unit) p) := by
  unfold getSchedContext; repeat lkm_step0

theorem lkm_threadGet {α : Type} (g : Tcb → α) (p : ObjRef) : LKM W (threadGet (Z := Unit) g p) := by
  unfold threadGet; repeat lkm_step0

theorem lkm_getScObjRef (g : SchedContext → Option ObjRef) (p : ObjRef) :
    LKM W (getScObjRef (Z := Unit) g p) := by
  unfold getScObjRef; exact lkm_bind (lkm_getSchedContext p) fun _ => lkm_pure _

theorem lkm_tcbSchedAction (a : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    LKM W (tcbSchedAction (Z := Unit) a t) := by
  unfold tcbSchedAction getTcbQueue setTcbQueue
  refine lkm_bind (lkm_threadGet _ _) fun _ => lkm_bind (lkm_threadGet _ _) fun _ => ?_
  repeat lkm_step0

macro "lkm_step" : tactic => `(tactic| first
  | with_reducible exact lkm_threadGet _ _ | with_reducible exact lkm_getSchedContext _
  | with_reducible exact lkm_getScObjRef _ _ | with_reducible exact lkm_tcbSchedAction _ _
  | lkm_step0)

macro "lkm_auto" : tactic => `(tactic| repeat lkm_step)

theorem lkm_rescheduleRequired : LKM W (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired setSchedulerAction getScRefillSufficient getScRefillReady
  lkm_auto

theorem lkm_tcbReleaseRemove (t : ObjRef) : LKM W (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove setReleaseQueue; lkm_auto

theorem lkm_tcbReleaseEnqueue (t : ObjRef) : LKM W (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue readyTimesAppend orderedInsert setReleaseQueue; lkm_auto

theorem lkm_postpone (p : ObjRef) : LKM W (postpone (Z := Unit) p) := by
  unfold postpone
  refine lkm_bind (lkm_getScObjRef _ _) fun _ => lkm_bind (lkm_assertOpt _) fun _ => ?_
  exact lkm_bind (lkm_tcbSchedAction _ _) fun _ => lkm_bind (lkm_tcbReleaseEnqueue _) fun _ =>
    lkm_modify (fun σ => rfl)

theorem lkm_schedContextResume (p : ObjRef) : LKM W (schedContextResume (Z := Unit) p) := by
  unfold schedContextResume getScRefillReady getScRefillSufficient getTcbQueue
  refine lkm_bind (lkm_getSchedContext _) fun _ => lkm_bind (lkm_assertOpt _) fun _ => ?_
  refine lkm_bind (lkm_gets _) fun _ => lkm_when _ ?_
  refine lkm_bind (lkm_threadGet _ _) fun _ => lkm_bind (lkm_getsThe _) fun _ =>
    lkm_bind (lkm_getsThe _) fun _ => lkm_when _ ?_
  refine lkm_bind (lkm_threadGet _ _) fun _ => lkm_bind (lkm_threadGet _ _) fun _ => ?_
  exact lkm_bind (lkm_bind (lkm_gets _) fun _ => lkm_pure _) fun _ =>
    lkm_bind (lkm_assert _) fun _ => lkm_postpone _

theorem lkm_refillUnblockCheck (p : ObjRef) : LKM W (refillUnblockCheck (Z := Unit) p) := by
  unfold refillUnblockCheck isRoundRobin getScRefillReady refillHeadOverlappingLoop mergeOverlappingRefills
    refillPopHead updateRefillHd getRefillHead
  refine lkm_bind (lkm_bind (lkm_getSchedContext _) fun _ => lkm_pure _) fun _ => ?_
  lkm_auto

theorem lkm_ifCondRefillUnblockCheck (o : Option ObjRef) (a b : Option Bool) :
    LKM W (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck
  refine lkm_maybeM (fun _ => ?_) _
  refine lkm_bind (lkm_getSchedContext _) fun _ => lkm_bind (lkm_gets _) fun _ =>
    lkm_bind (lkm_pure _) fun _ => lkm_when _ (lkm_when _ (lkm_refillUnblockCheck _))

theorem lkm_commitTime : LKM W (commitTime (Z := Unit)) := by
  unfold commitTime refillBudgetCheckRoundRobin refillBudgetCheck
  repeat (first | unfold updateRefillHd | unfold updateRefillTl | unfold refillAddTail | unfold refillPopHead | unfold getRefillHead | unfold getRefills | unfold getRefillTail | unfold refillFull | unfold refillSingle | unfold refillSize | unfold scheduleUsed | unfold chargeEntireHeadRefill | unfold handleOverrun | unfold headInsufficientLoop | unfold mergeNonoverlappingHeadRefill | unfold isRoundRobin | unfold getScActive | unfold getScRefillReady | unfold maybeAddEmptyTail)
  lkm_auto

theorem lkm_refillNew (p : ObjRef) (m : Nat) (b per : Ticks) : LKM W (refillNew (Z := Unit) p m b per) := by
  unfold refillNew
  repeat (first | unfold updateRefillHd | unfold updateRefillTl | unfold refillAddTail | unfold refillPopHead | unfold getRefillHead | unfold getRefills | unfold getRefillTail | unfold refillFull | unfold refillSingle | unfold refillSize | unfold scheduleUsed | unfold chargeEntireHeadRefill | unfold handleOverrun | unfold headInsufficientLoop | unfold mergeNonoverlappingHeadRefill | unfold isRoundRobin | unfold getScActive | unfold getScRefillReady | unfold maybeAddEmptyTail)
  lkm_auto

theorem lkm_refillUpdate (p : ObjRef) (per b : Ticks) (m : Nat) : LKM W (refillUpdate (Z := Unit) p per b m) := by
  unfold refillUpdate
  repeat (first | unfold updateRefillHd | unfold updateRefillTl | unfold refillAddTail | unfold refillPopHead | unfold getRefillHead | unfold getRefills | unfold getRefillTail | unfold refillFull | unfold refillSingle | unfold refillSize | unfold scheduleUsed | unfold chargeEntireHeadRefill | unfold handleOverrun | unfold headInsufficientLoop | unfold mergeNonoverlappingHeadRefill | unfold isRoundRobin | unfold getScActive | unfold getScRefillReady | unfold maybeAddEmptyTail)
  lkm_auto

theorem lkm_possibleSwitchTo (t : ObjRef) : LKM W (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo getTcbObjRef setSchedulerAction
  refine lkm_bind (lkm_threadGet _ _) fun _ => lkm_bind (lkm_gets _) fun _ => lkm_when _ ?_
  refine lkm_bind (lkm_gets _) fun _ => lkm_bind (lkm_threadGet _ _) fun _ => lkm_bind (lkm_gets _)
    fun _ => ?_
  split
  · exact lkm_tcbSchedAction _ _
  · split
    · exact lkm_bind lkm_rescheduleRequired fun _ => lkm_tcbSchedAction _ _
    · lkm_auto

macro "lkm_step2" : tactic => `(tactic| first
  | with_reducible exact lkm_commitTime | with_reducible exact lkm_refillNew _ _ _ _
  | with_reducible exact lkm_refillUpdate _ _ _ _ | with_reducible exact lkm_possibleSwitchTo _
  | with_reducible exact lkm_rescheduleRequired | with_reducible exact lkm_schedContextResume _
  | with_reducible exact lkm_tcbReleaseRemove _ | lkm_step)

/-- **SchedControl `ConfigureFlags` cuts links only.** -/
theorem lkm_configure (iv : SchedControlInvocation) :
    LKM W (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags getThreadState getScActive
  repeat lkm_step2

theorem lkm_setThreadState (t : ObjRef) (ts : ThreadState) : LKM W (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; repeat lkm_step2

theorem lkm_schedContextUnbindTcb (p : ObjRef) : LKM W (schedContextUnbindTcb (Z := Unit) p) := by
  unfold schedContextUnbindTcb; repeat lkm_step2

theorem lkm_schedContextUnbindNtfn (p : ObjRef) : LKM W (schedContextUnbindNtfn (Z := Unit) p) := by
  unfold schedContextUnbindNtfn; repeat lkm_step2

theorem lkm_returnConsumed (p : ObjRef) : LKM W (returnConsumed (Z := Unit) p) := by
  unfold returnConsumed schedContextUpdateConsumed; repeat lkm_step2

/-- **Bind of a TCB** cuts links only outside the SC and the thread. -/
theorem lkm_schedContextBindTcb (sc t : ObjRef) :
    LKM (fun p => p = sc ∨ p = t) (schedContextBindTcb (Z := Unit) sc t) := by
  unfold schedContextBindTcb
  refine lkm_bind (lk_threadSetW _ (Or.inr rfl)) fun _ => lkm_bind (lk_updateSchedContextW _ (Or.inl rfl)) fun _ =>
    lkm_bind (lkm_ifCondRefillUnblockCheck _ _ _) fun _ =>
    lkm_bind (lkm_schedContextResume _) fun _ => lkm_bind (lkm_gets _) fun _ => lkm_when _ ?_
  exact lkm_bind (lkm_tcbSchedAction _ _) fun _ => lkm_rescheduleRequired

/-- **Bind of a notification** cuts links only outside the SC and the
notification. -/
theorem lkm_schedContextBindNtfn (sc n : ObjRef) :
    LKM (fun p => p = sc ∨ p = n) (schedContextBindNtfn (Z := Unit) sc n) := by
  unfold schedContextBindNtfn
  exact lkm_bind (lk_updateSkObjRefW _ _ _ (Or.inr rfl)) fun _ => lk_updateSchedContextW _ (Or.inl rfl)

/-- **A YieldTo from an SC yielded to by none** cuts links only. -/
theorem lk_schedContextYieldTo {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) (hyf : x.scYieldFrom = none) :
    ∀ y ∈ (schedContextYieldTo (Z := Unit) p σ).1, LK W σ y.2 := by
  intro y hy
  unfold schedContextYieldTo at hy
  rw [nd_bind_one (getScObjRef_eq hk _), hyf] at hy
  refine (show LKM W _ from ?_) σ y hy
  refine lkm_bind ?_ fun _ => ?_
  · unfold NonDet.when; simp only [ne_eq, not_true_eq_false, ↓reduceIte]; exact lkm_pure' _
  unfold returnConsumed schedContextUpdateConsumed
  repeat lkm_step2

end Ops

/-- The objects a SchedContext invocation may link: Bind's SC and its new
thread or notification, none for the others. -/
def invLinkW : SchedContextInvocation → ObjRef → Prop
  | .invokeSchedContextBind sc (.threadCap t), p => p = sc ∨ p = t
  | .invokeSchedContextBind sc (.notificationCap n _ _), p => p = sc ∨ p = n
  | _, _ => False

/-- **The SC invocations cut links only** outside `invLinkW`: Bind,
UnbindObject, and a YieldTo from an SC yielded to by none. -/
theorem lk_invokeSchedContext {σ : State Unit} {inv : SchedContextInvocation}
    (h : (∃ sc cap, inv = .invokeSchedContextBind sc cap) ∨ (∃ sc cap, inv = .invokeSchedContextUnbindObject sc cap) ∨
      (∃ sc x n, inv = .invokeSchedContextYieldTo sc ∧ σ.kheap sc = some (.schedContext x n) ∧ x.scYieldFrom = none)) :
    ∀ y ∈ (invokeSchedContext (Z := Unit) inv σ).1, LK (invLinkW inv) σ y.2 := by
  rcases h with ⟨sc, cap, rfl⟩ | ⟨sc, cap, rfl⟩ | ⟨sc, x, n, rfl, hk, hyf⟩
  · refine (show LKM (invLinkW (.invokeSchedContextBind sc cap))
      (invokeSchedContext (Z := Unit) (.invokeSchedContextBind sc cap)) from ?_) σ
    unfold invokeSchedContext
    cases cap
    all_goals first
      | exact lkm_fail
      | exact lkm_bind (lkm_schedContextBindTcb _ _) fun _ => lkm_pure _
      | exact lkm_bind (lkm_schedContextBindNtfn _ _) fun _ => lkm_pure _
  · refine (show LKM (invLinkW (.invokeSchedContextUnbindObject sc cap))
      (invokeSchedContext (Z := Unit) (.invokeSchedContextUnbindObject sc cap)) from ?_) σ
    unfold invokeSchedContext
    cases cap
    all_goals first
      | exact lkm_fail
      | exact lkm_bind (lkm_schedContextUnbindTcb _) fun _ => lkm_pure _
      | exact lkm_bind (lkm_schedContextUnbindNtfn _) fun _ => lkm_pure _
  · exact lk_schedContextYieldTo hk hyf

end

end Fl4Proofs.P3.Sched
