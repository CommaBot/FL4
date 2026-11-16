/-
P3, scheduling contexts: **the spec steps of the SC caps' invocations
change only scheduling fields** (`ScTK`), what the IPC and VSpace
relations need to be framed across them (`tcbsc_step_lift`, ScXStep).

* `TKObj P o o'`: a TCB changes only its state, SC and yield-to fields, its
  state only when `P` and between states that block on no IPC object
  (`IpcFree`); an SC keeps its size; a notification changes only its SC;
  every other object stays.
* `ScTKw P σ σ'`: every object `TKObj`-steps (`P` per address), and the user
  memory, the CDT, the original caps, the domain schedule, the arch state,
  the interrupt states and nodes and the current thread are kept.
* `NKT m`: every outcome of `m` is `ScTKw (fun _ => False)`-related to its
  start (no thread changes state). The combinators mirror `Pres` (ScPres);
  the operations: `schedContextResume`, `postpone`, `possibleSwitchTo`,
  `rescheduleRequired`, `commitTime`, `refillNew`, `refillUpdate`,
  `schedContextBindTcb`, `schedContextBindNtfn`,
  `invokeSchedControlConfigureFlags`.
-/
import Fl4Proofs.P3.ScPresCfg
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical

noncomputable section

section Rel

/-- A thread state that blocks on no endpoint, notification or reply. -/
def IpcFree (ts : ThreadState) : Prop :=
  epBlocked ts = none ∧ ntfnBlocked ts = none ∧ ∀ r, ts ≠ .blockedOnReply r

/-- A TCB changed only in its state, SC and yield-to fields. -/
def TcbSchedOnly (x y : Tcb) : Prop :=
  y = { x with tcbState := y.tcbState, tcbSchedContext := y.tcbSchedContext, tcbYieldTo := y.tcbYieldTo }

theorem TcbSchedOnly.refl (x : Tcb) : TcbSchedOnly x x := rfl

theorem TcbSchedOnly.trans {x y z : Tcb} (h1 : TcbSchedOnly x y) (h2 : TcbSchedOnly y z) : TcbSchedOnly x z := by
  unfold TcbSchedOnly at *; rw [h2, h1]

/-- **The object steps of the SC code** (module docstring). -/
def TKObj (P : Prop) (o o' : KernelObject) : Prop :=
  o' = o ∨
  (∃ x y, o = .tcb x ∧ o' = .tcb y ∧ TcbSchedOnly x y ∧
    (y.tcbState = x.tcbState ∨ (P ∧ IpcFree x.tcbState ∧ IpcFree y.tcbState))) ∨
  (∃ x y n, o = .schedContext x n ∧ o' = .schedContext y n) ∨
  (∃ x y, o = .notification x ∧ o' = .notification y ∧ y = { x with ntfnSc := y.ntfnSc })

theorem TKObj.refl (P : Prop) (o : KernelObject) : TKObj P o o := Or.inl rfl

theorem TKObj.trans {P : Prop} {a b c : KernelObject} (h1 : TKObj P a b) (h2 : TKObj P b c) : TKObj P a c := by
  rcases h1 with rfl | ⟨x, y, rfl, rfl, e1, s1⟩ | ⟨x, y, n, rfl, rfl⟩ | ⟨x, y, rfl, rfl, e1⟩
  · exact h2
  · rcases h2 with rfl | ⟨y', z, e, rfl, e2, s2⟩ | ⟨_, _, _, e, -⟩ | ⟨_, _, e, -⟩
    · exact Or.inr (Or.inl ⟨x, y, rfl, rfl, e1, s1⟩)
    · cases e
      refine Or.inr (Or.inl ⟨x, z, rfl, rfl, e1.trans e2, ?_⟩)
      rcases s1 with s1 | ⟨p1, f1, g1⟩ <;> rcases s2 with s2 | ⟨p2, f2, g2⟩
      · exact Or.inl (s2.trans s1)
      · exact Or.inr ⟨p2, s1 ▸ f2, g2⟩
      · exact Or.inr ⟨p1, f1, s2 ▸ g1⟩
      · exact Or.inr ⟨p1, f1, g2⟩
    · cases e
    · cases e
  · rcases h2 with rfl | ⟨_, _, e, -⟩ | ⟨y', z, m, e, rfl⟩ | ⟨_, _, e, -⟩
    · exact Or.inr (Or.inr (Or.inl ⟨x, y, n, rfl, rfl⟩))
    · cases e
    · cases e; exact Or.inr (Or.inr (Or.inl ⟨x, z, n, rfl, rfl⟩))
    · cases e
  · rcases h2 with rfl | ⟨_, _, e, -⟩ | ⟨_, _, _, e, -⟩ | ⟨y', z, e, rfl, e2⟩
    · exact Or.inr (Or.inr (Or.inr ⟨x, y, rfl, rfl, e1⟩))
    · cases e
    · cases e
    · cases e; refine Or.inr (Or.inr (Or.inr ⟨x, z, rfl, rfl, ?_⟩)); rw [e2, e1]

theorem TKObj.mono {P Q : Prop} {a b : KernelObject} (h : TKObj P a b) (hPQ : P → Q) : TKObj Q a b := by
  rcases h with h | ⟨x, y, h1, h2, h3, h4⟩ | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨x, y, h1, h2, h3, h4.imp_right fun ⟨p, f, g⟩ => ⟨hPQ p, f, g⟩⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- `TKObj` on optional objects: none stays none. -/
def OTK (P : Prop) : Option KernelObject → Option KernelObject → Prop
  | none, none => True
  | some a, some b => TKObj P a b
  | _, _ => False

theorem OTK.refl (P : Prop) (o : Option KernelObject) : OTK P o o := by
  cases o <;> simp [OTK, TKObj.refl]

theorem OTK.trans {P : Prop} {a b c : Option KernelObject} (h1 : OTK P a b) (h2 : OTK P b c) : OTK P a c := by
  cases a <;> cases b <;> cases c <;> simp only [OTK] at h1 h2 ⊢
  exact h1.trans h2

theorem OTK.mono {P Q : Prop} {a b : Option KernelObject} (h : OTK P a b) (hPQ : P → Q) : OTK Q a b := by
  cases a <;> cases b <;> simp only [OTK] at h ⊢
  exact h.mono hPQ

/-- **The SC code's spec step** (module docstring). -/
structure ScTKw (P : ObjRef → Prop) (σ σ' : State Unit) : Prop where
  kh : ∀ p, OTK (P p) (σ.kheap p) (σ'.kheap p)
  um : σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory
  cdt : σ'.cdt = σ.cdt
  orig : σ'.isOriginalCap = σ.isOriginalCap
  dl : σ'.domainList = σ.domainList
  dsi : σ'.domainStartIndex = σ.domainStartIndex
  arch : σ'.archState = σ.archState
  ist : σ'.interruptStates = σ.interruptStates
  inode : σ'.interruptIrqNode = σ.interruptIrqNode
  ct : σ'.curThread = σ.curThread

theorem ScTKw.refl (P : ObjRef → Prop) (σ : State Unit) : ScTKw P σ σ :=
  ⟨fun _ => OTK.refl _ _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ScTKw.trans {P : ObjRef → Prop} {σ1 σ2 σ3 : State Unit} (h1 : ScTKw P σ1 σ2) (h2 : ScTKw P σ2 σ3) :
    ScTKw P σ1 σ3 :=
  ⟨fun p => (h1.kh p).trans (h2.kh p), h2.um.trans h1.um, h2.cdt.trans h1.cdt, h2.orig.trans h1.orig,
    h2.dl.trans h1.dl, h2.dsi.trans h1.dsi, h2.arch.trans h1.arch, h2.ist.trans h1.ist, h2.inode.trans h1.inode,
    h2.ct.trans h1.ct⟩

theorem ScTKw.mono {P Q : ObjRef → Prop} {σ σ' : State Unit} (h : ScTKw P σ σ') (hPQ : ∀ p, P p → Q p) :
    ScTKw Q σ σ' :=
  ⟨fun p => (h.kh p).mono (hPQ p), h.um, h.cdt, h.orig, h.dl, h.dsi, h.arch, h.ist, h.inode, h.ct⟩

/-- An update of `σ` at `p` with `o'`, `TKObj`-related to the object there. -/
theorem ScTKw.upd {P : ObjRef → Prop} {σ : State Unit} {p : ObjRef} {o o' : KernelObject} (hk : σ.kheap p = some o)
    (h : TKObj (P p) o o') : ScTKw P σ { σ with kheap := Function.update σ.kheap p (some o') } := by
  refine ⟨fun q => ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_cases e : q = p
  · subst e; simp only [Function.update_self, hk, OTK]; exact h
  · simp only [Function.update_of_ne e]; exact OTK.refl _ _

end Rel

/-! ## The combinators -/

section Comb

/-- Every outcome changes only scheduling fields, no thread state. -/
def NKT {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → ScTKw (fun _ => False) σ x.2

theorem NKT.of_eq {α : Type} {m : NonDet (State Unit) α} (hP : NKT m) {σ σ' : State Unit} {a : α} {X : Prop}
    (h : m σ = ({(a, σ')}, X)) : ScTKw (fun _ => False) σ σ' :=
  hP σ (a, σ') (by rw [h]; exact Set.mem_singleton _)

theorem nkt_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : NKT m)
    (hg : ∀ a, NKT (g a)) : NKT (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem nkt_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : NKT m)
    (hg : ∀ a, NKT (g a)) : NKT (NonDet.bind m g) := nkt_bind hm hg

theorem nkt_pure {α : Type} (a : α) : NKT (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ScTKw.refl _ σ

theorem nkt_pure' {α : Type} (a : α) : NKT (NonDet.pure a : NonDet (State Unit) α) := nkt_pure a

theorem nkt_gets {α : Type} (g : State Unit → α) : NKT (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ScTKw.refl _ σ

theorem nkt_get : NKT (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ScTKw.refl _ σ

theorem nkt_assert (P : Prop) : NKT (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact ScTKw.refl _ σ

theorem nkt_fail {α : Type} : NKT (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem nkt_assertOpt {α : Type} (o : Option α) : NKT (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact nkt_fail
  · exact nkt_pure' _

theorem nkt_getsThe {α : Type} (g : State Unit → Option α) : NKT (NonDet.getsThe g) := by
  intro σ x hx; exact nkt_assertOpt (g σ) σ x hx

theorem nkt_selectF {α : Type} (S : Set α × Prop) : NKT (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact ScTKw.refl _ σ

theorem nkt_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : NKT m1)
    (h2 : NKT m2) : NKT (if P then m1 else m2) := by
  split <;> assumption

theorem nkt_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : NKT m) :
    NKT (NonDet.when P m) := by
  unfold NonDet.when; exact nkt_ite P h (nkt_pure' _)

theorem nkt_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : NKT m) :
    NKT (NonDet.unless P m) := by
  unfold NonDet.unless; exact nkt_ite P (nkt_pure' _) h

theorem nkt_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, NKT (g a)) (o : Option α) :
    NKT (NonDet.maybeM g o) := by
  cases o
  · exact nkt_pure' _
  · exact h _

theorem nkt_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : NKT m) :
    NKT (NonDet.liftM g m) := nkt_bind' h fun _ => nkt_pure' _

/-- The fields a state update must keep. -/
def TKKeep (σ σ' : State Unit) : Prop :=
  σ'.kheap = σ.kheap ∧ σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory ∧ σ'.cdt = σ.cdt ∧
    σ'.isOriginalCap = σ.isOriginalCap ∧ σ'.domainList = σ.domainList ∧ σ'.domainStartIndex = σ.domainStartIndex ∧
    σ'.archState = σ.archState ∧ σ'.interruptStates = σ.interruptStates ∧
    σ'.interruptIrqNode = σ.interruptIrqNode ∧ σ'.curThread = σ.curThread

theorem ScTKw.of_keep {P : ObjRef → Prop} {σ σ' : State Unit} (h : TKKeep σ σ') : ScTKw P σ σ' := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := h
  exact ⟨fun p => by rw [e1]; exact OTK.refl _ _, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩

theorem nkt_modify {g : State Unit → State Unit} (hg : ∀ σ, TKKeep σ (g σ)) : NKT (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ScTKw.of_keep (hg σ)

theorem nkt_get_put {g : State Unit → State Unit} (hg : ∀ σ, TKKeep σ (g σ)) :
    NKT (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ScTKw.of_keep (hg σ)

theorem nkt_getObject (p : ObjRef) : NKT (getObject (Z := Unit) p) := nkt_getsThe _

theorem nkt_doExtendedOp (eop : DetExtMonad Unit) : NKT (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine nkt_bind nkt_get (fun _ => nkt_bind (nkt_selectF _) (fun _ => ?_))
  split
  exact nkt_modify (fun σ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem nkt_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, NKT (B r)) (r : α) : NKT (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => exact ScTKw.refl _ _
  | step _ hm _ ih => exact (hB _ _ _ hm).trans ih

theorem nkt_mapMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, NKT (g a)) (xs : List α) :
    NKT (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact nkt_pure' _
  | cons a xs' ih => exact nkt_bind' (h a) fun _ => ih

theorem nkt_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, NKT (g a)) (xs : List α) :
    NKT (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact nkt_pure' _
  | cons a xs' ih => exact nkt_bind' (h a) fun _ => nkt_bind' ih fun _ => nkt_pure' _

end Comb

/-! ## Object updates -/

section Obj

theorem nkt_setObject {p : ObjRef} {o : KernelObject} (h : ∀ k, aType k = aType o → TKObj False k o) :
    NKT (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨k, hk, hty, e⟩ := setObject_mem hx
  rw [e]; exact ScTKw.upd hk (h k hty)

theorem nkt_tcb_rw {p : ObjRef} {g : Tcb → Tcb} (hg : ∀ x, TKObj False (.tcb x) (.tcb (g x))) :
    NKT (NonDet.getsThe (getTcb (Z := Unit) p) >>= fun tcb => setObject p (.tcb (g tcb))) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getsThe_getTcb_mem hy
  rw [hs] at hx
  obtain ⟨k, hk', -, e⟩ := setObject_mem hx
  rw [hk] at hk'; cases hk'
  rw [e]; exact ScTKw.upd hk (hg _)

theorem nkt_threadSet {g : Tcb → Tcb} (hg : ∀ x, TKObj False (.tcb x) (.tcb (g x))) (p : ObjRef) :
    NKT (threadSet (Z := Unit) g p) := nkt_tcb_rw hg

theorem nkt_updateSchedContext (g : SchedContext → SchedContext) (p : ObjRef) :
    NKT (updateSchedContext (Z := Unit) p g) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getObject_mem hy
  obtain ⟨o, σ1⟩ := y
  simp only at hk hs hx; subst hs
  cases o
  all_goals first | exact hx.elim | skip
  obtain ⟨k, hk', -, e⟩ := setObject_mem hx
  rw [hk] at hk'; cases hk'
  rw [e]; exact ScTKw.upd hk (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩)))

theorem nkt_updateSkObjRef {α : Type} [Nonempty α] {C : α → KernelObject}
    {g : (Option ObjRef → Option ObjRef) → α → α} {new : Option ObjRef}
    (hg : ∀ a, TKObj False (C a) (C (g (fun _ => new) a))) (ref : ObjRef) :
    NKT (updateSkObjRef (Z := Unit) C g ref new) := by
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
    rw [e']; exact ScTKw.upd hk (hg e)

end Obj

/-! ## The operations -/

macro "nkt_step0" : tactic => `(tactic| first
  | with_reducible exact nkt_pure _ | with_reducible exact nkt_pure' _ | with_reducible exact nkt_fail
  | with_reducible exact nkt_gets _ | with_reducible exact nkt_get
  | with_reducible exact nkt_assert _ | with_reducible exact nkt_assertOpt _
  | with_reducible exact nkt_getObject _ | with_reducible exact nkt_getsThe _
  | with_reducible exact nkt_selectF _
  | ((with_reducible apply nkt_modify); intro _; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  | ((with_reducible apply nkt_get_put); intro _; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  | with_reducible exact nkt_doExtendedOp _
  | ((with_reducible apply nkt_threadSet); intro _; exact Or.inr (Or.inl ⟨_, _, rfl, rfl, rfl, Or.inl rfl⟩))
  | with_reducible exact nkt_updateSchedContext _ _
  | ((with_reducible apply nkt_updateSkObjRef); intro _; exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, rfl, rfl⟩)))
  | ((with_reducible apply nkt_updateSkObjRef); intro _; exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, rfl⟩)))
  | ((with_reducible apply nkt_updateSkObjRef); intro _; exact Or.inr (Or.inl ⟨_, _, rfl, rfl, rfl, Or.inl rfl⟩))
  | (with_reducible refine nkt_bind ?_ (fun _ => ?_))
  | (with_reducible refine nkt_bind' ?_ (fun _ => ?_))
  | (with_reducible apply nkt_ite) | (with_reducible apply nkt_when) | (with_reducible apply nkt_unless)
  | (with_reducible refine nkt_maybeM (fun _ => ?_) _) | (with_reducible apply nkt_liftM)
  | (with_reducible refine nkt_whileLoop (fun _ => ?_) _)
  | (with_reducible refine nkt_mapMx (fun _ => ?_) _)
  | (with_reducible refine nkt_mapM (fun _ => ?_) _)
  | split
  | (dsimp only))

theorem nkt_getSchedContext (p : ObjRef) : NKT (getSchedContext (Z := Unit) p) := by
  unfold getSchedContext; repeat nkt_step0

theorem nkt_threadGet {α : Type} (g : Tcb → α) (p : ObjRef) : NKT (threadGet (Z := Unit) g p) := by
  unfold threadGet; repeat nkt_step0

theorem nkt_getScObjRef (g : SchedContext → Option ObjRef) (p : ObjRef) :
    NKT (getScObjRef (Z := Unit) g p) := by
  unfold getScObjRef; exact nkt_bind (nkt_getSchedContext p) fun _ => nkt_pure _

theorem nkt_tcbSchedAction (a : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    NKT (tcbSchedAction (Z := Unit) a t) := by
  unfold tcbSchedAction getTcbQueue setTcbQueue
  refine nkt_bind (nkt_threadGet _ _) fun _ => nkt_bind (nkt_threadGet _ _) fun _ => ?_
  repeat nkt_step0

macro "nkt_step" : tactic => `(tactic| first
  | with_reducible exact nkt_threadGet _ _ | with_reducible exact nkt_getSchedContext _
  | with_reducible exact nkt_getScObjRef _ _ | with_reducible exact nkt_tcbSchedAction _ _
  | nkt_step0)

macro "nkt_auto" : tactic => `(tactic| repeat nkt_step)

theorem nkt_rescheduleRequired : NKT (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired setSchedulerAction getScRefillSufficient getScRefillReady
  nkt_auto

theorem nkt_tcbReleaseRemove (t : ObjRef) : NKT (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove setReleaseQueue; nkt_auto

theorem nkt_tcbReleaseEnqueue (t : ObjRef) : NKT (tcbReleaseEnqueue (Z := Unit) t) := by
  unfold tcbReleaseEnqueue readyTimesAppend orderedInsert setReleaseQueue; nkt_auto

theorem nkt_postpone (p : ObjRef) : NKT (postpone (Z := Unit) p) := by
  unfold postpone
  refine nkt_bind (nkt_getScObjRef _ _) fun _ => nkt_bind (nkt_assertOpt _) fun _ => ?_
  exact nkt_bind (nkt_tcbSchedAction _ _) fun _ => nkt_bind (nkt_tcbReleaseEnqueue _) fun _ =>
    nkt_modify (fun σ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem nkt_schedContextResume (p : ObjRef) : NKT (schedContextResume (Z := Unit) p) := by
  unfold schedContextResume getScRefillReady getScRefillSufficient getTcbQueue
  refine nkt_bind (nkt_getSchedContext _) fun _ => nkt_bind (nkt_assertOpt _) fun _ => ?_
  refine nkt_bind (nkt_gets _) fun _ => nkt_when _ ?_
  refine nkt_bind (nkt_threadGet _ _) fun _ => nkt_bind (nkt_getsThe _) fun _ =>
    nkt_bind (nkt_getsThe _) fun _ => nkt_when _ ?_
  refine nkt_bind (nkt_threadGet _ _) fun _ => nkt_bind (nkt_threadGet _ _) fun _ => ?_
  exact nkt_bind (nkt_bind (nkt_gets _) fun _ => nkt_pure _) fun _ =>
    nkt_bind (nkt_assert _) fun _ => nkt_postpone _

theorem nkt_refillUnblockCheck (p : ObjRef) : NKT (refillUnblockCheck (Z := Unit) p) := by
  unfold refillUnblockCheck isRoundRobin getScRefillReady refillHeadOverlappingLoop mergeOverlappingRefills
    refillPopHead updateRefillHd getRefillHead
  refine nkt_bind (nkt_bind (nkt_getSchedContext _) fun _ => nkt_pure _) fun _ => ?_
  nkt_auto

theorem nkt_ifCondRefillUnblockCheck (o : Option ObjRef) (a b : Option Bool) :
    NKT (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck
  refine nkt_maybeM (fun _ => ?_) _
  refine nkt_bind (nkt_getSchedContext _) fun _ => nkt_bind (nkt_gets _) fun _ =>
    nkt_bind (nkt_pure _) fun _ => nkt_when _ (nkt_when _ (nkt_refillUnblockCheck _))

theorem nkt_schedContextBindTcb (sc t : ObjRef) : NKT (schedContextBindTcb (Z := Unit) sc t) := by
  unfold schedContextBindTcb
  refine nkt_bind ?_ fun _ => nkt_bind ?_ fun _ => nkt_bind (nkt_ifCondRefillUnblockCheck _ _ _) fun _ =>
    nkt_bind (nkt_schedContextResume _) fun _ => nkt_bind (nkt_gets _) fun _ => nkt_when _ ?_
  · nkt_auto
  · nkt_auto
  · exact nkt_bind (nkt_tcbSchedAction _ _) fun _ => nkt_rescheduleRequired

theorem nkt_schedContextBindNtfn (sc n : ObjRef) : NKT (schedContextBindNtfn (Z := Unit) sc n) := by
  unfold schedContextBindNtfn; nkt_auto

theorem nkt_commitTime : NKT (commitTime (Z := Unit)) := by
  unfold commitTime refillBudgetCheckRoundRobin refillBudgetCheck
  repeat (first | unfold updateRefillHd | unfold updateRefillTl | unfold refillAddTail | unfold refillPopHead | unfold getRefillHead | unfold getRefills | unfold getRefillTail | unfold refillFull | unfold refillSingle | unfold refillSize | unfold scheduleUsed | unfold chargeEntireHeadRefill | unfold handleOverrun | unfold headInsufficientLoop | unfold mergeNonoverlappingHeadRefill | unfold isRoundRobin | unfold getScActive | unfold getScRefillReady | unfold maybeAddEmptyTail)
  nkt_auto

theorem nkt_refillNew (p : ObjRef) (m : Nat) (b per : Ticks) : NKT (refillNew (Z := Unit) p m b per) := by
  unfold refillNew
  repeat (first | unfold updateRefillHd | unfold updateRefillTl | unfold refillAddTail | unfold refillPopHead | unfold getRefillHead | unfold getRefills | unfold getRefillTail | unfold refillFull | unfold refillSingle | unfold refillSize | unfold scheduleUsed | unfold chargeEntireHeadRefill | unfold handleOverrun | unfold headInsufficientLoop | unfold mergeNonoverlappingHeadRefill | unfold isRoundRobin | unfold getScActive | unfold getScRefillReady | unfold maybeAddEmptyTail)
  nkt_auto

theorem nkt_refillUpdate (p : ObjRef) (per b : Ticks) (m : Nat) : NKT (refillUpdate (Z := Unit) p per b m) := by
  unfold refillUpdate
  repeat (first | unfold updateRefillHd | unfold updateRefillTl | unfold refillAddTail | unfold refillPopHead | unfold getRefillHead | unfold getRefills | unfold getRefillTail | unfold refillFull | unfold refillSingle | unfold refillSize | unfold scheduleUsed | unfold chargeEntireHeadRefill | unfold handleOverrun | unfold headInsufficientLoop | unfold mergeNonoverlappingHeadRefill | unfold isRoundRobin | unfold getScActive | unfold getScRefillReady | unfold maybeAddEmptyTail)
  nkt_auto

theorem nkt_possibleSwitchTo (t : ObjRef) : NKT (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo getTcbObjRef setSchedulerAction
  refine nkt_bind (nkt_threadGet _ _) fun _ => nkt_bind (nkt_gets _) fun _ => nkt_when _ ?_
  refine nkt_bind (nkt_gets _) fun _ => nkt_bind (nkt_threadGet _ _) fun _ => nkt_bind (nkt_gets _)
    fun _ => ?_
  split
  · exact nkt_tcbSchedAction _ _
  · split
    · exact nkt_bind nkt_rescheduleRequired fun _ => nkt_tcbSchedAction _ _
    · nkt_auto

macro "nkt_step2" : tactic => `(tactic| first
  | with_reducible exact nkt_commitTime | with_reducible exact nkt_refillNew _ _ _ _
  | with_reducible exact nkt_refillUpdate _ _ _ _ | with_reducible exact nkt_possibleSwitchTo _
  | with_reducible exact nkt_rescheduleRequired | with_reducible exact nkt_schedContextResume _
  | with_reducible exact nkt_tcbReleaseRemove _ | nkt_step)

/-- **SchedControl `ConfigureFlags` changes only scheduling fields.** -/
theorem nkt_invokeSchedControlConfigureFlags (iv : SchedControlInvocation) :
    NKT (invokeSchedControlConfigureFlags (Z := Unit) iv) := by
  unfold invokeSchedControlConfigureFlags getThreadState getScActive
  repeat nkt_step2

end

end Fl4Proofs.P3.Sched
