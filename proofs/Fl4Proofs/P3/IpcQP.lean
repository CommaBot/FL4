/-
P3 (DESIGN.md §9), IPC: **a frame of the IPC queues and the TCB priorities
for the spec's reply path** (spec side only), in the shape of IpcRelQ's
`RQ`.

`QPS σ σ'`: every object keeps its queue view (`qv`: a TCB's priority, an
endpoint's or notification's queue). `QPM m`: every outcome of `m` is
`QPS`-related to its start (`qp_auto`); up to `do_ipc_transfer`,
`handle_fault_reply`, `set_thread_state` and the sporadic unblock check.
`QPS.sorted`: the queues stay sorted by priority (`IpcSorted`).
-/
import Fl4Proofs.P3.ScIpcSorted
open Classical

namespace Fl4Proofs.P3.QPK
open Fl4Spec

noncomputable section

/-- The queue view of an object: a TCB's priority, an endpoint's queue, a
notification's queue; nothing else. -/
def qv : Option KernelObject → Nat × Nat × List ObjRef
  | some (.tcb x) => (1, x.tcbPriority.toNat, [])
  | some (.endpoint x) => (2, 0, x.epQueue)
  | some (.notification x) => (3, 0, x.ntfnObj.ntfnQueue)
  | _ => (0, 0, [])

/-- Every object keeps its queue view. -/
def QPS (σ σ' : State Unit) : Prop := ∀ p, qv (σ'.kheap p) = qv (σ.kheap p)

theorem QPS.refl (σ : State Unit) : QPS σ σ := fun _ => rfl

theorem QPS.trans {σ1 σ2 σ3 : State Unit} (h1 : QPS σ1 σ2) (h2 : QPS σ2 σ3) : QPS σ1 σ3 :=
  fun p => (h2 p).trans (h1 p)

theorem QPS.of_eq {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) : QPS σ σ' := by
  intro p; rw [h]

theorem qv_ep {o : Option KernelObject} {q : List ObjRef} {b c : Nat} (h : qv o = (2, b, q)) :
    ∃ y, o = some (.endpoint y) ∧ y.epQueue = q := by
  rcases o with _ | o
  · simp [qv] at h
  · cases o <;> simp [qv] at h
    exact ⟨_, rfl, h.2⟩

theorem qv_ntfn {o : Option KernelObject} {q : List ObjRef} {b : Nat} (h : qv o = (3, b, q)) :
    ∃ y, o = some (.notification y) ∧ y.ntfnObj.ntfnQueue = q := by
  rcases o with _ | o
  · simp [qv] at h
  · cases o <;> simp [qv] at h
    exact ⟨_, rfl, h.2⟩

/-- **`QPS` keeps the IPC queues' priority order** (ScIpcSorted's `IpcSorted`). -/
theorem QPS.sorted {σ σ' : State Unit} (h : QPS σ σ') (hS : Sched.IpcSorted σ) : Sched.IpcSorted σ' := by
  refine hS.frame (fun p x' hp => ?_) (fun p x' hp => ?_) (fun u => ?_)
  · have e := (h p).symm; rw [hp] at e
    obtain ⟨y, hy, ey⟩ := qv_ep (c := 0) e
    exact ⟨y, hy, ey.symm⟩
  · have e := (h p).symm; rw [hp] at e
    obtain ⟨y, hy, ey⟩ := qv_ntfn e
    exact ⟨y, hy, ey.symm⟩
  · have e := h u
    unfold Sched.prioOf
    rw [Sched.tcbsOf_eq, Sched.tcbsOf_eq]
    generalize σ'.kheap u = a at e ⊢
    generalize σ.kheap u = b at e ⊢
    rcases a with _ | a <;> rcases b with _ | b
    · rfl
    · cases b <;> simp_all [qv]
    · cases a <;> simp_all [qv]
    · cases a <;> cases b <;> simp_all [qv, BitVec.toNat_inj]

/-- Every outcome of `m` keeps the release queue (backward). -/
def QPM {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → QPS σ x.2

section Comb

theorem qp_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : QPM m)
    (hg : ∀ a, QPM (g a)) : QPM (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem qp_bind_pure {α β : Type} {a : α} {g : α → NonDet (State Unit) β} (h : QPM (g a)) :
    QPM ((pure a : NonDet (State Unit) α) >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ x hx

theorem qp_fail_bind {α β : Type} {g : α → NonDet (State Unit) β} :
    QPM ((NonDet.fail : NonDet (State Unit) α) >>= g) := by
  intro σ x ⟨y, hy, _⟩
  exact hy.elim

theorem qp_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : QPM m)
    (hg : ∀ a, QPM (g a)) : QPM (NonDet.bind m g) := qp_bind hm hg

theorem qp_pure {α : Type} (a : α) : QPM (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact QPS.refl _

theorem qp_pure' {α : Type} (a : α) : QPM (NonDet.pure a : NonDet (State Unit) α) := qp_pure a

theorem qp_gets {α : Type} (g : State Unit → α) : QPM (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact QPS.refl _

theorem qp_get : QPM (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact QPS.refl _

theorem qp_assert (P : Prop) : QPM (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact QPS.refl _

theorem qp_fail {α : Type} : QPM (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem qp_assertOpt {α : Type} (o : Option α) : QPM (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact qp_fail
  · exact qp_pure' _

theorem qp_getsThe {α : Type} (g : State Unit → Option α) : QPM (NonDet.getsThe g) := by
  intro σ x hx; exact qp_assertOpt (g σ) σ x hx

theorem qp_selectF {α : Type} (S : Set α × Prop) : QPM (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact QPS.refl _

theorem qp_select {α : Type} (S : Set α) : QPM (NonDet.select S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact QPS.refl _

theorem qp_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : QPM m1)
    (h2 : QPM m2) : QPM (if P then m1 else m2) := by
  split <;> assumption

theorem qp_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : QPM m) :
    QPM (NonDet.when P m) := by
  unfold NonDet.when; exact qp_ite P h (qp_pure' _)

theorem qp_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : QPM m) :
    QPM (NonDet.unless P m) := by
  unfold NonDet.unless; exact qp_ite P (qp_pure' _) h

theorem qp_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, QPM (g a)) (o : Option α) :
    QPM (NonDet.maybeM g o) := by
  cases o
  · exact qp_pure' _
  · exact h _

theorem qp_liftM {α β : Type} (g : α → β) {m : NonDet (State Unit) α} (h : QPM m) :
    QPM (NonDet.liftM g m) := qp_bind' h fun _ => qp_pure' _

theorem qp_modify {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap) :
    QPM (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact QPS.of_eq (hg σ)

theorem qp_get_put {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap) :
    QPM (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact QPS.of_eq (hg σ)

theorem qp_get_put' {g : State Unit → State Unit} (hg : ∀ σ, (g σ).kheap = σ.kheap) :
    QPM (do let s ← NonDet.get; NonDet.put (g s)) := qp_get_put hg

theorem qp_getObject (p : ObjRef) : QPM (getObject (Z := Unit) p) := qp_getsThe _

theorem qp_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, QPM (B r)) (r : α) : QPM (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => exact QPS.refl _
  | step _ hm _ ih => exact (hB _ _ _ hm).trans ih

theorem qp_mapMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, QPM (g a)) (xs : List α) :
    QPM (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact qp_pure' _
  | cons a xs' ih => exact qp_bind' (h a) fun _ => ih

theorem qp_forMx {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, QPM (g a)) (xs : List α) :
    QPM (NonDet.forMx xs g) := qp_mapMx h xs

theorem qp_mapM {α β : Type} {g : α → NonDet (State Unit) β} (h : ∀ a, QPM (g a)) (xs : List α) :
    QPM (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact qp_pure' _
  | cons a xs' ih => exact qp_bind' (h a) fun _ => qp_bind' ih fun _ => qp_pure' _

theorem qp_doMachineOp {α : Type} (mop : NonDet MachineState α) : QPM (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine qp_bind (qp_gets _) (fun _ => qp_bind (qp_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact qp_bind (qp_modify (fun σ => rfl)) (fun _ => qp_pure _)

theorem qp_doExtendedOp (eop : DetExtMonad Unit) : QPM (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine qp_bind qp_get (fun _ => qp_bind (qp_selectF _) (fun _ => ?_))
  split
  exact qp_modify (fun σ => rfl)

end Comb

/-- `QPM` for the exception monad. -/
def QPE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := QPM (ExceptT.run m)

section CombE
variable {ε : Type}

theorem qpe_bind {α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β} (hm : QPE m)
    (hg : ∀ a, QPE (g a)) : QPE (m >>= g) := by
  unfold QPE; rw [ExceptT.run_bind]
  refine qp_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact qp_pure _

theorem qpe_pure {α : Type} (a : α) : QPE (pure a : NonDetE (State Unit) ε α) := qp_pure _

theorem qpe_returnOk {α : Type} (a : α) : QPE (NonDetE.returnOk a : NonDetE (State Unit) ε α) := qp_pure _

theorem qpe_throw {α : Type} (e : ε) : QPE (NonDetE.throwError e : NonDetE (State Unit) ε α) := qp_pure _

theorem qpe_throw' {α : Type} (e : ε) : QPE (throw e : NonDetE (State Unit) ε α) := qp_pure _

theorem qpe_liftE {α : Type} {m : NonDet (State Unit) α} (h : QPM m) : QPE (NonDetE.liftE (ε := ε) m) := by
  unfold QPE NonDetE.liftE; rw [ExceptT.run_lift]
  exact qp_bind h fun _ => qp_pure _

theorem qpe_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : QPE m1)
    (h2 : QPE m2) : QPE (if P then m1 else m2) := by
  split <;> assumption

theorem qpe_whenE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : QPE m) :
    QPE (NonDetE.whenE P m) := by
  unfold NonDetE.whenE; exact qpe_ite P h (qpe_pure _)

theorem qpe_unlessE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : QPE m) :
    QPE (NonDetE.unlessE P m) := by
  unfold NonDetE.unlessE; exact qpe_ite P (qpe_pure _) h

theorem qpe_throwOpt {α : Type} (e : ε) (o : Option α) : QPE (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact qpe_throw' e
  · exact qpe_pure _

theorem qpe_assertE (P : Prop) : QPE (NonDetE.assertE P : NonDetE (State Unit) ε Unit) :=
  qpe_liftE (qp_assert P)

theorem qp_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : QPE m)
    (hh : ∀ e, QPM (h e)) : QPM (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine qp_bind' hm fun r => ?_
  cases r with
  | ok a => exact qp_pure' _
  | error e => exact hh e

theorem qpe_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : QPE m) (hh : ∀ e, QPE (h e)) : QPE (NonDetE.handleE m h) := by
  unfold NonDetE.handleE QPE
  rw [ExceptT.run_mk]
  refine qp_bind' hm fun r => ?_
  cases r with
  | ok a => exact qp_pure' _
  | error e => exact hh e

theorem qpe_liftME {α β : Type} (f : α → β) {m : NonDetE (State Unit) ε α} (h : QPE m) :
    QPE (NonDetE.liftME f m) := by
  unfold NonDetE.liftME; exact qpe_bind h fun _ => qpe_pure _

theorem qpe_mapMEx {α β : Type} {f : α → NonDetE (State Unit) ε β} (h : ∀ a, QPE (f a)) :
    ∀ xs : List α, QPE (NonDetE.mapMEx f xs)
  | [] => by unfold NonDetE.mapMEx; exact qpe_pure _
  | a :: rest => by unfold NonDetE.mapMEx; exact qpe_bind (h a) fun _ => qpe_mapMEx h rest

theorem qpe_mapME {α β : Type} {f : α → NonDetE (State Unit) ε β} (h : ∀ a, QPE (f a)) :
    ∀ xs : List α, QPE (NonDetE.mapME f xs)
  | [] => by unfold NonDetE.mapME; exact qpe_pure _
  | a :: rest => by
    unfold NonDetE.mapME; exact qpe_bind (h a) fun _ => qpe_bind (qpe_mapME h rest) fun _ => qpe_pure _

end CombE

theorem qo_cnode (r : Nat) (c : CnodeContents) : ∀ k, aType k = aType (.cnode r c) →
    qv (some k) = qv (some (.cnode r c)) := by
  intro k hk; cases k <;> simp only [aType] at hk <;> (try split_ifs at hk) <;> first | rfl | exact nomatch hk
theorem qo_reply (x : Reply) : ∀ k, aType k = aType (.reply x) → qv (some k) = qv (some (.reply x)) := by
  intro k hk; cases k <;> simp only [aType] at hk <;> (try split_ifs at hk) <;> first | rfl | exact nomatch hk
theorem qo_sc (y : SchedContext) (n : Nat) : ∀ k, aType k = aType (.schedContext y n) →
    qv (some k) = qv (some (.schedContext y n)) := by
  intro k hk; cases k <;> simp only [aType] at hk <;> (try split_ifs at hk) <;> first | rfl | exact nomatch hk
theorem qo_arch (x : ArchKernelObj) : ∀ k, aType k = aType (.archObj x) → qv (some k) = qv (some (.archObj x)) := by
  intro k hk; cases k <;> simp only [aType] at hk <;> (try split_ifs at hk) <;> first | rfl | exact nomatch hk

/-- One step of an `QPM` proof. -/
macro "qp_step0" : tactic => `(tactic| first
  | with_reducible exact qp_pure _ | with_reducible exact qp_pure' _ | with_reducible exact qp_fail
  | with_reducible exact qp_gets _ | with_reducible exact qp_get
  | with_reducible exact qp_assert _ | with_reducible exact qp_assertOpt _
  | with_reducible exact qp_getsThe _
  | with_reducible exact qp_selectF _ | with_reducible exact qp_select _
  | ((with_reducible apply qp_modify); intro _; rfl)
  | ((with_reducible apply qp_get_put); intro _; rfl)
  | (exact qp_get_put' (fun _ => rfl))
  | (exact qp_get_put (fun _ => rfl))
  | with_reducible exact qp_getObject _
  | with_reducible exact qp_doMachineOp _ | with_reducible exact qp_doExtendedOp _
  | (with_reducible refine qp_bind_pure ?_) | (with_reducible exact qp_fail_bind)
  | (with_reducible refine qp_bind ?_ (fun _ => ?_))
  | (with_reducible refine qp_bind' ?_ (fun _ => ?_))
  | (with_reducible apply qp_ite) | (with_reducible apply qp_when) | (with_reducible apply qp_unless)
  | (with_reducible refine qp_maybeM (fun _ => ?_) _) | (with_reducible apply qp_liftM)
  | (with_reducible refine qp_whileLoop (fun _ => ?_) _)
  | (with_reducible refine qp_mapMx (fun _ => ?_) _)
  | (with_reducible refine qp_mapM (fun _ => ?_) _)
  | (with_reducible refine qp_forMx (fun _ => ?_) _)
  | with_reducible exact qpe_pure _ | with_reducible exact qpe_returnOk _ | with_reducible exact qpe_throw _
  | with_reducible exact qpe_throw' _ | with_reducible exact qpe_throwOpt _ _ | with_reducible exact qpe_assertE _
  | (with_reducible refine qpe_bind ?_ (fun _ => ?_))
  | (with_reducible apply qpe_liftE) | (with_reducible apply qpe_ite) | (with_reducible apply qpe_whenE)
  | (with_reducible apply qpe_unlessE) | (with_reducible refine qp_catch ?_ (fun _ => ?_))
  | (with_reducible refine qpe_handleE ?_ (fun _ => ?_)) | (with_reducible apply qpe_liftME)
  | (with_reducible refine qpe_mapMEx (fun _ => ?_) _) | (with_reducible refine qpe_mapME (fun _ => ?_) _)
  | with_reducible exact qo_cnode _ _ | with_reducible exact qo_reply _ | with_reducible exact qo_sc _ _
  | with_reducible exact qo_arch _ | with_reducible exact fun _ => qo_reply _
  | (with_reducible intro _; exact ⟨rfl, rfl⟩)
  | (intro _; rfl)
  | (intro _; trivial)
  | split
  | (dsimp only)
  | (simp only [letFun])
  | (dsimp only [letFun])
  | (with_reducible exact qp_pure _)
  | (exact qp_pure _))

macro "qp_auto0" : tactic => `(tactic| repeat' qp_step0)

/-- An `QPM` lemma of a spec function (extended below, one rule per lemma). -/
syntax "qp_leaf" : tactic
macro_rules | `(tactic| qp_leaf) => `(tactic| fail "no qp_leaf")

macro "qp_auto" : tactic => `(tactic| repeat' (first | qp_leaf | qp_step0))

/-! ## Object steps -/

/-- The outcome of `set_object`: the object there had the same type. -/
theorem qp_setObject_mem {σ : State Unit} {p : ObjRef} {o : KernelObject} {x : Unit × State Unit}
    (hx : x ∈ (setObject (Z := Unit) p o σ).1) :
    ∃ k, σ.kheap p = some k ∧ aType k = aType o ∧ x.2 = { σ with kheap := Function.update σ.kheap p (some o) } := by
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨k, hk⟩ : ∃ k, σ.kheap p = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap p with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  obtain ⟨hk, rfl⟩ := hk
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨hty, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ⟨k, hk, hty, rfl⟩

/-- The state after writing `ko` at `o` over `k`, with the same view. -/
theorem qps_upd {σ : State Unit} {o : ObjRef} {k ko : KernelObject} (hk : σ.kheap o = some k)
    (hq : qv (some ko) = qv (some k)) : QPS σ { σ with kheap := Function.update σ.kheap o (some ko) } := by
  intro q
  by_cases h : q = o
  · subst h; simp only [Function.update_self]; rw [hk]; exact hq
  · simp only [Function.update_of_ne h]

/-- `set_object` of an object keeping the view of what it replaces. -/
theorem qp_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ k, aType k = aType o → qv (some k) = qv (some o)) :
    QPM (setObject (Z := Unit) p o) := by
  intro σ x hx
  obtain ⟨k, hk, hty, e⟩ := qp_setObject_mem hx
  rw [e]; exact qps_upd hk (ho k hty).symm
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible refine qp_setObject _ _ ?_)

theorem set_fin {σ : State Unit} {o : ObjRef} {k ko : KernelObject} (hk : σ.kheap o = some k)
    {x : Unit × State Unit} (hx : x ∈ (setObject (Z := Unit) o ko σ).1) (hq : qv (some ko) = qv (some k)) :
    QPS σ x.2 := by
  obtain ⟨k', hk', -, e⟩ := qp_setObject_mem hx
  rw [e]; exact qps_upd hk hq

theorem pure_set {σ : State Unit} {o : ObjRef} {ko : KernelObject} {x : Unit × State Unit}
    (hx : x ∈ (((pure ko : NonDet (State Unit) KernelObject) >>= fun obj' => setObject (Z := Unit) o obj') σ).1) :
    x ∈ (setObject (Z := Unit) o ko σ).1 := by
  obtain ⟨y2, hy2, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy2] at hx; exact hx

/-- The outcome of `update_sched_context`. -/
theorem updSc_mem {σ : State Unit} {q : ObjRef} {f : SchedContext → SchedContext} {x : Unit × State Unit}
    (hx : x ∈ (updateSchedContext (Z := Unit) q f σ).1) :
    ∃ y0 n0, σ.kheap q = some (.schedContext y0 n0) ∧
      x.2 = { σ with kheap := Function.update σ.kheap q (some (.schedContext (f y0) n0)) } := by
  unfold updateSchedContext at hx
  obtain ⟨y, hy, hx⟩ := hx
  have hy' : y = (the (σ.kheap q), σ) ∧ σ.kheap q ≠ none := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap q with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨Set.mem_singleton_iff.1 hy, by simp⟩
  obtain ⟨rfl, hne⟩ := hy'
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hne
  rw [hk] at hx
  cases k with
  | schedContext sc n =>
    obtain ⟨k', -, -, e⟩ := qp_setObject_mem (o := .schedContext (f sc) n) hx
    exact ⟨sc, n, hk, e⟩
  | _ => exact hx.elim

/-- `update_sched_context`. -/
theorem qp_updateSchedContext (q : ObjRef) (f : SchedContext → SchedContext) :
    QPM (updateSchedContext (Z := Unit) q f) := by
  intro σ x hx
  obtain ⟨sc, n, hk, e⟩ := updSc_mem hx
  rw [e]; exact qps_upd hk rfl
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_updateSchedContext _ _)

theorem qp_setCap (c : Cap) (sl : CslotPtr) : QPM (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl
  intro σ x hx
  unfold setCap at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨k, hk, rfl⟩ : ∃ k, σ.kheap o = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap o with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  dsimp only at hx
  cases k with
  | cnode sz cn =>
    dsimp only at hx; split_ifs at hx
    · exact set_fin hk (pure_set hx) rfl
    · obtain ⟨_, h, _⟩ := hx; exact h.elim
  | tcb t =>
    dsimp only at hx
    split_ifs at hx <;> first | exact set_fin hk (pure_set hx) rfl | (obtain ⟨_, h, _⟩ := hx; exact h.elim)
  | _ => obtain ⟨_, h, _⟩ := hx; exact h.elim
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_setCap _ _)

theorem qp_getCap (sl : CslotPtr) : QPM (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap
  refine qp_bind (qp_getObject o) (fun obj => ?_)
  cases obj <;> simp only [letFun] <;> qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_getCap _)

theorem qp_portOut {n : Nat} (f : BitVec n → MachineMonad Unit) (w : BitVec n) :
    QPM (portOut (Z := Unit) f w) := by
  unfold portOut; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_portOut _ _)

theorem qp_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α)
    (hC : ∀ k, aType k = aType (C e) → qv (some k) = qv (some (C e))) : QPM (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo
  exact qp_bind (qp_getObject _) fun _ => qp_bind (qp_assert _) fun _ => qp_bind (qp_assert _) fun _ =>
    qp_setObject _ _ hC
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible refine qp_setSimpleKo' _ _ _ ?_)

theorem qp_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef)
    (hC : ∀ e k, aType k = aType (C e) → qv (some k) = qv (some (C e))) :
    QPM (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef getSimpleKo
  refine qp_bind (qp_bind (qp_getObject _) fun _ => qp_bind (qp_assert _) fun _ => ?_) fun _ =>
    qp_setSimpleKo' _ _ _ (hC _)
  split
  · exact qp_pure _
  · exact qp_fail
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible refine qp_updateSkObjRef' _ _ _ _ ?_)

/-! ## The spec functions (VsDomOps, DomRecDel, AllDom's `DK` lemmas, for `QPM`) -/

theorem qp_setOriginal (slot : CslotPtr) (v : Bool) : QPM (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_setOriginal _ _)

theorem qp_updateCdt (f : Cdt → Cdt) : QPM (updateCdt (Z := Unit) f) := by
  unfold updateCdt; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_updateCdt _)

theorem qp_setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : QPM (setUntypedCapAsFull (Z := Unit) srcCap newCap srcSlot) := by
  unfold setUntypedCapAsFull; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_setUntypedCapAsFull _ _ _)

theorem qp_capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : QPM (capInsert (Z := Unit) newCap srcSlot destSlot) := by
  unfold capInsert; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_capInsert _ _ _)

theorem qp_threadSet' (f : Tcb → Tcb) (hf : ∀ x, (f x).tcbPriority = x.tcbPriority) (t : ObjRef) :
    QPM (threadSet (Z := Unit) f t) := by
  intro σ x hx
  unfold threadSet at hx
  obtain ⟨y, hy, hx⟩ := hx
  have hy' : ∃ x0, σ.kheap t = some (.tcb x0) ∧ y = (x0, σ) := by
    unfold NonDet.getsThe getTcb readObject at hy
    cases h : σ.kheap t with
    | none => rw [h] at hy; exact hy.elim
    | some k =>
      rw [h] at hy
      cases k with
      | tcb x0 => exact ⟨x0, rfl, Set.mem_singleton_iff.1 hy⟩
      | _ => exact hy.elim
  obtain ⟨x0, hk0, rfl⟩ := hy'
  exact set_fin hk0 hx (by simp [qv, hf])
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible refine qp_threadSet' _ ?_ _)

theorem qp_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : QPM (threadGet (Z := Unit) f t) := by
  unfold threadGet; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_threadGet' _ _)

theorem qp_setThreadState' (t : ObjRef) (ts : ThreadState) : QPM (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_setThreadState' _ _)

theorem qp_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    QPM (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_getSimpleKo' _ _)

theorem qp_getSchedContext' (q : ObjRef) : QPM (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_getSchedContext' _)

theorem qp_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : QPM (asUser (Z := Unit) t u) := by
  intro σ x hx
  unfold asUser at hx
  obtain ⟨y, hy, hx⟩ := hx
  have hy' : ∃ x0, σ.kheap t = some (.tcb x0) ∧ y = (x0, σ) := by
    unfold NonDet.getsThe getTcb readObject at hy
    cases h : σ.kheap t with
    | none => rw [h] at hy; exact hy.elim
    | some k =>
      rw [h] at hy
      cases k with
      | tcb x0 => exact ⟨x0, rfl, Set.mem_singleton_iff.1 hy⟩
      | _ => exact hy.elim
  obtain ⟨x0, hk0, rfl⟩ := hy'
  obtain ⟨y1, hy1, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy1] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  obtain ⟨-, e2⟩ := hy2
  obtain ⟨⟨a, uc'⟩, σ2⟩ := y2
  simp only at e2
  subst e2
  obtain ⟨y3, hy3, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy3] at hx
  obtain ⟨y4, hy4, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hx]
  exact set_fin hk0 hy4 rfl
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_asUser' _ _)

theorem qp_getThreadState' (t : ObjRef) : QPM (getThreadState (Z := Unit) t) := by
  unfold getThreadState; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_getThreadState' _)

theorem qp_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) : QPM (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_getSkObjRef' _ _ _)

theorem qp_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : QPM (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_getScObjRef' _ _)

theorem qp_lookupIpcBuffer' (b : Bool) (t : ObjRef) : QPM (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_lookupIpcBuffer' _ _)

theorem qp_zipWithMx' {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, QPM (g a b)) :
    ∀ l1 l2, QPM (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => qp_bind (h a b) (fun _ => qp_zipWithMx' h l1 l2)
  | [], _ => qp_pure' _
  | _ :: _, [] => qp_pure' _
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible refine qp_zipWithMx' (fun _ _ => ?_) _ _)

theorem qp_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : QPM (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_storeWordOffs' _ _ _)

theorem qp_set_bind {β : Type} {σ : State Unit} {t : ObjRef} {x0 : Tcb} {y : Tcb} {K : Unit → NonDet (State Unit) β}
    (hk : σ.kheap t = some (.tcb x0)) (hq : y.tcbPriority = x0.tcbPriority) (hK : ∀ u, QPM (K u)) :
    ∀ x ∈ ((setObject (Z := Unit) t (.tcb y) >>= K) σ).1, QPS σ x.2 := by
  intro x ⟨y3, hy3, hx⟩
  exact (set_fin hk hy3 (by simp [qv, hq])).trans (hK _ _ _ hx)

theorem qp_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : QPM (setMrs (Z := Unit) t b m) := by
  intro σ x hx
  unfold setMrs at hx
  obtain ⟨y, hy, hx⟩ := hx
  have hy' : ∃ x0, σ.kheap t = some (.tcb x0) ∧ y = (x0, σ) := by
    unfold NonDet.getsThe getTcb readObject at hy
    cases h : σ.kheap t with
    | none => rw [h] at hy; exact hy.elim
    | some k =>
      rw [h] at hy
      cases k with
      | tcb x0 => exact ⟨x0, rfl, Set.mem_singleton_iff.1 hy⟩
      | _ => exact hy.elim
  obtain ⟨x0, hk0, rfl⟩ := hy'
  obtain ⟨y1, hy1, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy1] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy2] at hx
  beta_reduce at hx
  refine qp_set_bind hk0 ?_ ?_ x hx
  · rfl
  · intro _; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_setMrs' _ _ _)

theorem qp_setMessageInfo' (t : ObjRef) (i : MessageInfo) : QPM (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_setMessageInfo' _ _)

theorem qp_archThreadSet' (f : ArchTcb → ArchTcb) (t : ObjRef) : QPM (archThreadSet (Z := Unit) f t) := by
  intro σ x hx
  unfold archThreadSet at hx
  obtain ⟨y, hy, hx⟩ := hx
  have hy' : ∃ x0, σ.kheap t = some (.tcb x0) ∧ y = (x0, σ) := by
    unfold NonDet.getsThe getTcb readObject at hy
    cases h : σ.kheap t with
    | none => rw [h] at hy; exact hy.elim
    | some k =>
      rw [h] at hy
      cases k with
      | tcb x0 => exact ⟨x0, rfl, Set.mem_singleton_iff.1 hy⟩
      | _ => exact hy.elim
  obtain ⟨x0, hk0, rfl⟩ := hy'
  exact set_fin hk0 hx rfl
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_archThreadSet' _ _)

theorem qp_getTcbQueue' (d : Domain) (p : Priority) : QPM (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_getTcbQueue' _ _)

theorem qp_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : QPM (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_setTcbQueue' _ _ _)

theorem qp_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) : QPM (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_tcbSchedAction' _ _)

theorem qp_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : QPM (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_getTcbObjRef' _ _)

theorem qp_setSchedulerAction' (a : SchedulerAction) : QPM (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_setSchedulerAction' _)

theorem qp_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : QPM (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_getScRefillSufficient' _ _)

theorem qp_getScRefillReady' (sc : ObjRef) : QPM (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_getScRefillReady' _)

theorem qp_tcbReleaseRemove' (t : ObjRef) : QPM (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove setReleaseQueue; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_tcbReleaseRemove' _)

theorem qp_rescheduleRequired' : QPM (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_rescheduleRequired' )

theorem qp_testReschedule' (t : ObjRef) : QPM (testReschedule (Z := Unit) t) := by
  unfold testReschedule; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_testReschedule' _)

theorem qp_possibleSwitchTo' (t : ObjRef) : QPM (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_possibleSwitchTo' _)

theorem qp_isRoundRobin' (sc : ObjRef) : QPM (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_isRoundRobin' _)

theorem qp_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : QPM (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_updateRefillHd' _ _)

theorem qp_getRefillHead' (sc : ObjRef) : QPM (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_getRefillHead' _)

theorem qp_refillPopHead' (sc : ObjRef) : QPM (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_refillPopHead' _)

theorem qp_mergeOverlappingRefills' (sc : ObjRef) : QPM (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_mergeOverlappingRefills' _)

theorem qp_refillHeadOverlappingLoop' (sc : ObjRef) : QPM (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_refillHeadOverlappingLoop' _)

theorem qp_refillUnblockCheck' (sc : ObjRef) : QPM (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_refillUnblockCheck' _)

theorem qp_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) : QPM (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_ifCondRefillUnblockCheck' _ _ _)

theorem qp_replyUnlinkSc' (sc r : ObjRef) : QPM (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_replyUnlinkSc' _ _)

theorem qp_schedContextUpdateConsumed' (sc : ObjRef) : QPM (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_schedContextUpdateConsumed' _)

theorem qpe_rab (p : Cap × CapRef) : QPE (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact qpe_liftE (qp_fail)
    · refine qpe_bind (qpe_whenE _ (qpe_throw _)) fun _ => qpe_bind (qpe_whenE _ (qpe_throw _)) fun _ =>
        qpe_bind (qpe_returnOk _) fun _ => ?_
      dsimp only
      split
      · exact qpe_returnOk _
      · refine qpe_bind (qpe_liftE (qp_getCap _)) fun nc => ?_
        split
        · exact qpe_rab _
        · exact qpe_returnOk _
  · exact qpe_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qpe_rab _)

theorem qpe_resolveAddressBits (p : Cap × CapRef) : QPE (resolveAddressBits (Z := Unit) p) := qpe_rab p
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qpe_resolveAddressBits _)

theorem qp_lookupSlotForThread' (thread : ObjRef) (cref : CapRef) : QPE (lookupSlotForThread (Z := Unit) thread cref) := by
  unfold lookupSlotForThread; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_lookupSlotForThread' _ _)

theorem qp_lookupCapAndSlot' (thread : ObjRef) (cptr : CapRef) : QPE (lookupCapAndSlot (Z := Unit) thread cptr) := by
  unfold lookupCapAndSlot; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_lookupCapAndSlot' _ _)

theorem qp_lookupCap' (thread : ObjRef) (ref : CapRef) : QPE (lookupCap (Z := Unit) thread ref) := by
  unfold lookupCap; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_lookupCap' _ _)

theorem qp_captransferFromWords' (ptr : Word) : QPM (captransferFromWords (Z := Unit) ptr) := by
  unfold captransferFromWords; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_captransferFromWords' _)

theorem qp_loadCapTransfer' (buffer : ObjRef) : QPM (loadCapTransfer (Z := Unit) buffer) := by
  unfold loadCapTransfer; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_loadCapTransfer' _)

theorem qp_setExtraBadge' (buffer : ObjRef) (badge : Word) (n : Nat) : QPM (setExtraBadge (Z := Unit) buffer badge n) := by
  unfold setExtraBadge; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_setExtraBadge' _ _ _)

theorem qpe_lookupErrorOnFailure' {α : Type} (b : Bool) {m : LFMonad Unit α} (h : QPE m) :
    QPE (lookupErrorOnFailure (Z := Unit) b m) := by
  unfold lookupErrorOnFailure; exact qpe_handleE h fun _ => qpe_throw _
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible refine qpe_lookupErrorOnFailure' _ ?_)

theorem qp_lookupSlotForCnodeOp' (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) : QPE (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_lookupSlotForCnodeOp' _ _ _ _)

theorem qp_lookupTargetSlot' (c : Cap) (r : CapRef) (n : Nat) : QPE (lookupTargetSlot (Z := Unit) c r n) := by
  unfold lookupTargetSlot; exact qp_lookupSlotForCnodeOp' _ _ _ _
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_lookupTargetSlot' _ _ _)

theorem qpe_bind_returnOk' {ε α β : Type} {a : α} {f : α → NonDetE (State Unit) ε β} (h : QPE (f a)) :
    QPE (NonDetE.returnOk a >>= f) := by
  intro σ x hx
  rw [ExceptT.run_bind] at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact h σ x hx
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible refine qpe_bind_returnOk' ?_)

theorem qp_ensureNoChildren' (cslotPtr : CslotPtr) : QPE (ensureNoChildren (Z := Unit) cslotPtr) := by
  unfold ensureNoChildren; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_ensureNoChildren' _)

theorem qpe_archDeriveCap' (c : ArchCap) : QPE (archDeriveCap (Z := Unit) c) := by
  unfold archDeriveCap; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qpe_archDeriveCap' _)

theorem qpe_deriveCap' (sl : CslotPtr) (c : Cap) : QPE (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qpe_deriveCap' _ _)

theorem qp_makeArchFaultMsg' (f : ArchFault) (t : ObjRef) : QPM (makeArchFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeArchFaultMsg <;> qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_makeArchFaultMsg' _ _)

theorem qpe_unifyFailure' {F α : Type} {m : NonDetE (State Unit) F α} (h : QPE m) :
    QPE (unifyFailure (Z := Unit) m) := by
  unfold unifyFailure; exact qpe_handleE h fun _ => qpe_throw _
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible refine qpe_unifyFailure' ?_)

theorem qp_emptyOnFailure' {F α : Type} {m : NonDetE (State Unit) F (List α)} (h : QPE m) :
    QPM (emptyOnFailure (Z := Unit) m) := by
  unfold emptyOnFailure; exact qp_catch h fun _ => qp_pure' _
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible refine qp_emptyOnFailure' ?_)

theorem qp_constOnFailure' {F α : Type} (c : α) {m : NonDetE (State Unit) F α} (h : QPE m) :
    QPM (constOnFailure (Z := Unit) c m) := by
  unfold constOnFailure; exact qp_catch h fun _ => qp_pure' _
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible refine qp_constOnFailure' _ ?_)

theorem qpe_capFaultOnFailure' {α : Type} (c : ObjRef) (rp : Bool) {m : LFMonad Unit α} (h : QPE m) :
    QPE (capFaultOnFailure (Z := Unit) c rp m) := by
  unfold capFaultOnFailure; exact qpe_handleE h fun _ => qpe_throw _
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible refine qpe_capFaultOnFailure' _ _ ?_)

theorem qp_loadWordOffs' (ptr : ObjRef) (offs : Nat) : QPM (loadWordOffs (Z := Unit) ptr offs) := by
  unfold loadWordOffs; exact qp_doMachineOp _
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_loadWordOffs' _ _)

theorem qp_getExtraCptrs' (b : Option ObjRef) (mi : MessageInfo) : QPM (getExtraCptrs (Z := Unit) b mi) := by
  cases b
  · unfold getExtraCptrs; exact qp_pure _
  · unfold getExtraCptrs; exact qp_liftM _ (qp_mapM (fun _ => qp_loadWordOffs' _ _) _)
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_getExtraCptrs' _ _)

theorem qp_getReceiveSlots' (t : ObjRef) (b : Option ObjRef) : QPM (getReceiveSlots (Z := Unit) t b) := by
  cases b <;> unfold getReceiveSlots <;> qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_getReceiveSlots' _ _)

theorem qp_transferCapsLoop' (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (slots : List CslotPtr) (mi : MessageInfo),
      QPM (transferCapsLoop (Z := Unit) ep rb n caps slots mi)
  | n, [], slots, mi => by unfold transferCapsLoop; qp_auto
  | n, (c, sl) :: rest, slots, mi => by
    have ih := qp_transferCapsLoop' ep rb (n + 1) rest
    unfold transferCapsLoop
    qp_auto
    all_goals first | exact ih _ _ | skip
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_transferCapsLoop' _ _ _ _ _ _)

theorem qp_lookupExtraCaps' (thread : ObjRef) (buffer : Option Data) (mi : MessageInfo) : QPE (lookupExtraCaps (Z := Unit) thread buffer mi) := by
  unfold lookupExtraCaps; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_lookupExtraCaps' _ _ _)

theorem qp_copyMrs' (sender : ObjRef) (sbuf : Option ObjRef) (receiver : ObjRef) (rbuf : Option ObjRef) (n : LengthType) : QPM (copyMrs (Z := Unit) sender sbuf receiver rbuf n) := by
  unfold copyMrs; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_copyMrs' _ _ _ _ _)

theorem qp_transferCaps' (info : MessageInfo) (caps : List (Cap × CslotPtr)) (endpoint : Option ObjRef) (receiver : ObjRef) (recvBuffer : Option ObjRef) : QPM (transferCaps (Z := Unit) info caps endpoint receiver recvBuffer) := by
  unfold transferCaps; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_transferCaps' _ _ _ _ _)

theorem qp_makeFaultMsg' (f : Fault) (t : ObjRef) : QPM (makeFaultMsg (Z := Unit) f t) := by
  cases f <;> unfold makeFaultMsg <;> qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_makeFaultMsg' _ _)

theorem qp_getMessageInfo' (thread : ObjRef) : QPM (getMessageInfo (Z := Unit) thread) := by
  unfold getMessageInfo; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_getMessageInfo' _)

theorem qp_doNormalTransfer' (sender : ObjRef) (sbuf endpoint : Option ObjRef) (badge : Data) (grant : Bool) (receiver : ObjRef) (rbuf : Option ObjRef) : QPM (doNormalTransfer (Z := Unit) sender sbuf endpoint badge grant receiver rbuf) := by
  unfold doNormalTransfer; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_doNormalTransfer' _ _ _ _ _ _ _)

theorem qp_doFaultTransfer' (badge : Data) (sender receiver : ObjRef) (buf : Option ObjRef) : QPM (doFaultTransfer (Z := Unit) badge sender receiver buf) := by
  unfold doFaultTransfer; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_doFaultTransfer' _ _ _ _)

theorem qp_doIpcTransfer' (sender : ObjRef) (ep : Option ObjRef) (badge : Badge) (grant : Bool) (receiver : ObjRef) : QPM (doIpcTransfer (Z := Unit) sender ep badge grant receiver) := by
  unfold doIpcTransfer; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_doIpcTransfer' _ _ _ _ _)

theorem qp_getMrs' (thread : ObjRef) (buf : Option ObjRef) (info : MessageInfo) : QPM (getMrs (Z := Unit) thread buf info) := by
  unfold getMrs; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_getMrs' _ _ _)

theorem qp_handleFaultReply' (f : Fault) (t : ObjRef) (x : Data) (y : List Data) :
    QPM (handleFaultReply (Z := Unit) f t x y) := by
  cases f <;> unfold handleFaultReply <;> qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_handleFaultReply' _ _ _ _)


/-- The sporadic unblock check of a thread's SC (`do_reply_transfer`'s, after
`reply_remove`). -/
theorem qp_unblock (t : ObjRef) :
    QPM (getTcbObjRef (Z := Unit) Tcb.tcbSchedContext t >>= ifSporadicCurScTestRefillUnblockCheck (Z := Unit)) := by
  qp_auto

theorem qp_schedContextDonate (sc t : ObjRef) : QPM (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_schedContextDonate _ _)

theorem qp_replyUnlinkTcb (t r : ObjRef) : QPM (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb setReplyObjRef; qp_auto
macro_rules | `(tactic| qp_leaf) => `(tactic| with_reducible exact qp_replyUnlinkTcb _ _)

theorem qp_replyRemove (c r : ObjRef) : QPM (replyRemove (Z := Unit) c r) := by
  unfold replyRemove; qp_auto

end

end Fl4Proofs.P3.QPK
