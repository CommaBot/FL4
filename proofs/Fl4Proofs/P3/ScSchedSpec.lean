/-
P3 (DESIGN.md §9), scheduler: **the spec's `schedule` is a scheduler step**
(`schs_schedule`): every outcome is `SchS`-related to its start, `SchStep`
with no thread changing state (the current thread, the current CR3 and the
FPU owner may change) and `SOK (true, true)` (the caps, MCPs, yield-to
links, SC replies and reply links kept). Spec side only.

* `SchK m`: the combinators (as ScTK's `NKT`, `schs_auto`), `schs_of` (an
  `NKT` and `Pres (true, true)` operation), `schs_modify` (`SchKeep`).
* `MK mop`: a machine operation keeping the memory; `schs_doMachineOp`.
* The FPU switch (`archThreadSet` of the owner flag, `asUser` of the FPU
  state), `setVmRoot`, `switchToThread`, `setNextInterrupt`.
-/
import Fl4Proofs.P3.ScXSched
open Classical

namespace Fl4Proofs.P3.Sched
open Fl4Spec

noncomputable section

/-! ## The step -/

/-- **A scheduler step** with no thread changing state, keeping the caps and
the IPC-side fields (`SOK (true, true)`). -/
def SchS (σ σ' : State Unit) : Prop := SchStep (fun _ => False) σ σ' ∧ SOK (true, true) σ σ'

theorem SchS.refl (σ : State Unit) : SchS σ σ := ⟨SchStep.refl _ σ, SOK.refl _ σ⟩

theorem SchS.trans {σ1 σ2 σ3 : State Unit} (h1 : SchS σ1 σ2) (h2 : SchS σ2 σ3) : SchS σ1 σ3 :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-- The fields a state update must keep. -/
def SchKeep (σ σ' : State Unit) : Prop :=
  σ'.kheap = σ.kheap ∧ σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory ∧ σ'.cdt = σ.cdt ∧
    σ'.isOriginalCap = σ.isOriginalCap ∧ σ'.domainList = σ.domainList ∧ σ'.domainStartIndex = σ.domainStartIndex ∧
    σ'.archState.x64AllocatedIoPorts = σ.archState.x64AllocatedIoPorts ∧
    σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 ∧
    σ'.archState.x64HugePages = σ.archState.x64HugePages ∧
    σ'.archState.x64AsidTable = σ.archState.x64AsidTable ∧ σ'.interruptStates = σ.interruptStates ∧
    σ'.interruptIrqNode = σ.interruptIrqNode ∧ σ'.idleSc = σ.idleSc

theorem SchS.of_keep {σ σ' : State Unit} (h : SchKeep σ σ') : SchS σ σ' := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e8', e9, e10, e11, e12⟩ := h
  exact ⟨⟨fun p => by rw [e1]; exact OTK.refl _ _, e2, e3, e4, e5, e6, e7, e8, e8', e9, e10, e11, e12⟩,
    ⟨fun p => by rw [e1]; exact ORel.refl _ _, e3, e4, e5, e6, e12⟩⟩

/-- An update of `σ` at `p` with `o'`, related to the object there. -/
theorem SchS.upd {σ : State Unit} {p : ObjRef} {o o' : KernelObject} (hk : σ.kheap p = some o)
    (h1 : TKObj False o o') (h2 : PK (true, true) o o') :
    SchS σ { σ with kheap := Function.update σ.kheap p (some o') } :=
  ⟨(ScTKw.upd (P := fun _ => False) hk h1).toSch, SOK.upd hk h2⟩

/-! ## The combinators -/

section Comb

/-- Every outcome is a scheduler step from its start. -/
def SchK {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → SchS σ x.2

theorem SchK.of_eq {α : Type} {m : NonDet (State Unit) α} (hP : SchK m) {σ σ' : State Unit} {a : α} {X : Prop}
    (h : m σ = ({(a, σ')}, X)) : SchS σ σ' :=
  hP σ (a, σ') (by rw [h]; exact Set.mem_singleton _)

theorem schs_of {α : Type} {m : NonDet (State Unit) α} (h1 : NKT m) (h2 : Pres (true, true) m) : SchK m :=
  fun σ x hx => ⟨(h1 σ x hx).toSch, h2 σ x hx⟩

theorem schs_bind {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : SchK m)
    (hg : ∀ a, SchK (g a)) : SchK (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem schs_bind' {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β} (hm : SchK m)
    (hg : ∀ a, SchK (g a)) : SchK (NonDet.bind m g) := schs_bind hm hg

theorem schs_pure {α : Type} (a : α) : SchK (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SchS.refl σ

theorem schs_pure' {α : Type} (a : α) : SchK (NonDet.pure a : NonDet (State Unit) α) := schs_pure a

theorem schs_gets {α : Type} (g : State Unit → α) : SchK (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SchS.refl σ

theorem schs_get : SchK (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SchS.refl σ

theorem schs_assert (P : Prop) : SchK (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact SchS.refl σ

theorem schs_fail {α : Type} : SchK (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem schs_assertOpt {α : Type} (o : Option α) : SchK (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact schs_fail
  · exact schs_pure' _

theorem schs_getsThe {α : Type} (g : State Unit → Option α) : SchK (NonDet.getsThe g) := by
  intro σ x hx; exact schs_assertOpt (g σ) σ x hx

theorem schs_selectF {α : Type} (S : Set α × Prop) : SchK (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact SchS.refl σ

theorem schs_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : SchK m1)
    (h2 : SchK m2) : SchK (if P then m1 else m2) := by
  split <;> assumption

theorem schs_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : SchK m) :
    SchK (NonDet.when P m) := by
  unfold NonDet.when; exact schs_ite P h (schs_pure' _)

theorem schs_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, SchK (g a)) (o : Option α) :
    SchK (NonDet.maybeM g o) := by
  cases o
  · exact schs_pure' _
  · exact h _

theorem schs_modify {g : State Unit → State Unit} (hg : ∀ σ, SchKeep σ (g σ)) : SchK (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact SchS.of_keep (hg σ)

theorem schs_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, SchK (B r)) (r : α) : SchK (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => exact SchS.refl _
  | step _ hm _ ih => exact (hB _ _ _ hm).trans ih

end Comb

/-- `SchK` for the exception monad. -/
def SchKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := SchK (ExceptT.run m)

section CombE
variable {ε : Type}

theorem schse_bind {α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β} (hm : SchKE m)
    (hg : ∀ a, SchKE (g a)) : SchKE (m >>= g) := by
  unfold SchKE; rw [ExceptT.run_bind]
  refine schs_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact schs_pure _

theorem schse_pure {α : Type} (a : α) : SchKE (pure a : NonDetE (State Unit) ε α) := schs_pure _

theorem schse_returnOk {α : Type} (a : α) : SchKE (NonDetE.returnOk a : NonDetE (State Unit) ε α) := schs_pure _

theorem schse_throw {α : Type} (e : ε) : SchKE (NonDetE.throwError e : NonDetE (State Unit) ε α) := schs_pure _

theorem schse_liftE {α : Type} {m : NonDet (State Unit) α} (h : SchK m) : SchKE (NonDetE.liftE (ε := ε) m) := by
  unfold SchKE NonDetE.liftE; rw [ExceptT.run_lift]
  exact schs_bind h fun _ => schs_pure _

theorem schse_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : SchKE m1)
    (h2 : SchKE m2) : SchKE (if P then m1 else m2) := by
  split <;> assumption

theorem schse_whenE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : SchKE m) :
    SchKE (NonDetE.whenE P m) := by
  unfold NonDetE.whenE; exact schse_ite P h (schse_pure _)

theorem schse_assertE (P : Prop) : SchKE (NonDetE.assertE P : NonDetE (State Unit) ε Unit) :=
  schse_liftE (schs_assert P)

theorem schs_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : SchKE m)
    (hh : ∀ e, SchK (h e)) : SchK (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine schs_bind' hm fun r => ?_
  cases r with
  | ok a => exact schs_pure' _
  | error e => exact hh e

end CombE

/-! ## Machine operations keeping the memory -/

section Machine

/-- Every outcome of a machine operation keeps the memory. -/
def MK {α : Type} (mop : NonDet MachineState α) : Prop :=
  ∀ ms y, y ∈ (mop ms).1 → y.2.underlyingMemory = ms.underlyingMemory

theorem mk_bind {α β : Type} {m : NonDet MachineState α} {g : α → NonDet MachineState β} (hm : MK m)
    (hg : ∀ a, MK (g a)) : MK (m >>= g) := by
  intro ms x ⟨y, hy, hx⟩
  exact (hg y.1 y.2 x hx).trans (hm ms y hy)

theorem mk_pure {α : Type} (a : α) : MK (pure a : NonDet MachineState α) := by
  intro ms x hx; rw [Set.mem_singleton_iff.1 hx]

theorem mk_gets {α : Type} (g : MachineState → α) : MK (NonDet.gets g) := by
  intro ms x hx; rw [Set.mem_singleton_iff.1 hx]

theorem mk_selectF {α : Type} (S : Set α × Prop) : MK (NonDet.selectF S : NonDet MachineState α) := by
  intro ms x hx; obtain ⟨-, h⟩ := hx; rw [h]

theorem mk_modify {g : MachineState → MachineState} (hg : ∀ ms, (g ms).underlyingMemory = ms.underlyingMemory) :
    MK (NonDet.modify g) := by
  intro ms x hx; rw [Set.mem_singleton_iff.1 hx]; exact hg ms

theorem mk_stateAssert (P : MachineState → Prop) : MK (NonDet.stateAssert P) := by
  intro ms x hx; obtain ⟨-, rfl⟩ := hx; rfl

theorem mk_machineRestLift {α : Type} (f : MachineRestMonad α) : MK (machineRestLift f) := by
  unfold machineRestLift
  exact mk_bind (mk_gets _) fun _ => mk_bind (mk_selectF _) fun _ => mk_bind (mk_modify fun _ => rfl) fun _ =>
    mk_pure _

theorem mk_machineOpLift (f : MachineRestMonad Unit) : MK (machineOpLift f) := mk_machineRestLift _

theorem mk_enableFpu : MK enableFpu := by
  unfold enableFpu; exact mk_bind (mk_machineOpLift _) fun _ => mk_modify fun _ => rfl

theorem mk_disableFpu : MK disableFpu := by
  unfold disableFpu; exact mk_bind (mk_machineOpLift _) fun _ => mk_modify fun _ => rfl

theorem mk_readFpuState : MK readFpuState := by
  unfold readFpuState; exact mk_bind (mk_stateAssert _) fun _ => mk_machineRestLift _

theorem mk_writeFpuState (v : FpuState) : MK (writeFpuState v) := by
  unfold writeFpuState; exact mk_bind (mk_stateAssert _) fun _ => mk_machineOpLift _

theorem mk_setDeadline (d : Word64) : MK (setDeadline d) := mk_machineOpLift _

theorem doMachineOp_mem2 {α : Type} {mop : NonDet MachineState α} {σ σ' : State Unit} {r : α}
    (h : (r, σ') ∈ (doMachineOp (Z := Unit) mop σ).1) :
    ∃ ms, (r, ms) ∈ (mop σ.machineState).1 ∧ σ' = { σ with machineState := ms } := by
  unfold doMachineOp at h
  simp only [Fl4Proofs.P3.Notif.nd_bind_apply', NonDet.gets, NonDet.selectF, NonDet.modify, Set.mem_setOf_eq,
    Set.mem_singleton_iff] at h
  obtain ⟨x, rfl, y, ⟨hy1, hy⟩, z, rfl, hz⟩ := h
  subst hy
  simp only [pure, NonDet.pure, Set.mem_singleton_iff, Prod.mk.injEq] at hz
  obtain ⟨rfl, rfl⟩ := hz
  exact ⟨_, hy1, rfl⟩

theorem schs_doMachineOp {α : Type} {mop : NonDet MachineState α} (h : MK mop) :
    SchK (doMachineOp (Z := Unit) mop) := by
  intro σ x hx
  obtain ⟨ms, hms, e⟩ := doMachineOp_mem2 (r := x.1) (σ' := x.2) hx
  rw [e]
  exact SchS.of_keep ⟨rfl, h _ _ hms, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Machine

/-- One step of an `SchK` proof. -/
macro "schs_step0" : tactic => `(tactic| first
  | with_reducible exact schs_pure _ | with_reducible exact schs_pure' _ | with_reducible exact schs_fail
  | with_reducible exact schs_gets _ | with_reducible exact schs_get
  | with_reducible exact schs_assert _ | with_reducible exact schs_assertOpt _
  | with_reducible exact schs_getsThe _ | with_reducible exact schs_selectF _
  | ((with_reducible apply schs_modify); intro _; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  | (with_reducible refine schs_bind ?_ (fun _ => ?_))
  | (with_reducible refine schs_bind' ?_ (fun _ => ?_))
  | (with_reducible apply schs_ite) | (with_reducible apply schs_when)
  | (with_reducible refine schs_maybeM (fun _ => ?_) _)
  | (with_reducible refine schs_whileLoop (fun _ => ?_) _)
  | with_reducible exact schse_pure _ | with_reducible exact schse_returnOk _ | with_reducible exact schse_throw _
  | with_reducible exact schse_assertE _
  | (with_reducible refine schse_bind ?_ (fun _ => ?_))
  | (with_reducible apply schse_liftE) | (with_reducible apply schse_ite) | (with_reducible apply schse_whenE)
  | (with_reducible refine schs_catch ?_ (fun _ => ?_))
  | split
  | (dsimp only))

/-- An `SchK` lemma of a spec function (extended below, one rule per lemma). -/
syntax "schs_leaf" : tactic
macro_rules | `(tactic| schs_leaf) => `(tactic| fail "no schs_leaf")

macro "schs_auto" : tactic => `(tactic| repeat' (first | schs_leaf | schs_step0))

/-! ## The leaves -/

section Leaves

theorem schs_doMachineOp_enableFpu : SchK (doMachineOp (Z := Unit) enableFpu) := schs_doMachineOp mk_enableFpu
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_doMachineOp_enableFpu)
theorem schs_doMachineOp_disableFpu : SchK (doMachineOp (Z := Unit) disableFpu) := schs_doMachineOp mk_disableFpu
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_doMachineOp_disableFpu)
theorem schs_doMachineOp_readFpuState : SchK (doMachineOp (Z := Unit) readFpuState) :=
  schs_doMachineOp mk_readFpuState
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_doMachineOp_readFpuState)
theorem schs_doMachineOp_writeFpuState (v : FpuState) : SchK (doMachineOp (Z := Unit) (writeFpuState v)) :=
  schs_doMachineOp (mk_writeFpuState v)
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_doMachineOp_writeFpuState _)
theorem schs_doMachineOp_setDeadline (d : Word64) : SchK (doMachineOp (Z := Unit) (setDeadline d)) :=
  schs_doMachineOp (mk_setDeadline d)
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_doMachineOp_setDeadline _)

theorem schs_threadGet {α : Type} (g : Tcb → α) (p : ObjRef) : SchK (threadGet (Z := Unit) g p) :=
  schs_of (nkt_threadGet g p) (pres_threadGet (true, true) g p)
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_threadGet _ _)
theorem schs_getTcbObjRef (g : Tcb → Option ObjRef) (p : ObjRef) : SchK (getTcbObjRef (Z := Unit) g p) :=
  schs_threadGet g p
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_getTcbObjRef _ _)
theorem schs_getSchedContext (p : ObjRef) : SchK (getSchedContext (Z := Unit) p) :=
  schs_of (nkt_getSchedContext p) (pres_getSchedContext (true, true) p)
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_getSchedContext _)
theorem schs_getObject (p : ObjRef) : SchK (getObject (Z := Unit) p) := schs_getsThe _
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_getObject _)
theorem schs_tcbSchedAction (a : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    SchK (tcbSchedAction (Z := Unit) a t) := schs_of (nkt_tcbSchedAction a t) (pres_tcbSchedAction (true, true) a t)
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_tcbSchedAction _ _)
theorem schs_rescheduleRequired : SchK (rescheduleRequired (Z := Unit)) :=
  schs_of nkt_rescheduleRequired (pres_rescheduleRequired (true, true))
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_rescheduleRequired)
theorem schs_tcbReleaseRemove (t : ObjRef) : SchK (tcbReleaseRemove (Z := Unit) t) :=
  schs_of (nkt_tcbReleaseRemove t) (pres_tcbReleaseRemove (true, true) t)
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_tcbReleaseRemove _)
theorem schs_possibleSwitchTo (t : ObjRef) : SchK (possibleSwitchTo (Z := Unit) t) :=
  schs_of (nkt_possibleSwitchTo t) (pres_possibleSwitchTo (true, true) t)
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_possibleSwitchTo _)
theorem schs_commitTime : SchK (commitTime (Z := Unit)) := schs_of nkt_commitTime (pres_commitTime (true, true))
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_commitTime)
theorem schs_ifCondRefillUnblockCheck (o : Option ObjRef) (a b : Option Bool) :
    SchK (ifCondRefillUnblockCheck (Z := Unit) o a b) :=
  schs_of (nkt_ifCondRefillUnblockCheck o a b) (pres_ifCondRefillUnblockCheck (true, true) o a b)
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_ifCondRefillUnblockCheck _ _ _)
theorem schs_doExtendedOp (eop : DetExtMonad Unit) : SchK (doExtendedOp (Z := Unit) eop) :=
  schs_of (nkt_doExtendedOp eop) (pres_doExtendedOp eop)
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_doExtendedOp _)

theorem schs_getCap (sl : CslotPtr) : SchK (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; schs_auto
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_getCap _)

theorem schs_getAsidPool (p : ObjRef) : SchK (getAsidPool (Z := Unit) p) := by
  unfold getAsidPool; schs_auto
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_getAsidPool _)

/-- The FPU owner flag of a TCB. -/
theorem schs_archThreadSet_fpu (b : Bool) (t : ObjRef) :
    SchK (archThreadSet (Z := Unit) (fun a => { a with tcbCurFpu := b }) t) := by
  unfold archThreadSet
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getsThe_getTcb_mem hy
  rw [hs] at hx
  obtain ⟨k, hk', -, e⟩ := setObject_mem hx
  rw [hk] at hk'; cases hk'
  rw [e]
  exact SchS.upd hk (Or.inr (Or.inl ⟨_, _, rfl, rfl, rfl, Or.inl rfl⟩)) (by simp [PK])
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_archThreadSet_fpu _ _)

/-- A user-context operation keeping the registers (the FPU state). -/
theorem schs_asUser {α : Type} (p : ObjRef) (u : UserMonad α)
    (hu : ∀ uc y, y ∈ (u uc).1 → y.2.userRegs = uc.userRegs) : SchK (asUser (Z := Unit) p u) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getsThe_getTcb_mem hy
  rw [hs] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy2] at hx
  obtain ⟨y3, hy3, hx⟩ := hx
  obtain ⟨hm3, e3⟩ := hy3
  obtain ⟨y4, hy4, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy4] at hx
  obtain ⟨y5, hy5, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hx]
  simp only at e3 hy5 hm3
  rw [e3] at hy5
  obtain ⟨k, hk', -, e⟩ := setObject_mem hy5
  rw [hk] at hk'; cases hk'
  rw [e]
  have hr := hu _ _ hm3
  refine SchS.upd hk (Or.inr (Or.inl ⟨_, _, rfl, rfl, ?_, Or.inl rfl⟩)) (by simp [PK])
  unfold TcbSchedOnly archTcbContextSet
  simp only [archTcbContextGet] at hr ⊢
  rw [← hr]

theorem schs_saveFpuState (t : ObjRef) : SchK (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState
  refine schs_bind schs_doMachineOp_readFpuState fun f => schs_asUser _ _ fun uc y hy => ?_
  unfold setFPUState at hy; rw [Set.mem_singleton_iff.1 hy]
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_saveFpuState _)

theorem schs_loadFpuState (t : ObjRef) : SchK (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState
  refine schs_bind (schs_asUser _ _ fun uc y hy => ?_) fun f => schs_doMachineOp_writeFpuState _
  unfold getFPUState at hy; rw [Set.mem_singleton_iff.1 hy]
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_loadFpuState _)

theorem schs_setX64CurrentFpuOwner (o : Option ObjRef) : SchK (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner; schs_auto
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_setX64CurrentFpuOwner _)

theorem schs_switchLocalFpuOwner (o : Option ObjRef) : SchK (switchLocalFpuOwner (Z := Unit) o) := by
  unfold switchLocalFpuOwner; schs_auto
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_switchLocalFpuOwner _)

theorem schs_lazyFpuRestore (t : ObjRef) : SchK (lazyFpuRestore (Z := Unit) t) := by
  unfold lazyFpuRestore; schs_auto
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_lazyFpuRestore _)

theorem schs_setCurrentCr3 (c : Cr3) : SchK (setCurrentCr3 (Z := Unit) c) := by
  unfold setCurrentCr3; schs_auto
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_setCurrentCr3 _)

theorem schs_findVspaceForAsid (asid : Asid) : SchKE (findVspaceForAsid (Z := Unit) asid) := by
  unfold findVspaceForAsid; schs_auto
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_findVspaceForAsid _)

theorem schs_setVmRoot (t : ObjRef) : SchK (setVmRoot (Z := Unit) t) := by
  unfold setVmRoot getCurrentCr3 setCurrentVspaceRoot; schs_auto
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_setVmRoot _)

theorem schs_switchToThread (t : ObjRef) : SchK (switchToThread (Z := Unit) t) := by
  unfold switchToThread archSwitchToThread; schs_auto
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_switchToThread _)

theorem schs_switchToIdleThread : SchK (switchToIdleThread (Z := Unit)) := by
  unfold switchToIdleThread archSwitchToIdleThread; schs_auto
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_switchToIdleThread)

theorem schs_guardedSwitchTo (t : ObjRef) : SchK (guardedSwitchTo (Z := Unit) t) := by
  unfold guardedSwitchTo; schs_auto
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_guardedSwitchTo _)

theorem schs_chooseThread : SchK (chooseThread (Z := Unit)) := by
  unfold chooseThread; schs_auto
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_chooseThread)

theorem schs_scheduleChooseNewThread : SchK (scheduleChooseNewThread (Z := Unit)) := by
  unfold scheduleChooseNewThread archPrepareNextDomain nextDomain Fl4Spec.setSchedulerAction; schs_auto
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_scheduleChooseNewThread)

theorem schs_awaken : SchK (awaken (Z := Unit)) := by
  unfold awaken tcbReleaseDequeue; schs_auto
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_awaken)

theorem schs_setNextInterrupt : SchK (setNextInterrupt (Z := Unit)) := by
  unfold setNextInterrupt getRefillHead; schs_auto
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_setNextInterrupt)

theorem schs_scAndTimer : SchK (scAndTimer (Z := Unit)) := by
  unfold scAndTimer switchSchedContext ifConstantBandwidthRefillUnblockCheck; schs_auto
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_scAndTimer)

theorem schs_scheduleSwitchThreadFastfail (ct it : ObjRef) (p q : Priority) :
    SchK (scheduleSwitchThreadFastfail (Z := Unit) ct it p q) := by
  unfold scheduleSwitchThreadFastfail; exact schs_pure _
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_scheduleSwitchThreadFastfail _ _ _ _)

theorem schs_setSchedulerAction (a : SchedulerAction) : SchK (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; schs_auto
macro_rules | `(tactic| schs_leaf) => `(tactic| with_reducible exact schs_setSchedulerAction _)

/-- **The spec's `schedule` is a scheduler step.** -/
theorem schs_schedule : SchK (schedule (Z := Unit)) := by
  unfold schedule checkDomainTime; schs_auto

end Leaves

end

end Fl4Proofs.P3.Sched
