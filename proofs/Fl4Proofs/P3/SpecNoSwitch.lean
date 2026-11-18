/-
P3 (DESIGN.md §9), scheduler: **the spec's deletions never leave a switch
pending** (`NoSwitch`, l4v `simple_sched_action`), spec side only.

* `ASt σ σ'`: the scheduler action kept or `choose_new_thread` (reflexive,
  transitive); `AK m`: every outcome of `m` is `ASt`-related to its start
  (the combinators and `ak_auto`, as VsDom's `FK`/`dk_auto`; the leaves as
  DomRecDel's `dk_` lemmas).
* The only switch-setting call on a deletion's path is `possible_switch_to`
  inside `cancel_all_ipc`, `cancel_all_signals` and `cancel_badged_sends`,
  each ending with `reschedule_required`, whose outcomes all have the
  action `choose_new_thread` (`ak_then_resched`).
* `arch_finalise_cap` keeps the action (XTopJointFinVsSpec's `archF`).
* `NoSwitch σ`: no switch pending; kept by every `AK` step (`AK.noSwitch`):
  `finalise_cap`, `empty_slot`, `cap_swap_for_delete`, `post_cap_deletion`,
  `preemption_point` (`AKE`).
-/
import Fl4Proofs.P3.DomRecDel
import Fl4Proofs.P3.XTopJointFinVsSpec
open Classical

namespace Fl4Proofs.P3.Vs
open Fl4Spec

noncomputable section

/-- **No switch pending** (l4v `simple_sched_action`). -/
def NoSwitch (σ : State Unit) : Prop := ∀ u, σ.schedulerAction ≠ .switchThread u

/-- The scheduler action kept, or `choose_new_thread`. -/
def ASt (σ σ' : State Unit) : Prop :=
  σ'.schedulerAction = σ.schedulerAction ∨ σ'.schedulerAction = .chooseNewThread

theorem ASt.refl (σ : State Unit) : ASt σ σ := Or.inl rfl

theorem ASt.trans {σ1 σ2 σ3 : State Unit} (h1 : ASt σ1 σ2) (h2 : ASt σ2 σ3) : ASt σ1 σ3 := by
  rcases h2 with e | e
  · rcases h1 with e' | e'
    · exact Or.inl (e.trans e')
    · exact Or.inr (e.trans e')
  · exact Or.inr e

theorem NoSwitch.ast {σ σ' : State Unit} (h : NoSwitch σ) (hA : ASt σ σ') : NoSwitch σ' := by
  intro u e
  rcases hA with e' | e'
  · exact h u (e'.symm.trans e)
  · rw [e'] at e; cases e

/-- Every outcome of `m` is `ASt`-related to its start. -/
def AK {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → ASt σ x.2

theorem AK.noSwitch {α : Type} {m : NonDet (State Unit) α} (h : AK m) {σ : State Unit} {x : α × State Unit}
    (hx : x ∈ (m σ).1) (hN : NoSwitch σ) : NoSwitch x.2 := hN.ast (h σ x hx)

/-- `AK` for the exception monad. -/
def AKE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := AK (ExceptT.run m)

theorem AKE.noSwitch {ε α : Type} {m : NonDetE (State Unit) ε α} (h : AKE m) {σ : State Unit}
    {x : Except ε α × State Unit} (hx : x ∈ (m.run σ).1) (hN : NoSwitch σ) : NoSwitch x.2 := hN.ast (h σ x hx)

theorem ak_of_archF {α : Type} {m : NonDet (State Unit) α} (h : FK archF m) : AK m := by
  intro σ x hx
  have e := h σ x hx
  simp only [archF, Prod.mk.injEq] at e
  exact Or.inl e.2.2.2.2.2.2.2.2.2.2.1

section Comb

theorem ak_bind {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : AK m)
    (hg : ∀ a, AK (g a)) : AK (m >>= g) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hg y.1 y.2 x hx)

theorem ak_bind' {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : AK m)
    (hg : ∀ a, AK (g a)) : AK (NonDet.bind m g) := ak_bind hm hg

theorem ak_pure {α : Type} (a : α) : AK (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ASt.refl σ

theorem ak_pure' {α : Type} (a : α) : AK (NonDet.pure a : NonDet (State Unit) α) := ak_pure a

theorem ak_gets {α : Type} (g : State Unit → α) : AK (NonDet.gets g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ASt.refl σ

theorem ak_get : AK (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact ASt.refl σ

theorem ak_assert (P : Prop) : AK (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact ASt.refl σ

theorem ak_fail {α : Type} : AK (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem ak_assertOpt {α : Type} (o : Option α) : AK (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact ak_fail
  · exact ak_pure' _

theorem ak_getsThe {α : Type} (g : State Unit → Option α) : AK (NonDet.getsThe g) := by
  intro σ x hx; exact ak_assertOpt (g σ) σ x hx

theorem ak_selectF {α : Type} (S : Set α × Prop) : AK (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact ASt.refl σ

theorem ak_select {α : Type} (S : Set α) : AK (NonDet.select S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact ASt.refl σ

theorem ak_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : AK m1)
    (h2 : AK m2) : AK (if P then m1 else m2) := by
  split <;> assumption

theorem ak_when (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : AK m) :
    AK (NonDet.when P m) := by
  unfold NonDet.when; exact ak_ite P h (ak_pure' _)

theorem ak_unless (P : Prop) [Decidable P] {m : NonDet (State Unit) Unit} (h : AK m) :
    AK (NonDet.unless P m) := by
  unfold NonDet.unless; exact ak_ite P (ak_pure' _) h

theorem ak_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, AK (g a)) (o : Option α) :
    AK (NonDet.maybeM g o) := by
  cases o
  · exact ak_pure' _
  · exact h _

theorem ak_liftM {α γ : Type} (g : α → γ) {m : NonDet (State Unit) α} (h : AK m) :
    AK (NonDet.liftM g m) := ak_bind' h fun _ => ak_pure' _

theorem ak_modify {g : State Unit → State Unit} (hg : ∀ σ, ASt σ (g σ)) : AK (NonDet.modify g) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hg σ

theorem ak_get_put {g : State Unit → State Unit} (hg : ∀ σ, ASt σ (g σ)) :
    AK (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hg σ

theorem ak_get_put' {g : State Unit → State Unit} (hg : ∀ σ, ASt σ (g σ)) :
    AK (do let s ← NonDet.get; NonDet.put (g s)) := ak_get_put hg

theorem ak_getObject (p : ObjRef) : AK (getObject (Z := Unit) p) := ak_getsThe _

theorem ak_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, AK (B r)) (r : α) : AK (NonDet.whileLoop C B r) := by
  intro σ x hx
  induction hx with
  | done _ => exact ASt.refl _
  | step _ hm _ ih => exact (hB _ _ _ hm).trans ih

theorem ak_mapMx {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, AK (g a)) (xs : List α) :
    AK (NonDet.mapMx g xs) := by
  induction xs with
  | nil => exact ak_pure' _
  | cons a xs' ih => exact ak_bind' (h a) fun _ => ih

theorem ak_forMx {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, AK (g a)) (xs : List α) :
    AK (NonDet.forMx xs g) := ak_mapMx h xs

theorem ak_mapM {α γ : Type} {g : α → NonDet (State Unit) γ} (h : ∀ a, AK (g a)) (xs : List α) :
    AK (NonDet.mapM g xs) := by
  induction xs with
  | nil => exact ak_pure' _
  | cons a xs' ih => exact ak_bind' (h a) fun _ => ak_bind' ih fun _ => ak_pure' _

theorem ak_doMachineOp {α : Type} (mop : NonDet MachineState α) : AK (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine ak_bind (ak_gets _) (fun _ => ak_bind (ak_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact ak_bind (ak_modify (fun σ => Or.inl rfl)) (fun _ => ak_pure _)

theorem ak_doExtendedOp (eop : DetExtMonad Unit) : AK (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp
  refine ak_bind ak_get (fun _ => ak_bind (ak_selectF _) (fun _ => ?_))
  split
  exact ak_modify (fun σ => Or.inl rfl)

/-- Every outcome of `m` has the action `choose_new_thread`. -/
def ChK {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, x ∈ (m σ).1 → x.2.schedulerAction = .chooseNewThread

theorem chk_bind {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ}
    (hg : ∀ a, ChK (g a)) : ChK (m >>= g) := by
  intro σ x hx
  obtain ⟨y, -, hx⟩ := hx
  exact hg y.1 y.2 x hx

theorem chk_set : ChK (setSchedulerAction (Z := Unit) .chooseNewThread) := by
  intro σ x hx
  unfold setSchedulerAction at hx
  rw [Set.mem_singleton_iff.1 hx]

/-- **`reschedule_required` leaves `choose_new_thread`**, whatever came before
(as IpcWake's `nkm_rescheduleRequired`: each branch ends with the action set). -/
theorem resched_choose : ChK (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired
  refine chk_bind (fun act => ?_)
  dsimp only
  split
  all_goals repeat' (first | exact chk_set | refine chk_bind (fun _ => ?_))

/-- **A computation followed by `reschedule_required`** is `AK`, whatever it
does (`cancel_all_ipc`, `cancel_all_signals`, `cancel_badged_sends`). -/
theorem ak_then_resched {α : Type} (m : NonDet (State Unit) α) :
    AK (m >>= fun _ => rescheduleRequired (Z := Unit)) := by
  intro σ x hx
  obtain ⟨y, -, hx⟩ := hx
  exact Or.inr (resched_choose _ _ hx)

theorem ak_setSchedulerAction_choose : AK (setSchedulerAction (Z := Unit) .chooseNewThread) := by
  unfold setSchedulerAction; exact ak_modify fun _ => Or.inr rfl

end Comb

section CombE
variable {ε : Type}

theorem ake_bind {α γ : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε γ} (hm : AKE m)
    (hg : ∀ a, AKE (g a)) : AKE (m >>= g) := by
  unfold AKE; rw [ExceptT.run_bind]
  refine ak_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact ak_pure _

theorem ake_pure {α : Type} (a : α) : AKE (pure a : NonDetE (State Unit) ε α) := ak_pure _

theorem ake_returnOk {α : Type} (a : α) : AKE (NonDetE.returnOk a : NonDetE (State Unit) ε α) := ak_pure _

theorem ake_throw {α : Type} (e : ε) : AKE (NonDetE.throwError e : NonDetE (State Unit) ε α) := ak_pure _

theorem ake_throw' {α : Type} (e : ε) : AKE (throw e : NonDetE (State Unit) ε α) := ak_pure _

theorem ake_liftE {α : Type} {m : NonDet (State Unit) α} (h : AK m) : AKE (NonDetE.liftE (ε := ε) m) := by
  unfold AKE NonDetE.liftE; rw [ExceptT.run_lift]
  exact ak_bind h fun _ => ak_pure _

theorem ake_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDetE (State Unit) ε α} (h1 : AKE m1)
    (h2 : AKE m2) : AKE (if P then m1 else m2) := by
  split <;> assumption

theorem ake_whenE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : AKE m) :
    AKE (NonDetE.whenE P m) := by
  unfold NonDetE.whenE; exact ake_ite P h (ake_pure _)

theorem ake_unlessE (P : Prop) [Decidable P] {m : NonDetE (State Unit) ε Unit} (h : AKE m) :
    AKE (NonDetE.unlessE P m) := by
  unfold NonDetE.unlessE; exact ake_ite P (ake_pure _) h

theorem ake_throwOpt {α : Type} (e : ε) (o : Option α) : AKE (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact ake_throw' e
  · exact ake_pure _

theorem ake_assertE (P : Prop) : AKE (NonDetE.assertE P : NonDetE (State Unit) ε Unit) :=
  ake_liftE (ak_assert P)

theorem ak_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : AKE m)
    (hh : ∀ e, AK (h e)) : AK (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine ak_bind' hm fun r => ?_
  cases r with
  | ok a => exact ak_pure' _
  | error e => exact hh e

theorem ake_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : AKE m) (hh : ∀ e, AKE (h e)) : AKE (NonDetE.handleE m h) := by
  unfold NonDetE.handleE AKE
  rw [ExceptT.run_mk]
  refine ak_bind' hm fun r => ?_
  cases r with
  | ok a => exact ak_pure' _
  | error e => exact hh e

theorem ake_liftME {α γ : Type} (g : α → γ) {m : NonDetE (State Unit) ε α} (h : AKE m) :
    AKE (NonDetE.liftME g m) := by
  unfold NonDetE.liftME; exact ake_bind h fun _ => ake_pure _

theorem ake_mapMEx {α γ : Type} {F : α → NonDetE (State Unit) ε γ} (h : ∀ a, AKE (F a)) :
    ∀ xs : List α, AKE (NonDetE.mapMEx F xs)
  | [] => by unfold NonDetE.mapMEx; exact ake_pure _
  | a :: rest => by unfold NonDetE.mapMEx; exact ake_bind (h a) fun _ => ake_mapMEx h rest

theorem ake_mapME {α γ : Type} {F : α → NonDetE (State Unit) ε γ} (h : ∀ a, AKE (F a)) :
    ∀ xs : List α, AKE (NonDetE.mapME F xs)
  | [] => by unfold NonDetE.mapME; exact ake_pure _
  | a :: rest => by
    unfold NonDetE.mapME; exact ake_bind (h a) fun _ => ake_bind (ake_mapME h rest) fun _ => ake_pure _

end CombE

/-- One step of an `AK` proof. -/
macro "ak_step0" : tactic => `(tactic| first
  | with_reducible exact ak_then_resched _
  | with_reducible exact ak_setSchedulerAction_choose
  | with_reducible exact ak_pure _ | with_reducible exact ak_pure' _ | with_reducible exact ak_fail
  | with_reducible exact ak_gets _ | with_reducible exact ak_get
  | with_reducible exact ak_assert _ | with_reducible exact ak_assertOpt _
  | with_reducible exact ak_getsThe _
  | with_reducible exact ak_selectF _ | with_reducible exact ak_select _
  | ((with_reducible apply ak_modify); intro _; first | exact Or.inl rfl | exact Or.inr rfl)
  | ((with_reducible apply ak_get_put); intro _; first | exact Or.inl rfl | exact Or.inr rfl)
  | (exact ak_get_put' (fun _ => Or.inl rfl))
  | (exact ak_get_put (fun _ => Or.inl rfl))
  | with_reducible exact ak_getObject _
  | with_reducible exact ak_doMachineOp _ | with_reducible exact ak_doExtendedOp _
  | (with_reducible refine ak_bind ?_ (fun _ => ?_))
  | (with_reducible refine ak_bind' ?_ (fun _ => ?_))
  | (with_reducible apply ak_ite) | (with_reducible apply ak_when) | (with_reducible apply ak_unless)
  | (with_reducible refine ak_maybeM (fun _ => ?_) _) | (with_reducible apply ak_liftM)
  | (with_reducible refine ak_whileLoop (fun _ => ?_) _)
  | (with_reducible refine ak_mapMx (fun _ => ?_) _)
  | (with_reducible refine ak_mapM (fun _ => ?_) _)
  | (with_reducible refine ak_forMx (fun _ => ?_) _)
  | with_reducible exact ake_pure _ | with_reducible exact ake_returnOk _ | with_reducible exact ake_throw _
  | with_reducible exact ake_throw' _ | with_reducible exact ake_throwOpt _ _ | with_reducible exact ake_assertE _
  | (with_reducible refine ake_bind ?_ (fun _ => ?_))
  | (with_reducible apply ake_liftE) | (with_reducible apply ake_ite) | (with_reducible apply ake_whenE)
  | (with_reducible apply ake_unlessE) | (with_reducible refine ak_catch ?_ (fun _ => ?_))
  | (with_reducible refine ake_handleE ?_ (fun _ => ?_)) | (with_reducible apply ake_liftME)
  | (with_reducible refine ake_mapMEx (fun _ => ?_) _) | (with_reducible refine ake_mapME (fun _ => ?_) _)
  | split
  | (dsimp only)
  | (simp only [letFun])
  | (dsimp only [letFun])
  | (with_reducible exact ak_pure _)
  | (exact ak_pure _))

/-- An `AK` lemma of a spec function (extended below, one rule per lemma). -/
syntax "ak_leaf" : tactic
macro_rules | `(tactic| ak_leaf) => `(tactic| fail "no ak_leaf")

macro "ak_auto" : tactic => `(tactic| repeat' (first | ak_leaf | ak_step0))

/-! ## The leaves (DomRecDel's, but `possible_switch_to` and its callers) -/

theorem ak_setObject' (p : ObjRef) (o : KernelObject) : AK (setObject (Z := Unit) p o) := by
  unfold setObject; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_setObject' _ _)

theorem ak_setCap' (c : Cap) (sl : CslotPtr) : AK (setCap (Z := Unit) c sl) := by
  obtain ⟨o, r⟩ := sl; unfold setCap; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_setCap' _ _)

theorem ak_getCap' (sl : CslotPtr) : AK (getCap (Z := Unit) sl) := by
  obtain ⟨o, r⟩ := sl; unfold getCap; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_getCap' _)

theorem ak_setOriginal' (slot : CslotPtr) (v : Bool) : AK (setOriginal (Z := Unit) slot v) := by
  unfold setOriginal; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_setOriginal' _ _)

theorem ak_updateCdt' (f : Cdt → Cdt) : AK (updateCdt (Z := Unit) f) := by
  unfold updateCdt; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_updateCdt' _)

theorem ak_setIoportMask' (f l : IoPort) (val : Bool) : AK (setIoportMask (Z := Unit) f l val) := by
  unfold setIoportMask; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_setIoportMask' _ _ _)

theorem ak_threadSet' (f : Tcb → Tcb) (t : ObjRef) : AK (threadSet (Z := Unit) f t) := by
  unfold threadSet; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_threadSet' _ _)

theorem ak_threadGet' {α : Type} (f : Tcb → α) (t : ObjRef) : AK (threadGet (Z := Unit) f t) := by
  unfold threadGet; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_threadGet' _ _)

theorem ak_setThreadState' (t : ObjRef) (ts : ThreadState) : AK (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_setThreadState' _ _)

theorem ak_getSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) :
    AK (getSimpleKo (Z := Unit) C q) := by
  unfold getSimpleKo; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_getSimpleKo' _ _)

theorem ak_setSimpleKo' {α : Type} [Nonempty α] (C : α → KernelObject) (q : ObjRef) (e : α) :
    AK (setSimpleKo (Z := Unit) C q e) := by
  unfold setSimpleKo; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_setSimpleKo' _ _ _)

theorem ak_updateSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (q : ObjRef) (new : Option ObjRef) :
    AK (updateSkObjRef (Z := Unit) C f q new) := by
  unfold updateSkObjRef; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_updateSkObjRef' _ _ _ _)

theorem ak_getSchedContext' (q : ObjRef) : AK (getSchedContext (Z := Unit) q) := by
  unfold getSchedContext; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_getSchedContext' _)

theorem ak_updateSchedContext' (q : ObjRef) (f : SchedContext → SchedContext) :
    AK (updateSchedContext (Z := Unit) q f) := by
  unfold updateSchedContext; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_updateSchedContext' _ _)

theorem ak_asUser' {α : Type} (t : ObjRef) (u : UserMonad α) : AK (asUser (Z := Unit) t u) := by
  unfold asUser; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_asUser' _ _)

theorem ak_replyUnlinkTcb' (t r : ObjRef) : AK (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_replyUnlinkTcb' _ _)

theorem ak_getThreadState' (t : ObjRef) : AK (getThreadState (Z := Unit) t) := by
  unfold getThreadState; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_getThreadState' _)

theorem ak_cancelIpc' (t : ObjRef) : AK (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc getThreadState blockedCancelIpc getBlockingObject tcbEpDequeue cancelSignal tcbNtfnDequeue
    replyRemoveTcb getReplyObjRef getSkObjRef
  ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_cancelIpc' _)

theorem ak_suspend' (t : ObjRef) : AK (suspend (Z := Unit) t) := by
  unfold suspend updateRestartPc tcbSchedAction getTcbQueue setTcbQueue tcbReleaseRemove
    schedContextCancelYieldTo getTcbObjRef getThreadState
  ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_suspend' _)

theorem ak_getSkObjRef' {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (q : ObjRef) : AK (getSkObjRef (Z := Unit) C f q) := by
  unfold getSkObjRef; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_getSkObjRef' _ _ _)

theorem ak_getScObjRef' (f : SchedContext → Option ObjRef) (q : ObjRef) : AK (getScObjRef (Z := Unit) f q) := by
  unfold getScObjRef; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_getScObjRef' _ _)

theorem ak_getIrqSlot' (irq : Irq) : AK (getIrqSlot (Z := Unit) irq) := by
  unfold getIrqSlot; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_getIrqSlot' _)

theorem ak_isFinalCap' (c : Cap) : AK (isFinalCap (Z := Unit) c) := by
  unfold isFinalCap; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_isFinalCap' _)

theorem ak_freeIoportRange' (f l : IoPort) : AK (freeIoportRange (Z := Unit) f l) := by
  unfold freeIoportRange; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_freeIoportRange' _ _)

theorem ak_setIrqState' (i : IrqState) (irq : Irq) : AK (setIrqState (Z := Unit) i irq) := by
  unfold setIrqState; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_setIrqState' _ _)

theorem ak_deletedIrqHandler' (irq : Irq) : AK (deletedIrqHandler (Z := Unit) irq) := by
  unfold deletedIrqHandler; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_deletedIrqHandler' _)

theorem ak_lookupIpcBuffer' (b : Bool) (t : ObjRef) : AK (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_lookupIpcBuffer' _ _)

theorem ak_zipWithMx' {α β γ : Type} {g : α → β → NonDet (State Unit) γ} (h : ∀ a b, AK (g a b)) :
    ∀ l1 l2, AK (NonDet.zipWithMx g l1 l2)
  | a :: l1, b :: l2 => ak_bind (h a b) (fun _ => ak_zipWithMx' h l1 l2)
  | [], _ => ak_pure' _
  | _ :: _, [] => ak_pure' _
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible refine ak_zipWithMx' (fun _ _ => ?_) _ _)

theorem ak_storeWordOffs' (p : ObjRef) (o : Nat) (v : Word) : AK (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_storeWordOffs' _ _ _)

theorem ak_setMrs' (t : ObjRef) (b : Option ObjRef) (m : List Message) : AK (setMrs (Z := Unit) t b m) := by
  unfold setMrs; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_setMrs' _ _ _)

theorem ak_setMessageInfo' (t : ObjRef) (i : MessageInfo) : AK (setMessageInfo (Z := Unit) t i) := by
  unfold setMessageInfo; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_setMessageInfo' _ _)

theorem ak_archThreadSet' (f : ArchTcb → ArchTcb) (t : ObjRef) : AK (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_archThreadSet' _ _)

theorem ak_saveFpuState' (t : ObjRef) : AK (saveFpuState (Z := Unit) t) := by
  unfold saveFpuState; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_saveFpuState' _)

theorem ak_loadFpuState' (t : ObjRef) : AK (loadFpuState (Z := Unit) t) := by
  unfold loadFpuState; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_loadFpuState' _)

theorem ak_setX64CurrentFpuOwner' (o : Option ObjRef) : AK (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_setX64CurrentFpuOwner' _)

theorem ak_switchLocalFpuOwner' (o : Option ObjRef) : AK (switchLocalFpuOwner (Z := Unit) o) := by
  unfold switchLocalFpuOwner; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_switchLocalFpuOwner' _)

theorem ak_getTcbQueue' (d : Domain) (p : Priority) : AK (getTcbQueue (Z := Unit) d p) := by
  unfold getTcbQueue; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_getTcbQueue' _ _)

theorem ak_setTcbQueue' (d : Domain) (p : Priority) (q : ReadyQueue) : AK (setTcbQueue (Z := Unit) d p q) := by
  unfold setTcbQueue; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_setTcbQueue' _ _ _)

theorem ak_tcbSchedAction' (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) : AK (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_tcbSchedAction' _ _)

theorem ak_getTcbObjRef' (f : Tcb → Option ObjRef) (t : ObjRef) : AK (getTcbObjRef (Z := Unit) f t) := by
  unfold getTcbObjRef; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_getTcbObjRef' _ _)

theorem ak_getScRefillSufficient' (sc : ObjRef) (u : Ticks) : AK (getScRefillSufficient (Z := Unit) sc u) := by
  unfold getScRefillSufficient; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_getScRefillSufficient' _ _)

theorem ak_getScRefillReady' (sc : ObjRef) : AK (getScRefillReady (Z := Unit) sc) := by
  unfold getScRefillReady; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_getScRefillReady' _)

theorem ak_tcbReleaseRemove' (t : ObjRef) : AK (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_tcbReleaseRemove' _)

theorem ak_rescheduleRequired' : AK (rescheduleRequired (Z := Unit)) :=
  fun σ x hx => Or.inr (resched_choose σ x hx)
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_rescheduleRequired' )

theorem ak_testReschedule' (t : ObjRef) : AK (testReschedule (Z := Unit) t) := by
  unfold testReschedule; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_testReschedule' _)

theorem ak_tcbEpDequeue' (t e : ObjRef) : AK (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_tcbEpDequeue' _ _)

theorem ak_tcbNtfnDequeue' (t n : ObjRef) : AK (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_tcbNtfnDequeue' _ _)

theorem ak_isRoundRobin' (sc : ObjRef) : AK (isRoundRobin (Z := Unit) sc) := by
  unfold isRoundRobin; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_isRoundRobin' _)

theorem ak_updateRefillHd' (sc : ObjRef) (f : Refill → Refill) : AK (updateRefillHd (Z := Unit) sc f) := by
  unfold updateRefillHd; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_updateRefillHd' _ _)

theorem ak_getRefillHead' (sc : ObjRef) : AK (getRefillHead (Z := Unit) sc) := by
  unfold getRefillHead; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_getRefillHead' _)

theorem ak_refillPopHead' (sc : ObjRef) : AK (refillPopHead (Z := Unit) sc) := by
  unfold refillPopHead; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_refillPopHead' _)

theorem ak_mergeOverlappingRefills' (sc : ObjRef) : AK (mergeOverlappingRefills (Z := Unit) sc) := by
  unfold mergeOverlappingRefills; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_mergeOverlappingRefills' _)

theorem ak_refillHeadOverlappingLoop' (sc : ObjRef) : AK (refillHeadOverlappingLoop (Z := Unit) sc) := by
  unfold refillHeadOverlappingLoop; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_refillHeadOverlappingLoop' _)

theorem ak_refillUnblockCheck' (sc : ObjRef) : AK (refillUnblockCheck (Z := Unit) sc) := by
  unfold refillUnblockCheck; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_refillUnblockCheck' _)

theorem ak_ifCondRefillUnblockCheck' (o : Option ObjRef) (a b : Option Bool) : AK (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_ifCondRefillUnblockCheck' _ _ _)

theorem ak_ifSporadicCurScAssertRefillUnblockCheck' (o : Option ObjRef) : AK (ifSporadicCurScAssertRefillUnblockCheck (Z := Unit) o) := by
  unfold ifSporadicCurScAssertRefillUnblockCheck; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_ifSporadicCurScAssertRefillUnblockCheck' _)

theorem ak_replyUnlinkSc' (sc r : ObjRef) : AK (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_replyUnlinkSc' _ _)

theorem ak_schedContextDonate' (sc t : ObjRef) : AK (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_schedContextDonate' _ _)

theorem ak_schedContextUpdateConsumed' (sc : ObjRef) : AK (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_schedContextUpdateConsumed' _)

theorem ak_replyFromKernel' (t : ObjRef) (x : Data × List Data) : AK (replyFromKernel (Z := Unit) t x) := by
  unfold replyFromKernel; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_replyFromKernel' _ _)

theorem ak_setConsumed' (sc t : ObjRef) : AK (setConsumed (Z := Unit) sc t) := by
  unfold setConsumed; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_setConsumed' _ _)

theorem ak_schedContextCancelYieldTo' (t : ObjRef) : AK (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_schedContextCancelYieldTo' _)

theorem ak_fpuRelease' (t : ObjRef) : AK (fpuRelease (Z := Unit) t) := by
  unfold fpuRelease; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_fpuRelease' _)

theorem ak_archPostCapDeletion' (c : ArchCap) : AK (archPostCapDeletion (Z := Unit) c) := by
  unfold archPostCapDeletion; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_archPostCapDeletion' _)

theorem ak_postCapDeletion' (c : Cap) : AK (postCapDeletion (Z := Unit) c) := by
  unfold postCapDeletion; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_postCapDeletion' _)

theorem ak_emptySlot' (sl : CslotPtr) (c : Cap) : AK (emptySlot (Z := Unit) sl c) := by
  unfold emptySlot; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_emptySlot' _ _)

theorem ak_cancelAllIpc' (e : ObjRef) : AK (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_cancelAllIpc' _)

theorem ak_schedContextMaybeUnbindNtfn' (n : ObjRef) : AK (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_schedContextMaybeUnbindNtfn' _)

theorem ak_unbindMaybeNotification' (n : ObjRef) : AK (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_unbindMaybeNotification' _)

theorem ak_cancelAllSignals' (n : ObjRef) : AK (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_cancelAllSignals' _)

theorem ak_replyRemove' (t r : ObjRef) : AK (replyRemove (Z := Unit) t r) := by
  unfold replyRemove; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_replyRemove' _ _)

theorem ak_unbindNotification' (t : ObjRef) : AK (unbindNotification (Z := Unit) t) := by
  unfold unbindNotification; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_unbindNotification' _)

theorem ak_schedContextUnbindTcb' (sc : ObjRef) : AK (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_schedContextUnbindTcb' _)

theorem ak_completeYieldTo' (t : ObjRef) : AK (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_completeYieldTo' _)

theorem ak_unbindFromSc' (t : ObjRef) : AK (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_unbindFromSc' _)

theorem ak_schedContextUnbindAllTcbs' (sc : ObjRef) : AK (schedContextUnbindAllTcbs (Z := Unit) sc) := by
  unfold schedContextUnbindAllTcbs; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_schedContextUnbindAllTcbs' _)

theorem ak_schedContextUnbindNtfn' (sc : ObjRef) : AK (schedContextUnbindNtfn (Z := Unit) sc) := by
  unfold schedContextUnbindNtfn; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_schedContextUnbindNtfn' _)

theorem ak_schedContextUnbindReply' (sc : ObjRef) : AK (schedContextUnbindReply (Z := Unit) sc) := by
  unfold schedContextUnbindReply; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_schedContextUnbindReply' _)

theorem ak_schedContextUnbindYieldFrom' (sc : ObjRef) : AK (schedContextUnbindYieldFrom (Z := Unit) sc) := by
  unfold schedContextUnbindYieldFrom; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_schedContextUnbindYieldFrom' _)

theorem ak_schedContextSetInactive' (sc : ObjRef) : AK (schedContextSetInactive (Z := Unit) sc) := by
  unfold schedContextSetInactive; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_schedContextSetInactive' _)

theorem ak_prepareThreadDelete' (t : ObjRef) : AK (prepareThreadDelete (Z := Unit) t) := by
  unfold prepareThreadDelete; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_prepareThreadDelete' _)

/-- `arch_finalise_cap` keeps the action (it keeps `archF`, XTopJointFinVsSpec). -/
theorem ak_archFinaliseCap' (c : ArchCap) (x : Bool) : AK (archFinaliseCap (Z := Unit) c x) :=
  ak_of_archF (fa_archFinaliseCap c x)
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_archFinaliseCap' _ _)

theorem ak_fastFinalise' (c : Cap) (b : Bool) : AK (fastFinalise (Z := Unit) c b) := by
  unfold fastFinalise; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_fastFinalise' _ _)

theorem ak_capDeleteOne' (sl : CslotPtr) : AK (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_capDeleteOne' _)

theorem ak_deletingIrqHandler' (irq : Irq) : AK (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_deletingIrqHandler' _)

theorem ak_capSwap' (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) : AK (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap setCdt; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_capSwap' _ _ _ _)

theorem ak_capSwapForDelete' (s1 s2 : CslotPtr) : AK (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_capSwapForDelete' _ _)

theorem ake_preemptionPoint' : AKE (preemptionPoint (Z := Unit)) := by
  unfold preemptionPoint orChoiceE updateTimeStamp getScActive; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ake_preemptionPoint')

theorem ak_cancelBadgedSends' (e : ObjRef) (b : Badge) : AK (cancelBadgedSends (Z := Unit) e b) := by
  unfold cancelBadgedSends; ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_cancelBadgedSends' _ _)

/-! ## `finalise_cap` and the deletion's other steps -/

theorem ak_finaliseCap (c : Cap) (b : Bool) : AK (finaliseCap (Z := Unit) c b) := by
  cases c <;> unfold finaliseCap <;> ak_auto
macro_rules | `(tactic| ak_leaf) => `(tactic| with_reducible exact ak_finaliseCap _ _)

theorem ak_finaliseCap_ns {c : Cap} {b : Bool} {σ : State Unit} {x : (Cap × Cap) × State Unit}
    (hx : x ∈ (finaliseCap (Z := Unit) c b σ).1) (hN : NoSwitch σ) : NoSwitch x.2 :=
  (ak_finaliseCap c b).noSwitch hx hN

end

end Fl4Proofs.P3.Vs
