/-
P3 (issue #16, fb3i): **the frame batch commutes with a change of one
thread's state and of the scheduler action** (spec side only), for the
spec's `Restart` before the batch that FL4 omits (KENTRY-PLAN fb3h, lead
decision (a)).

* `fbsM ct ts sa σ`: `σ` with the thread state of the TCB at `ct` (if any)
  set to `ts` and the scheduler action set to `sa` (`fbsK`: the object view).
* `CM ct m`: every outcome `(r, τ)` of `m` from `σ` gives the outcome
  `(r, fbsM ct ts sa τ)` of `m` from `fbsM ct ts sa σ` (`m` reads neither the
  thread state at `ct` nor the scheduler action, and writes neither). The
  combinators mirror `IK`'s (`cm_step0`, `cm_auto`, leaves by `cm_leaf`);
  the object leaves: `get_object` followed by a reader that ignores a TCB's
  state (`cm_getObject_bind`), `set_object` of a non-TCB (`cm_setObject`),
  `set_cap` (`cm_setCap`), `is_final_cap` (`cm_isFinalCap`), the extended op.
* **`cm_performFrameBatchX`**: `CM` of the batch with its frame deletes
  written out (SpecFbX).
* `capDelete_supX` / `fbEntry_supX` / **`performFrameBatch_supX`**: the
  converse of SpecFbX's inclusions (a frame's `fbDelX` round is a
  `cap_delete` outcome), so `performFrameBatch` and `performFrameBatchX`
  have the same outcomes.
* **`performFrameBatch_fbsM`**: an outcome `(r, τ)` of the batch from `σ`
  gives the outcome `(r, fbsM ct ts sa τ)` from `fbsM ct ts sa σ`.
-/
import Fl4Proofs.P3.SpecFbX
open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The state change -/

/-- A TCB with its thread state set to `ts`; other objects unchanged. -/
def fbsTo (ts : ThreadState) : KernelObject → KernelObject
  | .tcb y => .tcb { y with tcbState := ts }
  | o => o

/-- The object view at `q`: `fbsTo` at `ct`, unchanged elsewhere. -/
def fbsK (ct : ObjRef) (ts : ThreadState) (q : ObjRef) (o : KernelObject) : KernelObject :=
  if q = ct then fbsTo ts o else o

/-- `σ` with the thread state at `ct` set to `ts` and the scheduler action set to `sa`. -/
def fbsM (ct : ObjRef) (ts : ThreadState) (sa : SchedulerAction) (σ : State Unit) : State Unit :=
  { σ with kheap := fun q => (σ.kheap q).map (fbsK ct ts q), schedulerAction := sa }

theorem fbsM_kheap (ct : ObjRef) (ts : ThreadState) (sa : SchedulerAction) (σ : State Unit) (q : ObjRef) :
    (fbsM ct ts sa σ).kheap q = (σ.kheap q).map (fbsK ct ts q) := rfl

theorem fbsK_ntcb {ct : ObjRef} {ts : ThreadState} {q : ObjRef} {o : KernelObject} (h : ∀ t, o ≠ .tcb t) :
    fbsK ct ts q o = o := by
  unfold fbsK
  split
  · cases o
    case tcb t => exact absurd rfl (h t)
    all_goals rfl
  · rfl

theorem fbsK_ne {ct : ObjRef} {ts : ThreadState} {q : ObjRef} (o : KernelObject) (h : q ≠ ct) :
    fbsK ct ts q o = o := by
  unfold fbsK; rw [if_neg h]

theorem aType_fbsK (ct : ObjRef) (ts : ThreadState) (q : ObjRef) (o : KernelObject) :
    aType (fbsK ct ts q o) = aType o := by
  unfold fbsK fbsTo
  split
  · split <;> rfl
  · rfl

theorem capView_fbsK (ct : ObjRef) (ts : ThreadState) (q : ObjRef) (o : KernelObject) :
    capView (fbsK ct ts q o) = capView o := by
  unfold fbsK fbsTo
  split
  · split <;> rfl
  · rfl

theorem capAt_fbsM (ct : ObjRef) (ts : ThreadState) (sa : SchedulerAction) (σ : State Unit) (sl : CslotPtr) :
    capAt (fbsM ct ts sa σ) sl = capAt σ sl := by
  unfold capAt
  rw [fbsM_kheap]
  cases σ.kheap sl.1 with
  | none => rfl
  | some o => exact congrFun (capView_fbsK ct ts sl.1 o) sl.2

/-- Every outcome of `m` from `σ` gives the outcome with `fbsM` from `fbsM σ`. -/
def CM (ct : ObjRef) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ ts sa σ x, x ∈ (m σ).1 → (x.1, fbsM ct ts sa x.2) ∈ (m (fbsM ct ts sa σ)).1

/-- `CM` for the exception monad. -/
abbrev CME (ct : ObjRef) {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := CM ct (ExceptT.run m)

/-! ## Combinators -/

section Comb
variable {ct : ObjRef}

theorem cm_bind {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : CM ct m)
    (hg : ∀ a, CM ct (g a)) : CM ct (m >>= g) := by
  intro ts sa σ x ⟨y, hy, hx⟩
  exact ⟨(y.1, fbsM ct ts sa y.2), hm ts sa σ y hy, hg y.1 ts sa y.2 x hx⟩

theorem cm_bind' {α γ : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) γ} (hm : CM ct m)
    (hg : ∀ a, CM ct (g a)) : CM ct (NonDet.bind m g) := cm_bind hm hg

theorem cm_pure {α : Type} (a : α) : CM ct (pure a : NonDet (State Unit) α) := by
  intro ts sa σ x hx
  rw [Set.mem_singleton_iff.1 hx]; exact Set.mem_singleton _

theorem cm_pure' {α : Type} (a : α) : CM ct (NonDet.pure a : NonDet (State Unit) α) := cm_pure a

theorem cm_gets {α : Type} (g : State Unit → α) (h : ∀ ts sa σ, g (fbsM ct ts sa σ) = g σ) :
    CM ct (NonDet.gets g) := by
  intro ts sa σ x hx
  rw [Set.mem_singleton_iff.1 hx]
  show (g σ, fbsM ct ts sa σ) ∈ ({(g (fbsM ct ts sa σ), fbsM ct ts sa σ)} : Set _)
  rw [h]; exact Set.mem_singleton _

theorem cm_assert (P : Prop) : CM ct (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro ts sa σ x hx
  obtain ⟨hp, rfl⟩ := hx
  exact ⟨hp, rfl⟩

theorem cm_stateAssert (Q : State Unit → Prop) (h : ∀ ts sa σ, Q (fbsM ct ts sa σ) ↔ Q σ) :
    CM ct (NonDet.stateAssert Q) := by
  intro ts sa σ x hx
  obtain ⟨hp, rfl⟩ := hx
  exact ⟨(h ts sa σ).2 hp, rfl⟩

theorem cm_fail {α : Type} : CM ct (NonDet.fail : NonDet (State Unit) α) := fun _ _ _ _ hx => hx.elim

theorem cm_assertOpt {α : Type} (o : Option α) : CM ct (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact cm_fail
  · exact cm_pure' _

theorem cm_getsThe {α : Type} (g : State Unit → Option α) (h : ∀ ts sa σ, g (fbsM ct ts sa σ) = g σ) :
    CM ct (NonDet.getsThe g) := by
  intro ts sa σ x hx
  change x ∈ (NonDet.assertOpt (g σ) σ).1 at hx
  change (x.1, fbsM ct ts sa x.2) ∈ (NonDet.assertOpt (g (fbsM ct ts sa σ)) (fbsM ct ts sa σ)).1
  rw [h]; exact cm_assertOpt (g σ) ts sa σ x hx

theorem cm_selectF {α : Type} (S : Set α × Prop) : CM ct (NonDet.selectF S : NonDet (State Unit) α) := by
  intro ts sa σ x hx
  exact ⟨hx.1, congrArg (fbsM ct ts sa) hx.2⟩

theorem cm_select {α : Type} (S : Set α) : CM ct (NonDet.select S : NonDet (State Unit) α) := by
  intro ts sa σ x hx
  exact ⟨hx.1, congrArg (fbsM ct ts sa) hx.2⟩

theorem cm_ite {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDet (State Unit) α} (h1 : CM ct m1)
    (h2 : CM ct m2) : CM ct (if Q then m1 else m2) := by
  split <;> assumption

theorem cm_when (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : CM ct m) :
    CM ct (NonDet.when Q m) := by
  unfold NonDet.when; exact cm_ite Q h (cm_pure' _)

theorem cm_unless (Q : Prop) [Decidable Q] {m : NonDet (State Unit) Unit} (h : CM ct m) :
    CM ct (NonDet.unless Q m) := by
  unfold NonDet.unless; exact cm_ite Q (cm_pure' _) h

theorem cm_mapM {α β : Type} {f : α → NonDet (State Unit) β} (h : ∀ a, CM ct (f a)) :
    ∀ l, CM ct (NonDet.mapM f l)
  | [] => cm_pure' _
  | a :: as => by
    unfold NonDet.mapM
    exact cm_bind' (h a) fun _ => cm_bind' (cm_mapM h as) fun _ => cm_pure' _

theorem cm_maybeM {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, CM ct (g a)) (o : Option α) :
    CM ct (NonDet.maybeM g o) := by
  cases o
  · exact cm_pure' _
  · exact h _

theorem cm_liftM {α γ : Type} (g : α → γ) {m : NonDet (State Unit) α} (h : CM ct m) :
    CM ct (NonDet.liftM g m) := cm_bind' h fun _ => cm_pure' _

theorem cm_modify {g : State Unit → State Unit} (h : ∀ ts sa σ, g (fbsM ct ts sa σ) = fbsM ct ts sa (g σ)) :
    CM ct (NonDet.modify g) := by
  intro ts sa σ x hx
  rw [Set.mem_singleton_iff.1 hx]
  show ((), fbsM ct ts sa (g σ)) ∈ ({((), g (fbsM ct ts sa σ))} : Set _)
  rw [h]; exact Set.mem_singleton _

theorem cm_get_put {g : State Unit → State Unit} (h : ∀ ts sa σ, g (fbsM ct ts sa σ) = fbsM ct ts sa (g σ)) :
    CM ct (NonDet.get >>= fun s => NonDet.put (g s)) := by
  intro ts sa σ x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  rw [Set.mem_singleton_iff.1 hx]
  refine ⟨(fbsM ct ts sa σ, fbsM ct ts sa σ), Set.mem_singleton _, ?_⟩
  show ((), fbsM ct ts sa (g σ)) ∈ ({((), g (fbsM ct ts sa σ))} : Set _)
  rw [h]; exact Set.mem_singleton _

end Comb

section CombE
variable {ct : ObjRef} {ε : Type}

theorem cme_bind {α γ : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε γ} (hm : CME ct m)
    (hg : ∀ a, CME ct (g a)) : CME ct (m >>= g) := by
  unfold CME; rw [ExceptT.run_bind]
  refine cm_bind hm fun r => ?_
  cases r with
  | ok a => exact hg a
  | error e => exact cm_pure _

theorem cme_pure {α : Type} (a : α) : CME ct (pure a : NonDetE (State Unit) ε α) := cm_pure _

theorem cme_returnOk {α : Type} (a : α) : CME ct (NonDetE.returnOk a : NonDetE (State Unit) ε α) := cm_pure _

theorem cme_throw {α : Type} (e : ε) : CME ct (NonDetE.throwError e : NonDetE (State Unit) ε α) := cm_pure _

theorem cme_throw' {α : Type} (e : ε) : CME ct (throw e : NonDetE (State Unit) ε α) := cm_pure _

theorem cme_liftE {α : Type} {m : NonDet (State Unit) α} (h : CM ct m) : CME ct (NonDetE.liftE (ε := ε) m) := by
  unfold CME NonDetE.liftE; rw [ExceptT.run_lift]
  exact cm_bind h fun _ => cm_pure _

theorem cme_ite {α : Type} (Q : Prop) [Decidable Q] {m1 m2 : NonDetE (State Unit) ε α} (h1 : CME ct m1)
    (h2 : CME ct m2) : CME ct (if Q then m1 else m2) := by
  split <;> assumption

theorem cme_whenE (Q : Prop) [Decidable Q] {m : NonDetE (State Unit) ε Unit} (h : CME ct m) :
    CME ct (NonDetE.whenE Q m) := by
  unfold NonDetE.whenE; exact cme_ite Q h (cme_pure _)

theorem cme_unlessE (Q : Prop) [Decidable Q] {m : NonDetE (State Unit) ε Unit} (h : CME ct m) :
    CME ct (NonDetE.unlessE Q m) := by
  unfold NonDetE.unlessE; exact cme_ite Q (cme_pure _) h

theorem cme_throwOpt {α : Type} (e : ε) (o : Option α) : CME ct (NonDetE.throwOpt e o : NonDetE (State Unit) ε α) := by
  cases o
  · exact cme_throw' e
  · exact cme_pure _

theorem cme_assertE (Q : Prop) : CME ct (NonDetE.assertE Q : NonDetE (State Unit) ε Unit) :=
  cme_liftE (cm_assert Q)

theorem cm_catch {α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDet (State Unit) α} (hm : CME ct m)
    (hh : ∀ e, CM ct (h e)) : CM ct (NonDetE.catch m h) := by
  unfold NonDetE.catch
  refine cm_bind' hm fun r => ?_
  cases r with
  | ok a => exact cm_pure' _
  | error e => exact hh e

theorem cme_handleE {ε' α : Type} {m : NonDetE (State Unit) ε α} {h : ε → NonDetE (State Unit) ε' α}
    (hm : CME ct m) (hh : ∀ e, CME ct (h e)) : CME ct (NonDetE.handleE m h) := by
  unfold NonDetE.handleE CME
  rw [ExceptT.run_mk]
  refine cm_bind' hm fun r => ?_
  cases r with
  | ok a => exact cm_pure' _
  | error e => exact hh e

theorem cme_liftME {α γ : Type} (g : α → γ) {m : NonDetE (State Unit) ε α} (h : CME ct m) :
    CME ct (NonDetE.liftME g m) := by
  unfold NonDetE.liftME; exact cme_bind h fun _ => cme_pure _

end CombE

/-! ## Object leaves -/

section Obj
variable {ct : ObjRef}

theorem fbs_getObject_mem {p : ObjRef} {σ : State Unit} {y : KernelObject × State Unit}
    (hy : y ∈ (getObject (Z := Unit) p σ).1) : y.2 = σ ∧ σ.kheap p = some y.1 := by
  change y ∈ (NonDet.assertOpt (σ.kheap p) σ).1 at hy
  cases ho : σ.kheap p with
  | none => rw [ho] at hy; exact hy.elim
  | some o =>
    rw [ho] at hy
    rw [Set.mem_singleton_iff.1 hy]; exact ⟨rfl, rfl⟩

theorem fbs_getObject_of {p : ObjRef} {σ : State Unit} {o : KernelObject} (h : σ.kheap p = some o) (ts : ThreadState)
    (sa : SchedulerAction) : (fbsK ct ts p o, fbsM ct ts sa σ) ∈ (getObject (Z := Unit) p (fbsM ct ts sa σ)).1 := by
  change _ ∈ (NonDet.assertOpt ((fbsM ct ts sa σ).kheap p) (fbsM ct ts sa σ)).1
  rw [fbsM_kheap, h]; exact Set.mem_singleton _

/-- `get_object` followed by a reader that ignores a TCB's thread state. -/
theorem cm_getObject_bind {β : Type} (p : ObjRef) {k : KernelObject → NonDet (State Unit) β} (hk : ∀ o, CM ct (k o))
    (ht : ∀ (y : Tcb) (ts : ThreadState), k (.tcb { y with tcbState := ts }) = k (.tcb y)) :
    CM ct (getObject (Z := Unit) p >>= k) := by
  intro ts sa σ x ⟨y, hy, hx⟩
  obtain ⟨e1, e2⟩ := fbs_getObject_mem hy
  refine ⟨_, fbs_getObject_of e2 ts sa, ?_⟩
  have ek : ∀ o, k (fbsK ct ts p o) = k o := by
    intro o
    unfold fbsK
    split
    · cases o
      case tcb t => exact ht t ts
      all_goals rfl
    · rfl
  dsimp only
  rw [ek, ← e1]
  exact hk y.1 ts sa y.2 x hx

/-- `set_object`, with the object written seen through `fbsK`. -/
theorem fbs_setObject {p : ObjRef} {o : KernelObject} {σ : State Unit} {x : Unit × State Unit}
    (hx : x ∈ (setObject (Z := Unit) p o σ).1) (ts : ThreadState) (sa : SchedulerAction) :
    (x.1, fbsM ct ts sa x.2) ∈ (setObject (Z := Unit) p (fbsK ct ts p o) (fbsM ct ts sa σ)).1 := by
  unfold setObject at hx ⊢
  obtain ⟨y, hy, z, ⟨hz, rfl⟩, w, hw, hx⟩ := hx
  obtain ⟨e1, e2⟩ := fbs_getObject_mem hy
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  refine ⟨_, fbs_getObject_of e2 ts sa, ((), fbsM ct ts sa σ), ⟨by rw [aType_fbsK, aType_fbsK]; exact hz, rfl⟩,
    (fbsM ct ts sa σ, fbsM ct ts sa σ), Set.mem_singleton _, ?_⟩
  rw [e1]
  show ((), _) ∈ ({((), _)} : Set _)
  refine Set.mem_singleton_iff.2 (Prod.ext rfl ?_)
  show fbsM ct ts sa { σ with kheap := Function.update σ.kheap p (some o) } =
    ({ (fbsM ct ts sa σ) with kheap := Function.update (fbsM ct ts sa σ).kheap p (some (fbsK ct ts p o)) } : State Unit)
  have e : Function.update (fbsM ct ts sa σ).kheap p (some (fbsK ct ts p o)) =
      fun q => ((Function.update σ.kheap p (some o)) q).map (fbsK ct ts q) := by
    funext q
    by_cases hq : q = p
    · subst hq; simp
    · simp [Function.update_of_ne hq, fbsM_kheap]
  rw [e]; rfl

theorem cm_setObject (p : ObjRef) (o : KernelObject) (ho : ∀ t, o ≠ .tcb t) : CM ct (setObject (Z := Unit) p o) := by
  intro ts sa σ x hx
  have h := fbs_setObject (ct := ct) hx ts sa
  rwa [fbsK_ntcb ho] at h

theorem fbsK_self {ct : ObjRef} {ts : ThreadState} (o : KernelObject) : fbsK ct ts ct o = fbsTo ts o := if_pos rfl

/-- `set_cap`: the object written is the one read with the cap replaced. -/
theorem cm_setCap (c : Cap) (sl : CslotPtr) : CM ct (setCap (Z := Unit) c sl) := by
  obtain ⟨p, r⟩ := sl
  intro ts sa σ x hx
  unfold setCap at hx ⊢
  dsimp only at hx ⊢
  obtain ⟨⟨o, σ1⟩, hy, hx⟩ := hx
  obtain ⟨e1, e2⟩ := fbs_getObject_mem hy
  dsimp only at e1 e2 hx
  subst e1
  refine ⟨_, fbs_getObject_of e2 ts sa, ?_⟩
  dsimp only
  by_cases hp : p = ct
  · subst ct
    rw [fbsK_self]
    unfold fbsTo
    cases o <;> dsimp only at hx ⊢ <;> (try split_ifs at hx ⊢) <;>
      first
      | exact hx.elim
      | (obtain ⟨w, hw, hx⟩ := hx
         obtain rfl := Set.mem_singleton_iff.1 hw
         have h := fbs_setObject (ct := p) hx ts sa
         rw [fbsK_self] at h
         exact ⟨_, Set.mem_singleton _, h⟩)
      | (obtain ⟨w, hw, -⟩ := hx; exact hw.elim)
  · rw [fbsK_ne _ hp]
    cases o <;> dsimp only at hx ⊢ <;> (try split_ifs at hx ⊢) <;>
      first
      | exact hx.elim
      | (obtain ⟨w, hw, hx⟩ := hx
         obtain rfl := Set.mem_singleton_iff.1 hw
         have h := fbs_setObject (ct := ct) hx ts sa
         rw [fbsK_ne _ hp] at h
         exact ⟨_, Set.mem_singleton _, h⟩)
      | (obtain ⟨w, hw, -⟩ := hx; exact hw.elim)

end Obj

/-! ## Other leaves -/

section Leaves
variable {ct : ObjRef}

theorem fbs_getCap_single (sl : CslotPtr) (s : State Unit) (c : Cap) :
    (getCap (Z := Unit) sl s).1 = {(c, s)} ↔ capAt s sl = some c := by
  constructor
  · intro h
    have hm : (c, s) ∈ (getCap (Z := Unit) sl s).1 := by rw [h]; exact Set.mem_singleton _
    exact (getCap_capAt hm).2
  · intro h
    ext y
    constructor
    · intro hy
      obtain ⟨e1, e2⟩ := getCap_capAt hy
      rw [h] at e2
      exact Prod.ext (Option.some.inj e2).symm e1
    · intro hy
      rw [Set.mem_singleton_iff.1 hy]
      exact fbx_getCap_of_capAt h

theorem fbs_isFinalCap' (c : Cap) (ts : ThreadState) (sa : SchedulerAction) (σ : State Unit) :
    isFinalCap' (Z := Unit) c (fbsM ct ts sa σ) ↔ isFinalCap' (Z := Unit) c σ := by
  unfold isFinalCap'
  simp only [fbs_getCap_single, capAt_fbsM]

theorem cm_isFinalCap (c : Cap) : CM ct (isFinalCap (Z := Unit) c) := by
  unfold isFinalCap
  refine cm_gets _ fun ts sa σ => ?_
  simp only [fbs_isFinalCap']

theorem cm_doExtendedOp (eop : DetExtMonad Unit) : CM ct (doExtendedOp (Z := Unit) eop) := by
  intro ts sa σ x hx
  unfold doExtendedOp at hx ⊢
  obtain ⟨y, hy, z, hz, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hz
  obtain ⟨-, hz2⟩ := hz
  have ex : x = ((), σ) := by
    obtain ⟨⟨u, es⟩, t⟩ := z
    dsimp only at hz2 hx
    subst hz2
    exact Set.mem_singleton_iff.1 hx
  subst ex
  refine ⟨(fbsM ct ts sa σ, fbsM ct ts sa σ), Set.mem_singleton _, (((), fbsM ct ts sa σ), fbsM ct ts sa σ),
    ⟨Set.mem_singleton _, rfl⟩, Set.mem_singleton _⟩

end Leaves

/-- One step of a `CM` proof. -/
macro "cm_step0" : tactic => `(tactic| first
  | with_reducible exact cm_pure _ | with_reducible exact cm_pure' _ | with_reducible exact cm_fail
  | ((with_reducible apply cm_gets); intro _ _ _; rfl)
  | with_reducible exact cm_assert _ | with_reducible exact cm_assertOpt _
  | ((with_reducible apply cm_stateAssert); intro _ _ _; exact Iff.rfl)
  | ((with_reducible apply cm_getsThe); intro _ _ _; rfl)
  | with_reducible exact cm_selectF _ | with_reducible exact cm_select _
  | ((with_reducible apply cm_modify); intro _ _ _; rfl)
  | ((with_reducible apply cm_get_put); intro _ _ _; rfl)
  | with_reducible exact cm_setCap _ _ | with_reducible exact cm_isFinalCap _
  | with_reducible exact cm_doExtendedOp _
  | ((with_reducible refine cm_setObject _ _ ?_); intro _ h; cases h)
  | (with_reducible refine cm_getObject_bind _ (fun _ => ?_) ?_)
  | (with_reducible refine cm_bind ?_ (fun _ => ?_))
  | (with_reducible refine cm_bind' ?_ (fun _ => ?_))
  | (with_reducible apply cm_ite) | (with_reducible apply cm_when) | (with_reducible apply cm_unless)
  | (with_reducible refine cm_maybeM (fun _ => ?_) _) | (with_reducible refine cm_mapM (fun _ => ?_) _) | (with_reducible apply cm_liftM)
  | with_reducible exact cme_pure _ | with_reducible exact cme_returnOk _ | with_reducible exact cme_throw _
  | with_reducible exact cme_throw' _ | with_reducible exact cme_throwOpt _ _ | with_reducible exact cme_assertE _
  | (with_reducible refine cme_bind ?_ (fun _ => ?_))
  | (with_reducible apply cme_liftE) | (with_reducible apply cme_ite) | (with_reducible apply cme_whenE)
  | (with_reducible apply cme_unlessE) | (with_reducible refine cm_catch ?_ (fun _ => ?_))
  | (with_reducible refine cme_handleE ?_ (fun _ => ?_)) | (with_reducible apply cme_liftME)
  | (intro _ _; rfl)
  | split
  | (dsimp only [Function.comp_apply])
  | (dsimp only)
  | (simp only [letFun]))

open Lean Meta Elab Tactic in
/-- Unfold the spec function at the head of a `CM`/`CME` goal. -/
elab "cm_unfold" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let args := t.getAppArgs
  if args.size == 0 then throwError "cm_unfold: no arguments"
  let m := args.back!
  let m := if m.isAppOf ``ExceptT.run then m.getAppArgs.back! else m
  match m.getAppFn with
  | .const n _ =>
    if (`Fl4Spec).isPrefixOf n && !(`Fl4Spec.NonDet).isPrefixOf n && !(`Fl4Spec.NonDetE).isPrefixOf n then
      evalTactic (← `(tactic| unfold $(mkIdent n):ident))
    else throwError "cm_unfold: {n} is not a spec function"
  | _ => throwError "cm_unfold: no head constant"

/-- A `CM` lemma of a spec function (extended below, one rule per lemma). -/
syntax "cm_leaf" : tactic
macro_rules | `(tactic| cm_leaf) => `(tactic| fail "no cm_leaf")

macro "cm_auto" : tactic => `(tactic| repeat' (first | cm_leaf | cm_step0 | cm_unfold))

/-! ## The batch's steps -/

section Steps
variable {ct : ObjRef}

theorem cm_doMachineOp {α : Type} (mop : NonDet MachineState α) : CM ct (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp; cm_auto
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cm_doMachineOp _)

theorem cme_rab (p : Cap × CapRef) : CME ct (resolveAddressBits' (Z := Unit) p) := by
  rw [resolveAddressBits']
  split
  · split
    · exact cme_liftE cm_fail
    · refine cme_bind (cme_whenE _ (cme_throw _)) fun _ => cme_bind (cme_whenE _ (cme_throw _)) fun _ =>
        cme_bind (cme_returnOk _) fun _ => ?_
      dsimp only
      split
      · exact cme_returnOk _
      · refine cme_bind (cme_liftE (by unfold getCap; cm_auto)) fun nc => ?_
        split
        · exact cme_rab _
        · exact cme_returnOk _
  · exact cme_throw _
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have h1 : p.2.length ≠ 0 := by
    intro h; simp_all [List.drop_eq_nil_of_le]
  omega
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cme_rab _)

theorem cme_resolveAddressBits (p : Cap × CapRef) : CME ct (resolveAddressBits (Z := Unit) p) := cme_rab p
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cme_resolveAddressBits _)

theorem cme_lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) :
    CME ct (lookupSlotForCnodeOp (Z := Unit) isSource croot ptr depth) := by
  unfold lookupSlotForCnodeOp; cm_auto
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cme_lookupSlotForCnodeOp _ _ _ _)

theorem cme_lookupTargetSlot (c : Cap) (r : CapRef) (n : Nat) : CME ct (lookupTargetSlot (Z := Unit) c r n) :=
  cme_lookupSlotForCnodeOp _ _ _ _
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cme_lookupTargetSlot _ _ _)

theorem cme_lookupSourceSlot (c : Cap) (r : CapRef) (n : Nat) : CME ct (lookupSourceSlot (Z := Unit) c r n) :=
  cme_lookupSlotForCnodeOp _ _ _ _
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cme_lookupSourceSlot _ _ _)

theorem cm_getCap (sl : CslotPtr) : CM ct (getCap (Z := Unit) sl) := by
  unfold getCap; cm_auto
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cm_getCap _)

theorem cme_ensureEmpty (sl : CslotPtr) : CME ct (ensureEmpty (Z := Unit) sl) := by
  unfold ensureEmpty; cm_auto
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cme_ensureEmpty _)

theorem cme_deriveCap (sl : CslotPtr) (c : Cap) : CME ct (deriveCap (Z := Unit) sl c) := by
  unfold deriveCap; cm_auto
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cme_deriveCap _ _)

theorem cm_capInsert (c : Cap) (src dest : CslotPtr) : CM ct (capInsert (Z := Unit) c src dest) := by
  unfold capInsert; cm_auto
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cm_capInsert _ _ _)

theorem cme_findVspaceForAsid (a : Asid) : CME ct (findVspaceForAsid (Z := Unit) a) := by
  unfold findVspaceForAsid; cm_auto
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cme_findVspaceForAsid _)

theorem cme_createMappingEntries (base : Paddr) (vptr : VSpaceRef) (sz : VMPageSize) (r : VMRights)
    (at' : VMAttributes) (p : ObjRef) : CME ct (createMappingEntries (Z := Unit) base vptr sz r at' p) := by
  cases sz <;> unfold createMappingEntries <;> cm_auto
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cme_createMappingEntries _ _ _ _ _ _)

theorem cme_decodePageInvocation (label : Data) (args : List Data) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) : CME ct (decodePageInvocation (Z := Unit) label args cte cap ex) := by
  unfold decodePageInvocation; cm_auto
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cme_decodePageInvocation _ _ _ _ _)

theorem cm_performPageInvocation (iv : PageInvocation) : CM ct (performPageInvocation (Z := Unit) iv) := by
  unfold performPageInvocation; cm_auto
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cm_performPageInvocation _)

theorem cme_fbMap (b : Fl4FrameBatchInvocation) (sl : CslotPtr) (v : Data) : CME ct (fbMap (Z := Unit) b sl v) := by
  unfold fbMap; cm_auto
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cme_fbMap _ _ _)

theorem cm_unmapPage (sz : VMPageSize) (a : Asid) (v : VSpaceRef) (p : ObjRef) :
    CM ct (unmapPage (Z := Unit) sz a v p) := by
  unfold unmapPage; cm_auto
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cm_unmapPage _ _ _ _)

theorem cm_unmapPageUnflushed (sz : VMPageSize) (vs : ObjRef) (v : VSpaceRef) (p : ObjRef) :
    CM ct (unmapPageUnflushed (Z := Unit) sz vs v p) := by
  unfold unmapPageUnflushed; cm_auto
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cm_unmapPageUnflushed _ _ _ _)

/-- `arch_finalise_cap` of a frame cap (the only arch cap `fbDelX` finalises). -/
theorem cm_archFinaliseCap_frame (dev : Bool) (p : ObjRef) (R : CapRights) (mt : VMMapType) (sz : VMPageSize)
    (m : Option (Asid × VSpaceRef)) (fin : Bool) :
    CM ct (archFinaliseCap (Z := Unit) (.pageCap dev p R mt sz m) fin) := by
  rcases m with _ | ⟨a, v⟩ <;> cases fin <;> simp only [archFinaliseCap] <;> cm_auto
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cm_archFinaliseCap_frame _ _ _ _ _ _ _)

theorem cm_emptySlot (sl : CslotPtr) (c : Cap) : CM ct (emptySlot (Z := Unit) sl c) := by
  unfold emptySlot; cm_auto
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cm_emptySlot _ _)

theorem cme_fbDelX (sl : CslotPtr) : CME ct (fbDelX sl) := by
  unfold fbDelX; cm_auto
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible exact cme_fbDelX _)

theorem cme_fbCode {α : Type} {m : SEMonad Unit α} (h : CME ct m) : CME ct (fbCode (Z := Unit) m) := by
  unfold fbCode; exact cme_handleE h fun _ => cme_throw _
macro_rules | `(tactic| cm_leaf) => `(tactic| with_reducible refine cme_fbCode ?_)

/-- **One entry**. -/
theorem cme_fbEntryX (b : Fl4FrameBatchInvocation) (w : Data × Data × Data) : CME ct (fbEntryX b w) := by
  unfold fbEntryX fbDeleteX; cm_auto

theorem cm_fbRunX (b : Fl4FrameBatchInvocation) :
    ∀ (ws : List (Data × Data × Data)) (n : Nat) (d : Bool), CM ct (fbRunX b ws n d)
  | [], n, d => cm_pure _
  | w :: ws, n, d => by
    unfold fbRunX
    refine cm_bind (cme_fbEntryX b w) fun r => ?_
    cases r with
    | ok d' => exact cm_fbRunX b ws (n + 1) (d || d')
    | error c => exact cm_pure _

/-- **The batch** (frame deletes written out). -/
theorem cm_performFrameBatchX (b : Fl4FrameBatchInvocation) : CM ct (performFrameBatchX b) := by
  unfold performFrameBatchX
  refine cm_bind (cm_fbRunX b _ _ _) fun r => ?_
  obtain ⟨done, err, d⟩ := r
  exact cm_bind (cm_when _ (by unfold flushAll; exact cm_doMachineOp _)) fun _ => cm_pure _

end Steps

/-! ## The converse of SpecFbX's inclusions -/

theorem fbs_lfp_mem {σ α ι : Type} {F : (ι → NonDet σ α) → ι → NonDet σ α} {i : ι} {s : σ} {x : α × σ}
    (h : ∀ f : ι → NonDet σ α, (∀ k t, F f k t ≤ f k t) → x ∈ (f i s).1) : x ∈ (NonDet.lfp F i s).1 := by
  let S := {f : ι → σ → Set (α × σ) × Prop | ∀ k t, F f k t ≤ f k t}
  have hl : NonDet.lfp F = (sInf S : ι → σ → Set (α × σ) × Prop) := rfl
  let g : ι → σ → Set (α × σ) × Prop := fun k t => if k = i ∧ t = s then ({x}, False) else ⊥
  have hlow : g ≤ (sInf S : ι → σ → Set (α × σ) × Prop) := by
    apply le_sInf
    intro f hf k t
    by_cases h1 : k = i ∧ t = s
    · obtain ⟨rfl, rfl⟩ := h1
      simp only [g, and_self, ↓reduceIte]
      exact ⟨Set.singleton_subset_iff.2 (h f hf), fun h => h.elim⟩
    · simp only [g, h1, ↓reduceIte]; exact bot_le
  rw [hl]
  have := (hlow i s).1
  simp only [g, and_self, ↓reduceIte] at this
  exact this (Set.mem_singleton x)

theorem fbs_mem_liftE {σ ε α : Type} {m : NonDet σ α} {s : σ} {x : α × σ} (hx : x ∈ (m s).1) :
    ((.ok x.1 : Except ε α), x.2) ∈ ((NonDetE.liftE (ε := ε) m).run s).1 := by
  unfold NonDetE.liftE; rw [ExceptT.run_lift]
  exact ⟨x, hx, Set.mem_singleton _⟩

theorem fbs_mem_bindE {σ ε α β : Type} {m : NonDetE σ ε α} {f : α → NonDetE σ ε β} {s t : σ} {a : α}
    {y : Except ε β × σ} (h1 : (.ok a, t) ∈ (m.run s).1) (h2 : y ∈ ((f a).run t).1) :
    y ∈ ((m >>= f).run s).1 := by
  rw [ExceptT.run_bind]; exact ⟨_, h1, h2⟩

/-- **`fbDelX`'s round of a slot holding a frame cap is a `cap_delete` outcome.** -/
theorem capDelete_supX {sl : CslotPtr} {σ : State Unit} {dev : Bool} {p : ObjRef} {R : CapRights}
    {mt : VMMapType} {sz : VMPageSize} {m : Option (Asid × VSpaceRef)}
    (hc : capAt σ sl = some (.archObjectCap (.pageCap dev p R mt sz m))) :
    ∀ y ∈ ((fbDelX sl).run σ).1, y ∈ ((capDelete (Z := Unit) sl).run σ).1 := by
  intro y hy
  unfold fbDelX at hy
  obtain ⟨w, hw, rfl⟩ := fbx_mem_liftE hy
  obtain ⟨⟨c, σ'⟩, hgc, hw⟩ := hw
  obtain ⟨e1, e2⟩ := getCap_capAt hgc
  dsimp only at e1 e2 hw
  subst σ'
  rw [hc] at e2
  obtain rfl := Option.some.inj e2
  obtain ⟨⟨fin, σf⟩, hf, ⟨⟨r1, r2⟩, σz⟩, hz, hw⟩ := hw
  obtain ⟨e5, e6⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 hf)
  subst fin
  subst σf
  have hz1 := archFinaliseCap_frame hz
  dsimp only at hz1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hz1
  unfold capDelete
  refine fbs_mem_bindE (a := undefined) ?_ (Set.mem_singleton _)
  show (_ : Except Unit (Bool × Cap) × State Unit) ∈
    (NonDet.lfp (fun r c => recDelF (Z := Unit) r c) (.cTEDeleteCall sl true) σ).1
  apply fbs_lfp_mem
  intro f hf
  have hfin : ((.ok (true, .nullCap) : Except Unit (Bool × Cap)), σz) ∈ (f (.finaliseSlotCall sl true) σ).1 := by
    apply (hf _ σ).1
    show _ ∈ ((recDelF (Z := Unit) f (.finaliseSlotCall sl true)).run σ).1
    unfold recDelF withoutPreemption
    refine fbs_mem_bindE (fbs_mem_liftE (fbx_getCap_of_capAt hc)) ?_
    dsimp only
    rw [if_neg (by simp)]
    refine fbs_mem_bindE (fbs_mem_liftE (x := (decide (isFinalCap' (Z := Unit)
      (.archObjectCap (.pageCap dev p R mt sz m)) σ), σ)) (Set.mem_singleton _)) ?_
    refine fbs_mem_bindE (fbs_mem_liftE hz) ?_
    dsimp only
    rw [if_pos (show capRemoveable .nullCap sl from trivial)]
    exact Set.mem_singleton _
  apply (hf _ σ).1
  show _ ∈ ((recDelF (Z := Unit) f (.cTEDeleteCall sl true)).run σ).1
  unfold recDelF withoutPreemption
  refine fbs_mem_bindE hfin ?_
  dsimp only
  refine fbs_mem_bindE (fbs_mem_liftE (x := ((), w.2)) ?_) (Set.mem_singleton _)
  unfold NonDet.when; rw [if_pos (Or.inl rfl)]; exact hw

/-- **One entry**: every outcome of `fbEntryX` is one of `fbEntry`. -/
theorem fbEntry_supX (b : Fl4FrameBatchInvocation) (w : Data × Data × Data) (s : State Unit) :
    ∀ y ∈ ((fbEntryX b w).run s).1, y ∈ ((fbEntry (Z := Unit) b w).run s).1 := by
  rcases b with ⟨vs, asid, op, depth, mr, cr, attr, dd, cn, dcn, es⟩
  cases op
  case remap => exact fun y hy => hy
  case copyMap =>
    unfold fbEntry fbEntryX
    dsimp only
    refine fbx_sub_bindE (fun _ _ => True) (fun _ _ _ => trivial) fun dest t0 _ => ?_
    refine fbx_sub_bindE (fun _ _ => True) (fun _ _ _ => trivial) fun _ t1 _ => ?_
    refine fbx_sub_bindE (fun _ _ => True) (fun _ _ _ => trivial) fun src t2 _ => ?_
    refine fbx_sub_bindE (fun c t => t = t2 ∧ capAt t src = some c) (fun c t h => ?_) fun srcCap t3 h3 => ?_
    · obtain ⟨⟨c', t'⟩, hx, hxe⟩ := fbx_mem_liftE h
      simp only [Prod.mk.injEq, Except.ok.injEq] at hxe
      obtain ⟨rfl, rfl⟩ := hxe
      obtain ⟨e3, e4⟩ := getCap_capAt hx
      dsimp only at e3 e4
      exact ⟨e3, by rw [e3]; exact e4⟩
    refine fbx_sub_bindE (fun _ t => isPageCap srcCap = true ∧ t = t3) (fun _ t h =>
      fbx_unlessE_ok (fbx_fbCode_ok h)) fun _ t4 ⟨hpg, et4⟩ => ?_
    subst et4
    obtain ⟨dev, p, R, mt, sz, m, rfl⟩ := fbx_frame_of_isPageCap hpg
    refine fbx_sub_bindE (fun c t => IsFrameCap c) (fun c t h => ?_) fun newCap t5 h5 => ?_
    · have h' := fbx_fbCode_ok h
      simp only [maskCap, capRightsUpdate, acapRightsUpdate, deriveCap, archDeriveCap] at h'
      obtain ⟨e1, -⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h')
      simp only [Except.ok.injEq] at e1
      subst e1; exact trivial
    refine fbx_sub_bindE (fun _ t => capAt t dest = some newCap) (fun _ t h => ?_) fun _ t6 h6 => ?_
    · obtain ⟨x, hx, hxe⟩ := fbx_mem_liftE h
      obtain ⟨-, rfl⟩ := Prod.mk.inj hxe
      exact fbx_capInsert_at hx
    refine fbx_sub_bindE2 (fbx_sub_handleE2 fun c t7 h7 => ?_) (fun _ _ => True) (fun _ _ _ => trivial)
      fun _ _ _ => fun y hy => hy
    obtain ⟨e, he⟩ := fbx_fbCode_err h7
    have hca : capAt t7 dest = some newCap := by rw [fbx_fbMap_err he]; exact h6
    revert hca
    cases newCap
    case archObjectCap a =>
      cases a
      case pageCap dev' p' R' mt' sz' m' =>
        intro hca
        exact fbx_sub_bindE2 (fbx_sub_liftE (fbx_sub_catch (capDelete_supX hca))) (fun _ _ => True)
          (fun _ _ _ => trivial) fun _ _ _ => fun y hy => hy
      all_goals exact (h5 : False).elim
    all_goals exact (h5 : False).elim
  case delete =>
    unfold fbEntry fbEntryX
    dsimp only
    refine fbx_sub_bindE (fun _ _ => True) (fun _ _ _ => trivial) fun slot t0 _ => ?_
    refine fbx_sub_bindE (fun c t => capAt t slot = some c) (fun c t h => ?_) fun c t1 h1 => ?_
    · obtain ⟨⟨c', t'⟩, hx, hxe⟩ := fbx_mem_liftE h
      simp only [Prod.mk.injEq, Except.ok.injEq] at hxe
      obtain ⟨rfl, rfl⟩ := hxe
      obtain ⟨e3, e4⟩ := getCap_capAt hx
      dsimp only at e3 e4
      rw [e3]; exact e4
    cases c
    case archObjectCap a =>
      cases a
      case pageCap dev p R mt sz m =>
        have hdel : ∀ t2, capAt t2 slot = some (.archObjectCap (.pageCap dev p R .vmNoMap sz none)) ∨
            (t2 = t1) → ∀ cl : Bool, ∀ y ∈ ((fbDeleteX slot >>= fun _ =>
              (NonDetE.returnOk cl : NonDetE (State Unit) Data Bool)).run t2).1,
            y ∈ ((fbDelete (Z := Unit) slot >>= fun _ =>
              (NonDetE.returnOk cl : NonDetE (State Unit) Data Bool)).run t2).1 := by
          intro t2 h2 cl
          have hc2 : ∃ dev p R mt sz m, capAt t2 slot = some (.archObjectCap (.pageCap dev p R mt sz m)) := by
            rcases h2 with h2 | rfl
            · exact ⟨_, _, _, _, _, _, h2⟩
            · exact ⟨_, _, _, _, _, _, h1⟩
          obtain ⟨_, _, _, _, _, _, hc2⟩ := hc2
          exact fbx_sub_bindE2 (by unfold fbDelete fbDeleteX; exact fbx_sub_handleE (capDelete_supX hc2))
            (fun _ _ => True) (fun _ _ _ => trivial) fun _ _ _ => fun y hy => hy
        dsimp only
        rcases m with _ | ⟨asid', vaddr⟩
        · dsimp only
          refine fbx_sub_bindE2 (fun y hy => hy) (fun _ t => t = t1) (fun _ t h => ?_) fun cl t2 h2 =>
            hdel t2 (Or.inr h2) cl
          exact (Prod.mk.inj (Set.mem_singleton_iff.1 h)).2
        · dsimp only
          split
          · refine fbx_sub_bindE2 (fun y hy => hy)
              (fun _ t => capAt t slot = some (.archObjectCap (.pageCap dev p R .vmNoMap sz none)))
              (fun _ t h => ?_) fun cl t2 h2 => hdel t2 (Or.inl h2) cl
            obtain ⟨x, hx, hxe⟩ := fbx_mem_liftE h
            obtain ⟨-, rfl⟩ := Prod.mk.inj hxe
            obtain ⟨z1, -, hx⟩ := hx
            obtain ⟨z2, hz2, hx⟩ := hx
            rw [Set.mem_singleton_iff.1 hx]
            exact setCap_at hz2
          · refine fbx_sub_bindE2 (fun y hy => hy) (fun _ t => t = t1) (fun _ t h => ?_) fun cl t2 h2 =>
              hdel t2 (Or.inr h2) cl
            exact (Prod.mk.inj (Set.mem_singleton_iff.1 h)).2
      all_goals exact fun y hy => hy
    all_goals exact fun y hy => hy

/-- **The loop**. -/
theorem fbRun_supX (b : Fl4FrameBatchInvocation) :
    ∀ (ws : List (Data × Data × Data)) (n : Nat) (d : Bool) (s : State Unit),
      ∀ y ∈ (fbRunX b ws n d s).1, y ∈ (fbRun (Z := Unit) b ws n d s).1
  | [], n, d, s => fun y hy => hy
  | w :: ws, n, d, s => by
    unfold fbRunX fbRun
    refine fbx_sub_bind (fbEntry_supX b w s) fun r t _ => ?_
    cases r with
    | ok d' => exact fbRun_supX b ws (n + 1) (d || d') t
    | error c => exact fun y hy => hy

/-- **The batch**. -/
theorem performFrameBatch_supX (b : Fl4FrameBatchInvocation) (s : State Unit) :
    ∀ y ∈ (performFrameBatchX b s).1, y ∈ (performFrameBatch (Z := Unit) b s).1 := by
  unfold performFrameBatchX performFrameBatch
  exact fbx_sub_bind (fbRun_supX b _ _ _ s) fun _ _ _ => fun y hy => hy

/-- **The batch from the changed state**: an outcome `(r, τ)` of the batch from `σ` gives the outcome
`(r, fbsM ct ts sa τ)` from `fbsM ct ts sa σ`. -/
theorem performFrameBatch_fbsM (ct : ObjRef) (b : Fl4FrameBatchInvocation) (σ : State Unit) (ts : ThreadState)
    (sa : SchedulerAction) : ∀ x ∈ (performFrameBatch (Z := Unit) b σ).1,
      (x.1, fbsM ct ts sa x.2) ∈ (performFrameBatch (Z := Unit) b (fbsM ct ts sa σ)).1 :=
  fun x hx => performFrameBatch_supX b _ _ (cm_performFrameBatchX b ts sa σ x (performFrameBatch_subX b σ x hx))


/-! ## The scheduler fields the batch keeps -/

/-- The scheduler action, the current thread and the release queue. -/
def fbsF (σ : State Unit) : SchedulerAction × ObjRef × ReleaseQueue :=
  (σ.schedulerAction, σ.curThread, σ.releaseQueue)

/-- **The batch keeps `fbsF`.** -/
theorem fbsF_performFrameBatch (b : Fl4FrameBatchInvocation) (σ : State Unit) :
    ∀ x ∈ (performFrameBatch (Z := Unit) b σ).1, fbsF x.2 = fbsF σ := by
  intro x hx
  refine ik_performFrameBatchW (P := fun s => fbsF s = fbsF σ) b ?_ ?_ ?_ ?_ ?_ ?_ ?_ σ rfl x hx
  all_goals intros
  all_goals repeat' (first | (exact ik_doExtendedOp (fun _ _ h => h) _) | (exact ik_doMachineOp (fun _ _ h => h) _) | ik_step0 | ik_unfold)

end

end Fl4Proofs.P3.SInv
