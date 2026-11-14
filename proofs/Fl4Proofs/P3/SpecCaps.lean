/-
P3 (DESIGN.md §9), CSpace: **the spec's object finalisations keep the
caps** (`NKC`): every CNode and every TCB's cap slots, the CDT and the
original-cap bits are as before, and no CNode or TCB appears (`KSub`). An
operation built from reads, `set_object` of an object that is neither a
CNode nor a TCB, `thread_set` of a cap-preserving update and updates of
the other state fields keeps them. So `StateRel` carries over
(`StateRel.of_ckeep`) when FL4's slots are unchanged.

The finalise branches that do work for a final notification cap
(`finNtfn_nkc`: `sched_context_maybe_unbind_ntfn`,
`unbind_maybe_notification`, `cancel_all_signals`) and for a final reply
cap (`finReply_nkc`: `reply_remove` or `cancel_ipc` of its TCB).
-/
import Fl4Proofs.P3.CancelKSub
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open Fl4Spec

noncomputable section

/-- The spec state's caps kept, and no CNode or TCB created (`KSub`). -/
structure CKeep (σ σ' : State Unit) : Prop where
  ks : KSub σ σ'
  cn : ∀ o r cs, σ.kheap o = some (.cnode r cs) → wellFormedCnodeN r cs → σ'.kheap o = some (.cnode r cs)
  tc : ∀ o t, σ.kheap o = some (.tcb t) → ∃ t', σ'.kheap o = some (.tcb t') ∧ tcbCnodeMap t' = tcbCnodeMap t
  cdt : σ'.cdt = σ.cdt
  orig : σ'.isOriginalCap = σ.isOriginalCap

theorem CKeep.refl (σ : State Unit) : CKeep σ σ :=
  ⟨KSub.refl σ, fun _ _ _ h _ => h, fun _ t h => ⟨t, h, rfl⟩, rfl, rfl⟩

theorem CKeep.trans {σ1 σ2 σ3 : State Unit} (h1 : CKeep σ1 σ2) (h2 : CKeep σ2 σ3) : CKeep σ1 σ3 :=
  ⟨h1.ks.trans h2.ks, fun o r cs h hw => h2.cn o r cs (h1.cn o r cs h hw) hw, fun o t h => by
    obtain ⟨t1, h1', e1⟩ := h1.tc o t h
    obtain ⟨t2, h2', e2⟩ := h2.tc o t1 h1'
    exact ⟨t2, h2', e2.trans e1⟩, h2.cdt.trans h1.cdt, h2.orig.trans h1.orig⟩

/-- A state change that leaves the heap, the CDT and the original-cap bits. -/
theorem CKeep.of_eq {σ σ' : State Unit} (hk : σ'.kheap = σ.kheap) (hc : σ'.cdt = σ.cdt)
    (ho : σ'.isOriginalCap = σ.isOriginalCap) : CKeep σ σ' :=
  ⟨KSub.of_kheap hk, fun o r cs h _ => by rw [hk]; exact h, fun o t h => ⟨t, by rw [hk]; exact h, rfl⟩, hc, ho⟩

/-- **`StateRel` across a step keeping the caps.** -/
theorem StateRel.of_ckeep {th : TypedHeap} {mem : U64 → U64} {σ σ' : State Unit} (h : StateRel th mem σ)
    (hk : CKeep σ σ') : StateRel th mem σ' := by
  refine ⟨fun p r hp => ?_, fun t ht => ?_⟩
  · obtain ⟨cs, hc, hw, hs⟩ := h.cnode p r hp
    exact ⟨cs, hk.cn _ _ _ hc hw, hw, hs⟩
  · obtain ⟨x, hx, hs⟩ := h.tcb t ht
    obtain ⟨x', hx', e⟩ := hk.tc _ x hx
    exact ⟨x', hx', fun i hi => by rw [e]; exact hs i hi⟩

/-- Every outcome keeps the caps. -/
def NKC {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → CKeep σ x.2

theorem nkc_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : NKC m)
    (hf : ∀ a, NKC (f a)) : NKC (m >>= f) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hf y.1 y.2 x hx)

theorem nkc_pure {α : Type} (a : α) : NKC (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact CKeep.refl σ

theorem nkc_pure' {α : Type} (a : α) : NKC (NonDet.pure a : NonDet (State Unit) α) := nkc_pure a

theorem nkc_gets {α : Type} (f : State Unit → α) : NKC (NonDet.gets f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact CKeep.refl σ

theorem nkc_get : NKC (NonDet.get : NonDet (State Unit) (State Unit)) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact CKeep.refl σ

theorem nkc_modify {f : State Unit → State Unit} (hf : ∀ σ, (f σ).kheap = σ.kheap ∧ (f σ).cdt = σ.cdt ∧
    (f σ).isOriginalCap = σ.isOriginalCap) : NKC (NonDet.modify f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]
  exact CKeep.of_eq (hf σ).1 (hf σ).2.1 (hf σ).2.2

theorem nkc_assert (P : Prop) : NKC (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact CKeep.refl σ

theorem nkc_fail {α : Type} : NKC (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem nkc_assertOpt {α : Type} (o : Option α) : NKC (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact nkc_fail
  · exact nkc_pure' _

theorem nkc_getsThe {α : Type} (f : State Unit → Option α) : NKC (NonDet.getsThe f) := by
  intro σ x hx
  exact nkc_assertOpt (f σ) σ x hx

theorem nkc_ite {α : Type} (P : Prop) [Decidable P] {m1 m2 : NonDet (State Unit) α} (h1 : NKC m1) (h2 : NKC m2) :
    NKC (if P then m1 else m2) := by
  split <;> assumption

theorem nkc_when {P : Prop} {inst : Decidable P} {m : NonDet (State Unit) Unit} (h : NKC m) :
    NKC (@NonDet.when _ P inst m) := by
  unfold NonDet.when; split; exact h; exact nkc_pure' _

theorem nkc_unless {P : Prop} {inst : Decidable P} {m : NonDet (State Unit) Unit} (h : NKC m) :
    NKC (@NonDet.unless _ P inst m) := by
  unfold NonDet.unless; split; exact nkc_pure' _; exact h

theorem nkc_maybeM {α : Type} {f : α → NonDet (State Unit) Unit} (h : ∀ a, NKC (f a)) :
    ∀ o, NKC (NonDet.maybeM f o)
  | none => nkc_pure' _
  | some a => h a

theorem nkc_mapMx {α β : Type} {f : α → NonDet (State Unit) β} (hf : ∀ a, NKC (f a)) :
    ∀ l, NKC (NonDet.mapMx f l)
  | [] => nkc_pure' _
  | a :: l => nkc_bind (hf a) (fun _ => nkc_mapMx hf l)

theorem nkc_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, NKC (B r)) (r : α) : NKC (NonDet.whileLoop C B r) := by
  intro σ x hx
  change NonDet.WhileResults C B r σ x at hx
  induction hx with
  | done _ => exact CKeep.refl _
  | step _ hb _ ih => exact (hB _ _ _ hb).trans ih

theorem nkc_liftM {α β : Type} (f : α → β) {m : NonDet (State Unit) α} (h : NKC m) :
    NKC (NonDet.liftM f m) := by
  unfold NonDet.liftM; exact nkc_bind h (fun _ => nkc_pure _)

theorem nkc_getObject (p : ObjRef) : NKC (getObject (Z := Unit) p) := nkc_getsThe _

/-- `set_object` of an object other than a CNode or a TCB (`set_object`
keeps the type, so the old one was neither either). -/
theorem nkc_setObject {p : ObjRef} {o : KernelObject} (hc : ∀ r cs, o ≠ .cnode r cs) (ht : ∀ t, o ≠ .tcb t) :
    NKC (setObject (Z := Unit) p o) := by
  intro σ x hx
  have hks := nks_setObject p o σ x hx
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
  rw [Set.mem_singleton_iff.1 hx] at hks ⊢
  refine ⟨hks, fun o' r cs h hwf => ?_, fun o' t h => ?_, rfl, rfl⟩
  · by_cases e : o' = p
    · subst e; rw [hk] at h; cases h
      exfalso
      have : aType o = .aCapTable r := by rw [← hty]; simp [aType, hwf]
      obtain ⟨cs', rfl, -⟩ := aType_capTable this
      exact hc r cs' rfl
    · show Function.update σ.kheap p (some o) o' = _
      rw [Function.update_of_ne e]; exact h
  · by_cases e : o' = p
    · subst e; rw [hk] at h; cases h
      exfalso
      obtain ⟨t', rfl⟩ := aType_tcb (show aType o = .aTCB by rw [← hty]; rfl)
      exact ht t' rfl
    · exact ⟨t, by show Function.update σ.kheap p (some o) o' = _; rw [Function.update_of_ne e]; exact h, rfl⟩

/-- `thread_set` of an update keeping the TCB's caps. -/
theorem nkc_threadSet {f : Tcb → Tcb} (hf : ∀ t, tcbCnodeMap (f t) = tcbCnodeMap t) (p : ObjRef) :
    NKC (threadSet (Z := Unit) f p) := by
  intro σ x hx
  have hks := nks_threadSet f p σ x hx
  unfold threadSet at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨t0, ht0, rfl⟩ : ∃ t0, getTcb p σ = some t0 ∧ y = (t0, σ) := by
    unfold NonDet.getsThe NonDet.assertOpt at hy
    cases h : getTcb p σ with
    | none => rw [h] at hy; exact hy.elim
    | some t => rw [h] at hy; exact ⟨t, rfl, Set.mem_singleton_iff.1 hy⟩
  have hk0 : σ.kheap p = some (.tcb t0) := by
    unfold getTcb readObject at ht0
    cases h : σ.kheap p with
    | none => simp [h] at ht0
    | some k => cases k <;> simp_all
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨k, hk⟩ : ∃ k, σ.kheap p = some k ∧ z = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hz
    cases h : σ.kheap p with
    | none => rw [h] at hz; exact hz.elim
    | some k => rw [h] at hz; exact ⟨k, rfl, Set.mem_singleton_iff.1 hz⟩
  obtain ⟨hk, rfl⟩ := hk
  obtain ⟨u, hu, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hu
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx] at hks ⊢
  refine ⟨hks, fun o' r cs h _ => ?_, fun o' t h => ?_, rfl, rfl⟩
  · by_cases e : o' = p
    · subst e; rw [hk0] at h; cases h
    · show Function.update σ.kheap p (some (.tcb (f t0))) o' = _
      rw [Function.update_of_ne e]; exact h
  · by_cases e : o' = p
    · subst e; rw [hk0] at h; cases h
      exact ⟨f t0, by simp, hf t0⟩
    · exact ⟨t, by show Function.update σ.kheap p (some (.tcb (f t0))) o' = _; rw [Function.update_of_ne e]; exact h,
        rfl⟩

theorem nkc_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) :
    NKC (getSimpleKo (Z := Unit) f p) := by
  unfold getSimpleKo
  refine nkc_bind (nkc_getObject _) (fun _ => nkc_bind (nkc_assert _) (fun _ => ?_))
  split
  · exact nkc_pure _
  · exact nkc_fail

theorem nkc_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α)
    (hc : ∀ r cs, f e ≠ .cnode r cs) (ht : ∀ t, f e ≠ .tcb t) : NKC (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo
  exact nkc_bind (nkc_getObject _) (fun _ => nkc_bind (nkc_assert _) (fun _ =>
    nkc_bind (nkc_assert _) (fun _ => nkc_setObject hc ht)))

theorem nkc_threadGet {α : Type} (f : Tcb → α) (t : ObjRef) : NKC (threadGet (Z := Unit) f t) := by
  unfold threadGet; exact nkc_bind (nkc_getsThe _) (fun _ => nkc_pure _)

theorem nkc_getSchedContext (p : ObjRef) : NKC (getSchedContext (Z := Unit) p) := by
  unfold getSchedContext
  refine nkc_bind (nkc_getObject _) (fun o => ?_)
  cases o <;> first | exact nkc_pure _ | exact nkc_fail

theorem nkc_updateSchedContext (p : ObjRef) (f : SchedContext → SchedContext) :
    NKC (updateSchedContext (Z := Unit) p f) := by
  unfold updateSchedContext
  refine nkc_bind (nkc_getObject _) (fun o => ?_)
  cases o <;> first | exact nkc_setObject (fun _ _ h => by cases h) (fun _ h => by cases h) | exact nkc_fail


theorem nkc_setSchedulerAction (a : SchedulerAction) : NKC (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; exact nkc_modify (fun σ => ⟨rfl, rfl, rfl⟩)

macro "nkc_step" : tactic => `(tactic| first
  | exact nkc_pure _ | exact nkc_pure' _ | exact nkc_fail | exact nkc_gets _ | exact nkc_get
  | exact nkc_assert _ | exact nkc_assertOpt _ | exact nkc_getObject _ | exact nkc_getsThe _
  | exact nkc_modify (fun σ => ⟨rfl, rfl, rfl⟩)
  | (apply nkc_threadSet; intro _; rfl)
  | (apply nkc_setSimpleKo <;> intros <;> nofun)
  | exact nkc_getSimpleKo _ _ | exact nkc_threadGet _ _ | exact nkc_getSchedContext _
  | exact nkc_updateSchedContext _ _ | exact nkc_setSchedulerAction _
  | (apply nkc_when) | (apply nkc_unless) | (apply nkc_ite)
  | (apply nkc_maybeM; intro _)
  | (apply nkc_mapMx; intro _)
  | (apply nkc_whileLoop; intro _)
  | (apply nkc_liftM)
  | (refine nkc_bind ?_ (fun _ => ?_))
  | split)

macro "nkc_auto" : tactic => `(tactic| repeat nkc_step)

theorem nkc_setThreadState (t : ObjRef) (ts : ThreadState) : NKC (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct
  nkc_auto

theorem nkc_tcbSchedAction (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    NKC (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction getTcbQueue setTcbQueue
  nkc_auto

theorem nkc_rescheduleRequired : NKC (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired getScRefillSufficient getScRefillReady
  nkc_auto
  all_goals first | exact nkc_tcbSchedAction _ _ | skip

theorem nkc_possibleSwitchTo (t : ObjRef) : NKC (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo getTcbObjRef
  nkc_auto
  all_goals first | exact nkc_tcbSchedAction _ _ | exact nkc_rescheduleRequired | skip


theorem nkc_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (p : ObjRef) :
    NKC (getSkObjRef (Z := Unit) C f p) := by
  unfold getSkObjRef; nkc_auto

theorem nkc_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (p : ObjRef) (new : Option ObjRef)
    (hc : ∀ a r cs, C a ≠ .cnode r cs) (ht : ∀ a t, C a ≠ .tcb t) :
    NKC (updateSkObjRef (Z := Unit) C f p new) := by
  unfold updateSkObjRef
  exact nkc_bind (nkc_getSimpleKo _ _) (fun _ => nkc_setSimpleKo _ _ _ (hc _) (ht _))

theorem nkc_refillUnblockCheck (p : ObjRef) : NKC (refillUnblockCheck (Z := Unit) p) := by
  unfold refillUnblockCheck isRoundRobin getScRefillReady refillHeadOverlappingLoop mergeOverlappingRefills
    refillPopHead getRefillHead updateRefillHd
  nkc_auto

theorem nkc_ifCondRefillUnblockCheck (o : Option ObjRef) (a b : Option Bool) :
    NKC (ifCondRefillUnblockCheck (Z := Unit) o a b) := by
  unfold ifCondRefillUnblockCheck
  nkc_auto
  all_goals first | exact nkc_refillUnblockCheck _ | skip

macro "nkc_auto'" : tactic => `(tactic| repeat (first
  | exact nkc_setThreadState _ _ | exact nkc_tcbSchedAction _ _ | exact nkc_rescheduleRequired
  | exact nkc_possibleSwitchTo _ | exact nkc_refillUnblockCheck _ | exact nkc_ifCondRefillUnblockCheck _ _ _
  | exact nkc_getSkObjRef _ _ _
  | (apply nkc_updateSkObjRef <;> intros <;> nofun)
  | nkc_step))

/-! ## The notification branch -/

theorem nkc_cancelAllSignals (p : ObjRef) : NKC (cancelAllSignals (Z := Unit) p) := by
  unfold cancelAllSignals removeAndRestartNtfnQueuedThread tcbNtfnDequeue getTcbObjRef
  nkc_auto'

theorem nkc_unbindMaybeNotification (p : ObjRef) : NKC (unbindMaybeNotification (Z := Unit) p) := by
  unfold unbindMaybeNotification
  nkc_auto'

theorem nkc_schedContextMaybeUnbindNtfn (p : ObjRef) : NKC (schedContextMaybeUnbindNtfn (Z := Unit) p) := by
  unfold schedContextMaybeUnbindNtfn
  nkc_auto'

/-- **The spec's finalisation of a notification cap keeps the caps.** -/
theorem finNtfn_nkc (r : ObjRef) (b : Badge) (R : CapRights) (fin : Bool) :
    NKC (finaliseCap (Z := Unit) (.notificationCap r b R) fin) := by
  unfold finaliseCap
  refine nkc_liftM _ (nkc_when ?_)
  exact nkc_bind (nkc_schedContextMaybeUnbindNtfn r) (fun _ =>
    nkc_bind (nkc_unbindMaybeNotification r) (fun _ => nkc_cancelAllSignals r))


/-! ## The reply branch -/

theorem nkc_replyUnlinkTcb (t r : ObjRef) : NKC (replyUnlinkTcb (Z := Unit) t r) := by
  unfold replyUnlinkTcb getThreadState
  nkc_auto'

theorem nkc_replyUnlinkSc (sc r : ObjRef) : NKC (replyUnlinkSc (Z := Unit) sc r) := by
  unfold replyUnlinkSc
  nkc_auto'

theorem nkc_testReschedule (t : ObjRef) : NKC (testReschedule (Z := Unit) t) := by
  unfold testReschedule
  nkc_auto'

theorem nkc_tcbReleaseRemove (t : ObjRef) : NKC (tcbReleaseRemove (Z := Unit) t) := by
  unfold tcbReleaseRemove
  nkc_auto'

theorem nkc_getScObjRef (f : SchedContext → Option ObjRef) (p : ObjRef) : NKC (getScObjRef (Z := Unit) f p) := by
  unfold getScObjRef; exact nkc_bind (nkc_getSchedContext _) (fun _ => nkc_pure _)

theorem nkc_setThreadStateAct (t : ObjRef) : NKC (setThreadStateAct (Z := Unit) t) := by
  unfold setThreadStateAct; nkc_auto

theorem nkc_tcbNtfnDequeue (t n : ObjRef) : NKC (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; nkc_auto'

theorem nkc_tcbEpDequeue (t e : ObjRef) : NKC (tcbEpDequeue (Z := Unit) t e) := by
  unfold tcbEpDequeue; nkc_auto'

theorem nkc_getTcbObjRef (f : Tcb → Option ObjRef) (t : ObjRef) : NKC (getTcbObjRef (Z := Unit) f t) :=
  nkc_threadGet f t

theorem nkc_setTcbObjRef (f : (Option ObjRef → Option ObjRef) → Tcb → Tcb) (t : ObjRef) (new : Option ObjRef)
    (hf : ∀ g x, tcbCnodeMap (f g x) = tcbCnodeMap x := by intro _ _; rfl) :
    NKC (setTcbObjRef (Z := Unit) f t new) := nkc_threadSet (hf _) t

/-- Chains of binds of the lemmas above, without unfolding. -/
macro "nkc_chain" : tactic => `(tactic| repeat (first
  | with_reducible_and_instances exact nkc_setThreadState _ _ | with_reducible_and_instances exact nkc_setThreadStateAct _ | with_reducible_and_instances exact nkc_tcbSchedAction _ _
  | with_reducible_and_instances exact nkc_rescheduleRequired | with_reducible_and_instances exact nkc_possibleSwitchTo _ | with_reducible_and_instances exact nkc_replyUnlinkTcb _ _
  | with_reducible_and_instances exact nkc_replyUnlinkSc _ _ | with_reducible_and_instances exact nkc_testReschedule _ | with_reducible_and_instances exact nkc_tcbReleaseRemove _
  | with_reducible_and_instances exact nkc_getScObjRef _ _ | with_reducible_and_instances exact nkc_getTcbObjRef _ _ | with_reducible_and_instances exact nkc_getSkObjRef _ _ _ | with_reducible_and_instances exact nkc_tcbNtfnDequeue _ _
  | with_reducible_and_instances exact nkc_tcbEpDequeue _ _
  | with_reducible_and_instances exact nkc_getSchedContext _ | with_reducible_and_instances exact nkc_updateSchedContext _ _ | with_reducible_and_instances exact nkc_threadGet _ _
  | with_reducible_and_instances exact nkc_getSimpleKo _ _ | with_reducible_and_instances exact nkc_assert _ | with_reducible_and_instances exact nkc_assertOpt _ | with_reducible_and_instances exact nkc_gets _
  | with_reducible_and_instances exact nkc_pure _ | with_reducible_and_instances exact nkc_pure' _
  | with_reducible_and_instances exact nkc_setTcbObjRef _ _ _
  | exact nkc_threadSet (by intro _; rfl) _
  | with_reducible_and_instances exact nkc_updateSkObjRef _ _ _ _ (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
  | (with_reducible_and_instances apply nkc_liftM) | (with_reducible_and_instances apply nkc_when)
  | (with_reducible_and_instances refine nkc_bind ?_ (fun _ => ?_))))

theorem nkc_schedContextDonate (sc t : ObjRef) : NKC (schedContextDonate (Z := Unit) sc t) := by
  unfold schedContextDonate
  nkc_chain

theorem nkc_replyRemove (t r : ObjRef) : NKC (replyRemove (Z := Unit) t r) := by
  unfold replyRemove
  refine nkc_bind (nkc_getSimpleKo _ _) (fun _ => nkc_bind (nkc_assert _) (fun _ =>
    nkc_bind (nkc_gets _) (fun o => ?_)))
  cases o with
  | none => exact nkc_replyUnlinkTcb _ _
  | some sc =>
    dsimp only
    nkc_chain
    all_goals first | exact nkc_schedContextDonate _ _ | exact nkc_replyUnlinkTcb _ _

theorem nkc_replyRemoveTcb (t r : ObjRef) : NKC (replyRemoveTcb (Z := Unit) t r) := by
  unfold replyRemoveTcb
  refine nkc_bind (nkc_threadGet _ _) (fun _ => nkc_bind (nkc_assert _) (fun _ =>
    nkc_bind (nkc_gets _) (fun o => ?_)))
  cases o with
  | none => exact nkc_replyUnlinkTcb _ _
  | some sc =>
    dsimp only
    nkc_chain

theorem nkc_cancelIpc (t : ObjRef) : NKC (cancelIpc (Z := Unit) t) := by
  unfold cancelIpc
  refine nkc_bind (nkc_threadGet _ _) (fun st => nkc_bind (nkc_threadSet (by intro _; rfl) _) (fun _ => ?_))
  split
  · unfold blockedCancelIpc getBlockingObject; dsimp only; nkc_chain
  · unfold blockedCancelIpc getBlockingObject
    refine nkc_bind (nkc_assertOpt _) (fun _ => nkc_bind (nkc_tcbEpDequeue _ _) (fun _ => ?_))
    split <;> dsimp only <;> nkc_chain
  · unfold cancelSignal; nkc_chain
  · exact nkc_replyRemoveTcb _ _
  · exact nkc_pure _

/-- **The spec's finalisation of a reply cap keeps the caps.** -/
theorem finReply_nkc (r : ObjRef) (R : CapRights) (fin : Bool) :
    NKC (finaliseCap (Z := Unit) (.replyCap r R) fin) := by
  unfold finaliseCap
  refine nkc_liftM _ (nkc_when (nkc_bind (nkc_liftM _ (nkc_getSimpleKo _ _)) (fun o => ?_)))
  cases o with
  | none => exact nkc_pure _
  | some tp =>
    dsimp only
    refine nkc_bind (nkc_threadGet _ _) (fun st => ?_)
    split
    · exact nkc_replyRemove _ _
    · exact nkc_cancelIpc _

end

end Fl4Proofs.P3
