/-
P3 (DESIGN.md §9): **determinism of spec computations** (`Det`): at every
state, at most one outcome. The combinators (`det_bind`, `det_when`,
`det_maybeM`, `det_mapMx`, `det_whileLoop`, …) and the `det` tactic, then
the spec functions of a notification cap's `cap_delete_one`
(`det_capDeleteOne_ntfn`): its `fast_finalise` (`cancel_all_signals`,
`unbind_maybe_notification`, `sched_context_maybe_unbind_ntfn`) and
`empty_slot`. Used to turn an outcome chosen by one proof into the outcome
another proof is handed (`Det.eq`).
-/
import Fl4Proofs.P3.XTopPostDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Det
open Fl4Spec

/-- At every state, at most one outcome (a structure, so that `intro` does
not unfold it). -/
structure Det {σ α : Type} (m : NonDet σ α) : Prop where
  det : ∀ s x y, x ∈ (m s).1 → y ∈ (m s).1 → x = y

/-- At the state `s`, at most one outcome. -/
def DetAt {σ α : Type} (m : NonDet σ α) (s : σ) : Prop := ∀ x y, x ∈ (m s).1 → y ∈ (m s).1 → x = y

section
variable {σ α β : Type}

theorem Det.at {m : NonDet σ α} (h : Det m) (s : σ) : DetAt m s := h.det s

theorem det_pure (a : α) : Det (NonDet.pure a : NonDet σ α) := by
  constructor; intro s x y hx hy; rw [Set.mem_singleton_iff.1 hx, Set.mem_singleton_iff.1 hy]

theorem det_pure' (a : α) : Det (pure a : NonDet σ α) := det_pure a

theorem det_get : Det (NonDet.get : NonDet σ σ) := by
  constructor; intro s x y hx hy; rw [Set.mem_singleton_iff.1 hx, Set.mem_singleton_iff.1 hy]

theorem det_put (t : σ) : Det (NonDet.put t : NonDet σ Unit) := by
  constructor; intro s x y hx hy; rw [Set.mem_singleton_iff.1 hx, Set.mem_singleton_iff.1 hy]

theorem det_gets (f : σ → α) : Det (NonDet.gets f : NonDet σ α) := by
  constructor; intro s x y hx hy; rw [Set.mem_singleton_iff.1 hx, Set.mem_singleton_iff.1 hy]

theorem det_modify (f : σ → σ) : Det (NonDet.modify f : NonDet σ Unit) := by
  constructor; intro s x y hx hy; rw [Set.mem_singleton_iff.1 hx, Set.mem_singleton_iff.1 hy]

theorem det_fail : Det (NonDet.fail : NonDet σ α) := by
  constructor; intro s x y hx; cases hx

theorem det_assert (P : Prop) : Det (NonDet.assert P : NonDet σ Unit) := by
  constructor; intro s x y hx hy; rw [hx.2, hy.2]

theorem det_assertOpt (o : Option α) : Det (NonDet.assertOpt o : NonDet σ α) := by
  cases o
  · exact det_fail
  · exact det_pure _

theorem det_getsThe (f : σ → Option α) : Det (NonDet.getsThe f : NonDet σ α) := ⟨fun s =>
  (det_assertOpt (f s)).det s⟩

theorem det_stateAssert (P : σ → Prop) : Det (NonDet.stateAssert P) := ⟨fun s => (det_assert (P s)).det s⟩

theorem det_bind {m : NonDet σ α} {f : α → NonDet σ β} (hm : Det m) (hf : ∀ a, Det (f a)) :
    Det (m >>= f) := by
  constructor
  intro s x y hx hy
  obtain ⟨u, hu, hxu⟩ := hx
  obtain ⟨v, hv, hyv⟩ := hy
  have e := hm.det s u v hu hv
  subst e
  exact (hf u.1).det u.2 x y hxu hyv

theorem det_bind' {m : NonDet σ α} {f : α → NonDet σ β} (hm : Det m) (hf : ∀ a, Det (f a)) :
    Det (NonDet.bind m f) := det_bind hm hf

theorem detAt_bind {m : NonDet σ α} {f : α → NonDet σ β} {s : σ} (hm : DetAt m s)
    (hf : ∀ u ∈ (m s).1, DetAt (f u.1) u.2) : DetAt (m >>= f) s := by
  intro x y hx hy
  obtain ⟨u, hu, hxu⟩ := hx
  obtain ⟨v, hv, hyv⟩ := hy
  have e := hm u v hu hv
  subst e
  exact hf u hu x y hxu hyv

theorem det_when (P : Prop) {_ : Decidable P} {m : NonDet σ Unit} (h : Det m) : Det (NonDet.when P m) := by
  unfold NonDet.when; split
  · exact h
  · exact det_pure _

theorem det_unless (P : Prop) {_ : Decidable P} {m : NonDet σ Unit} (h : Det m) : Det (NonDet.unless P m) := by
  unfold NonDet.unless; split
  · exact det_pure _
  · exact h

theorem det_maybeM {f : α → NonDet σ Unit} (h : ∀ a, Det (f a)) (o : Option α) : Det (NonDet.maybeM f o) := by
  cases o
  · exact det_pure _
  · exact h _

theorem det_mapMx {f : α → NonDet σ β} (h : ∀ a, Det (f a)) : ∀ l, Det (NonDet.mapMx f l)
  | [] => det_pure _
  | a :: l => det_bind' (h a) fun _ => det_mapMx h l

theorem det_liftM {f : α → β} {m : NonDet σ α} (h : Det m) : Det (NonDet.liftM f m) :=
  det_bind' h fun _ => det_pure _

theorem det_selectF {S : Set α × Prop} (h : ∀ x y, x ∈ S.1 → y ∈ S.1 → x = y) :
    Det (NonDet.selectF S : NonDet σ α) := by
  constructor
  intro s x y hx hy
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨hx1, rfl⟩ := hx
  obtain ⟨hy1, rfl⟩ := hy
  simp only at hx1 hy1
  rw [h _ _ hx1 hy1]

theorem whileResults_det {C : α → σ → Prop} {B : α → NonDet σ α} (hB : ∀ r, Det (B r)) {r : α} {s : σ}
    {x : α × σ} (hx : NonDet.WhileResults C B r s x) :
    ∀ {y}, NonDet.WhileResults C B r s y → x = y := by
  induction hx with
  | done hc =>
    intro y hy
    cases hy with
    | done _ => rfl
    | step hc' _ _ => exact absurd hc' hc
  | step hc hm _ ih =>
    intro y hy
    cases hy with
    | done hc' => exact absurd hc hc'
    | step _ hm' hy' =>
      have e := (hB _).det _ _ _ hm hm'
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ih hy'

theorem det_whileLoop {C : α → σ → Prop} {B : α → NonDet σ α} (hB : ∀ r, Det (B r)) (r : α) :
    Det (NonDet.whileLoop C B r) := by
  constructor
  intro s x y hx hy
  exact whileResults_det hB hx hy

/-- **One outcome chosen, another handed**: they agree. -/
theorem DetAt.eq {m : NonDet σ α} {s : σ} (h : DetAt m s) {x y : α × σ} (hx : x ∈ (m s).1) (hy : y ∈ (m s).1) :
    x = y := h x y hx hy

end

/-- **The `det` tactic**: the combinators, and `split` for `if` and `match`. -/
macro "det" : tactic => `(tactic| repeat' (first
  | exact det_pure _ | exact det_pure' _ | exact det_get | exact det_put _ | exact det_gets _
  | exact det_modify _ | exact det_fail | exact det_assert _ | exact det_assertOpt _ | exact det_getsThe _
  | exact det_stateAssert _
  | apply det_bind | apply det_bind' | apply det_when | apply det_unless | apply det_maybeM | apply det_mapMx
  | apply det_liftM | apply det_whileLoop
  | (intro)
  | (split)))

/-! ## The spec functions of a notification cap's `cap_delete_one` -/

section Spec

theorem det_getObject (p : ObjRef) : Det (getObject (Z := Unit) p) := det_getsThe _

theorem det_setObject (p : ObjRef) (o : KernelObject) : Det (setObject (Z := Unit) p o) := by
  unfold setObject; det
  all_goals exact det_getObject _

theorem det_threadGet {α : Type} (f : Tcb → α) (t : ObjRef) : Det (threadGet (Z := Unit) f t) := by
  unfold threadGet; det

theorem det_threadSet (f : Tcb → Tcb) (t : ObjRef) : Det (threadSet (Z := Unit) f t) := by
  unfold threadSet; det
  all_goals exact det_setObject _ _

theorem det_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) :
    Det (getSimpleKo (Z := Unit) f p) := by
  unfold getSimpleKo; det
  all_goals exact det_getObject _

theorem det_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    Det (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo; det
  all_goals first | exact det_getObject _ | exact det_setObject _ _

theorem det_getSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject) (f : α → Option ObjRef) (p : ObjRef) :
    Det (getSkObjRef (Z := Unit) C f p) := by
  unfold getSkObjRef; det
  all_goals exact det_getSimpleKo _ _

theorem det_updateSkObjRef {α : Type} [Nonempty α] (C : α → KernelObject)
    (f : (Option ObjRef → Option ObjRef) → α → α) (p : ObjRef) (n : Option ObjRef) :
    Det (updateSkObjRef (Z := Unit) C f p n) := by
  unfold updateSkObjRef; det
  all_goals first | exact det_getSimpleKo _ _ | exact det_setSimpleKo _ _ _

theorem det_getSchedContext (p : ObjRef) : Det (getSchedContext (Z := Unit) p) := by
  unfold getSchedContext; det
  all_goals exact det_getObject _

theorem det_updateSchedContext (p : ObjRef) (f : SchedContext → SchedContext) :
    Det (updateSchedContext (Z := Unit) p f) := by
  unfold updateSchedContext; det
  all_goals first | exact det_getObject _ | exact det_setObject _ _

theorem det_getScObjRef (f : SchedContext → Option ObjRef) (p : ObjRef) : Det (getScObjRef (Z := Unit) f p) := by
  unfold getScObjRef; det
  all_goals exact det_getSchedContext _

theorem det_tcbNtfnDequeue (t n : ObjRef) : Det (tcbNtfnDequeue (Z := Unit) t n) := by
  unfold tcbNtfnDequeue; det
  all_goals first | exact det_getSimpleKo _ _ | exact det_setSimpleKo _ _ _

theorem det_rescheduleRequired : Det (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired tcbSchedAction getTcbQueue setTcbQueue setSchedulerAction
    getScRefillSufficient getScRefillReady; det
  all_goals exact det_threadGet _ _

theorem det_setThreadState (t : ObjRef) (ts : ThreadState) : Det (setThreadState (Z := Unit) t ts) := by
  unfold setThreadState setThreadStateAct setSchedulerAction; det
  all_goals exact det_threadSet _ _

theorem det_possibleSwitchTo (t : ObjRef) : Det (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo getTcbObjRef tcbSchedAction getTcbQueue setTcbQueue setSchedulerAction; det
  all_goals first | exact det_threadGet _ _ | exact det_rescheduleRequired

theorem det_refillUnblockCheck (p : ObjRef) : Det (refillUnblockCheck (Z := Unit) p) := by
  unfold refillUnblockCheck isRoundRobin getScRefillReady refillHeadOverlappingLoop mergeOverlappingRefills
    refillPopHead getRefillHead updateRefillHd; det
  all_goals first | exact det_getSchedContext _ | exact det_updateSchedContext _ _

theorem det_ifCondRefillUnblockCheck (o : Option ObjRef) (ac as' : Option Bool) :
    Det (ifCondRefillUnblockCheck (Z := Unit) o ac as') := by
  unfold ifCondRefillUnblockCheck; det
  all_goals first | exact det_getSchedContext _ | exact det_refillUnblockCheck _

theorem det_removeAndRestart (t n : ObjRef) : Det (removeAndRestartNtfnQueuedThread (Z := Unit) t n) := by
  unfold removeAndRestartNtfnQueuedThread getTcbObjRef; det
  all_goals first | exact det_tcbNtfnDequeue _ _ | exact det_setThreadState _ _ | exact det_threadGet _ _ | exact det_ifCondRefillUnblockCheck _ _ _ | exact det_possibleSwitchTo _

theorem det_cancelAllSignals (n : ObjRef) : Det (cancelAllSignals (Z := Unit) n) := by
  unfold cancelAllSignals; det
  all_goals first | exact det_getSimpleKo _ _ | exact det_removeAndRestart _ _ | exact det_rescheduleRequired

theorem det_unbindMaybeNotification (n : ObjRef) : Det (unbindMaybeNotification (Z := Unit) n) := by
  unfold unbindMaybeNotification doUnbindNotification setTcbObjRef; det
  all_goals first | exact det_getSkObjRef _ _ _ | exact det_updateSkObjRef _ _ _ _ | exact det_threadSet _ _

theorem det_schedContextMaybeUnbindNtfn (n : ObjRef) : Det (schedContextMaybeUnbindNtfn (Z := Unit) n) := by
  unfold schedContextMaybeUnbindNtfn doUnbindNtfnSc setScObjRef; det
  all_goals first | exact det_getSkObjRef _ _ _ | exact det_updateSkObjRef _ _ _ _ | exact det_updateSchedContext _ _

theorem det_fastFinalise_ntfn (r : ObjRef) (b : Badge) (rs : CapRights) (fin : Bool) :
    Det (fastFinalise (Z := Unit) (.notificationCap r b rs) fin) := by
  unfold fastFinalise; det
  all_goals first | exact det_schedContextMaybeUnbindNtfn _ | exact det_unbindMaybeNotification _ | exact det_cancelAllSignals _

theorem det_getCap (sl : CslotPtr) : Det (getCap (Z := Unit) sl) := by
  obtain ⟨p, c⟩ := sl
  unfold getCap; det
  all_goals exact det_getObject _

theorem det_setCap (cap : Cap) (sl : CslotPtr) : Det (setCap (Z := Unit) cap sl) := by
  obtain ⟨p, c⟩ := sl
  unfold setCap; det
  all_goals first | exact det_getObject _ | exact det_setObject _ _

theorem det_selectF_ext (eop : DetExtMonad Unit) (ex : State Unit) :
    Det (NonDet.selectF (NonDet.mkEf (StateExt.wrapExtOp (A := Unit) eop ex)) : NonDet (State Unit) _) := by
  apply det_selectF
  intro x y hx hy
  exact (Set.mem_singleton_iff.1 hx).trans (Set.mem_singleton_iff.1 hy).symm

theorem det_doExtendedOp (eop : DetExtMonad Unit) : Det (doExtendedOp (Z := Unit) eop) := by
  unfold doExtendedOp; det
  all_goals exact det_selectF_ext _ _

theorem det_emptySlot_null (sl : CslotPtr) : Det (emptySlot (Z := Unit) sl .nullCap) := by
  unfold emptySlot setCdt setOriginal postCapDeletion; det
  all_goals first | exact det_getCap _ | exact det_setCap _ _ | exact det_doExtendedOp _ | exact det_selectF_ext _ _

theorem det_isFinalCap (c : Cap) : Det (isFinalCap (Z := Unit) c) := det_gets _

/-- **A notification cap's `cap_delete_one` has one outcome.** -/
theorem detAt_capDeleteOne_ntfn {σ : State Unit} {sl : CslotPtr} {r : ObjRef} {b : Badge} {rs : CapRights}
    (hg : getCap (Z := Unit) sl σ = ({(.notificationCap r b rs, σ)}, False)) :
    DetAt (capDeleteOne (Z := Unit) sl) σ := by
  unfold capDeleteOne
  refine detAt_bind ((det_getCap sl).at σ) fun u hu => ?_
  rw [hg] at hu
  rw [Set.mem_singleton_iff.1 hu]
  dsimp only
  refine Det.at (det_unless _ ?_) σ
  det
  all_goals first | exact det_isFinalCap _ | exact det_fastFinalise_ntfn _ _ _ _ | exact det_emptySlot_null _ | exact det_selectF_ext _ _ | exact det_getCap _ | exact det_setCap _ _ | exact det_schedContextMaybeUnbindNtfn _ | exact det_unbindMaybeNotification _ | exact det_cancelAllSignals _

end Spec

end Fl4Proofs.P3.Det
