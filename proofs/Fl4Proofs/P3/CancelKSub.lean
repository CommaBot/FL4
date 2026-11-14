/-
P3 (DESIGN.md §9), CSpace: the spec's `cancel_badged_sends` creates no
CNode or TCB (`cancelBadgedSends_nks`): it only rewrites endpoints, TCBs,
scheduling contexts and the scheduler's state. This discharges the `KSub`
part of `CancelEpHyp`.
-/
import Fl4Proofs.P3.FinSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open Fl4Spec

noncomputable section

theorem nks_when {P : Prop} {inst : Decidable P} {m : NonDet (State Unit) Unit} (h : NKS m) :
    NKS (@NonDet.when _ P inst m) := by
  unfold NonDet.when; split; exact h; exact nks_pure' _

theorem nks_maybeM {α : Type} {f : α → NonDet (State Unit) Unit} (h : ∀ a, NKS (f a)) :
    ∀ o, NKS (NonDet.maybeM f o)
  | none => nks_pure' _
  | some a => h a

theorem nks_mapMx {α β : Type} {f : α → NonDet (State Unit) β} (hf : ∀ a, NKS (f a)) :
    ∀ l, NKS (NonDet.mapMx f l)
  | [] => nks_pure' _
  | a :: l => nks_bind (hf a) (fun _ => nks_mapMx hf l)

theorem nks_whileLoop {α : Type} {C : α → State Unit → Prop} {B : α → NonDet (State Unit) α}
    (hB : ∀ r, NKS (B r)) (r : α) : NKS (NonDet.whileLoop C B r) := by
  intro σ x hx
  change NonDet.WhileResults C B r σ x at hx
  induction hx with
  | done _ => exact KSub.refl _
  | step _ hb _ ih => exact (hB _ _ _ hb).trans ih

theorem nks_threadGet {α : Type} (f : Tcb → α) (t : ObjRef) : NKS (threadGet (Z := Unit) f t) := by
  unfold threadGet; exact nks_bind (nks_getsThe _) (fun _ => nks_pure _)

theorem nks_threadSet (f : Tcb → Tcb) (t : ObjRef) : NKS (threadSet (Z := Unit) f t) := by
  unfold threadSet; exact nks_bind (nks_getsThe _) (fun _ => nks_setObject _ _)

theorem nks_getSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) :
    NKS (getSimpleKo (Z := Unit) f p) := by
  unfold getSimpleKo
  refine nks_bind (nks_getObject _) (fun _ => nks_bind (nks_assert _) (fun _ => ?_))
  split
  · exact nks_pure _
  · exact nks_fail

theorem nks_setSimpleKo {α : Type} [Nonempty α] (f : α → KernelObject) (p : ObjRef) (e : α) :
    NKS (setSimpleKo (Z := Unit) f p e) := by
  unfold setSimpleKo
  exact nks_bind (nks_getObject _) (fun _ => nks_bind (nks_assert _) (fun _ =>
    nks_bind (nks_assert _) (fun _ => nks_setObject _ _)))

theorem nks_getSchedContext (p : ObjRef) : NKS (getSchedContext (Z := Unit) p) := by
  unfold getSchedContext
  refine nks_bind (nks_getObject _) (fun o => ?_)
  cases o <;> first | exact nks_pure _ | exact nks_fail

theorem nks_updateSchedContext (p : ObjRef) (f : SchedContext → SchedContext) :
    NKS (updateSchedContext (Z := Unit) p f) := by
  unfold updateSchedContext
  refine nks_bind (nks_getObject _) (fun o => ?_)
  cases o <;> first | exact nks_setObject _ _ | exact nks_fail

theorem nks_updateRefillHd (p : ObjRef) (f : Refill → Refill) : NKS (updateRefillHd (Z := Unit) p f) :=
  nks_updateSchedContext _ _

theorem nks_refillUnblockCheck (p : ObjRef) : NKS (refillUnblockCheck (Z := Unit) p) := by
  unfold refillUnblockCheck isRoundRobin getScRefillReady
  refine nks_bind (nks_bind (nks_getSchedContext _) (fun _ => nks_pure _)) (fun _ =>
    nks_bind (nks_getsThe _) (fun _ => nks_when ?_))
  refine nks_bind (nks_gets _) (fun _ => nks_bind (nks_updateRefillHd _ _) (fun _ =>
    nks_bind (nks_modify (fun σ => rfl)) (fun _ => ?_)))
  unfold refillHeadOverlappingLoop
  refine nks_whileLoop (fun _ => ?_) _
  unfold mergeOverlappingRefills refillPopHead getRefillHead
  exact nks_bind (nks_bind (nks_getsThe _) (fun _ => nks_bind (nks_updateSchedContext _ _) (fun _ => nks_pure _)))
    (fun _ => nks_updateRefillHd _ _)

theorem nks_tcbSchedAction (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    NKS (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction getTcbQueue setTcbQueue
  exact nks_bind (nks_threadGet _ _) (fun _ => nks_bind (nks_threadGet _ _) (fun _ =>
    nks_bind (nks_bind (nks_gets _) (fun _ => nks_pure _)) (fun _ => nks_bind (nks_pure _) (fun _ =>
      nks_modify (fun σ => rfl)))))

theorem nks_setSchedulerAction (a : SchedulerAction) : NKS (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; exact nks_modify (fun σ => rfl)

theorem nks_rescheduleRequired : NKS (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired getScRefillSufficient getScRefillReady
  refine nks_bind (nks_gets _) (fun act => ?_)
  dsimp only
  split
  · refine nks_bind (nks_gets _) (fun _ => nks_bind (nks_when ?_) (fun _ => nks_setSchedulerAction _))
    exact nks_bind (nks_threadGet _ _) (fun _ => nks_bind (nks_assertOpt _) (fun _ =>
      nks_bind (nks_getsThe _) (fun _ => nks_bind (nks_getsThe _) (fun _ =>
        nks_bind (nks_assert _) (fun _ => nks_tcbSchedAction _ _)))))
  · first | exact nks_setSchedulerAction _ | exact nks_bind (nks_pure _) (fun _ => nks_setSchedulerAction _)

theorem nks_possibleSwitchTo (t : ObjRef) : NKS (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo getTcbObjRef
  refine nks_bind (nks_threadGet _ _) (fun _ => nks_bind (nks_gets _) (fun _ => nks_when ?_))
  refine nks_bind (nks_gets _) (fun _ => nks_bind (nks_threadGet _ _) (fun _ => nks_bind (nks_gets _) (fun _ => ?_)))
  split
  · exact nks_tcbSchedAction _ _
  · split
    · exact nks_bind nks_rescheduleRequired (fun _ => nks_tcbSchedAction _ _)
    · exact nks_setSchedulerAction _

theorem nks_restartThreadIfNoFault (t : ObjRef) : NKS (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault getTcbObjRef ifSporadicCurScAssertRefillUnblockCheck ifCondRefillUnblockCheck
  refine nks_bind (nks_threadGet _ _) (fun _ => ?_)
  split
  · refine nks_bind (setThreadState_nks _ _) (fun _ => nks_bind (nks_threadGet _ _) (fun _ =>
      nks_bind (nks_maybeM (fun _ => ?_) _) (fun _ => nks_possibleSwitchTo _)))
    exact nks_bind (nks_getSchedContext _) (fun _ => nks_bind (nks_gets _) (fun _ => nks_bind (nks_pure _)
      (fun _ => nks_when (nks_when (nks_refillUnblockCheck _)))))
  · exact setThreadState_nks _ _

theorem cancelBadgedSends_nks (p : ObjRef) (b : Badge) : NKS (cancelBadgedSends (Z := Unit) p b) := by
  unfold cancelBadgedSends
  refine nks_bind (nks_getSimpleKo _ _) (fun ep => ?_)
  split
  · refine nks_bind (nks_mapMx (fun t => ?_) _) (fun _ => nks_rescheduleRequired)
    unfold removeAndRestartBadgedThread getThreadState
    refine nks_bind (nks_threadGet _ _) (fun _ => nks_when ?_)
    unfold tcbEpDequeue
    exact nks_bind (nks_bind (nks_getSimpleKo _ _) (fun _ => nks_bind (nks_pure _) (fun _ =>
      nks_bind (nks_assert _) (fun _ => nks_bind (nks_pure _) (fun _ => nks_bind (nks_pure _) (fun _ =>
        nks_setSimpleKo _ _ _)))))) (fun _ => nks_restartThreadIfNoFault _)
  · exact nks_pure _

end

end Fl4Proofs.P3
