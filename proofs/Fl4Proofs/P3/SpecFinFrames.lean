/-
P3 (DESIGN.md §9), CSpace: **the spec's finalisations of a final
endpoint, thread and scheduling-context cap keep the caps** (`NKC`,
SpecCaps): `cancel_all_ipc` (`finEp_nkc`); `unbind_notification`,
`unbind_from_sc`, `suspend` and `prepare_thread_delete` (`finThread_nkc`);
`sched_context_unbind_all_tcbs`, `_ntfn`, `_reply`, `_yield_from` and
`sched_context_set_inactive` (`finSc_nkc`).

Some of these read a TCB and write it back changed only in its arch part
(`as_user`, `set_mrs`): `NKCAt` is `NKC` from the states where the TCB is
the one read, with `nkcAt_setTcb` for the write-back.
-/
import Fl4Proofs.P3.SpecCaps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open Fl4Spec

noncomputable section

/-! ## Reads, then a write-back of the TCB read -/

/-- `NKC` from the states satisfying `I`. -/
def NKCAt {α : Type} (I : State Unit → Prop) (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, I σ → ∀ x, x ∈ (m σ).1 → CKeep σ x.2

/-- Every outcome leaves the state as it is. -/
def KeepSt {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → x.2 = σ

theorem keepSt_pure {α : Type} (a : α) : KeepSt (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]

theorem keepSt_selectF {α : Type} (S : Set α × Prop) : KeepSt (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; exact h

theorem nkcAt_of {α : Type} {I : State Unit → Prop} {m : NonDet (State Unit) α} (h : NKC m) : NKCAt I m :=
  fun σ _ x hx => h σ x hx

theorem nkcAt_bind_keep {α β : Type} {I : State Unit → Prop} {m : NonDet (State Unit) α}
    {f : α → NonDet (State Unit) β} (hm : KeepSt m) (hf : ∀ a, NKCAt I (f a)) : NKCAt I (m >>= f) := by
  intro σ hI x ⟨y, hy, hx⟩
  have e := hm σ y hy
  have := hf y.1 y.2 (by rw [e]; exact hI) x hx
  rwa [e] at this

theorem nkcAt_pure_bind {α β : Type} {I : State Unit → Prop} {a : α} {f : α → NonDet (State Unit) β}
    (hf : NKCAt I (f a)) : NKCAt I (pure a >>= f) := by
  intro σ hI x ⟨y, hy, hx⟩
  rw [Set.mem_singleton_iff.1 hy] at hx
  exact hf σ hI x hx

theorem nkcAt_bind {α β : Type} {I : State Unit → Prop} {m : NonDet (State Unit) α}
    {f : α → NonDet (State Unit) β} (hm : NKCAt I m) (hf : ∀ a, NKC (f a)) : NKCAt I (m >>= f) := by
  intro σ hI x ⟨y, hy, hx⟩
  exact (hm σ hI y hy).trans (hf y.1 y.2 x hx)

/-- Writing back a TCB with the caps of the one there. -/
theorem nkcAt_setTcb {p : ObjRef} {t0 t' : Tcb} (he : tcbCnodeMap t' = tcbCnodeMap t0) :
    NKCAt (fun σ => σ.kheap p = some (.tcb t0)) (setObject (Z := Unit) p (.tcb t')) := by
  intro σ hk0 x hx
  have hks := nks_setObject p _ σ x hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨k, hk⟩ : ∃ k, σ.kheap p = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap p with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  obtain ⟨hk, rfl⟩ := hk
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx] at hks ⊢
  refine ⟨hks, fun o' r cs h _ => ?_, fun o' t h => ?_, rfl, rfl⟩
  · by_cases e : o' = p
    · subst e; rw [hk0] at h; cases h
    · show Function.update σ.kheap p (some (.tcb t')) o' = _
      rw [Function.update_of_ne e]; exact h
  · by_cases e : o' = p
    · subst e; rw [hk0] at h; cases h
      exact ⟨t', by simp, he⟩
    · exact ⟨t, by show Function.update σ.kheap p (some (.tcb t')) o' = _; rw [Function.update_of_ne e]; exact h, rfl⟩

/-- Reading a TCB, then what follows from the states where it is the one
read. -/
theorem nkc_getTcb_bind {β : Type} (p : ObjRef) {g : Tcb → NonDet (State Unit) β}
    (hg : ∀ t0, NKCAt (fun σ => σ.kheap p = some (.tcb t0)) (g t0)) :
    NKC (NonDet.getsThe (getTcb (Z := Unit) p) >>= g) := by
  intro σ x ⟨y, hy, hx⟩
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
  exact hg t0 σ hk0 x hx

theorem nkc_asUser {α : Type} (p : ObjRef) (f : UserMonad α) : NKC (asUser (Z := Unit) p f) := by
  unfold asUser
  refine nkc_getTcb_bind p (fun t0 => nkcAt_pure_bind (nkcAt_bind_keep (keepSt_selectF _) (fun r => ?_)))
  obtain ⟨a, uc'⟩ := r
  exact nkcAt_pure_bind (nkcAt_bind (nkcAt_setTcb rfl) (fun _ => nkc_pure _))

theorem nkc_doMachineOp {α : Type} (mop : NonDet MachineState α) : NKC (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine nkc_bind (nkc_gets _) (fun _ => nkc_bind ?_ (fun x => ?_))
  · intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact CKeep.refl σ
  · obtain ⟨r, ms⟩ := x
    exact nkc_bind (nkc_modify (fun σ => ⟨rfl, rfl, rfl⟩)) (fun _ => nkc_pure _)

theorem nkc_zipWithMx {α β γ : Type} {f : α → β → NonDet (State Unit) γ} (hf : ∀ a b, NKC (f a b)) :
    ∀ l1 l2, NKC (NonDet.zipWithMx f l1 l2)
  | a :: l1, b :: l2 => nkc_bind (hf a b) (fun _ => nkc_zipWithMx hf l1 l2)
  | [], _ => nkc_pure' _
  | _ :: _, [] => nkc_pure' _

theorem nkc_storeWordOffs (p : ObjRef) (o : Nat) (v : Word) : NKC (storeWordOffs (Z := Unit) p o v) := by
  unfold storeWordOffs
  exact nkc_bind nkc_get (fun _ => nkc_bind (nkc_assert _) (fun _ => nkc_doMachineOp _))

theorem nkc_getCap (sl : CslotPtr) : NKC (getCap (Z := Unit) sl) := by
  obtain ⟨o, c⟩ := sl
  unfold getCap
  refine nkc_bind (nkc_getObject o) (fun obj => ?_)
  cases obj <;> simp only [] <;> nkc_auto

theorem nkc_lookupIpcBuffer (b : Bool) (t : ObjRef) : NKC (lookupIpcBuffer (Z := Unit) b t) := by
  unfold lookupIpcBuffer
  refine nkc_bind (nkc_threadGet _ _) (fun _ => nkc_bind (nkc_pure _) (fun _ => nkc_bind (nkc_getCap _) (fun c => ?_)))
  split
  · split <;> exact nkc_pure _
  · exact nkc_pure _

theorem nkc_setMrs (t : ObjRef) (buf : Option ObjRef) (msgs : List Message) :
    NKC (setMrs (Z := Unit) t buf msgs) := by
  unfold setMrs
  refine nkc_getTcb_bind t (fun t0 => nkcAt_pure_bind (nkcAt_pure_bind (nkcAt_bind (nkcAt_setTcb rfl) (fun _ => ?_))))
  refine nkc_bind (nkc_pure _) (fun _ => ?_)
  split
  · exact nkc_pure _
  · exact nkc_bind (nkc_zipWithMx (fun _ _ => nkc_storeWordOffs _ _ _) _ _) (fun _ => nkc_pure _)

theorem nkc_replyFromKernel (t : ObjRef) (x : Data × List Data) : NKC (replyFromKernel (Z := Unit) t x) := by
  unfold replyFromKernel setMessageInfo
  refine nkc_bind (nkc_pure _) (fun lm => ?_)
  obtain ⟨l, m⟩ := lm
  exact nkc_bind (nkc_lookupIpcBuffer _ _) (fun _ => nkc_bind (nkc_asUser _ _) (fun _ =>
    nkc_bind (nkc_setMrs _ _ _) (fun _ => nkc_asUser _ _)))

theorem nkc_archThreadSet (f : ArchTcb → ArchTcb) (t : ObjRef) : NKC (archThreadSet (Z := Unit) f t) := by
  unfold archThreadSet
  exact nkc_threadSet (f := fun tcb => { tcb with tcbArch := f tcb.tcbArch }) (by intro _; rfl) t

/-! ## The endpoint branch -/

theorem nkc_restartThreadIfNoFault (t : ObjRef) : NKC (restartThreadIfNoFault (Z := Unit) t) := by
  unfold restartThreadIfNoFault
  refine nkc_bind (nkc_threadGet _ _) (fun _ => nkc_ite _ ?_ (nkc_setThreadState _ _))
  exact nkc_bind (nkc_setThreadState _ _) (fun _ => nkc_bind (nkc_getTcbObjRef _ _) (fun _ =>
    nkc_bind (nkc_ifCondRefillUnblockCheck _ _ _) (fun _ => nkc_possibleSwitchTo _)))

theorem nkc_cancelAllIpc (e : ObjRef) : NKC (cancelAllIpc (Z := Unit) e) := by
  unfold cancelAllIpc
  refine nkc_bind (nkc_getSimpleKo _ _) (fun ep => ?_)
  split
  · exact nkc_pure _
  · refine nkc_bind (nkc_pure _) (fun q => nkc_bind (nkc_mapMx (fun t => ?_) _) (fun _ => nkc_rescheduleRequired))
    unfold removeAndRestartEpQueuedThread
    exact nkc_bind (nkc_tcbEpDequeue _ _) (fun _ => nkc_bind (nkc_threadGet _ _) (fun _ =>
      nkc_bind (nkc_pure _) (fun _ => nkc_bind (nkc_maybeM (fun _ => nkc_replyUnlinkTcb _ _) _) (fun _ =>
        nkc_restartThreadIfNoFault _))))

/-- **The spec's finalisation of an endpoint cap keeps the caps.** -/
theorem finEp_nkc (r : ObjRef) (b : Badge) (R : CapRights) (fin : Bool) :
    NKC (finaliseCap (Z := Unit) (.endpointCap r b R) fin) := by
  unfold finaliseCap
  exact nkc_liftM _ (nkc_when (nkc_cancelAllIpc r))

/-! ## The thread branch -/

theorem nkc_schedContextUnbindTcb (sc : ObjRef) : NKC (schedContextUnbindTcb (Z := Unit) sc) := by
  unfold schedContextUnbindTcb
  exact nkc_bind (nkc_getSchedContext _) (fun _ => nkc_bind (nkc_assertOpt _) (fun _ => nkc_bind (nkc_gets _)
    (fun _ => nkc_bind (nkc_when nkc_rescheduleRequired) (fun _ => nkc_bind (nkc_tcbSchedAction _ _) (fun _ =>
      nkc_bind (nkc_tcbReleaseRemove _) (fun _ => nkc_bind (nkc_setTcbObjRef _ _ _) (fun _ =>
        nkc_updateSchedContext _ _)))))))

theorem nkc_schedContextCancelYieldTo (t : ObjRef) : NKC (schedContextCancelYieldTo (Z := Unit) t) := by
  unfold schedContextCancelYieldTo
  exact nkc_bind (nkc_getTcbObjRef _ _) (fun _ => nkc_maybeM (fun _ =>
    nkc_bind (nkc_updateSchedContext _ _) (fun _ => nkc_setTcbObjRef _ _ _)) _)

theorem nkc_schedContextUpdateConsumed (sc : ObjRef) : NKC (schedContextUpdateConsumed (Z := Unit) sc) := by
  unfold schedContextUpdateConsumed
  refine nkc_bind (nkc_getSchedContext _) (fun _ => nkc_bind (nkc_pure _) (fun _ => ?_))
  exact nkc_ite _ (nkc_bind (nkc_updateSchedContext _ _) (fun _ => nkc_pure _))
    (nkc_bind (nkc_updateSchedContext _ _) (fun _ => nkc_pure _))

theorem nkc_completeYieldTo (t : ObjRef) : NKC (completeYieldTo (Z := Unit) t) := by
  unfold completeYieldTo setConsumed
  exact nkc_bind (nkc_getTcbObjRef _ _) (fun _ => nkc_maybeM (fun _ =>
    nkc_bind (nkc_bind (nkc_schedContextUpdateConsumed _) (fun _ => nkc_replyFromKernel _ _)) (fun _ =>
      nkc_schedContextCancelYieldTo _)) _)

theorem nkc_unbindNotification (t : ObjRef) : NKC (unbindNotification (Z := Unit) t) := by
  unfold unbindNotification
  refine nkc_bind (nkc_getTcbObjRef _ _) (fun _ => nkc_maybeM (fun _ => ?_) _)
  exact nkc_bind (nkc_updateSkObjRef _ _ _ _ (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)) (fun _ =>
    nkc_setTcbObjRef _ _ _)

theorem nkc_unbindFromSc (t : ObjRef) : NKC (unbindFromSc (Z := Unit) t) := by
  unfold unbindFromSc
  exact nkc_bind (nkc_getTcbObjRef _ _) (fun _ => nkc_bind (nkc_maybeM nkc_schedContextUnbindTcb _) (fun _ =>
    nkc_maybeM (fun _ => nkc_bind (nkc_getSchedContext _) (fun _ => nkc_maybeM nkc_completeYieldTo _)) _))

theorem nkc_suspend (t : ObjRef) : NKC (suspend (Z := Unit) t) := by
  unfold suspend updateRestartPc
  exact nkc_bind (nkc_cancelIpc _) (fun _ => nkc_bind (nkc_threadGet _ _) (fun _ =>
    nkc_bind (nkc_when (nkc_asUser _ _)) (fun _ => nkc_bind (nkc_tcbSchedAction _ _) (fun _ =>
      nkc_bind (nkc_tcbReleaseRemove _) (fun _ => nkc_bind (nkc_schedContextCancelYieldTo _) (fun _ =>
        nkc_setThreadState _ _))))))

theorem nkc_setX64CurrentFpuOwner (o : Option ObjRef) : NKC (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner
  exact nkc_bind (nkc_gets _) (fun _ => nkc_bind (nkc_maybeM (fun _ => nkc_archThreadSet _ _) _) (fun _ =>
    nkc_bind (nkc_modify (fun σ => ⟨rfl, rfl, rfl⟩)) (fun _ => nkc_maybeM (fun _ => nkc_archThreadSet _ _) _)))

theorem nkc_prepareThreadDelete (t : ObjRef) : NKC (prepareThreadDelete (Z := Unit) t) := by
  unfold prepareThreadDelete fpuRelease switchLocalFpuOwner saveFpuState loadFpuState
  refine nkc_bind (nkc_gets _) (fun _ => nkc_when ?_)
  refine nkc_bind (nkc_gets _) (fun _ => nkc_bind (nkc_doMachineOp _) (fun _ =>
    nkc_bind (nkc_maybeM (fun _ => nkc_bind (nkc_doMachineOp _) (fun _ => nkc_asUser _ _)) _) (fun _ =>
      nkc_bind ?_ (fun _ => nkc_setX64CurrentFpuOwner _))))
  exact nkc_doMachineOp _

/-- **The spec's finalisation of a thread cap keeps the caps.** -/
theorem finThread_nkc (r : ObjRef) (fin : Bool) : NKC (finaliseCap (Z := Unit) (.threadCap r) fin) := by
  unfold finaliseCap
  exact nkc_bind (nkc_when (nkc_unbindNotification r)) (fun _ => nkc_bind (nkc_when (nkc_unbindFromSc r))
    (fun _ => nkc_bind (nkc_when (nkc_suspend r)) (fun _ => nkc_bind (nkc_when (nkc_prepareThreadDelete r))
      (fun _ => nkc_pure _))))

/-! ## The scheduling-context branch -/

theorem nkc_schedContextUnbindAllTcbs (sc : ObjRef) : NKC (schedContextUnbindAllTcbs (Z := Unit) sc) := by
  unfold schedContextUnbindAllTcbs
  exact nkc_bind (nkc_getSchedContext _) (fun _ => nkc_when (nkc_schedContextUnbindTcb _))

theorem nkc_schedContextUnbindNtfn (sc : ObjRef) : NKC (schedContextUnbindNtfn (Z := Unit) sc) := by
  unfold schedContextUnbindNtfn
  exact nkc_bind (nkc_getScObjRef _ _) (fun _ => nkc_maybeM (fun _ =>
    nkc_bind (nkc_updateSkObjRef _ _ _ _ (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)) (fun _ =>
      nkc_updateSchedContext _ _)) _)

theorem nkc_schedContextUnbindReply (sc : ObjRef) : NKC (schedContextUnbindReply (Z := Unit) sc) := by
  unfold schedContextUnbindReply
  exact nkc_bind (nkc_liftM _ (nkc_getSchedContext _)) (fun _ => nkc_unless (nkc_bind
    (nkc_updateSkObjRef _ _ _ _ (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)) (fun _ =>
      nkc_updateSchedContext _ _)))

theorem nkc_schedContextUnbindYieldFrom (sc : ObjRef) : NKC (schedContextUnbindYieldFrom (Z := Unit) sc) := by
  unfold schedContextUnbindYieldFrom
  exact nkc_bind (nkc_getSchedContext _) (fun _ => nkc_maybeM nkc_completeYieldTo _)

theorem nkc_schedContextSetInactive (sc : ObjRef) : NKC (schedContextSetInactive (Z := Unit) sc) := by
  unfold schedContextSetInactive
  exact nkc_bind (nkc_updateSchedContext _ _) (fun _ => nkc_bind (nkc_updateSchedContext _ _) (fun _ =>
    nkc_bind (nkc_updateSchedContext _ _) (fun _ => nkc_updateSchedContext _ _)))

/-- **The spec's finalisation of a scheduling-context cap keeps the caps.** -/
theorem finSc_nkc (p : ObjRef) (n : Nat) (fin : Bool) :
    NKC (finaliseCap (Z := Unit) (.schedContextCap p n) fin) := by
  unfold finaliseCap
  exact nkc_bind (nkc_when (nkc_schedContextUnbindAllTcbs p)) (fun _ =>
    nkc_bind (nkc_when (nkc_schedContextUnbindNtfn p)) (fun _ =>
      nkc_bind (nkc_when (nkc_schedContextUnbindReply p)) (fun _ =>
        nkc_bind (nkc_when (nkc_schedContextUnbindYieldFrom p)) (fun _ =>
          nkc_bind (nkc_when (nkc_schedContextSetInactive p)) (fun _ => nkc_pure _)))))

end

end Fl4Proofs.P3
