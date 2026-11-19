/-
P3 (DESIGN.md §9), TCB invocations: **the scheduler invariant `Inv` across
`set_priority` and `suspend`** (spec side only), for the TCB invocations'
`JAtZ` leaves (IpcSchedTailJ's SetSchedParams tail, IpcCopyRegsJ's
CopyRegisters suspend).

* `Inv.ikKeep`: `Inv` across an `IK t` step keeping `t`'s state.
* `setPriority_inv`: `Inv` after `set_priority` of a thread that is not the
  current thread (a runnable queued thread is requeued with its facts; a
  runnable unqueued one only gets its priority; a blocked one is an `IK`
  step: its priority, the endpoint or notification queue reordered).
* `setPriority_objCover`, `setPriority_nsc`: the objects' kinds and the
  notifications' SCs kept.
-/
import Fl4Proofs.P3.ScRestartSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical Fl4Proofs.P3.Notif

noncomputable section

section Spec

/-- **`Inv` across an `IK t` step that keeps `t`'s state too.** -/
theorem Inv.ikKeep {t : ObjRef} {σ σ' : State Unit} (h : Inv σ) (hk : IK t σ σ')
    (hst : ∀ x x', σ.kheap t = some (.tcb x) → σ'.kheap t = some (.tcb x') → x'.tcbState = x.tcbState)
    (hsf : ∀ x x', σ.kheap t = some (.tcb x) → σ'.kheap t = some (.tcb x') →
      (∃ e d, x.tcbState = .blockedOnSend e d) → x'.tcbFault = x.tcbFault) :
    Inv σ' := by
  have tF : ∀ {p : ObjRef} {x : Tcb}, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧
      y.tcbSchedContext = x.tcbSchedContext ∧ y.tcbState = x.tcbState := by
    intro p x hx
    obtain ⟨y, hy, e1, e2⟩ := hk.tcbF hx
    by_cases e : p = t
    · subst e; exact ⟨y, hy, e1, hst x y hx hy⟩
    · exact ⟨y, hy, e1, e2 e⟩
  have tB : ∀ {p : ObjRef} {y : Tcb}, σ'.kheap p = some (.tcb y) → ∃ x, σ.kheap p = some (.tcb x) ∧
      y.tcbSchedContext = x.tcbSchedContext ∧ y.tcbState = x.tcbState := by
    intro p y hy
    obtain ⟨x, hx, e1, e2⟩ := hk.tcbB hy
    by_cases e : p = t
    · subst e; exact ⟨x, hx, e1, hst x y hx hy⟩
    · exact ⟨x, hx, e1, e2 e⟩
  have hrq := hk.2.1
  have hrl := hk.2.2.1
  have htm := hk.2.2.2
  have qd : ∀ u x scp y n, σ.kheap u = some (.tcb x) → x.tcbSchedContext = some scp →
      runnable x.tcbState = true → σ.kheap scp = some (.schedContext y n) → scActive y = true →
      ∃ x scp y n, σ'.kheap u = some (.tcb x) ∧ x.tcbSchedContext = some scp ∧
        runnable x.tcbState = true ∧ σ'.kheap scp = some (.schedContext y n) ∧ scActive y = true := by
    intro u x scp y n h1 h2 h3 h4 h5
    obtain ⟨x', k1, e1, f1⟩ := tF h1
    obtain ⟨y', k2, e2⟩ := hk.scF h4
    exact ⟨x', scp, y', n, k1, by rw [e1]; exact h2, by rw [f1]; exact h3, k2, by rw [e2.active]; exact h5⟩
  refine ⟨fun d p u hu => ?_, fun u hu => ?_, ?_, fun u x hx hc => ?_, fun p y n hy => ?_,
    fun u x p hx hp => ?_, fun q x p hx hp => ?_, fun p y n hy => ?_, fun p y n hy => ?_⟩
  · rw [hrq] at hu
    obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5⟩ := h.rq d p u hu
    exact qd u x scp y n h1 h2 h3 h4 h5
  · rw [hrl] at hu
    obtain ⟨x, scp, y, n, h1, h2, h3, h4, h5⟩ := h.rel u hu
    exact qd u x scp y n h1 h2 h3 h4 h5
  · rw [hrl]
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    have rt : ∀ u ∈ σ.releaseQueue, specRt σ' u = specRt σ u := by
      intro u hu
      obtain ⟨x, scp, y, n, h1, h2, -, h4, h5⟩ := h.rel u hu
      obtain ⟨x', k1, e1, -⟩ := tF h1
      obtain ⟨y', k2, e2⟩ := hk.scF h4
      have hne := h.ne _ _ _ h4 h5
      rw [specRt_eq k1 (by rw [e1]; exact h2) k2 (by rw [e2.1]; exact hne), specRt_eq h1 h2 h4 hne, e2.hd]
    rw [rt a ha, rt b hb]; exact hab
  · obtain ⟨x0, k0, e0, f0⟩ := tB hx
    have g0 : (∃ e d, x0.tcbState = .blockedOnSend e d) → x.tcbFault = x0.tcbFault := by
      intro hsd
      by_cases e : u = t
      · subst e; exact hsf x0 x k0 hx hsd
      · obtain ⟨x1, k1, g1⟩ := hk.tcbFB hx
        rw [k0] at k1; cases k1; exact g1 e
    intro x' scp y n h1 h2 h3 h4 h5
    rw [hx] at h1; cases h1
    obtain ⟨y0, k3, e3⟩ := hk.scB h3
    rw [hrl] at h5
    rw [released_congr htm]
    unfold released; rw [e3.hd]
    exact h.rd u x0 k0 (hc.congr f0.symm fun hs => (g0 (by rw [← f0]; exact hs)).symm) x0 scp y0 n k0 (by rw [← e0]; exact h2) k3
      (by rw [← e3.active]; exact h4) h5
  · obtain ⟨y0, k0, e0⟩ := hk.scB hy
    intro ha hp
    have r := h.refills p y0 n k0 (by rw [← e0.active]; exact ha) (by rw [← e0.2.2.1]; exact hp)
    unfold RefOK at r ⊢; rw [e0.hd, e0.1]; exact r
  · obtain ⟨x0, k0, e0, -⟩ := tB hx
    obtain ⟨y, n, k1, e1⟩ := h.back u x0 p k0 (by rw [← e0]; exact hp)
    obtain ⟨y', k2, e2⟩ := hk.scF k1
    exact ⟨y', n, k2, by rw [e2.2.2.2.1]; exact e1⟩
  · obtain ⟨x0, k0, e0⟩ := hk.ntfnB hx
    obtain ⟨y, n, k1⟩ := h.ntfnSc q x0 p k0 (by rw [← e0]; exact hp)
    obtain ⟨y', k2, -⟩ := hk.scF k1
    exact ⟨y', n, k2⟩
  · obtain ⟨y0, k0, e0⟩ := hk.scB hy
    intro ha
    rw [e0.1]; exact h.ne p y0 n k0 (by rw [← e0.active]; exact ha)
  · obtain ⟨y0, k0, e0⟩ := hk.scB hy
    intro ha hp
    exact RRok.of_refills (h.rr p y0 n k0 (by rw [← e0.active]; exact ha) (by rw [← e0.2.2.1]; exact hp)) e0.1

/-- `IK t` across a TCB update keeping its SC and state. -/
theorem IK.updTcb {t p : ObjRef} {σ : State Unit} {x y : Tcb} (hk : σ.kheap p = some (.tcb x))
    (h1 : y.tcbSchedContext = x.tcbSchedContext) (h2 : y.tcbState = x.tcbState)
    (h3 : p ≠ t → y.tcbFault = x.tcbFault) :
    IK t σ (updK σ p (.tcb y)) :=
  IK.upd hk ⟨fun x' e => by cases e; exact ⟨y, rfl, h1, fun _ => h2, h3⟩, fun _ _ e => (by cases e),
    fun _ e => (by cases e), fun _ _ => ⟨x, rfl⟩, fun _ _ e => (by cases e), fun _ e => by cases e⟩

/-- `IK t` across a step keeping the heap, the queues and the time. -/
theorem IK.of_eq {t : ObjRef} {σ σ' : State Unit} (hk : σ'.kheap = σ.kheap)
    (hq : σ'.readyQueues = σ.readyQueues) (hr : σ'.releaseQueue = σ.releaseQueue) (ht : σ'.curTime = σ.curTime) :
    IK t σ σ' :=
  ⟨fun p => by rw [hk]; exact OIK.refl _ _, hq, hr, ht⟩

theorem ikm_maybeM' {t : ObjRef} {α : Type} {g : α → NonDet (State Unit) Unit} (h : ∀ a, IKM t (g a))
    (o : Option α) : IKM t (NonDet.maybeM g o) := by
  cases o
  · first | exact ikm_pure _ | exact ikm_pure' _
  · exact h _

theorem rdo_tcbAppend (u : ObjRef) (qs : List ObjRef) : RdO (tcbAppend (Z := Unit) u qs) := by
  unfold tcbAppend orderedInsert
  exact rdo_bind (rdo_getsThe _) fun _ => rdo_bind (rdo_mapM (fun _ => rdo_getsThe _) _) fun _ =>
    rdo_bind (rdo_pure _) fun _ => rdo_bind (rdo_pure _) fun _ => rdo_pure _

theorem ikm_threadSetPriority {t : ObjRef} (u : ObjRef) (pr : Priority) :
    IKM t (threadSetPriority (Z := Unit) u pr) := by
  unfold threadSetPriority
  exact ikm_threadSet fun _ => ⟨rfl, fun _ => rfl, fun _ => rfl⟩

theorem ikm_reorderEp {t : ObjRef} (e u : ObjRef) : IKM t (reorderEp (Z := Unit) e u) := by
  unfold reorderEp
  exact ikm_bind (ikm_of_rdo (rdo_getSimpleKo _ _)) fun _ => ikm_bind (ikm_assert _) fun _ =>
    ikm_bind (ikm_pure _) fun _ => ikm_bind (ikm_assert _) fun _ => ikm_bind (ikm_pure _) fun _ =>
    ikm_bind (ikm_of_rdo (rdo_tcbAppend _ _)) fun _ => ikm_setSimpleKo notTSN_ep _ _

/-- `reorder_ntfn` keeps the notification's SC. -/
theorem ikm_reorderNtfn {t : ObjRef} (n u : ObjRef) : IKM t (reorderNtfn (Z := Unit) n u) := by
  intro σ x hx
  unfold reorderNtfn at hx
  obtain ⟨y1, hy1, hx⟩ := hx
  obtain ⟨e1, hk⟩ := rdn_getSimpleKo _ _ σ y1 hy1
  rw [e1] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  rw [rdo_assert _ σ y2 hy2] at hx
  obtain ⟨y3, hy3, hx⟩ := hx
  rw [rdo_pure _ σ y3 hy3] at hx
  obtain ⟨y4, hy4, hx⟩ := hx
  rw [rdo_assert _ σ y4 hy4] at hx
  obtain ⟨y5, hy5, hx⟩ := hx
  rw [rdo_pure _ σ y5 hy5] at hx
  obtain ⟨y6, hy6, hx⟩ := hx
  rw [rdo_tcbAppend _ _ σ y6 hy6] at hx
  dsimp only [setNotification, setSimpleKo] at hx
  obtain ⟨z1, hz1, hx⟩ := hx
  obtain ⟨hk1, hs1⟩ := getObject_mem hz1
  rw [hs1] at hx
  obtain ⟨z2, hz2, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hz2
  obtain ⟨z3, hz3, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hz3
  obtain ⟨k, hk', -, e'⟩ := setObject_mem hx
  rw [e']
  refine IK.upd hk ⟨fun _ e => (by cases e), fun _ _ e => (by cases e), fun x0 e => ?_, fun _ e => (by cases e),
    fun _ _ e => (by cases e), fun _ _ => ⟨_, rfl⟩⟩
  cases e
  exact ⟨_, rfl, rfl⟩

/-- The blocked branch of `set_priority` is an `IK u` step for every `u`. -/
theorem ikm_setPriority_blk {t : ObjRef} (u : ObjRef) (pr : Priority) (ts : ThreadState) :
    IKM t (do
      threadSetPriority (Z := Unit) u pr
      NonDet.maybeM (fun ep => reorderEp (Z := Unit) ep u) (epBlocked ts)
      NonDet.maybeM (fun ntfn => reorderNtfn (Z := Unit) ntfn u) (ntfnBlocked ts)) :=
  ikm_bind (ikm_threadSetPriority _ _) fun _ => ikm_bind (ikm_maybeM' (fun _ => ikm_reorderEp _ _) _) fun _ =>
    ikm_maybeM' (fun _ => ikm_reorderNtfn _ _) _

theorem objRef_ne_succ (t : ObjRef) : t ≠ t + 1 := by
  intro e
  have := congrArg (fun z => z - t) e
  simp at this

/-- An `IK u` step at every `u` keeps `t`'s state. -/
theorem IK.st_of_all {t : ObjRef} {σ σ' : State Unit} (h : ∀ u, IK u σ σ') :
    ∀ x x', σ.kheap t = some (.tcb x) → σ'.kheap t = some (.tcb x') → x'.tcbState = x.tcbState := by
  intro x x' hx hx'
  obtain ⟨y, hy, -, e⟩ := (h (t + 1)).tcbF hx
  rw [hx'] at hy; cases hy
  exact e (objRef_ne_succ t)

/-- `IK.st_of_all` for the fault. -/
theorem IK.fl_of_all {t : ObjRef} {σ σ' : State Unit} (h : ∀ u, IK u σ σ') :
    ∀ x x', σ.kheap t = some (.tcb x) → σ'.kheap t = some (.tcb x') →
      (∃ e d, x.tcbState = .blockedOnSend e d) → x'.tcbFault = x.tcbFault := by
  intro x x' hx hx' _
  obtain ⟨y, hy, e⟩ := (h (t + 1)).tcbFB hx'
  rw [hx] at hy; cases hy
  exact e (objRef_ne_succ t)

/-- `Inv` across a TCB update keeping its SC and state, and its fault if
blocked on send. -/
theorem Inv.updSame {σ : State Unit} (h : Inv σ) {t : ObjRef} {x y : Tcb} (hk : σ.kheap t = some (.tcb x))
    (h1 : y.tcbSchedContext = x.tcbSchedContext) (h2 : y.tcbState = x.tcbState)
    (h3 : y.tcbFault = x.tcbFault ∨ ∀ e d, x.tcbState ≠ .blockedOnSend e d) :
    Inv (updK σ t (.tcb y)) :=
  h.ikKeep (IK.updTcb hk h1 h2 fun h => absurd rfl h) (fun x0 x' h0 h' => by
    rw [hk] at h0; cases h0
    simp [updK] at h'; rw [← h']; exact h2) fun x0 x' h0 h' ⟨e, d, hs⟩ => by
    rw [hk] at h0; cases h0
    simp [updK] at h'; rw [← h']
    rcases h3 with h3 | h3
    · exact h3
    · exact absurd hs (h3 e d)

/-- `Inv` across a priority update. -/
theorem Inv.prioUpd {σ : State Unit} (h : Inv σ) {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (pr : Priority) : Inv (updK σ t (.tcb { x with tcbPriority := pr })) :=
  h.updSame hk rfl rfl (Or.inl rfl)

/-- `NSC` across a step keeping every notification's SC (backward). -/
theorem NSC.oik {N C : Set U64} {k : ObjRef → Prop} {σ σ' : State Unit} (h : NSC N C σ)
    (ho : ∀ p, OIK (k p) (σ.kheap p) (σ'.kheap p)) : NSC N C σ' := by
  intro n hn x p hx hp
  have := ho n.bv
  rw [hx] at this
  cases e : σ.kheap n.bv with
  | none => rw [e] at this; exact this.elim
  | some o =>
    rw [e] at this
    obtain ⟨x0, rfl⟩ := this.2.2.2.2.2 x rfl
    obtain ⟨y, hy, e1⟩ := this.2.2.1 x0 rfl
    cases hy
    exact h n hn x0 p e (by rw [← e1]; exact hp)

set_option maxHeartbeats 4000000 in
/-- **`Inv` after `set_priority`** of a thread that is not the current
thread (module docstring), and every object's kind, SC links and (but the
target's) state kept (`OIK`). -/
theorem setPriority_inv {σ σ' : State Unit} (h : Inv σ) {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hnc : t ≠ σ.curThread) (pr : Priority) (hm : ((), σ') ∈ (setPriority (Z := Unit) t pr σ).1) :
    Inv σ' ∧ ∀ p, OIK (p ≠ t) (σ.kheap p) (σ'.kheap p) := by
  have hts : ∀ σ0 : State Unit, σ0.kheap t = some (.tcb x) →
      threadSetPriority (Z := Unit) t pr σ0 =
        ({((), updK σ0 t (.tcb { x with tcbPriority := pr }))}, False) := fun σ0 h0 =>
    threadSet_eq _ h0
  cases hr : runnable x.tcbState
  · rw [Ipc.setPriority_blk hk hr pr] at hm
    have hik : ∀ u, IK u σ σ' := fun u => ikm_setPriority_blk (t := u) t pr x.tcbState σ _ hm
    exact ⟨h.ikKeep (hik t) (IK.st_of_all hik) (IK.fl_of_all hik), (hik t).1⟩
  rw [Ipc.setPriority_run hk hr pr] at hm
  split_ifs at hm with hq
  · have hq' : t ∈ σ.readyQueues x.tcbDomain x.tcbPriority := hq.resolve_right hnc
    rw [nd_bind_one (tcbSchedAction_gen hk _)] at hm
    set σa := setQ σ x.tcbDomain x.tcbPriority (tcbSchedDequeue t (σ.readyQueues x.tcbDomain x.tcbPriority))
      with hσa
    have hka : σa.kheap t = some (.tcb x) := hk
    have hIa : Inv σa := h.qchange (qchange_dequeue hk)
    rw [nd_bind_one (hts σa hka)] at hm
    set σb := updK σa t (.tcb { x with tcbPriority := pr }) with hσb
    have hkb : σb.kheap t = some (.tcb { x with tcbPriority := pr }) := by simp [hσb, updK]
    have hIb : Inv σb := hIa.prioUpd hka pr
    rw [nd_bind_one (tcbSchedAction_gen hkb _)] at hm
    set σc := setQ σb x.tcbDomain pr (tcbSchedEnqueue t (σb.readyQueues x.tcbDomain pr)) with hσc
    -- `t`'s ready-queue facts at `σb`
    have hRt : ∃ x scp y n, σb.kheap t = some (.tcb x) ∧ x.tcbSchedContext = some scp ∧
        runnable x.tcbState = true ∧ σb.kheap scp = some (.schedContext y n) ∧ scActive y = true := by
      obtain ⟨x0, scp, y, n, h1, h2, h3, h4, h5⟩ := h.rq _ _ t hq'
      rw [hk] at h1; cases h1
      have hsc : scp ≠ t := by rintro rfl; rw [hk] at h4; cases h4
      exact ⟨_, scp, y, n, hkb, h2, h3, by simp [hσb, updK, hsc]; exact h4, h5⟩
    have hIc : Inv σc := by
      refine hIb.congr' rfl (fun d p u hu => ?_) rfl rfl
      simp only [hσc, setQ] at hu
      split at hu
      · rename_i e
        obtain ⟨rfl, rfl⟩ := e
        unfold tcbSchedEnqueue at hu
        split at hu
        · rcases List.mem_cons.1 hu with rfl | hu
          · exact hRt
          · exact hIb.rq _ _ u hu
        · exact hIb.rq _ _ u hu
      · exact hIb.rq d p u hu
    obtain ⟨σd, hd, hqd⟩ := rescheduleRequired_qchange hIc.actReady
    rw [hd] at hm
    rw [show σ' = σd from (Prod.mk.inj (Set.mem_singleton_iff.1 hm)).2]
    refine ⟨hIc.qchange hqd, fun p => ?_⟩
    rw [hqd.1]
    exact (IK.updTcb (t := t) (σ := σ) (y := { x with tcbPriority := pr }) hk rfl rfl fun _ => rfl).1 p
  · rw [hts σ hk] at hm
    rw [show σ' = updK σ t (.tcb { x with tcbPriority := pr }) from (Prod.mk.inj (Set.mem_singleton_iff.1 hm)).2]
    exact ⟨h.prioUpd hk pr, (IK.updTcb (t := t) (y := { x with tcbPriority := pr }) hk rfl rfl fun _ => rfl).1⟩


/-! ## `suspend` -/

/-- `cancel_ipc` of a runnable thread clears its fault only. -/
theorem cancelIpc_run {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hr : runnable x.tcbState = true) :
    cancelIpc (Z := Unit) t σ = ({((), updK σ t (.tcb { x with tcbFault := none }))}, False) := by
  unfold cancelIpc
  rw [nd_bind_one (getThreadState_eq hk), nd_bind_one (threadSet_eq _ hk)]
  cases hts : x.tcbState <;> simp_all [runnable]

theorem ikm_cancelYieldTo {t : ObjRef} (u : ObjRef) : IKM t (schedContextCancelYieldTo (Z := Unit) u) := by
  unfold schedContextCancelYieldTo getTcbObjRef
  refine ikm_bind (ikm_threadGet _ _) fun o => ikm_maybeM' (fun sc => ?_) o
  exact ikm_bind (ikm_updateSchedContext (g := scYieldFromUpdate fun _ => none)
    (fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩) _) fun _ =>
    ikm_threadSet (g := tcbYieldToUpdate fun _ => none) fun _ => ⟨rfl, fun _ => rfl, fun _ => rfl⟩

/-- The spec's `tcb_release_remove`: the thread filtered out of the release
queue, the reprogram flag set or kept. -/
theorem tcbReleaseRemove_eq (σ : State Unit) (t : ObjRef) : ∃ bb,
    tcbReleaseRemove (Z := Unit) t σ =
      ({((), setRel σ (σ.releaseQueue.filter fun x => decide (t ≠ x)) bb)}, False) := by
  unfold tcbReleaseRemove
  rw [nd_gets_bind]
  unfold NonDet.when
  split
  · rw [nd_bind_one (show NonDet.modify (fun s : State Unit => { s with reprogramTimer := true }) σ =
      ({((), { σ with reprogramTimer := true })}, False) from rfl), nd_pure_bind']
    exact ⟨true, rfl⟩
  · rw [nd_bind_one (show NonDet.pure (σ := State Unit) () σ = ({((), σ)}, False) from rfl), nd_pure_bind']
    exact ⟨σ.reprogramTimer, rfl⟩

/-- `when _ (update_restart_pc t)`: an `IK t` step keeping `t`'s state,
domain and priority. -/
theorem restartPc_step {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) {P : Prop}
    [Decidable P] {y : Unit × State Unit} (h : y ∈ (NonDet.when P (updateRestartPc (Z := Unit) t) σ).1) :
    IK t σ y.2 ∧ ∃ x', y.2.kheap t = some (.tcb x') ∧ x'.tcbState = x.tcbState ∧ x'.tcbDomain = x.tcbDomain ∧
      x'.tcbPriority = x.tcbPriority ∧ x'.tcbFault = x.tcbFault := by
  unfold NonDet.when at h
  split_ifs at h
  · rw [Ipc.updateRestartPc_eq hk] at h
    rw [Set.mem_singleton_iff.1 h]
    exact ⟨IK.updTcb hk rfl rfl (fun _ => rfl), setReg x .faultIP (x.tcbArch.tcbContext.userRegs .nextIP), by simp [updK],
      rfl, rfl, rfl, rfl⟩
  · rw [Set.mem_singleton_iff.1 h]
    exact ⟨IK.refl _ _, x, hk, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **`Inv` after `suspend`**, the thread queued at most in its own ready
queue (FL4's single queue per thread, `SchedSpec.rq`): the thread ends
`Inactive` in no queue (`InvBut.ik`, `InvBut.inv`). The objects' kinds,
SC links and (but the thread's) states kept (`OIK`). -/
theorem suspend_inv {σ σ' : State Unit} (h : Inv σ) {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hq : ∀ d p, t ∈ σ.readyQueues d p → d = x.tcbDomain ∧ p = x.tcbPriority)
    (hm : ((), σ') ∈ (suspend (Z := Unit) t σ).1) :
    Inv σ' ∧ ∀ p, OIK (p ≠ t) (σ.kheap p) (σ'.kheap p) := by
  unfold suspend at hm
  obtain ⟨y1, h1, hm⟩ := hm
  obtain ⟨y2, h2, hm⟩ := hm
  have e2 : y2.2 = y1.2 :=
    (show RdO (getThreadState (Z := Unit) t) by unfold getThreadState; exact RdO.ofRdN (rdn_threadGet _ _)) _ _ h2
  rw [e2] at hm
  obtain ⟨y3, h3, hm⟩ := hm
  obtain ⟨y4, h4, hm⟩ := hm
  obtain ⟨y5, h5, hm⟩ := hm
  obtain ⟨y6, h6, hm⟩ := hm
  -- up to the release-queue removal
  have mid : InvBut y5.2 t ∧ NotQueued y5.2 t ∧ ∀ p, OIK (p ≠ t) (σ.kheap p) (y5.2.kheap p) := by
    cases hr : runnable x.tcbState
    · have hNQ : NotQueued σ t := h.notQueued hk hr
      have ik1 : IK t σ y1.2 := ikm_cancelIpc σ y1 h1
      obtain ⟨x1, hk1, -, -⟩ := ik1.tcbF hk
      obtain ⟨ik3, x3, hk3, -⟩ := restartPc_step hk1 h3
      have ik13 := ik1.trans ik3
      rw [tcbSchedAction_gen hk3] at h4
      have e4 := Set.mem_singleton_iff.1 h4
      have ik4 : IK t y3.2 y4.2 := by
        rw [e4]
        refine IK.of_eq rfl ?_ rfl rfl
        funext d' p'
        simp only [setQ]
        split_ifs with e
        · obtain ⟨rfl, rfl⟩ := e
          unfold tcbSchedDequeue
          exact List.filter_eq_self.2 fun a ha => decide_eq_true fun ea =>
            hNQ.1 x3.tcbDomain x3.tcbPriority (by rw [← ik13.2.1]; exact ea ▸ ha)
        · rfl
      obtain ⟨bb, hb⟩ := tcbReleaseRemove_eq y4.2 t
      rw [hb] at h5
      have e5 := Set.mem_singleton_iff.1 h5
      have ik5 : IK t y4.2 y5.2 := by
        rw [e5]
        refine IK.of_eq rfl rfl ?_ rfl
        show List.filter _ _ = _
        exact List.filter_eq_self.2 fun a ha => decide_eq_true fun ea =>
          hNQ.2 (by rw [← ik13.2.2.1, ← ik4.2.2.1]; exact ea ▸ ha)
      have ik := (ik13.trans ik4).trans ik5
      obtain ⟨hB, hN⟩ := (h.toBut t).ik hNQ ik
      exact ⟨hB, hN, ik.1⟩
    · rw [cancelIpc_run hk hr] at h1
      rw [Set.mem_singleton_iff.1 h1] at h3
      have hk1 : (updK σ t (.tcb { x with tcbFault := none })).kheap t = some (.tcb { x with tcbFault := none }) := by
        simp [updK]
      have hI1 : Inv (updK σ t (.tcb { x with tcbFault := none })) :=
        h.updSame hk rfl rfl (Or.inr (NotIpcBlk.of_runnable hr).2.1)
      have ik1 : IK t σ (updK σ t (.tcb { x with tcbFault := none })) := IK.updTcb hk rfl rfl fun h => absurd rfl h
      obtain ⟨ik3, x3, hk3, es3, ed3, ep3, ef3⟩ := restartPc_step hk1 h3
      have hI3 : Inv y3.2 := hI1.ikKeep ik3 (fun x0 x' h0 h' => by
        rw [hk1] at h0; cases h0; rw [hk3] at h'; cases h'; exact es3) fun x0 x' h0 h' _ => by
        rw [hk1] at h0; cases h0; rw [hk3] at h'; cases h'; exact ef3
      have ik13 := ik1.trans ik3
      rw [tcbSchedAction_gen hk3] at h4
      have e4 := Set.mem_singleton_iff.1 h4
      have hI4 : Inv y4.2 := by rw [e4]; exact hI3.qchange (qchange_dequeue hk3)
      have hnq4 : ∀ d p, t ∉ y4.2.readyQueues d p := by
        intro d p hm4
        rw [e4] at hm4
        simp only [setQ] at hm4
        split_ifs at hm4 with e
        · unfold tcbSchedDequeue at hm4
          simp at hm4
        · rw [ik13.2.1] at hm4
          obtain ⟨rfl, rfl⟩ := hq d p hm4
          exact e ⟨ed3.symm, ep3.symm⟩
      have hk4 : y4.2.kheap = y3.2.kheap := by rw [e4]; rfl
      obtain ⟨bb, hb⟩ := tcbReleaseRemove_eq y4.2 t
      rw [hb] at h5
      have e5 := Set.mem_singleton_iff.1 h5
      have hB : InvBut y5.2 t := by rw [e5]; exact hI4.relRemove t bb
      refine ⟨hB, ⟨fun d p => ?_, ?_⟩, fun p => ?_⟩
      · rw [e5]; exact hnq4 d p
      · rw [e5]; simp [setRel]
      · rw [e5]; show OIK _ _ (y4.2.kheap p); rw [hk4]; exact ik13.1 p
  obtain ⟨hB5, hN5, ho5⟩ := mid
  have ik6 : IK t y5.2 y6.2 := ikm_cancelYieldTo t y5.2 y6 h6
  have hik7 : IKM t (setThreadState (Z := Unit) t ThreadState.inactive) := ikm_setThreadState _
  have ik7 : IK t y6.2 σ' := hik7 y6.2 ((), σ') hm
  have ik := ik6.trans ik7
  obtain ⟨hB, -⟩ := hB5.ik hN5 ik
  refine ⟨hB.inv fun x' hx' hc => ?_, fun p => (ho5 p).trans (ik.1 p)⟩
  exfalso
  obtain ⟨x6, hk6, -⟩ := ik7.tcbB hx'
  have hm' : ((), σ') ∈ (setThreadState (Z := Unit) t ThreadState.inactive y6.2).1 := hm
  rw [Notif.setThreadState_eq .inactive hk6] at hm'
  rw [(Prod.mk.inj (Set.mem_singleton_iff.1 hm')).2] at hx'
  rw [stsAct_kheap] at hx'
  simp [updK] at hx'
  subst hx'
  simp [inClassR, runnable] at hc

/-- The SCs' sizes back across a step keeping every object's kind (`OIK`). -/
theorem oik_szKeep {k : ObjRef → Prop} {σ σ' : State Unit} (ho : ∀ p, OIK (k p) (σ.kheap p) (σ'.kheap p)) :
    ∀ p y n, σ'.kheap p = some (.schedContext y n) → ∃ y0, σ.kheap p = some (.schedContext y0 n) := by
  intro p y n hp
  have := ho p
  rw [hp] at this
  cases e : σ.kheap p with
  | none => rw [e] at this; exact this.elim
  | some o =>
    rw [e] at this
    obtain ⟨y0, m, rfl⟩ := this.2.2.2.2.1 y n rfl
    obtain ⟨z, e', -⟩ := this.2.1 y0 m rfl
    cases e'
    exact ⟨y0, rfl⟩

end Spec

end

end Fl4Proofs.P3.Sched
