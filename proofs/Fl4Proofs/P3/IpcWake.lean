/-
P3 (DESIGN.md §9), IPC: **the wake-up tail on the merged footprint**
(the `wakeTail` field of `IpcSchedHyps`).

* `SFootI`: the scheduler's written words at the precision of P1's queue
  footprints (`QFoot`): the `Sched` links and `IN_QUEUES` word of TCBs, and
  core `c`'s node; `enqueue_sfootI`, `reschedule_required_sfootI`,
  `possible_switch_to_sfootI` (ScKFoot's proofs on this footprint).
  `sfootI_not_ifoot`: none of these words is read by `IpcRel`;
  `sfootI_iwords`: all of them are IPC or node words (for `RelTopI`).
* `NKM`: every outcome of `possible_switch_to` keeps the machine state and
  the domain schedule.
* `switch_top`: `possible_switch_to` refines `possible_switch_to` keeping
  `IFoot`, `IKView` and `SRT … SRE`.
* `IpcWakeHyps`: the SchedContext steps of the wake-up
  (`maybe_donate_sched_context`, `unblock_sporadic`: SchedNtfn's `WakeHyps`
  on `IFoot`/`IKView` and `SRT … SRE`); `wakeTail_top`: the `wakeTail`
  field from them.
-/
import Fl4Proofs.P3.IpcCancel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The scheduler's written words**: the `Sched` links and `IN_QUEUES`
word of TCBs, and core `c`'s node. -/
def SFootI (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (c : U64) (s : S) (b : U64) : Prop :=
  (∃ y ∈ T, b = core.num.U64.wrapping_add y 3480#u64 ∨ b = core.num.U64.wrapping_add y 3488#u64 ∨
    b = core.num.U64.wrapping_add y 3592#u64) ∨
  (L.nodeBase s c ≤ b.val ∧ b.val < L.nodeBase s c + 4288)

/-- A queue footprint is in the scheduler's written words. -/
theorem qfoot_sfootI {T : Set U64} {c : U64} {s : S} {W : List U64} {P : Nat → Prop} {t b : U64}
    (hT : TcbPlaced T) (hW : ∀ w ∈ W, w ∈ T) (ht : t ∈ T) (hN : NodePlaced st T s c) (hcpu : L.cpu s = c)
    (h : L.QFoot s W c P t b) : SFootI st T c s b := by
  rcases h with ⟨w, hw, e | e⟩ | ⟨o, -, ho, -, e⟩ | e | ⟨o, -, ho, -, e⟩
  · exact Or.inl ⟨w, hW w hw, Or.inl e⟩
  · exact Or.inl ⟨w, hW w hw, Or.inr (Or.inl e)⟩
  · exact Or.inr ⟨by rw [e, nodeAt_val hN ho]; omega, by rw [e, nodeAt_val hN ho]; omega⟩
  · exact Or.inl ⟨t, ht, Or.inr (Or.inr e)⟩
  · rw [hcpu] at e
    exact Or.inr ⟨by rw [e, nodeAt_val hN ho]; omega, by rw [e, nodeAt_val hN ho]; omega⟩

theorem SFootI.ksb {T : Set U64} {c : U64} {s s' : S} (h : L.ksb s' = L.ksb s) {b : U64} :
    SFootI st T c s' b ↔ SFootI st T c s b := by
  simp only [SFootI, LawfulStore.nodeBase, h]

theorem WritesIn.sfootI_trans {T : Set U64} {c : U64} {s s1 s2 : S} (h1 : WritesIn st s s1 (SFootI st T c s))
    (h2 : WritesIn st s1 s2 (SFootI st T c s1)) : WritesIn st s s2 (SFootI st T c s) :=
  (h1.trans h2).mono fun b hb => by
    rcases hb with hb | hb
    · exact hb
    · exact (SFootI.ksb h1.1).1 hb

/-- **`enqueue`'s footprint**, for a thread that is queued or not released. -/
theorem enqueue_sfootI {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) :
    sched.enqueue st s t ⦃ s' => WritesIn st s s' (SFootI st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hp := hc.prio t ht
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hR1 : ReadyQueues st T s (L.mem s (affA t)) Q := by rw [haf]; exact hc.ready
  have hnq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → t ∉ Q (L.mem s (prioA t)) :=
    fun h0 hm => ((hc.queued t ht).2 hm) h0
  refine WP.spec_mono (sched.enqueue.foot s t _ hc.tcbs ht hp hN hN' (hR1.1.rel _ hp) hnq) ?_
  rintro s' ⟨hw, -⟩
  rw [haf] at hw
  refine hw.mono fun b hb => qfoot_sfootI hc.tcbs (fun w hw' => ?_) ht hc.node hc.cur hb
  rcases List.mem_cons.1 hw' with rfl | hw'
  · exact ht
  · exact (hc.ready.1.rel _ hp).mem w hw'

/-- A node word is in the footprint. -/
theorem sfootI_node {T : Set U64} {c : U64} {s : S} (hN : NodePlaced st T s c) {o : U64} (ho : o.val < 4288) :
    SFootI st T c s (L.nodeAt s c o) :=
  Or.inr ⟨by rw [nodeAt_val hN ho]; omega, by rw [nodeAt_val hN ho]; omega⟩

/-- **`reschedule_required`'s footprint.** -/
theorem reschedule_required_sfootI {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) :
    sched.reschedule_required st s ⦃ s' => WritesIn st s s' (SFootI st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN := hc.node
  have hact : ∀ s1 : S, WritesIn st s s1 (SFootI st T c s) →
      sched.set_action st s1 sched.ACTION_CHOOSE_NEW ⦃ s' => WritesIn st s s' (SFootI st T c s) ⦄ := by
    intro s1 h1
    refine WP.spec_mono (sched.set_action.spec' s1 _) ?_
    rintro s' rfl
    refine WritesIn.sfootI_trans h1 ((writesIn_wr ?_).mono fun b hb => ?_)
    · rw [nodeAt_ksb h1.1, h1.2.1, hc.cur]; exact nodeAt_aligned hN (by simp [layout.node.SCHED_ACTION])
        (by simp [layout.node.SCHED_ACTION])
    · rw [hb, nodeAt_ksb h1.1, h1.2.1, hc.cur]
      have ho : (layout.node.SCHED_ACTION).val < 4288 := by simp [layout.node.SCHED_ACTION]
      refine (SFootI.ksb h1.1).2 (Or.inr ⟨by rw [nodeAt_val hN ho]; omega, by rw [nodeAt_val hN ho]; omega⟩)
  unfold sched.reschedule_required
  step with sched.action.spec' as ⟨act, hact'⟩
  rw [hc.cur] at hact'
  have e0 : sched.ACTION_RESUME_CURRENT = 0#u64 := by unfold sched.ACTION_RESUME_CURRENT; rfl
  have e1 : sched.ACTION_CHOOSE_NEW = 1#u64 := by unfold sched.ACTION_CHOOSE_NEW; rfl
  by_cases h1 : act = sched.ACTION_RESUME_CURRENT
  · have : (act != sched.ACTION_RESUME_CURRENT) = false := by simpa using h1
    simp only [this, Bool.false_eq_true, ↓reduceIte, bind_ok]; exact hact s (WritesIn.refl _ _)
  have g1 : (act != sched.ACTION_RESUME_CURRENT) = true := by simpa using h1
  by_cases h2 : act = sched.ACTION_CHOOSE_NEW
  · have : (act != sched.ACTION_CHOOSE_NEW) = false := by simpa using h2
    simp only [g1, this, Bool.false_eq_true, ↓reduceIte, bind_ok]; exact hact s (WritesIn.refl _ _)
  have g2 : (act != sched.ACTION_CHOOSE_NEW) = true := by simpa using h2
  simp only [g1, g2, ↓reduceIte]
  have hT : act ∈ T := by
    rw [hact']
    rcases hS.actW with h | h | h
    · rw [hact', h] at h1; exact absurd e0.symm h1
    · rw [hact', h] at h2; exact absurd e1.symm h2
    · exact h
  step with sched.is_schedulable.spec' as ⟨b, _hb⟩
  by_cases hb : b = true
  · rw [if_pos hb]; exact WP.spec_bind (enqueue_sfootI hS hT) hact
  · rw [if_neg hb]; simp only [bind_ok]; exact hact s (WritesIn.refl _ _)

/-- **`possible_switch_to`'s footprint.** -/
theorem possible_switch_to_sfootI {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hR : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ) (hr : ActReady σ) {t : U64} (ht : t ∈ T) :
    sched.possible_switch_to st s t ⦃ s' => WritesIn st s s' (SFootI st T c s) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  unfold sched.possible_switch_to
  step with Fl4Proofs.P1.obj.Tcb.sc.spec
  split
  · exact (WP.spec_ok _).mpr (WritesIn.refl _ _)
  step with Fl4Proofs.P1.sched.in_release_queue.spec
  split
  · exact (WP.spec_ok _).mpr (WritesIn.refl _ _)
  step with Sched.sched.cur_domain.spec'
  step with Fl4Proofs.P1.obj.Tcb.domain.spec
  split
  · exact enqueue_sfootI hS ht
  step with Fl4Proofs.P1.obj.Tcb.affinity.spec
  step
  split
  · exact enqueue_sfootI hS ht
  step with Sched.sched.action.spec'
  split
  · refine WP.spec_bind (WP.spec_and (reschedule_required_refines s σ hR hS hr) (reschedule_required_sfootI hS)) ?_
    rintro s1 ⟨⟨σ1, -, -, -, -, hS1⟩, hw1⟩
    exact WP.spec_mono (enqueue_sfootI hS1 ht) fun s2 hw2 => WritesIn.sfootI_trans hw1 hw2
  · step with Sched.sched.set_action.spec'
    subst s'_post
    have ho : (layout.node.SCHED_ACTION).val < 4288 := by simp [layout.node.SCHED_ACTION]
    rw [show L.cpu s = c from hc.cur]
    exact (writesIn_wr (nodeAt_aligned hc.node ho (by simp [layout.node.SCHED_ACTION]))).mono fun b hb =>
      hb ▸ sfootI_node hc.node ho


end

end

end Fl4Proofs.P3.Sched

/-! ## The spec: what `possible_switch_to` keeps besides the caps -/

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section NKM
open Fl4Spec

/-- The fields a scheduler step keeps: the machine state, the domain
schedule, the arch state, the IRQ state and node, the current thread. -/
def MK (σ σ' : State Unit) : Prop :=
  σ'.machineState = σ.machineState ∧ σ'.domainList = σ.domainList ∧
    σ'.domainStartIndex = σ.domainStartIndex ∧ σ'.archState = σ.archState ∧
    σ'.interruptStates = σ.interruptStates ∧ σ'.interruptIrqNode = σ.interruptIrqNode ∧
    σ'.curThread = σ.curThread

theorem MK.refl (σ : State Unit) : MK σ σ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem MK.trans {σ1 σ2 σ3 : State Unit} (h1 : MK σ1 σ2) (h2 : MK σ2 σ3) : MK σ1 σ3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.1.trans h1.2.2.2.2.1, h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2⟩

/-- Every outcome keeps the machine state, the domain schedule, the arch and
IRQ state and the current thread (`MK`). -/
def NKM {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ x, x ∈ (m σ).1 → MK σ x.2

theorem nkm_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : NKM m)
    (hf : ∀ a, NKM (f a)) : NKM (m >>= f) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hf y.1 y.2 x hx)

theorem nkm_pure {α : Type} (a : α) : NKM (pure a : NonDet (State Unit) α) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact MK.refl σ

theorem nkm_pure' {α : Type} (a : α) : NKM (NonDet.pure a : NonDet (State Unit) α) := nkm_pure a

theorem nkm_gets {α : Type} (f : State Unit → α) : NKM (NonDet.gets f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact MK.refl σ

theorem nkm_modify {f : State Unit → State Unit} (hf : ∀ σ, MK σ (f σ)) : NKM (NonDet.modify f) := by
  intro σ x hx; rw [Set.mem_singleton_iff.1 hx]; exact hf σ

theorem nkm_assert (P : Prop) : NKM (NonDet.assert P : NonDet (State Unit) Unit) := by
  intro σ x hx; obtain ⟨-, rfl⟩ := hx; exact MK.refl σ

theorem nkm_fail {α : Type} : NKM (NonDet.fail : NonDet (State Unit) α) := by
  intro σ x hx; exact hx.elim

theorem nkm_assertOpt {α : Type} (o : Option α) : NKM (NonDet.assertOpt o : NonDet (State Unit) α) := by
  cases o
  · exact nkm_fail
  · exact nkm_pure' _

theorem nkm_getsThe {α : Type} (f : State Unit → Option α) : NKM (NonDet.getsThe f) := by
  intro σ x hx
  exact nkm_assertOpt (f σ) σ x hx

theorem nkm_when {P : Prop} {inst : Decidable P} {m : NonDet (State Unit) Unit} (h : NKM m) :
    NKM (@NonDet.when _ P inst m) := by
  unfold NonDet.when; split; exact h; exact nkm_pure' _

theorem nkm_threadGet {α : Type} (f : Tcb → α) (t : ObjRef) : NKM (threadGet (Z := Unit) f t) := by
  unfold threadGet; exact nkm_bind (nkm_getsThe _) (fun _ => nkm_pure _)

theorem nkm_tcbSchedAction (f : ObjRef → List ObjRef → List ObjRef) (t : ObjRef) :
    NKM (tcbSchedAction (Z := Unit) f t) := by
  unfold tcbSchedAction getTcbQueue setTcbQueue
  exact nkm_bind (nkm_threadGet _ _) (fun _ => nkm_bind (nkm_threadGet _ _) (fun _ =>
    nkm_bind (nkm_bind (nkm_gets _) (fun _ => nkm_pure _)) (fun _ => nkm_bind (nkm_pure _) (fun _ =>
      nkm_modify (fun σ => MK.refl σ)))))

theorem nkm_setSchedulerAction (a : SchedulerAction) : NKM (setSchedulerAction (Z := Unit) a) := by
  unfold setSchedulerAction; exact nkm_modify (fun σ => MK.refl σ)

theorem nkm_rescheduleRequired : NKM (rescheduleRequired (Z := Unit)) := by
  unfold rescheduleRequired getScRefillSufficient getScRefillReady
  refine nkm_bind (nkm_gets _) (fun act => ?_)
  dsimp only
  split
  · refine nkm_bind (nkm_gets _) (fun _ => nkm_bind (nkm_when ?_) (fun _ => nkm_setSchedulerAction _))
    exact nkm_bind (nkm_threadGet _ _) (fun _ => nkm_bind (nkm_assertOpt _) (fun _ =>
      nkm_bind (nkm_getsThe _) (fun _ => nkm_bind (nkm_getsThe _) (fun _ =>
        nkm_bind (nkm_assert _) (fun _ => nkm_tcbSchedAction _ _)))))
  · first | exact nkm_setSchedulerAction _ | exact nkm_bind (nkm_pure _) (fun _ => nkm_setSchedulerAction _)

theorem nkm_possibleSwitchTo (t : ObjRef) : NKM (possibleSwitchTo (Z := Unit) t) := by
  unfold possibleSwitchTo getTcbObjRef
  refine nkm_bind (nkm_threadGet _ _) (fun _ => nkm_bind (nkm_gets _) (fun _ => nkm_when ?_))
  refine nkm_bind (nkm_gets _) (fun _ => nkm_bind (nkm_threadGet _ _) (fun _ => nkm_bind (nkm_gets _) (fun _ => ?_)))
  split
  · exact nkm_tcbSchedAction _ _
  · split
    · exact nkm_bind nkm_rescheduleRequired (fun _ => nkm_tcbSchedAction _ _)
    · exact nkm_setSchedulerAction _

/-- The merged view from the same heap and user memory. -/
theorem IKView.of_kheap {σ σ' : State Unit} (hk : σ'.kheap = σ.kheap)
    (hu : σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory) : IKView σ σ' :=
  ⟨⟨fun p x h => by rw [hk]; exact h, fun p x h => ⟨x, by rw [hk]; exact h, rfl, rfl, rfl⟩⟩,
    ⟨fun p x h => by rw [hk]; exact h, fun p x h => ⟨x, by rw [hk]; exact h, rfl⟩,
      fun p x h => ⟨x, by rw [hk]; exact h, rfl, rfl, rfl, rfl, rfl⟩, hu⟩,
    fun p x h => ⟨x, by rw [hk]; exact h, rfl⟩⟩

end NKM

/-! ## The scheduler's words and the merged footprint -/

section Foot
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- A word of core `c`'s node is a `nodeAt` word. -/
theorem node_word {s : S} (hN : NodePlaced st T s c) {b : U64} (h1 : L.nodeBase s c ≤ b.val)
    (h2 : b.val < L.nodeBase s c + 4288) : ∃ o : U64, o.val < 4288 ∧ L.nodeAt s c o = b := by
  have hb := b.hBounds
  have hv : (⟨BitVec.ofNat 64 (b.val - L.nodeBase s c)⟩ : U64).val = b.val - L.nodeBase s c := by
    show (BitVec.ofNat 64 (b.val - L.nodeBase s c)).toNat = _
    simp only [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
  refine ⟨⟨BitVec.ofNat 64 (b.val - L.nodeBase s c)⟩, by rw [hv]; omega, ?_⟩
  apply UScalar.eq_of_val_eq
  rw [nodeAt_val hN (by rw [hv]; omega), hv]; omega

/-- **No word the scheduler writes is read by the merged relation.** -/
theorem sfootI_not_ifoot (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hA : EpSchedApart st T C E R B c s σ) {b : U64} (h1 : SFootI st T c s b)
    (h2 : IFoot N T E R B b) : False := by
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hP := hP0.e
  rcases h1 with ⟨y, hy, hb⟩ | ⟨g1, g2⟩
  · have hya := hP.tcb y hy
    obtain ⟨K, hK, hbv⟩ : ∃ K : Nat, (K = 3480 ∨ K = 3488 ∨ K = 3592) ∧ b.val = y.val + K := by
      rcases hb with rfl | rfl | rfl
      · exact ⟨3480, by decide, tfield_val hya (by decide)⟩
      · exact ⟨3488, by decide, tfield_val hya (by decide)⟩
      · exact ⟨3592, by decide, tfield_val hya (by decide)⟩
    rcases h2 with (⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, h | h⟩ | ⟨wp, hw, h⟩) | ⟨n, hn, n1, n2⟩ | ⟨t, ht, h⟩
    · have := hP.et e he y hy; omega
    · have := hP.rt r hr y hy; omega
    · by_cases e : t = y
      · subst e; obtain ⟨-, h2⟩ := h; unfold TOffN at h2; omega
      · have := tcb_disj hP ht hy (Ne.symm e); have := h.range; omega
    · by_cases e : t = y
      · subst e; unfold TL at h; omega
      · have := tcb_disj hP ht hy (Ne.symm e); unfold TL at h; omega
    · have := hP.bt wp hw y hy; rw [← h] at this; omega
    · have := hP0.n.disj n hn y hy; omega
    · have hv := congrArg UScalar.val h
      rw [scA_val (hP.tcb t ht)] at hv
      by_cases e : t = y
      · subst e; omega
      · have := tcb_disj hP ht hy (Ne.symm e); omega
  · obtain ⟨o, ho, rfl⟩ := node_word hc.node g1 g2
    rcases h2 with hE | ⟨n, hn, n1, n2⟩ | ⟨t, ht, e⟩
    · exact hA.node _ g1 g2 hE
    · exact hS.nodeNW o ho (Or.inl ⟨n, hn, n1, n2⟩)
    · exact nodeAt_ne_tfield hc.node ho ht (hc.tcbs t ht) (K := 3464#u64) (by simp) e

/-- **Every word the scheduler writes is an IPC or node word.** -/
theorem sfootI_iwords (hT : TcbPlaced T) {s : S} {b : U64} (h : SFootI st T c s b) :
    IWords N T E R B b ∨ NodeW (L.ksb s) c b := by
  rcases h with ⟨y, hy, hb⟩ | ⟨g1, g2⟩
  · have hya := hT y hy
    refine Or.inl (Or.inl ⟨y, hy, ?_⟩)
    rcases hb with rfl | rfl | rfl <;> (rw [tfield_val hya (by decide)]; simp)
  · have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
    exact Or.inr ⟨by omega, by omega⟩

/-- The wake tail writes no IPC-buffer word outside the node. -/
theorem sfootI_nobuf (hT : TcbPlaced T) {s : S} {b : U64} (h : SFootI st T c s b) :
    NodeW (L.ksb s) c b ∨ NoBufW T b := by
  rcases h with ⟨y, hy, hb⟩ | ⟨g1, g2⟩
  · refine Or.inr ?_
    rcases hb with rfl | rfl | rfl <;> exact NoBufW.off hT hy (by decide) (by decide)
  · have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
    exact Or.inl ⟨by omega, by omega⟩

end Foot

/-! ## `possible_switch_to` and the wake tail -/

section Wake
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **`possible_switch_to` refines `possible_switch_to`** keeping the merged
footprint and view and `SRT … SRE`. -/
theorem switch_top (hP0 : IPlaced N T E R B) (s : S) (σ : Fl4Spec.State Unit)
    (hR : IpcRel N T E R B (L.mem s) σ) (hS : SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ)
    (hr : ActReady σ) (t : U64) (ht : t ∈ T) :
    sched.possible_switch_to st s t ⦃ s' => ∃ σ', Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      σ'.kheap = σ.kheap ∧ Agree (L.mem s) (L.mem s') (IFoot N T E R B) ∧ IKView σ σ' ∧
      SRT st th cr N T C E R B c (SRE st N T C E R B c) s' σ' ⦄ := by
  refine WP.spec_mono (WP.spec_and (possible_switch_to_refines s σ hR.toN hS.2.1 hr t ht)
    (possible_switch_to_sfootI hR.toN hS.2.1 hr ht)) ?_
  rintro s' ⟨⟨σ', heq, hk, -, hSch⟩, hW⟩
  have hmem : ((), σ') ∈ (Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ).1 := by rw [heq]; rfl
  obtain ⟨hms, hdl, hds, har, hist, hino, hct⟩ := nkm_possibleSwitchTo t.bv σ _ hmem
  have hck : CKeep σ σ' := nkc_possibleSwitchTo t.bv σ _ hmem
  refine ⟨σ', heq, hk, fun a ha hf => hW.mem_eq ha (fun hs => sfootI_not_ifoot hP0 hS.2.1 hS.2.2 hs hf),
    IKView.of_kheap hk (by rw [hms]), hS.1.frameN hW (fun a ha => sfootI_iwords hP0.e.tcb ha) (fun a ha => sfootI_nobuf hP0.e.tcb ha) hck hdl hds (VsKeep.of_kheap hk har hist hino hct),
    hSch, hS.2.2.mono hW.1 (SzKeep.of_kheap hk)⟩

/-- **The SchedContext steps of the wake-up** (SchedNtfn's `WakeHyps`) on
the merged footprint and view and `SRT … SRE`. -/
structure IpcWakeHyps (st : machine.Store S) (ar : machine.Arch A) [L : LawfulStore st] (th : TypedHeap)
    (cr : Fl4Spec.Cr3) (N T C E R : Set U64)
    (B : Set (U64 × Fl4Spec.Word)) (c : U64) : Prop where
  donate : ∀ s (a : A) σ (t n : U64) (x : Fl4Spec.Tcb), IpcRel N T E R B (L.mem s) σ →
    SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ → t ∈ T → n ∈ N → σ.kheap t.bv = some (.tcb x) →
    x.tcbState = .running →
    notification.maybe_donate_sched_context st ar s a t n ⦃ r => ∃ σ1,
      Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σ = ({((), σ1)}, False) ∧
      IpcRel N T E R B (L.mem r.1) σ1 ∧
      SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 σ1 ∧ ActReady σ1 ⦄
  unblock : ∀ s σ (t : U64), IpcRel N T E R B (L.mem s) σ → SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ →
    t ∈ T →
    notification.unblock_sporadic st s t ⦃ s' => ¬ (specUnblock t.bv σ).2 ∧
      ∃ σ', ((), σ') ∈ (specUnblock t.bv σ).1 ∧ Agree (L.mem s) (L.mem s') (IFoot N T E R B) ∧
        IKView σ σ' ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) s' σ' ⦄

/-- **The `wakeTail` field of `IpcSchedHyps` for `SRT … SRE`**, from
`IpcWakeHyps` (SchedNtfn's `wakeTail_of` on the merged footprint). -/
theorem wakeTail_top (hP0 : IPlaced N T E R B) (hW : IpcWakeHyps st ar th cr N T C E R B c) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (t n : U64) (x : Fl4Spec.Tcb) (hR : IpcRel N T E R B (L.mem s) σ)
    (hS : SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ) (ht : t ∈ T) (hn : n ∈ N)
    (hk : σ.kheap t.bv = some (.tcb x)) (hx : x.tcbState = .running) :
    rustWakeTail st ar s a t n ⦃ r => ¬ (specWakeTail t.bv n.bv σ).2 ∧ ∃ σ', ((), σ') ∈ (specWakeTail t.bv n.bv σ).1 ∧
      IpcRel N T E R B (L.mem r.1) σ' ∧ SRT st th cr N T C E R B c (SRE st N T C E R B c) r.1 σ' ⦄ := by
  unfold rustWakeTail
  refine WP.spec_bind (hW.donate s a σ t n x hR hS ht hn hk hx) ?_
  rintro ⟨s4, a2⟩ ⟨σ1, hd, hR1, hS1, hr1⟩
  step with Sched.sched.is_schedulable.spec' as ⟨b1, b1_post⟩
  rw [schedulable_eq hR1.toN hS1.2.1 ht] at b1_post
  have hmid : (if b1 = true then sched.possible_switch_to st s4 t else ok s4) ⦃ s5 => ∃ σ2,
      (Fl4Spec.NonDet.when (Fl4Spec.schedulable t.bv σ1 = true) (Fl4Spec.possibleSwitchTo t.bv)) σ1 =
        ({((), σ2)}, False) ∧ Agree (L.mem s4) (L.mem s5) (IFoot N T E R B) ∧ IKView σ1 σ2 ∧
        SRT st th cr N T C E R B c (SRE st N T C E R B c) s5 σ2 ⦄ := by
    rw [b1_post]
    by_cases e : Fl4Spec.schedulable t.bv σ1 = true
    · simp only [e, ↓reduceIte, Fl4Spec.NonDet.when]
      refine WP.spec_mono (switch_top hP0 s4 σ1 hR1 hS1 hr1 t ht) ?_
      rintro s5 ⟨σ2, hp, -, hf, hv, hS2⟩
      exact ⟨σ2, hp, hf, hv, hS2⟩
    · simp only [e, Bool.false_eq_true, ↓reduceIte, Fl4Spec.NonDet.when, WP.spec_ok]
      exact ⟨σ1, rfl, Agree.rfl', IKView.refl _, hS1⟩
  refine WP.spec_bind hmid ?_
  rintro s5 ⟨σ2, hw2, hf2, hv2, hS2⟩
  have hR2 : IpcRel N T E R B (L.mem s5) σ2 := hR1.frame hP0 hf2 hv2
  refine WP.spec_bind (hW.unblock s5 σ2 t hR2 hS2 ht) ?_
  rintro s6 ⟨hnf, σ', hm, hf3, hv3, hS3⟩
  simp only [WP.spec_ok]
  have hspec : specWakeTail t.bv n.bv σ = specUnblock t.bv σ2 := by
    unfold specWakeTail
    rw [nd_bind_one hd, nd_gets_bind, nd_bind_one hw2]
    rfl
  rw [hspec]
  exact ⟨hnf, σ', hm, hR2.frame hP0 hf3 hv3, hS3⟩

/-- **`IpcSchedHyps` for `SRT … SRE`**, everything proved but the named
facts: `notQueued` (l4v `valid_sched`), the SchedContext steps of the
wake-up (`IpcWakeHyps`) and the receiver facts of `cancel_ipc`
(`CancelRecvHyp`). -/
theorem ipcSchedHyps_full (hP0 : IPlaced N T E R B)
    (hNQ : ∀ s σ (t : U64) (x : Fl4Spec.Tcb), IpcRel N T E R B (L.mem s) σ →
      SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ →
      σ.kheap t.bv = some (.tcb x) → Fl4Spec.runnable x.tcbState = false → NotQueued σ t.bv)
    (hW : IpcWakeHyps st ar th cr N T C E R B c)
    (hX : ∀ s σ (t : U64) (x : Fl4Spec.Tcb), IpcRel N T E R B (L.mem s) σ →
      SRT st th cr N T C E R B c (SRE st N T C E R B c) s σ → t ∈ T → σ.kheap t.bv = some (.tcb x) →
      Fl4Spec.receiveBlocked x.tcbState = true → CancelRecvHyp E (L.mem s) σ t x) :
    IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)) :=
  ipcSchedHyps_top hP0.e ⟨hNQ, fun s a σ t n x hR hS ht hn hk hx _ => wakeTail_top hP0 hW s a σ t n x hR hS ht hn hk hx,
    cancelIpc_top hP0 hX⟩

end Wake

end

end Fl4Proofs.P3.Ipc
