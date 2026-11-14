/-
P3 (DESIGN.md §9), scheduler: **the ready-queue operations refine l4v's**:
`sched::enqueue` ↔ `tcb_sched_action tcb_sched_enqueue`, `sched::append`
↔ `tcb_sched_action tcb_sched_append`, `sched::dequeue` ↔
`tcb_sched_action tcb_sched_dequeue`, on related states (`SchedRel`, and
the notification relation for the TCB's priority).

The FL4 side reuses P1: `enqueue.ready` / `dequeue.ready` /
`append.ready` (the ready queues and bitmap of the thread's core) and the
footprints `enqueue.foot` etc. (`QFoot`: `Sched` links of the queue, the
core's node words from offset 128, the thread's `IN_QUEUES`, the current
core's `IPI_PENDING`). `SchedRel.qstep` turns these into `SchedRel` for the
updated ghost list and the spec's `set_tcb_queue`.
-/
import Fl4Proofs.P3.SchedTcb
import Fl4Proofs.P1.QueueSchedInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- A word outside every TCB and outside core `c`'s node is not in a queue
footprint. -/
theorem not_qfoot_out {T : Set U64} {s : S} {W : List U64} {c t a : U64} {P : Nat → Prop} (hT : TcbPlaced T)
    (hW : ∀ w ∈ W, w ∈ T) (hN : NodePlaced st T s c) (hcur : L.cpu s = c) (ht : t ∈ T)
    (hat : ∀ y ∈ T, a.val < y.val ∨ y.val + 4096 ≤ a.val)
    (han : a.val < L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ a.val) : ¬ L.QFoot s W c P t a := by
  rintro (⟨w, hw, e | e⟩ | ⟨o, -, ho, -, e⟩ | e | ⟨o, -, ho, -, e⟩) <;> have hv := congrArg UScalar.val e
  · have := nextA_inside (hT w (hW w hw)) .Sched; have := hat w (hW w hw); omega
  · have := prevA_inside (hT w (hW w hw)) .Sched; have := hat w (hW w hw); omega
  · rw [nodeAt_val hN ho] at hv; omega
  · rw [inqA_val (hT t ht)] at hv; have := hat t ht; omega
  · rw [hcur, nodeAt_val hN ho] at hv; omega

theorem specPrio_inj {p q : U64} (hp : p.val < 256) (hq : q.val < 256) (h : specPrio p = specPrio q) : p = q := by
  apply UScalar.eq_of_val_eq
  have := congrArg BitVec.toNat h
  simp only [specPrio, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq] at this
  exact this

theorem specPrio_eq {p : U64} {x : Fl4Spec.Tcb} (h : p.val = x.tcbPriority.toNat) : specPrio p = x.tcbPriority := by
  apply BitVec.eq_of_toNat_eq
  simp only [specPrio, BitVec.toNat_ofNat, h]
  exact Nat.mod_eq_of_lt x.tcbPriority.isLt

/-- The spec's state with ready queue `(0, p)` set to `q` (l4v `set_tcb_queue`). -/
def setRq (σ : Fl4Spec.State Unit) (p : Fl4Spec.Priority) (q : List Fl4Spec.ObjRef) : Fl4Spec.State Unit :=
  { σ with readyQueues := fun d' p' => if d' = 0 ∧ p' = p then q else σ.readyQueues d' p' }

/-- One ready queue (of thread `t`'s priority) replaced: `SchedRel` holds
for the updated ghost list and the spec's `set_tcb_queue`. -/
theorem SchedRel.qstep {N T C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {Q : U64 → List U64} {R : List U64} (hc : SchedCore st T c s Q R)
    (hs : SchedSpec st T C c s Q R σ) {t : U64} (ht : t ∈ T) {W xs' : List U64} {tIn : Prop}
    (hW1 : ∀ w ∈ W, w = t ∨ w ∈ Q (L.mem s (prioA t))) (hWt : t ∈ W → t ∉ R)
    (hw : WritesIn st s s' (L.QFoot s W c (128 ≤ ·) t))
    (hRc : ReadyQueues st T s' c (Function.update Q (L.mem s (prioA t)) xs'))
    (hmem : ∀ y, y ∈ xs' ↔ (y = t ∧ tIn) ∨ (y ≠ t ∧ y ∈ Q (L.mem s (prioA t))))
    (hqq : (L.mem s' (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 ↔ tIn)
    (hqr : L.mem s' (inqA t) &&& sched.Q_RELEASE = L.mem s (inqA t) &&& sched.Q_RELEASE)
    (hnr : tIn → t ∉ R) :
    SchedRel st N T C c s' (setRq σ (specPrio (L.mem s (prioA t))) (xs'.map UScalar.bv)) := by
  set p := L.mem s (prioA t) with hpdef
  have hT := hc.tcbs
  have hN := hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hN
  have hp : p.val < 256 := hc.prio t ht
  have hW : ∀ w ∈ W, w ∈ T := fun w hw' => by
    rcases hW1 w hw' with rfl | hq
    · exact ht
    · exact ((hc.ready.1.rel p hp).mem w hq)
  have hk : L.ksb s' = L.ksb s := hw.1
  have haff : ∀ y ∈ T, L.mem s' (affA y) = L.mem s (affA y) := fun y hy => aff_qfoot hT hW hN hN' ht hw hy
  have hprio : ∀ y ∈ T, L.mem s' (prioA y) = L.mem s (prioA y) := fun y hy => prio_qfoot hT hW hN hN' ht hw hy
  have hinq : ∀ y ∈ T, y ≠ t → L.mem s' (inqA y) = L.mem s (inqA y) :=
    fun y hy hyt => inq_qfoot hT hW hN hN' ht hw hy hyt
  have hnode : ∀ o : U64, o.val < 128 → o.val % 8 = 0 → o.val ≠ 120 →
      nodeW st s' c o = nodeW st s c o := by
    intro o ho h8 h120
    unfold Fl4Proofs.P3.Sched.nodeW
    exact node_qfoot hT hW hN hN' ht hw hN (by omega) h8 (fun _ => by omega)
      (fun _ => h120)
  have hact : nodeW st s' c layout.node.SCHED_ACTION = nodeW st s c layout.node.SCHED_ACTION :=
    hnode _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  have hcd : L.mem s' (curDomA st s) = L.mem s (curDomA st s) := by
    have h2 := hN.fits
    have hv : (curDomA st s).val = (L.ksb s).val + 8 := by
      simp only [LawfulStore.nodeBase] at h2
      simp [curDomA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have hal : Aligned (curDomA st s) := by
      have h1 := hN.align
      unfold Aligned; rw [hv]; simp only [LawfulStore.nodeBase] at h1; omega
    refine hw.mem_eq hal (not_qfoot_out hT hW hN hc.cur ht (fun y hy => ?_) ?_)
    · have := hc.ksOut y hy; rw [hv]; omega
    · rw [hv]; simp only [LawfulStore.nodeBase]; omega
  have hmx : ∀ sc ∈ C, ScAgree st s s' sc := fun sc hsc a ha hin =>
    hw.mem_eq ha (not_qfoot_out hT hW hN hc.cur ht (hS.scOut sc hsc a hin).2.2.1 (hS.scOut sc hsc a hin).2.1)
  have hm := hs.rmax_eq hmx
  -- members of other queues and of the release queue are outside `W`
  have hWR : ∀ y ∈ R, y ∉ W := by
    intro y hy hyW
    rcases hW1 y hyW with rfl | hq
    · exact hWt hyW hy
    · have hyT := (hc.ready.1.rel p hp).mem y hq
      exact hc.excl y hyT (by rw [hc.inQ p hp y hq]; exact hq) hy
  have hupd : ∀ p' y, y ∈ Function.update Q p xs' p' ↔ (p' = p ∧ y ∈ xs') ∨ (p' ≠ p ∧ y ∈ Q p') := by
    intro p' y
    by_cases e : p' = p
    · subst e; simp
    · simp [e]
  have hcore : SchedCore st T c s' (Function.update Q p xs') R := by
    refine ⟨hT, nodePlaced_ksb hN hk, hw.2.1.trans hc.cur, fun y hy => (haff y hy).trans (hc.aff y hy),
      fun y hy => (hprio y hy) ▸ hc.prio y hy, hRc, ?_, fun p' hp' y hy => ?_, fun y hy => ?_,
      fun y hy => ?_, fun y hy hq => ?_, ?_, ?_, by rw [hk]; exact hc.ksOut⟩
    · rw [relQ_qfoot hT hW hN hN' ht hw hN (fun _ => by omega)]
      exact hc.release.qfoot hT hW hN hN' ht hw (fun _ => hWR)
    · rcases (hupd p' y).1 hy with ⟨rfl, hy'⟩ | ⟨-, hy'⟩
      · rcases (hmem y).1 hy' with ⟨rfl, -⟩ | ⟨-, hq⟩
        · exact hprio y ht
        · exact (hprio y ((hc.ready.1.rel _ hp).mem y hq)).trans (hc.inQ _ hp y hq)
      · exact (hprio y ((hc.ready.1.rel p' hp').mem y hy')).trans (hc.inQ p' hp' y hy')
    · rw [hprio y hy]
      by_cases e : y = t
      · subst e
        rw [hqq, ← hpdef, Function.update_self, hmem]
        simp
      · rw [hinq y hy e, hc.queued y hy, hupd]
        constructor
        · intro hq
          by_cases e2 : L.mem s (prioA y) = p
          · exact Or.inl ⟨e2, (hmem y).2 (Or.inr ⟨e, e2 ▸ hq⟩)⟩
          · exact Or.inr ⟨e2, hq⟩
        · rintro (⟨e3, hq⟩ | ⟨-, hq⟩)
          · rcases (hmem y).1 hq with ⟨e5, -⟩ | ⟨-, hq'⟩
            · exact absurd e5 e
            · rw [e3]; exact hq'
          · exact hq
    · by_cases e : y = t
      · subst e; rw [hqr]; exact hc.released y hy
      · rw [hinq y hy e]; exact hc.released y hy
    · rw [hprio y hy] at hq
      rcases (hupd _ y).1 hq with ⟨e3, hq'⟩ | ⟨-, hq'⟩
      · rcases (hmem y).1 hq' with ⟨rfl, hin⟩ | ⟨-, hq''⟩
        · exact hnr hin
        · exact hc.excl y hy (by rw [e3]; exact hq'')
      · exact hc.excl y hy hq'
    · rw [hnode _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
        (by simp [layout.node.CUR_THREAD])]; exact hc.curT
    · rw [hnode _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])
        (by simp [layout.node.IDLE_THREAD])]; exact hc.idleT
  refine ⟨hS.placed, fun o ho => by rw [nodeAt_ksb hk]; exact hS.nodeNW o ho,
    by rw [curDomA_ksb hk]; exact hS.domNW, scOut_transfer hk hm hS.scOut, scDisj_transfer hm hS.scDisj,
    by rw [hact]; exact hS.actW,
    by rw [hact]; exact hS.act, by rw [hnode _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
      (by simp [layout.node.REPROGRAM])]; exact hS.repr, hs.core_eq hmx hS.core, Function.update Q p xs', R, hcore, ?_⟩
  refine ⟨fun p' hp' => ?_, fun d p' hd => ?_, hs.rel, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_, fun y hy => ?_,
    fun sc hsc => ?_⟩
  · show (if (0 : Fl4Spec.Domain) = 0 ∧ specPrio p' = specPrio p then _ else _) = _
    by_cases e : p' = p
    · subst e; simp
    · have : specPrio p' ≠ specPrio p := fun h => e (specPrio_inj hp' hp h)
      simp only [true_and, this, ↓reduceIte, Function.update_of_ne e]
      exact hs.rq p' hp'
  · show (if d = 0 ∧ p' = specPrio p then _ else _) = _
    simp only [hd, false_and, ↓reduceIte]; exact hs.rqDom d p' hd
  · rw [hnode _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD])]; exact hs.curThread
  · rw [hnode _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])]
    exact hs.curSc
  · rw [hnode _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])]
    exact hs.curTime
  · rw [hnode _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])]
    exact hs.consumed
  · rw [curDomA_ksb hk, hcd]; exact hs.curDom
  · obtain ⟨x, hkx, h1, h2, h3, h4⟩ := hs.tcb y hy
    have ed : L.mem s' (domA y) = L.mem s (domA y) :=
      field_qfoot hT hW hN hN' ht hw hy (K := 3432#u64) (by simp) (by simp) (by simp) (fun _ => by simp)
    have es : L.mem s' (scA y) = L.mem s (scA y) :=
      field_qfoot hT hW hN hN' ht hw hy (K := 3464#u64) (by simp) (by simp) (by simp) (fun _ => by simp)
    exact ⟨x, hkx, h1, by rw [ed]; exact h2, by rw [es]; exact h3, by rw [hprio y hy]; exact h4⟩
  · have es : L.mem s' (scA y) = L.mem s (scA y) :=
      field_qfoot hT hW hN hN' ht hw hy (K := 3464#u64) (by simp) (by simp) (by simp) (fun _ => by simp)
    rw [es]; exact hs.scMem y hy
  · obtain ⟨x, n, hkx, e⟩ := hs.scs sc hsc
    exact ⟨x, n, hkx, e.agree (hmx sc hsc)⟩

/-! ## The footprint of a queue operation is outside the notification footprint -/

theorem qfoot_footEq {N T C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {Q : U64 → List U64} {R : List U64} (hc : SchedCore st T c s Q R)
    {W : List U64} {t : U64} (ht : t ∈ T) (hW : ∀ w ∈ W, w ∈ T) {P : Nat → Prop}
    (hw : WritesIn st s s' (L.QFoot s W c P t)) : FootEq N T (L.mem s) (L.mem s') := by
  have hP := hS.placed
  have hT := hc.tcbs
  have hN := hc.node
  intro a ha hf
  refine hw.mem_eq ha ?_
  -- a TCB field of the footprint
  have tf : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → (K = 3480#u64 ∨ K = 3488#u64 ∨ K = 3592#u64) →
      a ≠ core.num.U64.wrapping_add y K := by
    intro y hy K hK hKs e
    subst e
    rcases hf with ⟨n, hn, h1, h2⟩ | ⟨z, hz, e | e | e | e | e | e⟩
    · rw [tfield_val (hT y hy) hK] at h1 h2
      have := hP.disj n hn y hy; omega
    all_goals first
      | (rw [tStA_eq, tt_eq_iff (hT y hy) (hT z hz) hK (by simp)] at e;
          rcases hKs with rfl | rfl | rfl <;> simp at e)
      | (rw [tBlockA_eq, tt_eq_iff (hT y hy) (hT z hz) hK (by simp)] at e;
          rcases hKs with rfl | rfl | rfl <;> simp at e)
      | (rw [badgeRegA_eq, tt_eq_iff (hT y hy) (hT z hz) hK (by simp)] at e;
          rcases hKs with rfl | rfl | rfl <;> simp at e)
      | (rw [prioA_eq', tt_eq_iff (hT y hy) (hT z hz) hK (by simp)] at e;
          rcases hKs with rfl | rfl | rfl <;> simp at e)
      | (rw [nextEp_eq, tt_eq_iff (hT y hy) (hT z hz) hK (by simp)] at e;
          rcases hKs with rfl | rfl | rfl <;> simp at e)
      | (rw [prevEp_eq, tt_eq_iff (hT y hy) (hT z hz) hK (by simp)] at e;
          rcases hKs with rfl | rfl | rfl <;> simp at e)
  -- a node word
  have nw : ∀ o : U64, o.val < 4288 → a ≠ L.nodeAt s c o := by
    intro o ho e
    subst e
    rcases hf with hf | ⟨z, hz, e | e | e | e | e | e⟩
    · exact hS.nodeNW o ho (Or.inl hf)
    · exact hS.nodeNW o ho (Or.inr ⟨z, hz, Or.inl e⟩)
    · exact hS.nodeNW o ho (Or.inr ⟨z, hz, Or.inr (Or.inl e)⟩)
    · exact hS.nodeNW o ho (Or.inr ⟨z, hz, Or.inr (Or.inr (Or.inl e))⟩)
    · exact nodeAt_ne_tfield hN ho hz (hT z hz) (K := 3448#u64) (by simp) e
    · exact hS.nodeNW o ho (Or.inr ⟨z, hz, Or.inr (Or.inr (Or.inr (Or.inl e)))⟩)
    · exact hS.nodeNW o ho (Or.inr ⟨z, hz, Or.inr (Or.inr (Or.inr (Or.inr e)))⟩)
  rintro (⟨w, hw', e | e⟩ | ⟨o, -, ho, -, e⟩ | e | ⟨o, -, ho, -, e⟩)
  · exact tf w (hW w hw') _ (by simp) (Or.inl rfl) e
  · exact tf w (hW w hw') _ (by simp) (Or.inr (Or.inl rfl)) e
  · exact nw o ho e
  · exact tf t ht _ (by simp) (Or.inr (Or.inr rfl)) e
  · rw [hc.cur] at e; exact nw o ho e

/-! ## The spec's `tcb_sched_action` -/

theorem tcbSchedAction_eq {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hd : x.tcbDomain = 0) (f : Fl4Spec.ObjRef → List Fl4Spec.ObjRef → List Fl4Spec.ObjRef) :
    Fl4Spec.tcbSchedAction (Z := Unit) f t σ =
      ({((), setRq σ x.tcbPriority (f t (σ.readyQueues 0 x.tcbPriority)))}, False) := by
  unfold Fl4Spec.tcbSchedAction
  rw [nd_bind_one (threadGet_eq _ hk), nd_bind_one (threadGet_eq _ hk)]
  unfold Fl4Spec.getTcbQueue
  rw [nd_bind_one (nd_bind_one (show (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.readyQueues) σ =
    ({(σ.readyQueues, σ)}, False) from rfl) _), nd_pure_bind']
  simp only [hd]
  rfl

/-! ## `enqueue` and `dequeue` -/

/-- **`enqueue` refines `tcb_sched_action tcb_sched_enqueue`**, for a thread
that is queued already or not in the release queue (seL4's precondition). -/
theorem enqueue_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (t : U64) (ht : t ∈ T)
    (hr : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    sched.enqueue st s t ⦃ s' => ∃ σ', Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedEnqueue t.bv σ =
      ({((), σ')}, False) ∧ σ'.kheap = σ.kheap ∧ σ'.releaseQueue = σ.releaseQueue ∧
      FootEq N T (L.mem s) (L.mem s') ∧ SchedRel st N T C c s' σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hp := hc.prio t ht
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hR1 : ReadyQueues st T s (L.mem s (affA t)) Q := by rw [haf]; exact hc.ready
  have hnq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 → ∀ p : U64, p.val < 256 → t ∉ Q p := by
    intro h0 p hp' hm
    have e := hc.inQ p hp' t hm
    exact ((hc.queued t ht).2 (by rw [e]; exact hm)) h0
  obtain ⟨x, hk, hd, -, -, hpr⟩ := hs.tcb t ht
  have h1 := sched.enqueue.ready s t Q hT ht hp hN hN' hR1 hnq
  have h2 := sched.enqueue.foot s t _ hT ht hp hN hN' (hR1.1.rel _ hp) (fun h0 => hnq h0 _ hp)
  refine WP.spec_mono (WP.spec_and h1 h2) ?_
  rintro s' ⟨hRc, hw, hinq⟩
  rw [haf] at hRc hw
  have hW : ∀ w ∈ t :: Q (L.mem s (prioA t)), w ∈ T := by
    intro w hw'; rcases List.mem_cons.1 hw' with rfl | hw'
    · exact ht
    · exact (hc.ready.1.rel _ hp).mem w hw'
  have hspec := tcbSchedAction_eq hk hd Fl4Spec.tcbSchedEnqueue
  rw [← specPrio_eq hpr, hs.rq _ hp] at hspec
  by_cases hqd : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
  · simp only [hqd, ne_eq, not_false_eq_true, ↓reduceIte] at hRc hinq
    have htq := (hc.queued t ht).1 hqd
    have hst := hS.qstep hc hs ht (W := t :: Q _) (xs' := Q (L.mem s (prioA t))) (tIn := True)
      (fun w hw => List.mem_cons.1 hw) (fun _ => hc.excl t ht htq) hw (by rw [Function.update_eq_self]; exact hRc)
      (fun y => by by_cases e : y = t <;> simp [e, htq]) (by rw [hinq]; simpa using hqd) (by rw [hinq])
      (fun _ => hc.excl t ht htq)
    refine ⟨_, hspec, rfl, rfl, qfoot_footEq hS hc ht hW hw, ?_⟩
    have : Fl4Spec.tcbSchedEnqueue t.bv ((Q (L.mem s (prioA t))).map UScalar.bv) = (Q (L.mem s (prioA t))).map UScalar.bv := by
      unfold Fl4Spec.tcbSchedEnqueue; rw [ite_f (by rw [not_not, mem_map_bv]; exact htq)]
    rw [this]; exact hst
  · have hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := not_not.1 hqd
    simp only [hqd, ↓reduceIte] at hRc hinq
    have htq := hnq hq0 _ hp
    have hnr : t ∉ R := fun hm => ((hc.released t ht).2 hm) (hr hq0)
    have hst := hS.qstep hc hs ht (W := t :: Q _) (xs' := t :: Q (L.mem s (prioA t))) (tIn := True)
      (fun w hw => List.mem_cons.1 hw) (fun _ => hnr) hw hRc
      (fun y => by by_cases e : y = t <;> simp [e])
      (by rw [hinq, or_qq_qq]; simp) (by rw [hinq, or_qq_qr]) (fun _ => hnr)
    refine ⟨_, hspec, rfl, rfl, qfoot_footEq hS hc ht hW hw, ?_⟩
    have : Fl4Spec.tcbSchedEnqueue t.bv ((Q (L.mem s (prioA t))).map UScalar.bv) =
        (t :: Q (L.mem s (prioA t))).map UScalar.bv := by
      unfold Fl4Spec.tcbSchedEnqueue; rw [ite_t (by rw [mem_map_bv]; exact htq)]; rfl
    rw [this]; exact hst

/-- **`dequeue` refines `tcb_sched_action tcb_sched_dequeue`**. -/
theorem dequeue_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (t : U64) (ht : t ∈ T) :
    sched.dequeue st s t ⦃ s' => ∃ σ', Fl4Spec.tcbSchedAction (Z := Unit) Fl4Spec.tcbSchedDequeue t.bv σ =
      ({((), σ')}, False) ∧ σ'.kheap = σ.kheap ∧ σ'.releaseQueue = σ.releaseQueue ∧
      FootEq N T (L.mem s) (L.mem s') ∧ SchedRel st N T C c s' σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hp := hc.prio t ht
  have haf := hc.aff t ht
  have hN : NodePlaced st T s (L.mem s (affA t)) := by rw [haf]; exact hc.node
  have hN' : NodePlaced st T s (L.cpu s) := by rw [hc.cur]; exact hc.node
  have hR1 : ReadyQueues st T s (L.mem s (affA t)) Q := by rw [haf]; exact hc.ready
  have hq : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 → t ∈ Q (L.mem s (prioA t)) := (hc.queued t ht).1
  obtain ⟨x, hk, hd, -, -, hpr⟩ := hs.tcb t ht
  have h1 := sched.dequeue.ready s t Q hT ht hp hN hR1 hq
  have h2 := sched.dequeue.foot s t _ hT ht hp hN hN' (hR1.1.rel _ hp) hq
  refine WP.spec_mono (WP.spec_and h1 h2) ?_
  rintro s' ⟨hRc, hw, hinq⟩
  rw [haf] at hRc hw
  have hQT : ∀ w ∈ Q (L.mem s (prioA t)), w ∈ T := fun w hw' => (hc.ready.1.rel _ hp).mem w hw'
  have hnd := (hc.ready.1.rel _ hp).nodup
  have hspec := tcbSchedAction_eq hk hd Fl4Spec.tcbSchedDequeue
  rw [← specPrio_eq hpr, hs.rq _ hp] at hspec
  have hdeq : Fl4Spec.tcbSchedDequeue t.bv ((Q (L.mem s (prioA t))).map UScalar.bv) =
      ((Q (L.mem s (prioA t))).erase t).map UScalar.bv := removeAll_map hnd t
  rw [hdeq] at hspec
  by_cases hqd : (L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64
  · simp only [hqd, ne_eq, not_false_eq_true, ↓reduceIte] at hRc hinq
    have htq := hq hqd
    have hst := hS.qstep hc hs ht (W := Q _) (xs' := (Q (L.mem s (prioA t))).erase t) (tIn := False)
      (fun w hw => Or.inr hw) (fun _ => hc.excl t ht htq) hw hRc
      (fun y => by
        by_cases e : y = t
        · subst e; simp [hnd.not_mem_erase]
        · simp [e, List.mem_erase_of_ne e])
      (by rw [hinq, andn_qq_qq]; simp) (by rw [hinq, andn_qq_qr]) (fun h => h.elim)
    exact ⟨_, hspec, rfl, rfl, qfoot_footEq hS hc ht hQT hw, hst⟩
  · have hq0 : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := not_not.1 hqd
    simp only [hqd, ↓reduceIte] at hRc hinq
    have htq : t ∉ Q (L.mem s (prioA t)) := fun hm => ((hc.queued t ht).2 hm) hq0
    have e : (Q (L.mem s (prioA t))).erase t = Q (L.mem s (prioA t)) := List.erase_of_not_mem htq
    rw [e] at hspec
    have hst := hS.qstep hc hs ht (W := Q _) (xs' := Q (L.mem s (prioA t))) (tIn := False)
      (fun w hw => Or.inr hw) (fun h => absurd h htq) hw (by rw [Function.update_eq_self]; exact hRc)
      (fun y => by by_cases e : y = t <;> simp [e, htq])
      (by rw [hinq]; exact ⟨fun h => h hq0, False.elim⟩) (by rw [hinq]) (fun h => h.elim)
    exact ⟨_, hspec, rfl, rfl, qfoot_footEq hS hc ht hQT hw, hst⟩

end

end

end Fl4Proofs.P3.Sched
