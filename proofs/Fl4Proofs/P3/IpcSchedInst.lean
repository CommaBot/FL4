/-
P3 (DESIGN.md §9), IPC: **instantiating `IpcSchedHyps`** with the scheduler
relation, `SR := SchedRel ∧ EpSchedApart` (`SRE`), and with `RelTopI`
(`SRT … SRE`, IpcTopFrame.lean).

* `stableN`, `block`: `SchedRel.stable` (SchedRel.lean).
* `stableE`: `SchedRel.stableE` (here): the endpoint code's words (`EWrite`)
  are none of the words `SchedRel` reads (`sagree_of_ewrite`: the node, the
  TCBs' scheduler fields, the domain words, the SC objects; the placement
  `EpSchedApart` keeps the endpoints, replies and buffer words apart from
  the node, the domain words and the SC objects), and an `EpStep` keeps what
  it reads of the spec (`SchedRel.of_sagreeE`).
* `scheduleTcb`: `schedule_tcb_refinesE`, `schedule_tcb_refines`
  (SchedTcb.lean) on the endpoint relation's state word
  (`schedulable_eqE`), keeping `IFoot` (the action word is outside it,
  `node_wr_ifoot`). For `RelTopI`, `relTopI_schedule_tcb`: the action word
  is a node word, apart from the slots (`IpcApart.node`).
* Not closed here (the fields of `IpcSchedRest`): `notQueued` (l4v
  `valid_sched`: a thread that is not runnable is in no ready or release
  queue, an invariant), `wakeTail` (the wake-up tail on `IFoot`/`IKView`:
  `maybe_donate_sched_context` and `unblock_sporadic`, the SchedContext
  steps of SchedNtfn's `WakeHyps`, with `possible_switch_to` keeping the
  merged footprint) and `cancelIpc` (the IPC cancel path, not yet proved).
-/
import Fl4Proofs.P3.IpcTopFrame
import Fl4Proofs.P3.SchedNtfn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

/-! ## The spec side of an endpoint step -/

section Spec
variable {σ σ' : Fl4Spec.State Unit}

theorem EpStep.abs (h : EpStep σ σ') :
    σ'.readyQueues = σ.readyQueues ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.curThread = σ.curThread ∧
    σ'.schedulerAction = σ.schedulerAction ∧ σ'.curSc = σ.curSc ∧ σ'.curTime = σ.curTime ∧
    σ'.consumedTime = σ.consumedTime ∧ σ'.reprogramTimer = σ.reprogramTimer ∧ σ'.curDomain = σ.curDomain ∧
    σ'.domainTime = σ.domainTime ∧ σ'.idleThread = σ.idleThread := by
  have e := h.2.1
  exact ⟨(by have := congrArg Fl4Spec.AbstractState.readyQueues e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.releaseQueue e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.curThread e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.schedulerAction e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.curSc e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.curTime e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.consumedTime e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.reprogramTimer e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.curDomain e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.domainTime e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.idleThread e; exact this)⟩

theorem EpStep.tcbSched (h : EpStep σ σ') {p : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap p = some (.tcb x)) : ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbDomain = x.tcbDomain ∧
      y.tcbSchedContext = x.tcbSchedContext ∧ y.tcbPriority = x.tcbPriority := by
  rcases h.2.2 p with e | ⟨a, b, ha, -⟩ | ⟨a, b, ha, -, -⟩ | ⟨a, b, ha, hb, e⟩
  · exact ⟨x, e.trans hk, rfl, rfl, rfl⟩
  · rw [hk] at ha; cases ha
  · rw [hk] at ha; cases ha
  · rw [hk] at ha; cases ha
    refine ⟨b, hb, ?_, ?_, ?_⟩ <;> rw [e]

theorem EpStep.sc (h : EpStep σ σ') {p : Fl4Spec.ObjRef} {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) : σ'.kheap p = some (.schedContext x n) := by
  rcases h.2.2 p with e | ⟨a, b, ha, -⟩ | ⟨a, b, ha, -, -⟩ | ⟨a, b, ha, -, -⟩
  · exact e.trans hk
  all_goals (rw [hk] at ha; cases ha)


/-- **A spec step the scheduler relation does not see**: the scheduler
fields of the abstract state kept, the TCBs' domain, SC and priority kept,
the SC objects kept and none created. -/
def SchedStep (σ σ' : Fl4Spec.State Unit) : Prop :=
  (σ'.readyQueues = σ.readyQueues ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.curThread = σ.curThread ∧
    σ'.schedulerAction = σ.schedulerAction ∧ σ'.curSc = σ.curSc ∧ σ'.curTime = σ.curTime ∧
    σ'.consumedTime = σ.consumedTime ∧ σ'.reprogramTimer = σ.reprogramTimer ∧ σ'.curDomain = σ.curDomain ∧
    σ'.domainTime = σ.domainTime ∧ σ'.idleThread = σ.idleThread) ∧
  (∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbDomain = x.tcbDomain ∧
      y.tcbSchedContext = x.tcbSchedContext ∧ y.tcbPriority = x.tcbPriority) ∧
  (∀ p x n, σ.kheap p = some (.schedContext x n) → σ'.kheap p = some (.schedContext x n)) ∧
  SzKeep σ σ'

theorem EpStep.schedStep (h : EpStep σ σ') : SchedStep σ σ' :=
  ⟨EpStep.abs h, fun _ _ hk => EpStep.tcbSched h hk, fun _ _ _ hk => EpStep.sc h hk, SzKeep.epStep h⟩

/-- Replacing a TCB by one with the same domain, SC and priority. -/
theorem SchedStep.updK_tcb {p : Fl4Spec.ObjRef} {x x' : Fl4Spec.Tcb} (hk : σ.kheap p = some (.tcb x))
    (h1 : x'.tcbDomain = x.tcbDomain) (h2 : x'.tcbSchedContext = x.tcbSchedContext)
    (h3 : x'.tcbPriority = x.tcbPriority) : SchedStep σ (updK σ p (.tcb x')) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun q y hq => ?_, fun q y n hq => ?_,
    SzKeep.updK hk (fun _ _ h => by cases h)⟩
  · by_cases e : q = p
    · subst e; rw [hk] at hq; cases hq
      exact ⟨x', by simp [updK], h1, h2, h3⟩
    · exact ⟨y, by simp [updK, e, hq], rfl, rfl, rfl⟩
  · have e : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    simp [updK, e, hq]

/-- `set_thread_state_act` keeps the caps and the domain schedule. -/
theorem stsAct_ckeep (σ : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) :
    CKeep σ (stsAct σ t) ∧ (stsAct σ t).domainList = σ.domainList ∧
      (stsAct σ t).domainStartIndex = σ.domainStartIndex := by
  unfold stsAct; split
  · exact ⟨CKeep.of_eq rfl rfl rfl, rfl, rfl⟩
  · exact ⟨CKeep.refl σ, rfl, rfl⟩

end Spec

/-! ## The placement and the stability under the endpoint code -/

section Stable
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **The endpoint subsystem's words apart from the scheduler's**: core
`c`'s node, the domain words and the SC objects hold no endpoint word. -/
structure EpSchedApart (st : machine.Store S) [L : LawfulStore st] (T C E R : Set U64)
    (B : Set (U64 × Fl4Spec.Word)) (c : U64) (s : S) (σ : Fl4Spec.State Unit) : Prop where
  node : ∀ a : U64, L.nodeBase s c ≤ a.val → a.val < L.nodeBase s c + 4288 → ¬ EFoot T E R B a
  dom : ¬ EWrite T E R B (curDomA st s)
  dt : ¬ EWrite T E R B (dtA st s)
  sc : ∀ sc ∈ C, ∀ x n, σ.kheap sc.bv = some (.schedContext x n) → ∀ a : U64, Fl4Proofs.P3.Sched.ScObj sc n a →
    ¬ EWrite T E R B a

theorem EpSchedApart.mono {s s' : S} {σ σ' : Fl4Spec.State Unit} (h : EpSchedApart st T C E R B c s σ)
    (hk : L.ksb s' = L.ksb s) (hz : SzKeep σ σ') : EpSchedApart st T C E R B c s' σ' := by
  have hnb : L.nodeBase s' c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hk]
  refine ⟨fun a h1 h2 => h.node a (hnb ▸ h1) (hnb ▸ h2), by rw [curDomA_ksb hk]; exact h.dom,
    by rw [dtA_ksb hk]; exact h.dt, fun sc hsc x n hx a ha => ?_⟩
  obtain ⟨x0, hx0⟩ := hz _ x n hx
  exact h.sc sc hsc x0 n hx0 a ha

/-- A scheduler field of a TCB is no endpoint word. -/
theorem tfield_not_ewrite (hP : EPlaced T E R B) {y K : U64} (hy : y ∈ T) (hK : SchedField K) :
    ¬ EWrite T E R B (core.num.U64.wrapping_add y K) := by
  have hya := hP.tcb y hy
  obtain ⟨h1, -, -⟩ := schedField_ok hK
  have hv := tfield_val hya h1
  have hK' : K.val = 3520 ∨ K.val = 3448 ∨ K.val = 3432 ∨ K.val = 3464 ∨ K.val = 3592 ∨ K.val = 3480 ∨
      K.val = 3488 := by
    rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rintro (⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, h | h⟩ | ⟨wp, hw, h⟩)
  · have := hP.et e he y hy; omega
  · have := hP.rt r hr y hy; omega
  · by_cases e : y = t
    · subst e; obtain ⟨-, h2⟩ := h; unfold TWOffN at h2; omega
    · have := tcb_disj hP ht hy e; have := h.tf.range; omega
  · by_cases e : y = t
    · subst e; unfold TL at h; omega
    · have := tcb_disj hP ht hy e; unfold TL at h; omega
  · have := hP.bt wp hw y hy; rw [← h] at this; omega

/-- Writes of the endpoint code keep what `SchedRel` reads. -/
theorem sagree_of_ewrite {s s' : S} {σ : Fl4Spec.State Unit} (hP : EPlaced T E R B)
    (hS : SchedRel st N T C c s σ) (hA : EpSchedApart st T C E R B c s σ) (hw : WritesIn st s s' (EWrite T E R B)) :
    SAgree st T C c s s' := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  refine ⟨hw.1, hw.2.1, fun o ho h8 _ _ => hw.mem_eq (nodeAt_aligned hc.node ho h8) fun hE => ?_,
    fun y hy K hK => ?_, hw.mem_eq ?_ hA.dom, hw.mem_eq ?_ hA.dt, fun sc hsc a ha hin => hw.mem_eq ha ?_⟩
  · have hv := nodeAt_val hc.node ho
    exact hA.node _ (by rw [hv]; omega) (by rw [hv]; omega) hE.foot
  · obtain ⟨h1, h2, -⟩ := schedField_ok hK
    exact hw.mem_eq (field_aligned (hc.tcbs y hy) h1 h2) (tfield_not_ewrite hP hy hK)
  · have h1 := hc.node.align
    have h2 := hc.node.fits
    unfold Aligned curDomA
    simp only [LawfulStore.nodeBase] at h1 h2
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    omega
  · have h1 := hc.node.align
    have h2 := hc.node.fits
    unfold Aligned dtA
    simp only [LawfulStore.nodeBase] at h1 h2
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    omega
  · obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
    exact hA.sc sc hsc x n hk a (hx.in_obj hin)

/-- **The scheduler relation from agreeing memory and a step it does not see.** -/
theorem _root_.Fl4Proofs.P3.Sched.SchedRel.of_sagreeE {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (ha : SAgree st T C c s s')
    (hact : nodeW st s' c layout.node.SCHED_ACTION = nodeW st s c layout.node.SCHED_ACTION)
    (hrp : nodeW st s' c layout.node.REPROGRAM = nodeW st s c layout.node.REPROGRAM)
    (hnw : ∀ o : U64, o.val < 4288 → ¬ NWrite N T (L.nodeAt s c o))
    (hdw : ¬ NWrite N T (curDomA st s)) (htw : ¬ NWrite N T (dtA st s))
    (hn : SchedStep σ σ') : SchedRel st N T C c s' σ' := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hs' := hs.agree ha
  obtain ⟨⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩, hnT, hnS, hnZ⟩ := hn
  refine ⟨hS.placed, fun o ho => by rw [Sched.nodeAt_ksb (st := st) ha.ksb]; exact hnw o ho,
    by rw [curDomA_ksb ha.ksb]; exact hdw, by rw [dtA_ksb ha.ksb]; exact htw,
    scOut_transfer ha.ksb hnZ hS.scOut,
    scDisj_transfer hnZ hS.scDisj, by rw [hact]; exact hS.actW,
    by rw [hact, e4]; exact hS.act, by rw [hrp, e8]; exact hS.repr, hs.core_eq ha.sc hS.core, Q, R0,
    hc.agree ha.toC, ?_⟩
  refine ⟨fun p hp => by rw [e1]; exact hs'.rq p hp, fun d p hd => by rw [e1]; exact hs'.rqDom d p hd,
    by rw [e2]; exact hs'.rel, by rw [e3]; exact hs'.curThread,
    by rw [e5]; exact hs'.curSc, by rw [e6]; exact hs'.curTime, by rw [e7]; exact hs'.consumed,
    by rw [e9]; exact hs'.curDom, fun t ht => ?_, hs'.scMem,
    fun sc hsc => ?_, hs'.idleSc, by rw [e10]; exact hs'.domTime, by rw [e11]; exact hs'.idleTh⟩
  · obtain ⟨x, hk, h1, h2, h3, h4⟩ := hs'.tcb t ht
    obtain ⟨y, hky, f1, f2, f3⟩ := hnT _ _ hk
    exact ⟨y, hky, f1.trans h1, h2, f2.trans h3, f3 ▸ h4⟩
  · obtain ⟨x, n, hk, e⟩ := hs'.scs sc hsc
    exact ⟨x, n, hnS _ _ _ hk, e⟩

/-- **The scheduler relation is kept by an endpoint step.** -/
theorem _root_.Fl4Proofs.P3.Sched.SchedRel.stableE {s s' : S} {σ σ' : Fl4Spec.State Unit} (hP : EPlaced T E R B)
    (hS : SchedRel st N T C c s σ) (hA : EpSchedApart st T C E R B c s σ)
    (hw : WritesIn st s s' (EWrite T E R B)) (hn : EpStep σ σ') : SchedRel st N T C c s' σ' := by
  have ha := sagree_of_ewrite hP hS hA hw
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hnode : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) :=
    fun o ho h8 => hw.mem_eq (nodeAt_aligned hc.node ho h8) fun hE => by
      have hv := nodeAt_val hc.node ho
      exact hA.node _ (by rw [hv]; omega) (by rw [hv]; omega) hE.foot
  refine hS.of_sagreeE ha ?_ ?_ hS.nodeNW hS.domNW hS.dtNW (EpStep.schedStep hn)
  · unfold Fl4Proofs.P3.Sched.nodeW; rw [Sched.nodeAt_ksb (st := st) hw.1]
    exact hnode _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  · unfold Fl4Proofs.P3.Sched.nodeW; rw [Sched.nodeAt_ksb (st := st) hw.1]
    exact hnode _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])

end Stable

/-! ## `schedule_tcb` on the endpoint relation -/

section Sched
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- `is_schedulable` is `schedulable`, from the endpoint relation's state
word. -/
theorem schedulable_eqE {s : S} {σ : Fl4Spec.State Unit}
    (hR : EpStateRel T E R B (L.mem s) σ) (hS : SchedRel st N T C c s σ) {t : U64} (ht : t ∈ T) :
    decide ((L.mem s (tStA t) = sched.TS_RUNNING ∨ L.mem s (tStA t) = sched.TS_RESTART ∨ L.mem s (tStA t) = sched.TS_RUNNING_VM) ∧
      L.mem s (scA t) ≠ 0#u64 ∧ L.rmax s (L.mem s (scA t)) > 0#u64 ∧
      (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) = Fl4Spec.schedulable t.bv σ := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨x, hk, h1, -, h3, -⟩ := hs.tcb t ht
  have hx := hR.at_tcb ht hk
  unfold Fl4Spec.schedulable
  apply decide_eq_decide.2
  have p1 : Fl4Spec.optPred (fun st => Fl4Spec.runnable st = true)
      (Fl4Spec.optMapSome (Fl4Spec.tcbsOf σ) Fl4Spec.Tcb.tcbState) t.bv ↔ Fl4Spec.runnable x.tcbState = true := by
    simp [Fl4Spec.optPred, Fl4Spec.optMapSome, Fl4Spec.optMap, Fl4Spec.tcbsOfKh, Fl4Spec.tcbOf, hk]
  have p3 : t.bv ∉ σ.releaseQueue ↔ (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    rw [hs.rel, mem_map_bv, ← not_iff_not, not_not, ← hc.released t ht]
  have p2 : Fl4Spec.optPred (fun sc => Fl4Spec.scActive sc = true)
      (Fl4Spec.optMap (Fl4Spec.optMap (Fl4Spec.tcbsOf σ) Fl4Spec.Tcb.tcbSchedContext) (Fl4Spec.scsOf σ)) t.bv ↔
      (L.mem s (scA t) ≠ 0#u64 ∧ L.rmax s (L.mem s (scA t)) > 0#u64) := by
    by_cases h0 : L.mem s (scA t) = 0#u64
    · rw [h0, optRef_zero] at h3
      simp [Fl4Spec.optPred, Fl4Spec.optMap, Fl4Spec.tcbsOfKh, Fl4Spec.tcbOf, hk, h3, h0]
    · rw [optRef_ne h0] at h3
      obtain ⟨y, n, hky, e⟩ := hs.scs _ (hs.scMem t ht h0)
      simp only [Fl4Spec.optPred, Fl4Spec.optMap, Fl4Spec.tcbsOfKh, Fl4Spec.tcbOf, hk, h3, Fl4Spec.scsOfKh,
        hky, Fl4Spec.scOf, Fl4Spec.scActive, Fl4Spec.activeSc, decide_eq_true_eq, ne_eq, h0, not_false_eq_true,
        true_and, gt_iff_val]
      rw [e.max]; simp
  rw [p1, p2, p3, ← runnable_iff hx.st]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, ⟨b, c⟩, d⟩, fun ⟨a, ⟨b, c⟩, d⟩ => ⟨a, b, c, d⟩⟩

/-- Writing a node word of core `c` keeps the merged footprint. -/
theorem node_wr_ifoot {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ)
    (hA : EpSchedApart st T C E R B c s σ) {o v : U64} (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    Agree (L.mem s) (L.mem (L.wr s (L.nodeAt s c o) v)) (IFoot N T E R B) := by
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  intro a ha hf
  refine rd_wr_ne (nodeAt_aligned hc.node ho h8) ha ?_
  rintro rfl
  have hv := nodeAt_val hc.node ho
  rcases hf with hE | ⟨n, hn, h1, h2⟩ | ⟨t, ht, e⟩
  · exact hA.node _ (by rw [hv]; omega) (by rw [hv]; omega) hE
  · exact hS.nodeNW o ho (Or.inl ⟨n, hn, h1, h2⟩)
  · exact nodeAt_ne_tfield hc.node ho ht (hc.tcbs t ht) (K := 3464#u64) (by simp) e

/-- **`schedule_tcb` refines `set_thread_state_act`** on the endpoint
relation (`schedule_tcb_refines` with `schedulable_eqE`), keeping the merged
footprint. -/
theorem schedule_tcb_refinesE (s : S) (σ : Fl4Spec.State Unit)
    (hR : EpStateRel T E R B (L.mem s) σ) (hS : SchedRel st N T C c s σ) (hA : EpSchedApart st T C E R B c s σ)
    (t : U64) (ht : t ∈ T) :
    sched.schedule_tcb st s t ⦃ s' => Agree (L.mem s) (L.mem s') (IFoot N T E R B) ∧
      SchedRel st N T C c s' (stsAct σ t.bv) ⦄ := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hcur := hc.cur
  have hsch := schedulable_eqE hR hS ht
  have ha := hS.act
  have hfoot0 : Agree (L.mem s) (L.mem s) (IFoot N T E R B) := fun _ _ _ => rfl
  unfold sched.schedule_tcb
  step
  step
  rw [t1_post, hcur] at b_post
  by_cases e1 : t = nodeW st s c layout.node.CUR_THREAD
  · have hb : b = true := b_post.2 e1
    simp only [hb, ↓reduceIte]
    step
    rw [i_post, hcur]
    by_cases e2 : nodeW st s c layout.node.SCHED_ACTION = sched.ACTION_RESUME_CURRENT
    · have hres : σ.schedulerAction = .resumeCurThread := by
        have e0 : sched.ACTION_RESUME_CURRENT = 0#u64 := by unfold sched.ACTION_RESUME_CURRENT; rfl
        rw [e2, e0] at ha
        cases h : σ.schedulerAction <;> rw [h] at ha <;> simp only [ActRel] at ha <;>
          first | rfl | exact absurd rfl ha.1 | exact absurd ha (by decide)
      simp only [e2, ↓reduceIte]
      step
      rw [hsch] at b1_post
      by_cases e3 : Fl4Spec.schedulable t.bv σ = true
      · simp only [b1_post, e3, ↓reduceIte, WP.spec_ok]
        refine ⟨hfoot0, ?_⟩
        rw [stsAct_eq_self (by intro h; exact h.2.2 e3)]; exact hS
      · simp only [b1_post, e3, Bool.false_eq_true, ↓reduceIte]
        step
        subst s'_post
        rw [hcur]
        have e4 : stsAct σ t.bv = { σ with schedulerAction := .chooseNewThread } := by
          unfold stsAct
          have h' : t.bv = σ.curThread ∧ σ.schedulerAction = .resumeCurThread ∧
            ¬ Fl4Spec.schedulable t.bv σ = true := ⟨by rw [hs.curThread, e1], hres, e3⟩
          split_ifs with hh
          · rfl
          · exact absurd h' hh
        have hch : sched.ACTION_CHOOSE_NEW = 1#u64 := by unfold sched.ACTION_CHOOSE_NEW; rfl
        rw [e4, hch]
        exact ⟨node_wr_ifoot hS hA (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]),
          hS.set_action (Or.inr (Or.inl rfl)) rfl⟩
    · simp only [e2, ↓reduceIte, WP.spec_ok]
      refine ⟨hfoot0, ?_⟩
      have hnr : σ.schedulerAction ≠ .resumeCurThread := by
        intro h; rw [h] at ha
        have e0 : sched.ACTION_RESUME_CURRENT = 0#u64 := by unfold sched.ACTION_RESUME_CURRENT; rfl
        exact e2 (by rw [e0]; exact ha)
      rw [stsAct_eq_self (by intro h; exact hnr h.2.1)]; exact hS
  · have hb : b = false := by
      cases b
      · rfl
      · exact absurd (b_post.1 rfl) e1
    simp only [hb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨hfoot0, ?_⟩
    rw [stsAct_eq_self (by intro h; exact bv_ne e1 (h.1.trans hs.curThread))]; exact hS

/-- `schedule_tcb` leaves the state or writes the action word. -/
theorem schedule_tcb_cases (s : S) (t : U64) :
    sched.schedule_tcb st s t ⦃ s' => s' = s ∨
      s' = L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) sched.ACTION_CHOOSE_NEW ⦄ := by
  unfold sched.schedule_tcb
  step with Sched.sched.cur_thread.spec' as ⟨t1, _ht1⟩
  step as ⟨b, _hb⟩
  split
  · step with Sched.sched.action.spec' as ⟨i, _hi⟩
    split
    · step with Sched.sched.is_schedulable.spec' as ⟨b1, _hb1⟩
      split
      · exact (WP.spec_ok _).mpr (Or.inl rfl)
      · exact WP.spec_mono (Sched.sched.set_action.spec' s _) fun s' h => Or.inr h
    · exact (WP.spec_ok _).mpr (Or.inl rfl)
  · exact (WP.spec_ok _).mpr (Or.inl rfl)

/-- **`schedule_tcb` keeps `RelTopI`**: it writes at most the action word of
core `c`'s node. -/
theorem relTopI_schedule_tcb (s : S) (σ : Fl4Spec.State Unit) (hS : SchedRel st N T C c s σ)
    (hT : RelTopI (L := L) th cr N T C E R B c s σ) (t : U64) :
    sched.schedule_tcb st s t ⦃ s' => RelTopI (L := L) th cr N T C E R B c s' (stsAct σ t.bv) ⦄ := by
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  obtain ⟨hK, hdl, hds⟩ := stsAct_ckeep σ t.bv
  refine WP.spec_mono (schedule_tcb_cases s t) ?_
  rintro s' (rfl | rfl)
  · exact hT.frameN (W := fun _ => False) (WritesIn.refl _ _) (fun _ h => h.elim) (fun _ h => h.elim) hK hdl hds
      (VsKeep.stsAct σ t.bv)
  · rw [hc.cur]
    have ho : (layout.node.SCHED_ACTION).val < 4288 := by simp [layout.node.SCHED_ACTION]
    have hv := nodeAt_val hc.node ho
    refine hT.frameN (writesIn_wr (nodeAt_aligned hc.node ho (by simp [layout.node.SCHED_ACTION])))
      (fun a ha => Or.inr ?_) (fun a ha => Or.inl ?_) hK hdl hds (VsKeep.stsAct σ t.bv)
    all_goals
      have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
      subst ha
      unfold NodeW; rw [hv, ← hnb]; omega

end Sched

/-! ## The instantiation -/

section Inst
variable {S A : Type} (st : machine.Store S) (ar : machine.Arch A) [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **The scheduler relation for the IPC proofs**: `SchedRel` with the
endpoint words apart from the scheduler's. -/
def SRE (N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  SchedRel st N T C c s σ ∧ EpSchedApart st T C E R B c s σ

/-- **The fields of `IpcSchedHyps` not closed by the scheduler relation**,
for a relation `SR` (see the module docstring). -/
structure IpcSchedRest (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (SR : S → Fl4Spec.State Unit → Prop) :
    Prop where
  notQueued : ∀ s σ (t : U64) (x : Fl4Spec.Tcb), IpcRel N T E R B (L.mem s) σ → SR s σ →
    σ.kheap t.bv = some (.tcb x) →
    Fl4Spec.runnable x.tcbState = false → NotQueued σ t.bv
  wakeTail : ∀ s (a : A) σ (t n : U64) (x : Fl4Spec.Tcb), IpcRel N T E R B (L.mem s) σ → SR s σ → t ∈ T →
    n ∈ N → σ.kheap t.bv = some (.tcb x) → x.tcbState = .running → NotQueued σ t.bv →
    rustWakeTail st ar s a t n ⦃ r => ¬ (specWakeTail t.bv n.bv σ).2 ∧ ∃ σ', ((), σ') ∈ (specWakeTail t.bv n.bv σ).1 ∧
      IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄
  cancelIpc : ∀ s (a : A) σ (t : U64) (x : Fl4Spec.Tcb), IpcRel N T E R B (L.mem s) σ → SR s σ → t ∈ T →
    σ.kheap t.bv = some (.tcb x) → Fl4Spec.receiveBlocked x.tcbState = true →
    ipc.cancel_ipc st ar s a t ⦃ r => ∃ σ' x', Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      IpcRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ∧ σ'.kheap t.bv = some (.tcb x') ∧ x'.tcbState = .inactive ∧
      RelIfBound σ' t.bv ⦄

variable {st ar}

/-- **`IpcSchedHyps` for the scheduler relation** `SRE`: the stabilities,
`block` and `scheduleTcb` proved, the rest (`IpcSchedRest`) given. -/
theorem ipcSchedHyps_sre (hP : EPlaced T E R B) (hX : IpcSchedRest st ar N T E R B (SRE st N T C E R B c)) :
    IpcSchedHyps st ar N T E R B (SRE st N T C E R B c) where
  stableN s s' σ σ' h hW hK _ := ⟨h.1.stable hW hK, h.2.mono hW.1 (SzKeep.ntfnStep hK)⟩
  stableE s s' σ σ' h hW hK := ⟨h.1.stableE hP h.2 hW hK, h.2.mono hW.1 (SzKeep.epStep hK)⟩
  notQueued := hX.notQueued
  block s s' σ σ' t h _ _ _ _ hW hK _ := ⟨h.1.stable hW hK, h.2.mono hW.1 (SzKeep.ntfnStep hK)⟩
  scheduleTcb s σ t hR _ h ht := by
    refine WP.spec_mono (WP.spec_and (schedule_tcb_refinesE s σ hR h.1 h.2 t ht) (schedule_tcb_cases s t)) ?_
    rintro s' ⟨⟨hF, hS'⟩, hc⟩
    refine ⟨hF, hS', h.2.mono ?_ (VsKeep.stsAct σ t.bv).2.2.2.2.2.1⟩
    rcases hc with rfl | rfl
    · rfl
    · exact L.ksb_wr _ _ _
  wakeTail := hX.wakeTail
  cancelIpc := hX.cancelIpc

/-- **`IpcSchedHyps` with the CSpace relation** (`SRT … SRE`): `RelTopI`
across `schedule_tcb` too; the rest given for `SRT`. -/
theorem ipcSchedHyps_top (hP : EPlaced T E R B)
    (hX : IpcSchedRest st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c))) :
    IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c (SRE st N T C E R B c)) where
  stableN s s' σ σ' h hW hK _ := ⟨h.1.stableN h.2.1.placed hW hK,
    h.2.1.stable hW hK, h.2.2.mono hW.1 (SzKeep.ntfnStep hK)⟩
  stableE s s' σ σ' h hW hK := ⟨h.1.stableE hW hK, h.2.1.stableE hP h.2.2 hW hK,
    h.2.2.mono hW.1 (SzKeep.epStep hK)⟩
  notQueued := hX.notQueued
  block s s' σ σ' t h _ _ _ _ hW hK _ := ⟨h.1.stableN h.2.1.placed hW hK,
    h.2.1.stable hW hK, h.2.2.mono hW.1 (SzKeep.ntfnStep hK)⟩
  scheduleTcb s σ t hR _ h ht := by
    refine WP.spec_mono (WP.spec_and (WP.spec_and (schedule_tcb_refinesE s σ hR h.2.1 h.2.2 t ht)
      (schedule_tcb_cases s t)) (relTopI_schedule_tcb s σ h.2.1 h.1 t)) ?_
    rintro s' ⟨⟨⟨hF, hS'⟩, hc⟩, hT'⟩
    refine ⟨hF, hT', hS', h.2.2.mono ?_ (VsKeep.stsAct σ t.bv).2.2.2.2.2.1⟩
    rcases hc with rfl | rfl
    · rfl
    · exact L.ksb_wr _ _ _
  wakeTail := hX.wakeTail
  cancelIpc := hX.cancelIpc

end Inst

end

end Fl4Proofs.P3.Ipc
