/-
P3 (DESIGN.md §9), scheduling contexts: **`switch_sched_context` refines
l4v `switch_sched_context`** (`switch_sched_context_refines`): on a change
of SC, `refill_unblock_check` of the incoming one (constant bandwidth), then
`commit_time` of the outgoing one if the timer is to be reprogrammed, then
the incoming SC becomes current. It keeps the full `Inv` under `OffOK`.
-/
import Fl4Proofs.P3.ScOffset
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- Writing the node's `CUR_SC` word. -/
theorem SchedRel.set_node_cursc {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (v : U64) :
    SchedRel st N T C c (L.wr s (L.nodeAt s c layout.node.CUR_SC) v) { σ with curSc := v.bv } ∧
      FootEq N T (L.mem s) (L.mem (L.wr s (L.nodeAt s c layout.node.CUR_SC) v)) ∧
      ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 24 →
        nodeW st (L.wr s (L.nodeAt s c layout.node.CUR_SC) v) c o = nodeW st s c o := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN := hc.node
  have h24 : layout.node.CUR_SC.val = 24 := by simp [layout.node.CUR_SC]
  have hA : Aligned (L.nodeAt s c layout.node.CUR_SC) := nodeAt_aligned hN (by omega) (by omega)
  set s' := L.wr s (L.nodeAt s c layout.node.CUR_SC) v
  have hk : L.ksb s' = L.ksb s := L.ksb_wr _ _ _
  have hne : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 24 →
      L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) := by
    intro o ho h8 hne
    refine rd_wr_ne hA (nodeAt_aligned hN ho h8) fun e => hne ?_
    have := congrArg UScalar.val e
    rw [nodeAt_val hN (by omega), nodeAt_val hN ho] at this; omega
  have nw : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 24 → nodeW st s' c o = nodeW st s c o := by
    intro o ho h8 h; unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hk]; exact hne o ho h8 h
  have htf : ∀ y ∈ T, ∀ K, SchedField K →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK
    obtain ⟨h1, h2, -⟩ := schedField_ok hK
    exact rd_wr_ne hA (field_aligned (hc.tcbs y hy) h1 h2) (nodeAt_ne_tfield hN (by omega) hy (hc.tcbs y hy) h1)
  have hdom : L.mem s' (curDomA st s) = L.mem s (curDomA st s) := by
    refine rd_wr_ne hA (curDomA_aligned hN) fun e => ?_
    have := congrArg UScalar.val e
    rw [nodeAt_val hN (by omega), curDomA_val hN] at this
    simp only [LawfulStore.nodeBase] at this; omega
  have hscw : ∀ sc ∈ C, ScAgree st s s' sc := by
    intro sc hsc a hal hin
    refine rd_wr_ne hA hal fun e => ?_
    have := congrArg UScalar.val e
    rw [nodeAt_val hN (by omega)] at this
    have := (hS.scOutIn hsc hin).2.1; omega
  have hca : CAgree st T c s s' := ⟨hk, L.cpu_wr _ _ _, fun o ho h8 _ _ _ _ h _ _ => hne o ho h8 h,
    fun y hy K hK => htf y hy K (by rcases hK with h | h | h | h | h <;> simp [SchedField, h])⟩
  have hm := hs.rmax_eq hscw
  refine ⟨⟨hS.placed, fun o ho => by rw [nodeAt_ksb hk]; exact hS.nodeNW o ho,
    by rw [curDomA_ksb hk]; exact hS.domNW, by rw [dtA_ksb hk]; exact hS.dtNW,
    scOut_transfer hk (SzKeep.of_kheap rfl) hS.scOut, scDisj_transfer (SzKeep.of_kheap rfl) hS.scDisj,
    by rw [nw _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION])]; exact hS.actW,
    by rw [nw _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION])]; exact hS.act,
    by rw [nw _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
      (by simp [layout.node.REPROGRAM])]; exact hS.repr,
    hs.core_eq hscw hS.core, Q, R, hc.agree hca, ?_⟩, node_wr_foot hS (by omega) (by omega), nw⟩
  refine ⟨hs.rq, hs.rqDom, hs.rel, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_, fun y hy => ?_, fun sc hsc => ?_,
    by rw [nw layout.node.IDLE_SC (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC])]; exact hs.idleSc,
    by rw [dtA_ksb hk, dt_wr_node hN (by omega) (by omega)]; exact hs.domTime,
    by rw [nw layout.node.IDLE_THREAD (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])]; exact hs.idleTh⟩
  · rw [nw layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD])]; exact hs.curThread
  · show v.bv = _
    unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hk, rd_wr_eq hA]
  · rw [nw layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      (by simp [layout.node.CUR_TIME])]; exact hs.curTime
  · rw [nw layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
      (by simp [layout.node.CONSUMED])]; exact hs.consumed
  · rw [curDomA_ksb hk, hdom]; exact hs.curDom
  · obtain ⟨x, hkx, h1, h2, h3, h4⟩ := hs.tcb y hy
    have e1 : L.mem s' (domA y) = L.mem s (domA y) := htf y hy _ (by simp [SchedField])
    have e2 : L.mem s' (scA y) = L.mem s (scA y) := htf y hy _ (by simp [SchedField])
    have e3 : L.mem s' (prioA y) = L.mem s (prioA y) := htf y hy _ (by simp [SchedField])
    exact ⟨x, hkx, h1, by rw [e1]; exact h2, by rw [e2]; exact h3, by rw [e3]; exact h4⟩
  · have e2 : L.mem s' (scA y) = L.mem s (scA y) := htf y hy _ (by simp [SchedField])
    rw [e2]; exact hs.scMem y hy
  · obtain ⟨x, n, hkx, e⟩ := hs.scs sc hsc
    exact ⟨x, n, hkx, e.agree (hscw sc hsc)⟩

@[step] theorem obj.Sc.sporadic.spec' (s : S) (sc : obj.Sc) :
    obj.Sc.sporadic st sc s ⦃ v => v = L.mem s (scW sc 64#u64) ⦄ := by
  unfold obj.Sc.sporadic; step*; simp_all [scW, layout.sc.SPORADIC]

theorem sc_constant_bandwidth_spec (s : S) (sc : obj.Sc) :
    sporadic.sc_constant_bandwidth st s sc ⦃ b => b = decide (L.mem s (scW sc 64#u64) = 0#u64) ⦄ := by
  unfold sporadic.sc_constant_bandwidth
  step with obj.Sc.sporadic.spec' as ⟨i, hi⟩
  simp [hi]

end

section Spec
open Fl4Spec

theorem ifCB_eq {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) :
    ifConstantBandwidthRefillUnblockCheck (Z := Unit) (some p) σ =
      (if x.scSporadic = false then refillUnblockCheck p σ else ({((), σ)}, False)) := by
  unfold ifConstantBandwidthRefillUnblockCheck ifCondRefillUnblockCheck
  simp only [NonDet.maybeM]
  rw [nd_bind_one (getSchedContext_eq hk), nd_gets_bind, nd_pure_bind']
  simp only [NonDet.when]
  cases x.scSporadic <;> simp <;> rfl

/-- TCBs are kept, SCs keep their size and refill max, and the idle thread and
the scheduler action are kept. -/
def SwKeep (σ σ' : State Unit) : Prop :=
  (∀ q x, σ.kheap q = some (.tcb x) → σ'.kheap q = some (.tcb x)) ∧
  (∀ q y0 m, σ.kheap q = some (.schedContext y0 m) → ∃ y, σ'.kheap q = some (.schedContext y m) ∧
    y.scRefillMax = y0.scRefillMax) ∧ σ'.idleThread = σ.idleThread ∧ σ'.schedulerAction = σ.schedulerAction

theorem SwKeep.refl (σ : State Unit) : SwKeep σ σ := ⟨fun _ _ h => h, fun _ y0 _ h => ⟨y0, h, rfl⟩, rfl, rfl⟩

theorem SwKeep.trans {σ₁ σ₂ σ₃ : State Unit} (h₁ : SwKeep σ₁ σ₂) (h₂ : SwKeep σ₂ σ₃) : SwKeep σ₁ σ₃ :=
  ⟨fun q x h => h₂.1 q x (h₁.1 q x h), fun q y0 m h => by
    obtain ⟨y1, h1, e1⟩ := h₁.2.1 q y0 m h
    obtain ⟨y2, h2, e2⟩ := h₂.2.1 q y1 m h1
    exact ⟨y2, h2, e2.trans e1⟩, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem SwKeep.of_kheap {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) (hi : σ'.idleThread = σ.idleThread)
    (ha : σ'.schedulerAction = σ.schedulerAction) : SwKeep σ σ' :=
  ⟨fun q x hq => by rw [h]; exact hq, fun q y0 m hq => ⟨y0, by rw [h]; exact hq, rfl⟩, hi, ha⟩

/-- **`ActIdle` under `SwKeep`**, with the release queue and the action kept. -/
theorem ActIdle.swKeep {σ σ' : State Unit} (h : ActIdle σ) (hk : SwKeep σ σ')
    (hr : σ'.releaseQueue = σ.releaseQueue)
    (ha : σ'.schedulerAction = σ.schedulerAction ∨ ∀ t, σ'.schedulerAction ≠ .switchThread t) : ActIdle σ' :=
  h.keep ⟨fun q x _ hq => hk.1 q x hq, fun q y0 m hq => by
    obtain ⟨y, h1, h2⟩ := hk.2.1 q y0 m hq
    exact ⟨y, h1, by unfold scActive activeSc; rw [h2]⟩⟩ (fun u hu => by rw [hr] at hu; exact hu) ha hk.2.2.1

theorem IdleOK.swKeep {σ σ' : State Unit} (h : IdleOK σ) (hk : SwKeep σ σ')
    (hr : σ'.releaseQueue = σ.releaseQueue) : IdleOK σ' := by
  obtain ⟨x, h1, h2, h3, h4⟩ := h
  exact ⟨x, by rw [hk.2.2.1]; exact hk.1 _ _ h1, h2, h3, by rw [hk.2.2.1, hr]; exact h4⟩

theorem SwKeep.of_headKeeps {σ σ' : State Unit} {p : ObjRef} (h : HeadKeeps σ σ' p)
    (hp : ∃ y n, σ.kheap p = some (.schedContext y n)) : SwKeep σ σ' := by
  obtain ⟨-, -, -, hact, -, hid, -, hfr, hsc⟩ := h
  refine ⟨fun q x hq => ?_, fun q y0 m hq => ?_, hid, hact⟩
  · have : q ≠ p := by
      rintro rfl; obtain ⟨y, n, hy⟩ := hp; rw [hq] at hy; cases hy
    rw [hfr _ this]; exact hq
  · by_cases e : q = p
    · subst e; obtain ⟨y, h1, -, h3⟩ := hsc y0 m hq; exact ⟨y, h1, h3⟩
    · exact ⟨y0, by rw [hfr _ e]; exact hq, rfl⟩

/-- What `refill_unblock_check` of `p` keeps. -/
theorem unblock_keeps {σ σ' : State Unit} {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills ≠ [])
    (h : refillUnblockCheck (Z := Unit) p σ = ({((), σ')}, False)) :
    σ'.curSc = σ.curSc ∧ σ'.curThread = σ.curThread ∧ σ'.releaseQueue = σ.releaseQueue ∧
      σ'.curTime = σ.curTime ∧ σ'.consumedTime = σ.consumedTime ∧ σ'.readyQueues = σ.readyQueues ∧
      (∀ q, q ≠ p → σ'.kheap q = σ.kheap q) := by
  have hm : ((), σ') ∈ (refillUnblockCheck (Z := Unit) p σ).1 := by rw [h]; rfl
  rcases unblock_result hk hne hm with ⟨rfl, -⟩ | ⟨z, rfl, -⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun q hq => by simp [updK, hq]⟩

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- A node word's write is in the scheduler footprint. -/
theorem sfoot_wr_node {T : Set U64} {c : U64} {s : S} (hN : NodePlaced st T s c) {o : U64} (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) (v : U64) : WritesIn st s (L.wr s (L.nodeAt s c o) v) (SFoot st T c s) :=
  (writesIn_wr (nodeAt_aligned hN ho h8)).mono fun b hb => hb ▸ sfoot_node hN ho

/-- The spec's `switch_sched_context` after the unblock step. -/
def sscTail (scp : Fl4Spec.ObjRef) : Fl4Spec.SMonad Unit Unit := do
  let reprogram ← Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.reprogramTimer
  Fl4Spec.NonDet.when reprogram <| Fl4Spec.commitTime
  Fl4Spec.NonDet.modify fun s => { s with curSc := scp }

/-- **`switch_sched_context` after the unblock step**: `commit_time` if the
timer is to be reprogrammed, then the new SC is current. -/
theorem ssc_tail_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hscC : nodeW st s c layout.node.CUR_SC ∈ C) (nsc : U64)
    {u0 : Fl4Spec.ObjRef} (hown0 : ∀ x n, σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) →
      x.scTcb = some u0 ∨ x.scTcb = none)
    (hback : ∀ xt, σ.kheap u0 = some (.tcb xt) → xt.tcbSchedContext = some σ.curSc)
    (hnr : 0 < σ.consumedTime → u0 ∉ σ.releaseQueue) (hoff : OffOK σ)
    (hmrt : sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    (do
      let i1 ← st.cur_cpu s
      let i2 ← obj.node_get st s i1 layout.node.REPROGRAM
      let s3 ← if i2 != 0#u64 then sched.commit_time st ar s a else ok s
      let c' ← st.cur_cpu s3
      let s4 ← obj.node_set st s3 c' layout.node.CUR_SC nsc
      ok (s4, a)) ⦃ r => ∃ σ', sscTail nsc.bv σ = ({((), σ')}, False) ∧ SchedRel st N T C c r.1 σ' ∧
        NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧ σ'.curSc = nsc.bv ∧
        σ'.curThread = σ.curThread ∧ σ'.releaseQueue = σ.releaseQueue ∧ SwKeep σ σ' ∧ r.2 = a ∧
        WritesIn st s r.1 (KFoot st T N C c s σ) ⦄ := by
  have hc0 := hS.lists.choose_spec.choose_spec.1.cur
  have hpo : ∃ y n, σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext y n) := by
    obtain ⟨Q, R, -, hs⟩ := hS.lists
    obtain ⟨y, n, hk, -⟩ := hs.scs _ hscC
    exact ⟨y, n, hk⟩
  have hrep := hS.repr
  step with LawfulStore.cur_cpu_spec as ⟨i1, hi1⟩
  rw [hc0] at hi1
  subst i1
  step with obj.node_get.spec as ⟨i2, hi2⟩
  -- the CUR_SC write, from any state related to `σ3`
  have fin : ∀ (s3 : S) (σ3 : Fl4Spec.State Unit), SchedRel st N T C c s3 σ3 → NtfnStateRel N T (L.mem s3) σ3 →
      NSC N C σ3 → Inv σ3 → σ3.curThread = σ.curThread → σ3.releaseQueue = σ.releaseQueue → SwKeep σ σ3 →
      (Fl4Spec.NonDet.when σ.reprogramTimer Fl4Spec.commitTime) σ = ({((), σ3)}, False) →
      WritesIn st s s3 (KFoot st T N C c s σ) →
      (do
        let c' ← st.cur_cpu s3
        let s4 ← obj.node_set st s3 c' layout.node.CUR_SC nsc
        ok (s4, a)) ⦃ r => ∃ σ', sscTail nsc.bv σ = ({((), σ')}, False) ∧ SchedRel st N T C c r.1 σ' ∧
          NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧ σ'.curSc = nsc.bv ∧
          σ'.curThread = σ.curThread ∧ σ'.releaseQueue = σ.releaseQueue ∧ SwKeep σ σ' ∧ r.2 = a ∧
          WritesIn st s r.1 (KFoot st T N C c s σ) ⦄ := by
    intro s3 σ3 hS3 hR3 hN3 hI3 e1 e2 e3 h3 hw3
    step with LawfulStore.cur_cpu_spec as ⟨c3, hc3⟩
    rw [hS3.lists.choose_spec.choose_spec.1.cur] at hc3
    subst c3
    step with obj.node_set.spec as ⟨s4, hs4⟩
    subst hs4
    obtain ⟨hS4, hf4, -⟩ := hS3.set_node_cursc nsc
    refine ⟨{ σ3 with curSc := nsc.bv }, ?_, hS4, hR3.frame hS3.placed hf4 (KView.of_kheap rfl), hN3,
      hI3.congr rfl rfl rfl rfl, rfl, e1, e2, e3, WritesIn.kfoot_sfoot hw3 (sfoot_wr_node
        hS3.lists.choose_spec.choose_spec.1.node (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) nsc)⟩
    unfold sscTail
    rw [nd_gets_bind, nd_bind_one h3]; rfl
  split
  · rename_i hne
    have hw : nodeW st s c layout.node.REPROGRAM ≠ 0#u64 := by
      rw [hi2] at hne; simpa [nodeW] using hne
    have hrt : σ.reprogramTimer = true := by rw [hrep]; simpa using hw
    refine WP.spec_bind (commit_time_inv s a σ hS hR hN hI hscC hown0 hback hS.idle hnr hoff hmrt hmb) ?_
    rintro s3 ⟨σ3, h1, hS3, hR3, hN3, hI3, hK, hw3⟩
    exact fin s3 σ3 hS3 hR3 hN3 hI3 hK.2.1 hK.2.2.1 (SwKeep.of_headKeeps hK hpo) (by rw [hrt]; exact h1) hw3
  · rename_i hne
    have hw : nodeW st s c layout.node.REPROGRAM = 0#u64 := by
      apply UScalar.eq_of_val_eq
      rw [hi2] at hne; simp only [nodeW]; simpa using hne
    have hrt : σ.reprogramTimer = false := by rw [hrep]; simp [hw]
    rw [bind_ok]
    exact fin s σ hS hR hN hI rfl rfl (SwKeep.refl σ) (by rw [hrt]; rfl) (WritesIn.refl _ _)

/-- **`switch_sched_context` refines l4v `switch_sched_context`** and keeps
the full `Inv`. Hypotheses: the current thread is bound to an SC and not in
the release queue (it was chosen); the current (outgoing) SC is one of `C`,
its owner `u0` is bound back to it and not released, and `OffOK`. -/
theorem switch_sched_context_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hscC : nodeW st s c layout.node.CUR_SC ∈ C)
    (hb0 : L.mem s (scA (nodeW st s c layout.node.CUR_THREAD)) ≠ 0#u64)
    (hctr : (nodeW st s c layout.node.CUR_THREAD).bv ∉ σ.releaseQueue)
    {u0 : Fl4Spec.ObjRef} (hown0 : ∀ x n, σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) →
      x.scTcb = some u0 ∨ x.scTcb = none)
    (hback : ∀ xt, σ.kheap u0 = some (.tcb xt) → xt.tcbSchedContext = some σ.curSc)
    (hnr : 0 < σ.consumedTime → u0 ∉ σ.releaseQueue) (hoff : OffOK σ)
    (hna : (L.rmax s (L.mem s (scA (nodeW st s c layout.node.CUR_THREAD)))).val ≠ 0)
    (hmrt : sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    sched.switch_sched_context st ar s a ⦃ r => ∃ σ', Fl4Spec.switchSchedContext (Z := Unit) σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      σ'.curSc = (L.mem s (scA (nodeW st s c layout.node.CUR_THREAD))).bv ∧ σ'.curThread = σ.curThread ∧
      σ'.releaseQueue = σ.releaseQueue ∧ SwKeep σ σ' ∧ r.2 = a ∧ WritesIn st s r.1 (KFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  set ct := nodeW st s c layout.node.CUR_THREAD with hctd
  set osc := nodeW st s c layout.node.CUR_SC with hoscd
  set nsc := L.mem s (scA ct) with hnscd
  have hct : ct ∈ T := hc.curT
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb _ hct
  have hxs : xt.tcbSchedContext = some nsc.bv := by rw [hsct, optRef_ne hb0]
  have hnC : nsc ∈ C := hs.scMem _ hct hb0
  obtain ⟨x, n, hk, hx⟩ := hs.scs _ hscC
  obtain ⟨x', n', hk', hx'⟩ := hs.scs _ hnC
  have hx'S := hx'.act hna
  have hne' : x'.scRefills ≠ [] := by rw [hx'S.refills]; exact refills_ne hx'S.wf
  have hspec : Fl4Spec.switchSchedContext (Z := Unit) σ = (Fl4Spec.NonDet.when (nsc.bv ≠ osc.bv) (do
      Fl4Spec.NonDet.modify fun s : Fl4Spec.State Unit => { s with reprogramTimer := true }
      Fl4Spec.ifConstantBandwidthRefillUnblockCheck (some nsc.bv)) >>= fun _ => sscTail nsc.bv) σ := by
    unfold Fl4Spec.switchSchedContext sscTail
    rw [nd_gets_bind, nd_gets_bind, hs.curSc, hs.curThread]
    unfold Fl4Spec.getTcbObjRef
    rw [nd_bind_one (threadGet_eq _ hkt), hxs,
      nd_bind_one (show Fl4Spec.NonDet.assertOpt (σ := Fl4Spec.State Unit) (some nsc.bv) σ = ({(nsc.bv, σ)}, False)
        from rfl), nd_bind_one (getSchedContext_eq hk)]
  unfold sched.switch_sched_context
  step with sched.cur_thread.spec' as ⟨ct', hct'⟩
  rw [hc.cur] at hct'
  subst ct'
  step with obj.Tcb.sc.spec as ⟨i, hi⟩
  subst i
  step with sched.cur_sc.spec' as ⟨osc', hosc'⟩
  rw [hc.cur] at hosc'
  subst osc'
  rw [sc_ne_eq]
  simp only [bind_ok]
  by_cases hb : osc = nsc
  · split
    · rename_i h; exact absurd hb (of_decide_eq_true h)
    rw [bind_ok]
    refine WP.spec_mono (ssc_tail_refines s a σ hS hR hN hI hscC nsc hown0 hback hnr hoff hmrt hmb) ?_
    rintro r ⟨σ', h1, h2⟩
    refine ⟨σ', ?_, h2⟩
    rw [hspec, Fl4Spec.NonDet.when, if_neg (fun h => h (by rw [hb])),
      nd_bind_one (show Fl4Spec.NonDet.pure (σ := Fl4Spec.State Unit) () σ = ({((), σ)}, False) from rfl)]
    exact h1
  · have hb' : nsc.bv ≠ osc.bv := fun e => hb (eq_of_bv e).symm
    split
    swap
    · rename_i h; exact absurd (decide_eq_true hb) h
    step with sched.set_reprogram.spec' as ⟨s3, hs3⟩
    rw [hc.cur] at hs3
    subst hs3
    obtain ⟨hS3, hf3, -⟩ := hS.set_reprogram
    set σr : Fl4Spec.State Unit := { σ with reprogramTimer := true } with hσr
    have hR3 : NtfnStateRel N T (L.mem (L.wr s (L.nodeAt s c layout.node.REPROGRAM) 1#u64)) σr :=
      hR.frame hS.placed hf3 (KView.of_kheap rfl)
    have hIr : Inv σr := hI.congr rfl rfl rfl rfl
    have hNr : NSC N C σr := hN
    have hkr' : σr.kheap nsc.bv = some (.schedContext x' n') := hk'
    have hwR : WritesIn st s (L.wr s (L.nodeAt s c layout.node.REPROGRAM) 1#u64) (KFoot st T N C c s σ) :=
      WritesIn.kfoot_of_sfoot (sfoot_wr_node hc.node (by simp [layout.node.REPROGRAM])
        (by simp [layout.node.REPROGRAM]) _)
    -- the spec's unblock step, from the state after it
    have pre : ∀ σ2, (Fl4Spec.ifConstantBandwidthRefillUnblockCheck (Z := Unit) (some nsc.bv)) σr =
        ({((), σ2)}, False) → Fl4Spec.switchSchedContext (Z := Unit) σ = sscTail nsc.bv σ2 := by
      intro σ2 h2
      rw [hspec, Fl4Spec.NonDet.when, if_pos hb', nd_bind_assoc',
        nd_bind_one (show Fl4Spec.NonDet.modify (fun s : Fl4Spec.State Unit => { s with reprogramTimer := true }) σ =
          ({((), σr)}, False) from rfl), nd_bind_one h2]
    -- the tail from a state `σ2` that differs from `σr` only in the incoming SC
    have tail : ∀ (s2 : S) (σ2 : Fl4Spec.State Unit), SchedRel st N T C c s2 σ2 → NtfnStateRel N T (L.mem s2) σ2 →
        NSC N C σ2 → Inv σ2 → σ2.curSc = σ.curSc → σ2.curThread = σ.curThread →
        σ2.releaseQueue = σ.releaseQueue → σ2.curTime = σ.curTime → σ2.consumedTime = σ.consumedTime →
        (∀ q, q ≠ nsc.bv → σ2.kheap q = σ.kheap q) → (∃ y m, σ2.kheap nsc.bv = some (.schedContext y m)) →
        SwKeep σ σ2 → (Fl4Spec.ifConstantBandwidthRefillUnblockCheck (Z := Unit) (some nsc.bv)) σr = ({((), σ2)}, False) →
        WritesIn st s s2 (KFoot st T N C c s σ) →
        (do
          let i1 ← st.cur_cpu s2
          let i2 ← obj.node_get st s2 i1 layout.node.REPROGRAM
          let s3 ← if i2 != 0#u64 then sched.commit_time st ar s2 a else ok s2
          let c' ← st.cur_cpu s3
          let s4 ← obj.node_set st s3 c' layout.node.CUR_SC nsc
          ok (s4, a)) ⦃ r => ∃ σ', Fl4Spec.switchSchedContext (Z := Unit) σ = ({((), σ')}, False) ∧
            SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
            σ'.curSc = nsc.bv ∧ σ'.curThread = σ.curThread ∧ σ'.releaseQueue = σ.releaseQueue ∧
            SwKeep σ σ' ∧ r.2 = a ∧ WritesIn st s r.1 (KFoot st T N C c s σ) ⦄ := by
      intro s2 σ2 hS2 hR2 hN2 hI2 e1 e2 e3 e4 e5 e6 e7 e8 h2 hw2
      have esc : nodeW st s2 c layout.node.CUR_SC = osc :=
        eq_of_bv (by rw [← hS2.lists.choose_spec.choose_spec.2.curSc, e1, hs.curSc])
      have hko : σ2.kheap osc.bv = σ.kheap osc.bv := e6 _ (Ne.symm hb')
      refine WP.spec_mono (ssc_tail_refines s2 a σ2 hS2 hR2 hN2 hI2 (by rw [esc]; exact hscC) nsc
        (u0 := u0) (fun y m hy => hown0 y m (by rw [esc, hko] at hy; exact hy))
        (fun xu hxu => by
          by_cases e : u0 = nsc.bv
          · obtain ⟨y, m, hy⟩ := e7
            rw [e, hy] at hxu; cases hxu
          · rw [e6 _ e] at hxu; rw [e1]; exact hback xu hxu)
        (by rw [e3, e5]; exact hnr)
        (fun hc0 y m hy => by
          rw [e5] at hc0; rw [e1, hs.curSc, hko, ← hs.curSc] at hy
          rw [e5, e4]; exact hoff hc0 y m hy) hmrt hmb) ?_
      rintro r ⟨σ', h1, h3⟩
      refine ⟨σ', by rw [pre σ2 h2]; exact h1, ?_⟩
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h3
      exact ⟨a1, a2, a3, a4, a5, a6.trans e2, a7.trans e3, e8.trans a8, a9,
        WritesIn.kfoot_trans hw2 (SzKeepC.of_fwd hS fun p x n hp => by
          obtain ⟨y, hy, -⟩ := e8.2.1 p x n hp; exact ⟨y, hy⟩) a10⟩
    have hnr' : Fl4Spec.refillReady σr.curTime (Fl4Spec.refillHd x') = true → x'.scPeriod ≠ 0 →
        ∀ u ∈ σr.releaseQueue, ∀ xu, σr.kheap u = some (.tcb xu) → xu.tcbSchedContext ≠ some nsc.bv := by
      intro _ _ u hu xu hku hsu
      obtain ⟨y, m, hky, hyt⟩ := hI.back u xu nsc.bv hku hsu
      obtain ⟨y2, m2, hky2, hyt2⟩ := hI.back ct.bv xt nsc.bv hkt hxs
      rw [hky] at hky2; cases hky2
      rw [hyt] at hyt2; cases hyt2
      exact hctr hu
    step with sc_constant_bandwidth_spec as ⟨b1, hb1⟩
    have hsp' : x'.scSporadic = decide (L.mem (L.wr s (L.nodeAt s c layout.node.REPROGRAM) 1#u64) (scW nsc 64#u64) ≠ 0#u64) := by
      obtain ⟨Q3, R3, hc3, hs3⟩ := hS3.lists
      obtain ⟨x3, n3, hk3, hx3⟩ := hs3.scs nsc hnC
      rw [hkr'] at hk3; cases hk3
      exact hx3.sporadic
    split
    · rename_i hcb
      have hw0 := of_decide_eq_true (hb1 ▸ hcb)
      have hspf : x'.scSporadic = false := by rw [hsp']; exact decide_eq_false (not_not.2 hw0)
      have hna3 : (L.rmax (L.wr s (L.nodeAt s c layout.node.REPROGRAM) 1#u64) nsc).val ≠ 0 := by
        obtain ⟨Q3, R3, hc3, hs3⟩ := hS3.lists
        obtain ⟨x3, n3, hk3, hx3⟩ := hs3.scs nsc hnC
        rw [hkr'] at hk3; cases hk3
        rw [hx3.max, ← hx'.max]; exact hna
      refine WP.spec_bind (WP.spec_and (unblock_check_refines _ σr hS3 hnC hna3)
        (unblock_check_kfoot hS3 hnC hna3)) ?_
      rintro s2 ⟨⟨σ2, hu, hf2, hkv2, hS2⟩, hwu⟩
      obtain ⟨k1, k2, k3, k4, k5, -, k7⟩ := unblock_keeps hkr' hne' hu
      have hm : ((), σ2) ∈ (Fl4Spec.refillUnblockCheck (Z := Unit) nsc.bv σr).1 := by rw [hu]; rfl
      have hI2 : Inv σ2 := hIr.unblock hkr' hne' hnr' hm
      have hex : ∃ y m, σ2.kheap nsc.bv = some (.schedContext y m) := by
        rcases unblock_result hkr' hne' hm with ⟨rfl, -⟩ | ⟨z, rfl, -⟩
        · exact ⟨x', n', hkr'⟩
        · exact ⟨z, n', by simp [updK]⟩
      have hsw : SwKeep σ σ2 := by
        rcases unblock_result hkr' hne' hm with ⟨rfl, -⟩ | ⟨z, rfl, -, -, hzy, -⟩
        · exact SwKeep.of_kheap rfl rfl rfl
        · refine ⟨fun q xq hq => ?_, fun q y0 m hq => ?_, rfl, rfl⟩
          · have : q ≠ nsc.bv := by rintro rfl; rw [hk'] at hq; cases hq
            simp only [updK_kheap, ne_eq, this, not_false_eq_true, Function.update_of_ne]; exact hq
          · by_cases e : q = nsc.bv
            · subst e; rw [hk'] at hq; cases hq
              exact ⟨z, by simp [updK], by rw [hzy]⟩
            · exact ⟨y0, by simp only [updK_kheap, ne_eq, e, not_false_eq_true, Function.update_of_ne]; exact hq, rfl⟩
      exact tail _ σ2 hS2 (hR3.frame hS3.placed hf2 hkv2) (hNr.kview hR3 hkv2) hI2 k1 k2 k3 k4 k5 k7 hex hsw
        (by rw [ifCB_eq hkr', if_pos hspf]; exact hu) (WritesIn.kfoot_trans hwR (SzKeepC.of (SzKeep.of_kheap rfl)) hwu)
    · rename_i hcb
      have hw0 : L.mem (L.wr s (L.nodeAt s c layout.node.REPROGRAM) 1#u64) (scW nsc 64#u64) ≠ 0#u64 :=
        fun h => hcb (by rw [hb1]; exact decide_eq_true h)
      have hspf : ¬ x'.scSporadic = false := by
        rw [hsp', decide_eq_true hw0]; decide
      rw [bind_ok]
      exact tail _ σr hS3 hR3 hNr hIr rfl rfl rfl rfl rfl (fun _ _ => rfl) ⟨x', n', hkr'⟩ (SwKeep.of_kheap rfl rfl rfl)
        (by rw [ifCB_eq hkr', if_neg hspf]) hwR

/-- **`switch_sched_context` establishes `CurInv`**: the chosen thread (bound
to an SC, not released, not blocked on a notification) runs on its SC,
which is active unless it is the idle SC. -/
theorem switch_sched_context_cur {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hscC : nodeW st s c layout.node.CUR_SC ∈ C)
    (hb0 : L.mem s (scA (nodeW st s c layout.node.CUR_THREAD)) ≠ 0#u64)
    (hctr : (nodeW st s c layout.node.CUR_THREAD).bv ∉ σ.releaseQueue)
    (hnb : ∀ xt, σ.kheap (nodeW st s c layout.node.CUR_THREAD).bv = some (.tcb xt) →
      NotIpcBlk xt.tcbState)
    (hact : (L.mem s (scA (nodeW st s c layout.node.CUR_THREAD))).bv ≠ Fl4Spec.idleScPtr → ∀ x n,
      σ.kheap (L.mem s (scA (nodeW st s c layout.node.CUR_THREAD))).bv = some (.schedContext x n) →
      Fl4Spec.scActive x = true)
    {u0 : Fl4Spec.ObjRef} (hown0 : ∀ x n, σ.kheap (nodeW st s c layout.node.CUR_SC).bv = some (.schedContext x n) →
      x.scTcb = some u0 ∨ x.scTcb = none)
    (hback : ∀ xt, σ.kheap u0 = some (.tcb xt) → xt.tcbSchedContext = some σ.curSc)
    (hnr : 0 < σ.consumedTime → u0 ∉ σ.releaseQueue) (hoff : OffOK σ)
    (hmrt : sporadic.max_release_time ar a ⦃ mrt => mrt.bv = Fl4Spec.MAX_RELEASE_TIME ⦄)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    sched.switch_sched_context st ar s a ⦃ r => ∃ σ', Fl4Spec.switchSchedContext (Z := Unit) σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧ CurInv σ' ∧
      (ActIdle σ → ActIdle σ') ∧ r.2 = a ∧ WritesIn st s r.1 (KFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hct := hc.curT
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb _ hct
  have hxs : xt.tcbSchedContext = some (L.mem s (scA (nodeW st s c layout.node.CUR_THREAD))).bv := by
    rw [hsct, optRef_ne hb0]
  obtain ⟨x', n', hk', -⟩ := hs.scs _ (hs.scMem _ hct hb0)
  have hna : (L.rmax s (L.mem s (scA (nodeW st s c layout.node.CUR_THREAD)))).val ≠ 0 := by
    obtain ⟨x0, n0, hk0, hx0⟩ := hs.scs _ (hs.scMem _ hct hb0)
    by_cases hi : (L.mem s (scA (nodeW st s c layout.node.CUR_THREAD))).bv = Fl4Spec.idleScPtr
    · exact hx0.idle hi
    · exact hx0.rmax_ne (hact hi x0 n0 hk0)
  refine WP.spec_mono (switch_sched_context_refines s a σ hS hR hN hI hscC hb0 hctr hown0 hback hnr hoff hna hmrt hmb) ?_
  rintro r ⟨σ', h1, h2, h3, h4, h5, e1, e2, e3, hsw, e4, hw⟩
  refine ⟨σ', h1, h2, h3, h4, h5, ⟨⟨xt, ?_, ?_, hnb xt hkt⟩, ?_, fun hid y m hy => ?_, ?_⟩,
    fun hA => hA.swKeep hsw e3 (Or.inl hsw.2.2.2), e4, hw⟩
  · rw [e2, hs.curThread]; exact hsw.1 _ _ hkt
  · rw [e1]; exact hxs
  · obtain ⟨y, hy, -⟩ := hsw.2.1 _ _ _ hk'
    exact ⟨y, n', by rw [e1]; exact hy⟩
  · rw [e1] at hid hy
    obtain ⟨y1, hy1, hm1⟩ := hsw.2.1 _ _ _ hk'
    rw [hy] at hy1; cases hy1
    have := hact hid x' n' hk'
    unfold Fl4Spec.scActive Fl4Spec.activeSc at this ⊢; rw [hm1]; exact this
  · rw [e2, e3, hs.curThread]; exact hctr

end

end

end Fl4Proofs.P3.Sched
