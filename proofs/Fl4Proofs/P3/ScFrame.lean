/-
P3 (DESIGN.md §9), scheduling contexts: frames.

* `whileLoop` with a deterministic body (`wl_done`, `wl_step`).
* `SchedSpec.transfer`: `SchedSpec` for a new FL4 state and a new spec
  state, from agreement on the scheduler's words and the spec's
  scheduler fields and TCBs, given the SCs' relation.
* `SchedRel.sc_update`: writes inside one SC of `C` (its `ScIn` words), and
  the spec's object at that pointer replaced by a related one (same size),
  keep `SchedRel`; `scin_footEq`, `KView.of_sc`: the notification
  relation's footprint and view are untouched.
* `SchedRel.set_reprogram`: writing the `REPROGRAM` word (as
  `refill_unblock_check` does) ↔ `reprogram_timer := true`.
-/
import Fl4Proofs.P3.Sched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

/-! ## `whileLoop` with a deterministic body -/

section While
open Fl4Spec
variable {σ α : Type} {C : α → σ → Prop} {B : α → NonDet σ α}

theorem reach_stuck {r : α} {s : σ} (h : ¬ C r s) {r1 : α} {s1 : σ}
    (hr : NonDet.WhileReach C B r s r1 s1) : r1 = r ∧ s1 = s := by
  induction hr with
  | start => exact ⟨rfl, rfl⟩
  | step _ hc _ ih => obtain ⟨rfl, rfl⟩ := ih; exact absurd hc h

theorem wl_done {r : α} {s : σ} (h : ¬ C r s) : NonDet.whileLoop C B r s = ({(r, s)}, False) := by
  unfold NonDet.whileLoop
  refine Prod.ext (Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩) (eq_false ?_)
  · cases hx with
    | done _ => rfl
    | step hc _ _ => exact absurd hc h
  · rw [Set.mem_singleton_iff] at hx; subst hx; exact NonDet.WhileResults.done h
  · rintro (⟨r', s', hr, hc, -⟩ | ⟨f, hf0, hf⟩)
    · obtain ⟨rfl, rfl⟩ := reach_stuck h hr; exact h hc
    · have := (hf 0).1; rw [hf0] at this; exact h this

/-- Reaching a round from `(r, s)`, whose first round goes to `(r', s')`. -/
theorem reach_det {r r' : α} {s s' : σ} (hc : C r s) (hb : B r s = ({(r', s')}, False)) {r1 : α} {s1 : σ} :
    NonDet.WhileReach C B r s r1 s1 ↔ (r1 = r ∧ s1 = s) ∨ NonDet.WhileReach C B r' s' r1 s1 := by
  constructor
  · intro h
    induction h with
    | start => exact Or.inl ⟨rfl, rfl⟩
    | step h2 hc2 hm ih =>
      rcases ih with ⟨rfl, rfl⟩ | ih
      · rw [hb] at hm
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        exact Or.inr NonDet.WhileReach.start
      · exact Or.inr (NonDet.WhileReach.step ih hc2 hm)
  · rintro (⟨rfl, rfl⟩ | h)
    · exact .start
    · have h0 : NonDet.WhileReach C B r s r' s' :=
        NonDet.WhileReach.step NonDet.WhileReach.start hc (by rw [hb]; rfl)
      induction h with
      | start => exact h0
      | step _ hc2 hm ih => exact NonDet.WhileReach.step ih hc2 hm

theorem wl_step {r r' : α} {s s' : σ} (hc : C r s) (hb : B r s = ({(r', s')}, False)) :
    NonDet.whileLoop C B r s = NonDet.whileLoop C B r' s' := by
  unfold NonDet.whileLoop
  refine Prod.ext (Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩) (propext ⟨?_, ?_⟩)
  · cases hx with
    | done h => exact absurd hc h
    | step _ hm hw =>
      rw [hb] at hm
      simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact hw
  · exact NonDet.WhileResults.step hc (by rw [hb]; rfl) hx
  · rintro (⟨r1, s1, hr, hc1, hf⟩ | ⟨f, hf0, hf⟩)
    · rcases (reach_det hc hb).1 hr with ⟨rfl, rfl⟩ | hr'
      · rw [hb] at hf; exact hf.elim
      · exact Or.inl ⟨r1, s1, hr', hc1, hf⟩
    · right
      refine ⟨fun n => f (n + 1), ?_, fun n => hf (n + 1)⟩
      have := (hf 0).2; rw [hf0, hb] at this
      simpa using this
  · rintro (⟨r1, s1, hr, hc1, hf⟩ | ⟨f, hf0, hf⟩)
    · exact Or.inl ⟨r1, s1, (reach_det hc hb).2 (Or.inr hr), hc1, hf⟩
    · right
      refine ⟨fun n => Nat.casesOn n (r, s) f, rfl, fun n => ?_⟩
      cases n with
      | zero => exact ⟨hc, by show f 0 ∈ (B r s).1; rw [hf0, hb]; rfl⟩
      | succ n => exact hf n

end While

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-! ## `SchedSpec` for new states -/

theorem SchedSpec.transfer {T C C' : Set U64} {c : U64} {s s' : S} {Q : U64 → List U64} {R : List U64}
    {σ σ' : Fl4Spec.State Unit} (h : SchedSpec st T C c s Q R σ) (ha : SAgree st T C' c s s')
    (e1 : σ'.readyQueues = σ.readyQueues) (e2 : σ'.releaseQueue = σ.releaseQueue)
    (e3 : σ'.curThread = σ.curThread) (e4 : σ'.curSc = σ.curSc) (e5 : σ'.curTime = σ.curTime)
    (e6 : σ'.consumedTime = σ.consumedTime) (e7 : σ'.curDomain = σ.curDomain)
    (htcb : ∀ t ∈ T, ∀ x, σ.kheap t.bv = some (.tcb x) → σ'.kheap t.bv = some (.tcb x))
    (hscs : ∀ sc ∈ C, ∃ x n, σ'.kheap sc.bv = some (.schedContext x n) ∧ ScRel1 st s' sc x n) :
    SchedSpec st T C c s' Q R σ' := by
  have w : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 56 → nodeW st s' c o = nodeW st s c o :=
    fun o h1 h2 h3 h4 => ha.nodeW h1 h2 h3 h4
  refine ⟨fun p hp => by rw [e1]; exact h.rq p hp, fun d p hd => by rw [e1]; exact h.rqDom d p hd,
    by rw [e2]; exact h.rel, ?_, ?_, ?_, ?_, ?_, fun t ht => ?_, fun t ht => ?_, hscs⟩
  · rw [e3, w _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD])]; exact h.curThread
  · rw [e4, w _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])]; exact h.curSc
  · rw [e5, w _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      (by simp [layout.node.CUR_TIME])]; exact h.curTime
  · rw [e6, w _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
      (by simp [layout.node.CONSUMED])]; exact h.consumed
  · rw [e7, curDomA_ksb ha.ksb, ha.dom]; exact h.curDom
  · obtain ⟨x, hk, h1, h2, h3, h4⟩ := h.tcb t ht
    exact ⟨x, htcb t ht x hk, h1, by rw [ha.dom' ht]; exact h2, by rw [ha.scw ht]; exact h3,
      by rw [ha.prio ht]; exact h4⟩
  · rw [ha.scw ht]; exact h.scMem t ht

theorem curDomA_aligned {T : Set U64} {s : S} {c : U64} (hN : NodePlaced st T s c) : Aligned (curDomA st s) := by
  have h1 := hN.align; have h2 := hN.fits
  unfold Aligned curDomA
  simp only [LawfulStore.nodeBase] at h1 h2
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

theorem curDomA_val {T : Set U64} {s : S} {c : U64} (hN : NodePlaced st T s c) :
    (curDomA st s).val = (L.ksb s).val + 8 := by
  have h2 := hN.fits
  simp only [LawfulStore.nodeBase] at h2
  simp [curDomA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

/-! ## Writing inside one SC -/

/-- The spec state with the SC at `p` replaced. -/
abbrev updSc (σ : Fl4Spec.State Unit) (p : Fl4Spec.ObjRef) (x : Fl4Spec.SchedContext) (n : Nat) :
    Fl4Spec.State Unit := updK σ p (.schedContext x n)

theorem KView.of_sc {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x0 x : Fl4Spec.SchedContext} {n0 n : Nat}
    (hk : σ.kheap p = some (.schedContext x0 n0)) : KView σ (updSc σ p x n) := by
  refine ⟨fun q y hq => ?_, fun q y hq => ⟨y, ?_, rfl, rfl, rfl⟩⟩
  · have : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    simp [this, hq]
  · have : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    simp [this, hq]

/-- Writes inside the SC `sc0` are outside the notification footprint. -/
theorem scin_footEq {N T C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {sc0 : U64} (hsc0 : sc0 ∈ C) (hw : WritesIn st s s' (ScIn st s sc0)) :
    FootEq N T (L.mem s) (L.mem s') := by
  intro a ha hf
  refine hw.mem_eq ha fun hin => ?_
  obtain ⟨h1, -, h3, -⟩ := hS.scOut sc0 hsc0 a hin
  rcases hf with hf | ⟨t, ht, e | e | e | e | e | e⟩
  · exact h1 (Or.inl hf)
  · exact h1 (Or.inr ⟨t, ht, Or.inl e⟩)
  · exact h1 (Or.inr ⟨t, ht, Or.inr (Or.inl e)⟩)
  · exact h1 (Or.inr ⟨t, ht, Or.inr (Or.inr (Or.inl e))⟩)
  · subst e
    have hta := hS.placed.tcb t ht
    have := h3 t ht
    rw [prioA_val hta] at this; omega
  · exact h1 (Or.inr ⟨t, ht, Or.inr (Or.inr (Or.inr (Or.inl e)))⟩)
  · exact h1 (Or.inr ⟨t, ht, Or.inr (Or.inr (Or.inr (Or.inr e)))⟩)

/-- **Writes inside one SC**, with the spec's SC object replaced by a related
one of the same size and refill-max, keep `SchedRel`. -/
theorem SchedRel.sc_update {N T C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {sc0 : U64} (hsc0 : sc0 ∈ C) {x0 : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap sc0.bv = some (.schedContext x0 n)) (hw : WritesIn st s s' (ScIn st s sc0))
    (hm0 : L.rmax s' sc0 = L.rmax s sc0) (x : Fl4Spec.SchedContext) (hx : ScRel1 st s' sc0 x n) :
    SchedRel st N T C c s' (updSc σ sc0.bv x n) := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN := hc.node
  have hk' : L.ksb s' = L.ksb s := hw.1
  have nout : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) :=
    fun o ho h8 => hw.mem_eq (nodeAt_aligned hN ho h8) fun hin => by
      have := (hS.scOut sc0 hsc0 _ hin).2.1; rw [nodeAt_val hN ho] at this; omega
  have hoth : ∀ sc ∈ C, sc ≠ sc0 → ScAgree st s s' sc := fun sc hsc hne a ha hin =>
    hw.mem_eq ha (hS.scDisj sc hsc sc0 hsc0 hne a hin)
  have hag : SAgree st T {sc | sc ∈ C ∧ sc ≠ sc0} c s s' := by
    refine ⟨hk', hw.2.1, fun o ho h8 _ _ => nout o ho h8, fun y hy K hK => ?_, ?_, fun sc ⟨hsc, hne⟩ => hoth sc hsc hne⟩
    · obtain ⟨h1, h2, -⟩ := schedField_ok hK
      refine hw.mem_eq (field_aligned (hc.tcbs y hy) h1 h2) fun hin => ?_
      have := (hS.scOut sc0 hsc0 _ hin).2.2.1 y hy
      rw [tfield_val (hc.tcbs y hy) h1] at this; omega
    · refine hw.mem_eq (curDomA_aligned hN) fun hin => ?_
      have := (hS.scOut sc0 hsc0 _ hin).2.2.2
      rw [curDomA_val hN] at this; omega
  have hm : ∀ sc ∈ C, L.rmax s' sc = L.rmax s sc := by
    intro sc hsc
    by_cases e : sc = sc0
    · subst e; exact hm0
    · obtain ⟨y, m, -, ey⟩ := hs.scs sc hsc
      simp only [LawfulStore.rmax, maxA_eq]
      exact hoth sc hsc e _ (ey.hdr (by simp) (by simp)).1 (ey.hdr (by simp) (by simp)).2
  have nw : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → nodeW st s' c o = nodeW st s c o := by
    intro o ho h8; unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hk']; exact nout o ho h8
  refine ⟨hS.placed, fun o ho => by rw [nodeAt_ksb hk']; exact hS.nodeNW o ho,
    by rw [curDomA_ksb hk']; exact hS.domNW, scOut_transfer hk' hm hS.scOut, scDisj_transfer hm hS.scDisj,
    by rw [nw _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])]; exact hS.actW,
    by rw [nw _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])]; exact hS.act,
    by rw [nw _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])]; exact hS.repr,
    Q, R, hc.agree hag.toC, ?_⟩
  refine hs.transfer hag rfl rfl rfl rfl rfl rfl rfl (fun t ht y hy => ?_) (fun sc hsc => ?_)
  · have : t.bv ≠ sc0.bv := by intro e; rw [e, hk] at hy; cases hy
    simp [this, hy]
  · by_cases e : sc = sc0
    · subst e; exact ⟨x, n, by simp, hx⟩
    · obtain ⟨y, m, hky, ey⟩ := hs.scs sc hsc
      exact ⟨y, m, by simp [bv_inj e, hky], ey.agree (hoth sc hsc e)⟩

/-! ## Writing the `REPROGRAM` word -/

theorem SchedRel.set_reprogram {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) :
    SchedRel st N T C c (L.wr s (L.nodeAt s c layout.node.REPROGRAM) 1#u64) { σ with reprogramTimer := true } ∧
      FootEq N T (L.mem s) (L.mem (L.wr s (L.nodeAt s c layout.node.REPROGRAM) 1#u64)) ∧
      WritesIn st s (L.wr s (L.nodeAt s c layout.node.REPROGRAM) 1#u64)
        (· = L.nodeAt s c layout.node.REPROGRAM) := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hN := hc.node
  have h56 : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have hA : Aligned (L.nodeAt s c layout.node.REPROGRAM) := nodeAt_aligned hN (by omega) (by omega)
  set s' := L.wr s (L.nodeAt s c layout.node.REPROGRAM) 1#u64
  have hk : L.ksb s' = L.ksb s := L.ksb_wr _ _ _
  have hag : SAgree st T C c s s' := by
    refine ⟨hk, L.cpu_wr _ _ _, fun o ho h8 _ hne => ?_, fun y hy K hK => ?_, ?_, fun sc hsc => ?_⟩
    · refine rd_wr_ne hA (nodeAt_aligned hN ho h8) fun e => hne ?_
      have := congrArg UScalar.val e
      rw [nodeAt_val hN (by omega), nodeAt_val hN ho] at this; omega
    · obtain ⟨h1, h2, -⟩ := schedField_ok hK
      exact rd_wr_ne hA (field_aligned (hc.tcbs y hy) h1 h2) (nodeAt_ne_tfield hN (by omega) hy (hc.tcbs y hy) h1)
    · refine rd_wr_ne hA (curDomA_aligned hN) fun e => ?_
      have := congrArg UScalar.val e
      rw [nodeAt_val hN (by omega), curDomA_val hN] at this
      simp only [LawfulStore.nodeBase] at this; omega
    · intro a hal hin
      refine rd_wr_ne hA hal fun e => ?_
      have := congrArg UScalar.val e
      rw [nodeAt_val hN (by omega)] at this
      have := (hS.scOut sc hsc a hin).2.1; omega
  have hrp : nodeW st s' c layout.node.REPROGRAM = 1#u64 := by
    unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hk]; exact rd_wr_eq hA
  have hact : nodeW st s' c layout.node.SCHED_ACTION = nodeW st s c layout.node.SCHED_ACTION := by
    unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hk]
    refine rd_wr_ne hA (nodeAt_aligned hN (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])) ?_
    intro e; have := congrArg UScalar.val e
    rw [nodeAt_val hN (by omega), nodeAt_val hN (by simp [layout.node.SCHED_ACTION])] at this
    simp [layout.node.SCHED_ACTION] at this
  have hm := hs.rmax_eq hag.sc
  refine ⟨⟨hS.placed, fun o ho => by rw [nodeAt_ksb hk]; exact hS.nodeNW o ho,
    by rw [curDomA_ksb hk]; exact hS.domNW, scOut_transfer hk hm hS.scOut, scDisj_transfer hm hS.scDisj,
    by rw [hact]; exact hS.actW, by rw [hact]; exact hS.act, by rw [hrp]; rfl, Q, R, hc.agree hag.toC, ?_⟩,
    node_wr_foot hS (by omega) (by omega), writesIn_wr hA⟩
  have hs' := hs.agree hag
  exact ⟨hs'.rq, hs'.rqDom, hs'.rel, hs'.curThread, hs'.curSc, hs'.curTime, hs'.consumed,
    hs'.curDom, hs'.tcb, hs'.scMem, hs'.scs⟩

end

end

end Fl4Proofs.P3.Sched
