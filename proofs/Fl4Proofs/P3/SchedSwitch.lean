/-
P3 (DESIGN.md §9), scheduler: **`reschedule_required` and
`possible_switch_to` refine l4v's** (`Z = Unit`).

The spec's `reschedule_required` asserts that a schedulable switch-to
candidate has a ready and sufficient head refill (l4v `valid_sched_action`,
an invariant about refills, which this relation does not cover); it is the
explicit hypothesis `ActReady`. Without it the spec fails where FL4 (which
does not check) just enqueues the candidate.
-/
import Fl4Proofs.P3.SchedQueue
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

/-! ## The spec -/

section Spec
open Fl4Spec

theorem setAction_eq (σ : State Unit) (a : SchedulerAction) :
    setSchedulerAction (Z := Unit) a σ = ({((), { σ with schedulerAction := a })}, False) := rfl

theorem rescheduleRequired_noswitch {σ : State Unit} (h : ∀ t, σ.schedulerAction ≠ .switchThread t) :
    rescheduleRequired (Z := Unit) σ = ({((), { σ with schedulerAction := .chooseNewThread })}, False) := by
  unfold rescheduleRequired
  rw [nd_gets_bind]
  cases e : σ.schedulerAction with
  | switchThread t => exact absurd e (h t)
  | _ => rfl

theorem rescheduleRequired_notsched {σ : State Unit} {t : ObjRef} (h : σ.schedulerAction = .switchThread t)
    (hs : schedulable t σ = false) :
    rescheduleRequired (Z := Unit) σ = ({((), { σ with schedulerAction := .chooseNewThread })}, False) := by
  unfold rescheduleRequired
  rw [nd_gets_bind, h]
  dsimp only
  rw [nd_gets_bind, hs]
  simp only [NonDet.when, Bool.false_eq_true, ↓reduceIte]
  rw [nd_bind_one (show NonDet.pure (σ := State Unit) () σ = ({((), σ)}, False) from rfl)]
  rfl

theorem rescheduleRequired_sched {σ σ1 : State Unit} {t : ObjRef} (h : σ.schedulerAction = .switchThread t)
    (hs : schedulable t σ = true) (hr : ActReady σ)
    (he : tcbSchedAction (Z := Unit) tcbSchedEnqueue t σ = ({((), σ1)}, False)) :
    rescheduleRequired (Z := Unit) σ = ({((), { σ1 with schedulerAction := .chooseNewThread })}, False) := by
  obtain ⟨x, scp, hk, hsc, h1, h2⟩ := hr t h hs
  have hm : (do
      let scOpt ← threadGet (Z := Unit) Tcb.tcbSchedContext t
      let scp ← NonDet.assertOpt scOpt
      let sufficient ← getScRefillSufficient scp 0
      let ready ← getScRefillReady scp
      NonDet.assert ((sufficient && ready) = true)
      tcbSchedAction tcbSchedEnqueue t) σ = ({((), σ1)}, False) := by
    rw [nd_bind_one (threadGet_eq _ hk), hsc]
    rw [nd_bind_one (show NonDet.assertOpt (σ := State Unit) (some scp) σ = ({(scp, σ)}, False) from rfl), nd_bind_one h1, nd_bind_one h2, nd_bind_one (assert_true (by rfl) σ)]
    exact he
  unfold rescheduleRequired
  rw [nd_gets_bind, h]
  dsimp only
  rw [nd_gets_bind, hs]
  simp only [NonDet.when, ↓reduceIte]
  rw [nd_bind_one hm]
  rfl

end Spec

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem FootEq.trans' {N T : Set U64} {m₁ m₂ m₃ : U64 → U64} (h₁ : FootEq N T m₁ m₂) (h₂ : FootEq N T m₂ m₃) :
    FootEq N T m₁ m₃ := fun a ha hf => (h₂ a ha hf).trans (h₁ a ha hf)

theorem FootEq.rfl' {N T : Set U64} {m : U64 → U64} : FootEq N T m m := fun _ _ _ => rfl

theorem resume_val' : sched.ACTION_RESUME_CURRENT = 0#u64 := by unfold sched.ACTION_RESUME_CURRENT; rfl
theorem choose_val' : sched.ACTION_CHOOSE_NEW = 1#u64 := by unfold sched.ACTION_CHOOSE_NEW; rfl

/-- **`reschedule_required` refines `reschedule_required`**. -/
theorem reschedule_required_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hR : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ) (hr : ActReady σ) :
    sched.reschedule_required st s ⦃ s' => ∃ σ', Fl4Spec.rescheduleRequired (Z := Unit) σ = ({((), σ')}, False) ∧
      σ'.kheap = σ.kheap ∧ σ'.releaseQueue = σ.releaseQueue ∧
      FootEq N T (L.mem s) (L.mem s') ∧ SchedRel st N T C c s' σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hcur := hc.cur
  have ha := hS.act
  unfold sched.reschedule_required
  step
  rw [act_post, hcur]
  have hpart : (if (nodeW st s c layout.node.SCHED_ACTION != sched.ACTION_RESUME_CURRENT) = true then
      if (nodeW st s c layout.node.SCHED_ACTION != sched.ACTION_CHOOSE_NEW) = true then do
        let b ← sched.is_schedulable st s (nodeW st s c layout.node.SCHED_ACTION)
        if b = true then sched.enqueue st s (nodeW st s c layout.node.SCHED_ACTION) else ok s
      else ok s
    else ok s) ⦃ s1 => ∃ σ1, Fl4Spec.rescheduleRequired (Z := Unit) σ =
        ({((), { σ1 with schedulerAction := .chooseNewThread })}, False) ∧ σ1.kheap = σ.kheap ∧
      σ1.releaseQueue = σ.releaseQueue ∧ FootEq N T (L.mem s) (L.mem s1) ∧ SchedRel st N T C c s1 σ1 ⦄ := by
    by_cases h0 : nodeW st s c layout.node.SCHED_ACTION = 0#u64
    · have hns : ∀ t, σ.schedulerAction ≠ .switchThread t := by
        intro t e; rw [e] at ha; exact ha.1 h0
      have hb : (nodeW st s c layout.node.SCHED_ACTION != sched.ACTION_RESUME_CURRENT) = false := by
        rw [resume_val', h0]; rfl
      rw [hb]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [WP.spec_ok]
      exact ⟨σ, rescheduleRequired_noswitch hns, rfl, rfl, FootEq.rfl', hS⟩
    · by_cases h1 : nodeW st s c layout.node.SCHED_ACTION = 1#u64
      · have hns : ∀ t, σ.schedulerAction ≠ .switchThread t := by
          intro t e; rw [e] at ha; exact ha.2.1 h1
        have hb0 : (nodeW st s c layout.node.SCHED_ACTION != sched.ACTION_RESUME_CURRENT) = true := by
          rw [resume_val']; simpa using h0
        have hb1 : (nodeW st s c layout.node.SCHED_ACTION != sched.ACTION_CHOOSE_NEW) = false := by
          rw [choose_val', h1]; rfl
        rw [hb0, hb1]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [WP.spec_ok]
        exact ⟨σ, rescheduleRequired_noswitch hns, rfl, rfl, FootEq.rfl', hS⟩
      · have hwT : nodeW st s c layout.node.SCHED_ACTION ∈ T := by
          rcases hS.actW with e | e | e
          · exact absurd e h0
          · exact absurd e h1
          · exact e
        have hsw : σ.schedulerAction = .switchThread (nodeW st s c layout.node.SCHED_ACTION).bv := by
          cases e : σ.schedulerAction <;> rw [e] at ha <;> simp only [ActRel] at ha <;>
            first | exact absurd ha h0 | exact absurd ha h1 | rw [ha.2.2]
        have hb0 : (nodeW st s c layout.node.SCHED_ACTION != sched.ACTION_RESUME_CURRENT) = true := by
          rw [resume_val']; simpa using h0
        have hb1 : (nodeW st s c layout.node.SCHED_ACTION != sched.ACTION_CHOOSE_NEW) = true := by
          rw [choose_val']; simpa using h1
        rw [hb0, hb1]
        simp only [↓reduceIte]
        step
        rw [schedulable_eq hR hS hwT] at b_post
        by_cases e3 : Fl4Spec.schedulable (nodeW st s c layout.node.SCHED_ACTION).bv σ = true
        · rw [b_post, e3]
          simp only [↓reduceIte]
          have hrel : (L.mem s (inqA (nodeW st s c layout.node.SCHED_ACTION)) &&& sched.Q_RELEASE) = 0#u64 := by
            have := e3; rw [← schedulable_eq hR hS hwT] at this
            exact (of_decide_eq_true this).2.2.2
          refine WP.spec_mono (enqueue_refines s σ hS _ hwT (fun _ => hrel)) ?_
          rintro s1 ⟨σ1, he, hk1, hr1, hf, hS1⟩
          exact ⟨σ1, rescheduleRequired_sched hsw e3 hr he, hk1, hr1, hf, hS1⟩
        · have e3' : Fl4Spec.schedulable (nodeW st s c layout.node.SCHED_ACTION).bv σ = false := by simpa using e3
          rw [b_post, e3']
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [WP.spec_ok]
          exact ⟨σ, rescheduleRequired_notsched hsw e3', rfl, rfl, FootEq.rfl', hS⟩
  refine WP.spec_bind hpart ?_
  rintro s1 ⟨σ1, hm, hk1, hr1, hf, hS1⟩
  step
  subst s'_post
  have hc1 := hS1.lists.choose_spec.choose_spec.1.cur
  rw [hc1, choose_val']
  exact ⟨{ σ1 with schedulerAction := .chooseNewThread }, hm, hk1, hr1,
    FootEq.trans' hf (node_wr_foot hS1 (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])),
    hS1.set_action (Or.inr (Or.inl rfl)) rfl⟩

/-! ## `possible_switch_to` -/

@[step] theorem sched.cur_domain.spec' (s : S) : sched.cur_domain st s ⦃ v => v = L.mem s (curDomA st s) ⦄ := by
  unfold sched.cur_domain; step*; simp_all [curDomA, layout.ks.CUR_DOMAIN]

theorem possibleSwitchTo_unfold {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) :
    Fl4Spec.possibleSwitchTo (Z := Unit) t σ =
      (if x.tcbSchedContext ≠ none ∧ ¬ Fl4Spec.inReleaseQueue t σ = true then
        (if x.tcbDomain ≠ σ.curDomain then Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedEnqueue t
         else if σ.schedulerAction ≠ .resumeCurThread then (do
           Fl4Spec.rescheduleRequired
           Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedEnqueue t)
         else Fl4Spec.setSchedulerAction (.switchThread t)) σ
      else ({((), σ)}, False)) := by
  unfold Fl4Spec.possibleSwitchTo Fl4Spec.getTcbObjRef
  rw [nd_bind_one (threadGet_eq _ hk), nd_gets_bind]
  unfold Fl4Spec.NonDet.when
  by_cases h : x.tcbSchedContext ≠ none ∧ ¬ Fl4Spec.inReleaseQueue t σ = true
  · simp only [eq_true h, ↓reduceIte]
    rw [nd_gets_bind, nd_bind_one (threadGet_eq _ hk), nd_gets_bind]
  · simp only [eq_false h, ↓reduceIte]
    rfl

theorem tcb_ne01 {t : U64} (h : TcbAddr t) : t ≠ 0#u64 ∧ t ≠ 1#u64 := by
  have := h.ne0; have := h.align
  refine ⟨fun e => by subst e; simp_all, fun e => by subst e; simp_all⟩

/-- **`possible_switch_to` refines `possible_switch_to`**. -/
theorem possible_switch_to_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hR : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ) (hr : ActReady σ) (t : U64) (ht : t ∈ T) :
    sched.possible_switch_to st s t ⦃ s' => ∃ σ', Fl4Spec.possibleSwitchTo (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      σ'.kheap = σ.kheap ∧ FootEq N T (L.mem s) (L.mem s') ∧ SchedRel st N T C c s' σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, hk, hd, hdw, hsc, -⟩ := hs.tcb t ht
  have hspec := possibleSwitchTo_unfold (t := t.bv) hk
  have hrel : Fl4Spec.inReleaseQueue t.bv σ = decide (t ∈ R) := by
    simp only [Fl4Spec.inReleaseQueue, hs.rel]; exact decide_eq_decide.2 mem_map_bv
  have hdom : ¬ x.tcbDomain ≠ σ.curDomain := by rw [hd, hs.curDom.1]; exact fun h => h rfl
  unfold sched.possible_switch_to
  step
  by_cases h0 : L.mem s (scA t) = 0#u64
  · rw [i_post]; simp only [h0, ↓reduceIte, WP.spec_ok]
    rw [h0, optRef_zero] at hsc
    refine ⟨σ, ?_, rfl, FootEq.rfl', hS⟩
    rw [hspec, ite_f (by rw [hsc]; simp)]
  · rw [i_post]; simp only [h0, ↓reduceIte]
    step
    by_cases h1 : (L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64
    · have hb : b = true := by rw [b_post]; exact decide_eq_true h1
      rw [hb]; simp only [↓reduceIte, WP.spec_ok]
      refine ⟨σ, ?_, rfl, FootEq.rfl', hS⟩
      rw [hspec, ite_f (by rw [hrel]; simp [(hc.released t ht).1 h1])]
    · have hb : b = false := by rw [b_post]; exact decide_eq_false h1
      have h1' : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := not_not.1 h1
      have htR : t ∉ R := fun hm => h1 ((hc.released t ht).2 hm)
      have hcond : x.tcbSchedContext ≠ none ∧ ¬ Fl4Spec.inReleaseQueue t.bv σ = true := by
        rw [hsc, optRef_ne h0, hrel]; simp [htR]
      rw [hspec, ite_t hcond, ite_f hdom] at *
      rw [hb]; simp only [Bool.false_eq_true, ↓reduceIte]
      step
      step
      rw [i1_post, i2_post, hs.curDom.2, hdw]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      step
      step
      rw [i3_post, i4_post, hc.aff t ht, hc.cur]
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      step
      rw [i5_post, hc.cur]
      have ha := hS.act
      by_cases h5 : nodeW st s c layout.node.SCHED_ACTION = 0#u64
      · have hres : σ.schedulerAction = .resumeCurThread := by
          cases e : σ.schedulerAction <;> rw [e] at ha <;> simp only [ActRel] at ha <;>
            first | rfl | exact absurd h5 ha.1 | (rw [h5] at ha; exact absurd ha (by decide))
        have hb5 : (nodeW st s c layout.node.SCHED_ACTION != sched.ACTION_RESUME_CURRENT) = false := by
          rw [resume_val', h5]; rfl
        rw [hb5]; simp only [Bool.false_eq_true, ↓reduceIte]
        step
        subst s'_post
        rw [hc.cur]
        obtain ⟨n0, n1⟩ := tcb_ne01 (hc.tcbs t ht)
        refine ⟨{ σ with schedulerAction := .switchThread t.bv }, ?_, rfl,
          node_wr_foot hS (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]),
          hS.set_action (Or.inr (Or.inr ht)) ⟨n0, n1, rfl⟩⟩
        rw [hspec, ite_f (by rw [hres]; exact fun h => h rfl)]
        rfl
      · have hnres : σ.schedulerAction ≠ .resumeCurThread := by
          intro e; rw [e] at ha; exact h5 ha
        have hb5 : (nodeW st s c layout.node.SCHED_ACTION != sched.ACTION_RESUME_CURRENT) = true := by
          rw [resume_val']; simpa using h5
        rw [hb5]; simp only [↓reduceIte]
        refine WP.spec_bind (reschedule_required_refines s σ hR hS hr) ?_
        rintro s1 ⟨σ1, hrr, hk1, hr1, hf1, hS1⟩
        obtain ⟨Q1, R1, hc1, hs1⟩ := hS1.lists
        have hrel1 : (L.mem s1 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
          by_contra hne
          have hm := (hc1.released t ht).1 hne
          apply htR
          have : t.bv ∈ σ.releaseQueue := by rw [← hr1, hs1.rel]; exact List.mem_map_of_mem hm
          rw [hs.rel, mem_map_bv] at this; exact this
        refine WP.spec_mono (enqueue_refines s1 σ1 hS1 t ht (fun _ => hrel1)) ?_
        rintro s2 ⟨σ2, he, hk2, -, hf2, hS2⟩
        refine ⟨σ2, ?_, hk2.trans hk1, FootEq.trans' hf1 hf2, hS2⟩
        rw [hspec, ite_t hnres, nd_bind_one hrr, he]

end

end

end Fl4Proofs.P3.Sched
