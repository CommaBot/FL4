/-
P3 (DESIGN.md §9), scheduling contexts: **`postpone`** (`postpone_refines`):
the SC's thread leaves its ready queue (`dequeue_refines`), enters the
release queue (`release_enqueue_refines`), and the timer is reprogrammed
(`SchedRel.set_reprogram`), for a thread with an SC that is not in the
release queue, given `RelOK`.
-/
import Fl4Proofs.P3.ScRelease
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

theorem readTcbReadyTime_congr {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) {u p : ObjRef} {x : Tcb}
    {y : SchedContext} {n : Nat} (hk : σ.kheap u = some (.tcb x)) (hsc : x.tcbSchedContext = some p)
    (hky : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills ≠ []) :
    readTcbReadyTime (Z := Unit) u σ' = readTcbReadyTime (Z := Unit) u σ := by
  rw [readTcbReadyTime_eq hk hsc hky hne, readTcbReadyTime_eq (by rw [h]; exact hk) hsc (by rw [h]; exact hky) hne]

end Spec

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- `RelOK` only reads the heap and the release queue. -/
theorem RelOK.transfer' {N T C : Set U64} {c : U64} {s : S} {σ σ' : Fl4Spec.State Unit} (h : RelOK σ)
    (hS : SchedRel st N T C c s σ) (hq : σ'.releaseQueue = σ.releaseQueue)
    (htcb : ∀ u ∈ σ.releaseQueue, ∀ x, σ.kheap u = some (.tcb x) → σ'.kheap u = some (.tcb x))
    (hscs : ∀ p y n, σ.kheap p = some (.schedContext y n) → ∃ y', σ'.kheap p = some (.schedContext y' n) ∧
      y'.scRefills = y.scRefills) :
    RelOK σ' := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hrt : ∀ u ∈ σ.releaseQueue, specRt σ' u = specRt σ u := by
    intro u hu
    obtain ⟨x, p, hkx, hsc⟩ := h.sc u hu
    rw [hs.rel] at hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
    obtain ⟨x', hk', -, -, hsc', -⟩ := hs.tcb v (hc.release.mem v hv)
    rw [hkx] at hk'; cases hk'
    rw [hsc'] at hsc
    have h0 := (optRef_some hsc).1
    obtain ⟨y, n, hky, hy⟩ := hs.scs _ (hs.scMem v (hc.release.mem v hv) h0)
    rw [(optRef_some hsc).2] at hky
    have hne : y.scRefills ≠ [] := by rw [hy.refills]; exact refills_ne hy.wf
    obtain ⟨y', hky', hrf⟩ := hscs _ y n hky
    have hu' : v.bv ∈ σ.releaseQueue := by rw [hs.rel]; exact List.mem_map_of_mem hv
    unfold specRt
    rw [readTcbReadyTime_eq hkx (by rw [hsc', hsc]) hky hne,
      readTcbReadyTime_eq (htcb _ hu' x hkx) (by rw [hsc', hsc]) hky' (by rw [hrf]; exact hne)]
    unfold Fl4Spec.refillHd; rw [hrf]
  refine ⟨fun u hu => ?_, ?_⟩
  · rw [hq] at hu; obtain ⟨x, p, hkx, hsc⟩ := h.sc u hu
    exact ⟨x, p, htcb u hu x hkx, hsc⟩
  · rw [hq]
    exact List.Pairwise.imp_of_mem (fun {a b} ha hb hab => by rw [hrt a ha, hrt b hb]; exact hab) h.sorted

theorem RelOK.transfer {N T C : Set U64} {c : U64} {s : S} {σ σ' : Fl4Spec.State Unit} (h : RelOK σ)
    (hS : SchedRel st N T C c s σ) (hk : σ'.kheap = σ.kheap) (hq : σ'.releaseQueue = σ.releaseQueue) :
    RelOK σ' :=
  h.transfer' hS hq (fun _ _ x hx => by rw [hk]; exact hx) (fun p y n hy => ⟨y, by rw [hk]; exact hy, rfl⟩)

theorem scTcbA_eq (sc : U64) : scTcbA sc = scW sc 24#u64 := by unfold scTcbA scW layout.sc.TCB; rfl
theorem scCoreA_eq (sc : U64) : scCoreA sc = scW sc 16#u64 := by unfold scCoreA scW layout.sc.CORE; rfl

/-- **`postpone` refines `postpone`**, for the SC's thread `t`, which has an
SC and is not in the release queue, given `RelOK`. -/
theorem postpone_refines {N T C : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hRel : RelOK σ) {sc : U64} (hsc : sc ∈ C) {t : U64} (ht : t ∈ T)
    (htw : L.mem s (scW sc 24#u64) = t) (h0 : L.mem s (scA t) ≠ 0#u64)
    (hr0 : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64) :
    sched.postpone st s sc ⦃ s' => ∃ σ', Fl4Spec.postpone (Z := Unit) sc.bv σ = ({((), σ')}, False) ∧
      σ'.kheap = σ.kheap ∧ σ'.schedulerAction = σ.schedulerAction ∧ σ'.curTime = σ.curTime ∧
      (∀ u, u ∈ σ'.releaseQueue ↔ u = t.bv ∨ u ∈ σ.releaseQueue) ∧
      FootEq N T (L.mem s) (L.mem s') ∧ WritesIn st s s' (SFoot st T c s) ∧ SchedRel st N T C c s' σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb t ht
  have ht0 : t ≠ 0#u64 := fun e => (hc.tcbs t ht).ne0 (by rw [e]; rfl)
  have hspec : Fl4Spec.postpone (Z := Unit) sc.bv σ = (do
      Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedDequeue t.bv
      Fl4Spec.tcbReleaseEnqueue t.bv
      Fl4Spec.NonDet.modify fun s : Fl4Spec.State Unit => { s with reprogramTimer := true }) σ := by
    have hg : Fl4Spec.getScObjRef (Z := Unit) Fl4Spec.SchedContext.scTcb sc.bv σ = ({(x.scTcb, σ)}, False) := by
      unfold Fl4Spec.getScObjRef; rw [nd_bind_one (getSchedContext_eq hk)]; rfl
    unfold Fl4Spec.postpone
    rw [nd_bind_one hg, hx.tcb, htw, optRef_ne ht0]
    exact nd_bind_one (show Fl4Spec.NonDet.assertOpt (σ := Fl4Spec.State Unit) (some t.bv) σ = ({(t.bv, σ)}, False)
      from rfl) _
  unfold sched.postpone
  step as ⟨i, i_post⟩
  have hi : i = t := by rw [i_post, scTcbA_eq, htw]
  subst hi
  refine WP.spec_bind (WP.spec_and (dequeue_refines s σ hS i ht) (dequeue_sfoot hS ht)) ?_
  rintro s1 ⟨⟨σ1, hd, hk1, hq1, hf1, hS1⟩, hw1⟩
  obtain ⟨Q1, R1, hc1, hs1⟩ := hS1.lists
  -- the thread is in no queue now, and still has its SC
  have hxt1 : σ1.kheap i.bv = some (.tcb xt) := by rw [hk1]; exact hkt
  obtain ⟨xt1, hkt1, -, -, hsct1, hpr1⟩ := hs1.tcb i ht
  rw [hxt1] at hkt1; cases hkt1
  have h01 : L.mem s1 (scA i) ≠ 0#u64 := by
    intro e; rw [e, optRef_zero, hsct, optRef_ne h0] at hsct1; cases hsct1
  have hr01 : (L.mem s1 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hne
    have hm := (hc1.released i ht).1 hne
    have : i.bv ∈ σ.releaseQueue := by rw [← hq1, hs1.rel]; exact List.mem_map_of_mem hm
    rw [hs.rel, mem_map_bv] at this
    exact (hc.released i ht).2 this hr0
  have hq01 : (L.mem s1 (inqA i) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hne
    have hm := (hc1.queued i ht).1 hne
    -- σ1's queue of `i`'s priority is the old one without `i`
    obtain ⟨xd, hkd, hdd, -, -, hprd⟩ := hs.tcb i ht
    rw [hkt] at hkd; cases hkd
    have e := tcbSchedAction_eq hkt hdd Fl4Spec.tcbSchedDequeue
    rw [hd] at e
    have e' := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst e))).2
    have hp1 : (L.mem s1 (prioA i)).val < 256 := hc1.prio i ht
    have := hs1.rq _ hp1
    rw [e', specPrio_eq hpr1] at this
    simp only [setRq, true_and, ↓reduceIte] at this
    have hmem : i.bv ∈ Fl4Spec.tcbSchedDequeue i.bv (σ.readyQueues 0 xt.tcbPriority) := by
      rw [this]; exact List.mem_map_of_mem hm
    simp [Fl4Spec.tcbSchedDequeue] at hmem
  have hRel1 : RelOK σ1 := hRel.transfer hS hk1 hq1
  refine WP.spec_bind (WP.spec_and (release_enqueue_refines s1 σ1 hS1 hRel1 i ht h01 hq01 hr01)
    (release_enqueue_sfoot hS1 ht hr01)) ?_
  rintro s2 ⟨⟨q, b, he, hqm, hf2, hS2⟩, hw2⟩
  step as ⟨cpu, cpu_post⟩
  have hcpu : cpu = c := by rw [cpu_post, scCoreA_eq]; exact hS2.core sc hsc
  subst hcpu
  step as ⟨s3, s3_post⟩
  have hc2 := hS2.lists.choose_spec.choose_spec.1.cur
  obtain ⟨hS3, hf3, hw3⟩ := hS2.set_reprogram
  rw [← s3_post] at hS3 hf3 hw3
  have hw3' : WritesIn st s2 s3 (SFoot st T cpu s2) := hw3.mono fun b hb => by
    subst hb; exact sfoot_node hS2.lists.choose_spec.choose_spec.1.node (by simp [layout.node.REPROGRAM])
  have hσ1 : σ1 = setRq σ xt.tcbPriority (Fl4Spec.tcbSchedDequeue i.bv (σ.readyQueues 0 xt.tcbPriority)) := by
    obtain ⟨xd, hkd, hdd, -, -, -⟩ := hs.tcb i ht
    rw [hkt] at hkd; cases hkd
    have e := tcbSchedAction_eq hkt hdd Fl4Spec.tcbSchedDequeue
    rw [hd] at e
    exact (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst e))).2
  refine ⟨_, ?_, by rw [← hk1]; rfl, by rw [hσ1]; rfl, by rw [hσ1]; rfl, fun u => ?_,
    FootEq.trans' (FootEq.trans' hf1 hf2) hf3, WritesIn.sfoot_trans (WritesIn.sfoot_trans hw1 hw2) hw3', hS3⟩
  · rw [hspec, nd_bind_one hd, nd_bind_one he]
    rfl
  · show u ∈ q ↔ _
    rw [hqm, hq1]

end

/-! ## `sched_context_resume` -/

section Spec
open Fl4Spec

theorem schedulable_rel {σ : State Unit} {t : ObjRef} (h : t ∈ σ.releaseQueue) : schedulable t σ = false := by
  unfold schedulable; simp [h]

theorem getTcbQueue_eq (σ : State Unit) (d : Domain) (p : Priority) :
    getTcbQueue (Z := Unit) d p σ = ({(σ.readyQueues d p, σ)}, False) := by
  unfold getTcbQueue
  rw [nd_gets_bind]; rfl

/-- The spec's `sched_context_resume` on a bound SC. -/
theorem resume_spec_eq {σ : State Unit} {p t : ObjRef} {x : SchedContext} {n : Nat} {xt : Tcb}
    (hk : σ.kheap p = some (.schedContext x n)) (htc : x.scTcb = some t) (hkt : σ.kheap t = some (.tcb xt))
    (hne : x.scRefills ≠ [])
    (hrun : schedulable t σ = true → runnable xt.tcbState = true ∧ scActive x = true)
    (hnq : schedulable t σ = true → t ∉ σ.readyQueues xt.tcbDomain xt.tcbPriority) :
    schedContextResume (Z := Unit) p σ =
      if schedulable t σ = true ∧ ¬(refillReady σ.curTime (refillHd x) = true ∧
        refillSufficient 0 (refillHd x) = true) then postpone p σ else ({((), σ)}, False) := by
  unfold schedContextResume
  rw [nd_bind_one (getSchedContext_eq hk), htc,
    nd_bind_one (show NonDet.assertOpt (σ := State Unit) (some t) σ = ({(t, σ)}, False) from rfl), nd_gets_bind]
  by_cases hs : schedulable t σ = true
  · obtain ⟨h1, h2⟩ := hrun hs
    simp only [NonDet.when, hs, ↓reduceIte, true_and]
    rw [nd_bind_one (threadGet_eq _ hkt), nd_bind_one (getScRefillReady_eq hk hne),
      nd_bind_one (getScRefillSufficient_eq hk hne 0)]
    by_cases hc : refillReady σ.curTime (refillHd x) = true ∧ refillSufficient 0 (refillHd x) = true
    · rw [ite_f (fun h => h.2.2 hc), ite_f (fun h => h hc)]; rfl
    · rw [ite_t ⟨h1, h2, hc⟩, ite_t hc]
      rw [nd_bind_one (threadGet_eq _ hkt), nd_bind_one (threadGet_eq _ hkt), nd_bind_one (getTcbQueue_eq _ _ _),
        nd_bind_one (assert_true (hnq hs) σ)]
  · simp only [NonDet.when, hs, Bool.false_eq_true, ↓reduceIte, false_and]; rfl

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`resume` refines `sched_context_resume`**, for an SC bound both ways
to a thread `t` that is in no ready queue, given `RelOK` and the platform's
`MIN_BUDGET`. Also: what `ActReady` needs afterwards. -/
theorem resume_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ) (hRel : RelOK σ)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {sc : U64} (hsc : sc ∈ C) (hsc0 : sc ≠ 0#u64) {t : U64} (ht : t ∈ T)
    (htw : L.mem s (scW sc 24#u64) = t) (hts : L.mem s (scA t) = sc)
    (hnq : ∀ x, σ.kheap t.bv = some (.tcb x) → t.bv ∉ σ.readyQueues x.tcbDomain x.tcbPriority) :
    schedcontext.resume st ar s a sc ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.schedContextResume (Z := Unit) sc.bv σ =
      ({((), σ')}, False) ∧ σ'.kheap = σ.kheap ∧ σ'.schedulerAction = σ.schedulerAction ∧
      σ'.curTime = σ.curTime ∧ (∀ u, u ∈ σ.releaseQueue → u ∈ σ'.releaseQueue) ∧
      (Fl4Spec.schedulable t.bv σ' = true → σ' = σ ∧
        Fl4Spec.getScRefillSufficient (Z := Unit) sc.bv 0 σ = ({(true, σ)}, False) ∧
        Fl4Spec.getScRefillReady (Z := Unit) sc.bv σ = ({(true, σ)}, False)) ∧
      FootEq N T (L.mem s) (L.mem r.1) ∧ WritesIn st s r.1 (SFoot st T c s) ∧ SchedRel st N T C c r.1 σ' ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
  obtain ⟨xt, hkt, hdt, -, hsct, hprt⟩ := hs.tcb t ht
  have hxt := hR.at_tcb ht hkt
  have ht0 : t ≠ 0#u64 := fun e => (hc.tcbs t ht).ne0 (by rw [e]; rfl)
  have hne : x.scRefills ≠ [] := by rw [hx.refills]; exact refills_ne hx.wf
  have hsched := schedulable_eq hR hS ht
  rw [hts] at hsched
  have hspec := resume_spec_eq (p := sc.bv) (t := t.bv) hk (by rw [hx.tcb, htw, optRef_ne ht0]) hkt hne
    (fun h => by
      rw [← hsched] at h
      obtain ⟨h1, -, h3, -⟩ := of_decide_eq_true h
      refine ⟨(runnable_iff hxt.st).1 h1, ?_⟩
      simp only [Fl4Spec.scActive, Fl4Spec.activeSc, decide_eq_true_eq, ← hx.max]
      rw [gt_iff_val] at h3; simpa using h3)
    (fun _ => hnq xt hkt)
  have fin : ∀ σ' (s' : S), Fl4Spec.schedContextResume (Z := Unit) sc.bv σ = ({((), σ')}, False) →
      σ' = σ → FootEq N T (L.mem s) (L.mem s') → WritesIn st s s' (SFoot st T c s) → SchedRel st N T C c s' σ' →
      (Fl4Spec.schedulable t.bv σ = true → Fl4Spec.getScRefillSufficient (Z := Unit) sc.bv 0 σ = ({(true, σ)}, False) ∧
        Fl4Spec.getScRefillReady (Z := Unit) sc.bv σ = ({(true, σ)}, False)) →
      (s', a).2 = a ∧ ∃ σ'', Fl4Spec.schedContextResume (Z := Unit) sc.bv σ = ({((), σ'')}, False) ∧
        σ''.kheap = σ.kheap ∧ σ''.schedulerAction = σ.schedulerAction ∧ σ''.curTime = σ.curTime ∧
        (∀ u, u ∈ σ.releaseQueue → u ∈ σ''.releaseQueue) ∧
        (Fl4Spec.schedulable t.bv σ'' = true → σ'' = σ ∧
          Fl4Spec.getScRefillSufficient (Z := Unit) sc.bv 0 σ = ({(true, σ)}, False) ∧
          Fl4Spec.getScRefillReady (Z := Unit) sc.bv σ = ({(true, σ)}, False)) ∧
        FootEq N T (L.mem s) (L.mem (s', a).1) ∧ WritesIn st s (s', a).1 (SFoot st T c s) ∧ SchedRel st N T C c (s', a).1 σ'' := by
    intro σ' s' he e hf hw hS' hrs
    subst e
    exact ⟨rfl, σ', he, rfl, rfl, rfl, fun _ h => h, fun h => ⟨rfl, hrs h⟩, hf, hw, hS'⟩
  unfold schedcontext.resume
  step as ⟨b, b_post⟩
  simp only [b_post, hsc0, decide_false, Bool.false_eq_true, ↓reduceIte]
  step as ⟨i, i_post⟩
  have hi : i = t := by rw [i_post, scTcbA_eq, htw]
  subst hi
  step as ⟨b1, b1_post⟩
  simp only [b1_post, ht0, decide_false, Bool.false_eq_true, ↓reduceIte]
  step with sched.is_schedulable.spec' as ⟨b2, b2_post⟩
  rw [hts, hsched] at b2_post
  subst b2_post
  by_cases hsb : Fl4Spec.schedulable i.bv σ = true
  · simp only [hsb, ↓reduceIte]
    have hr0 : (L.mem s (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by
      rw [← hsched] at hsb; exact (of_decide_eq_true hsb).2.2.2
    have hpost : sched.postpone st s sc ⦃ s1 => (s1, a).2 = a ∧ ∃ σ', Fl4Spec.schedContextResume (Z := Unit) sc.bv σ =
        ({((), σ')}, False) ∧ σ'.kheap = σ.kheap ∧ σ'.schedulerAction = σ.schedulerAction ∧
        σ'.curTime = σ.curTime ∧ (∀ u, u ∈ σ.releaseQueue → u ∈ σ'.releaseQueue) ∧
        (Fl4Spec.schedulable i.bv σ' = true → σ' = σ ∧
          Fl4Spec.getScRefillSufficient (Z := Unit) sc.bv 0 σ = ({(true, σ)}, False) ∧
          Fl4Spec.getScRefillReady (Z := Unit) sc.bv σ = ({(true, σ)}, False)) ∧
        FootEq N T (L.mem s) (L.mem (s1, a).1) ∧ WritesIn st s (s1, a).1 (SFoot st T c s) ∧ SchedRel st N T C c (s1, a).1 σ' ⦄ →
        (do let s1 ← sched.postpone st s sc; ok (s1, a)) ⦃ r => r.2 = a ∧ ∃ σ', Fl4Spec.schedContextResume (Z := Unit) sc.bv σ =
        ({((), σ')}, False) ∧ σ'.kheap = σ.kheap ∧ σ'.schedulerAction = σ.schedulerAction ∧
        σ'.curTime = σ.curTime ∧ (∀ u, u ∈ σ.releaseQueue → u ∈ σ'.releaseQueue) ∧
        (Fl4Spec.schedulable i.bv σ' = true → σ' = σ ∧
          Fl4Spec.getScRefillSufficient (Z := Unit) sc.bv 0 σ = ({(true, σ)}, False) ∧
          Fl4Spec.getScRefillReady (Z := Unit) sc.bv σ = ({(true, σ)}, False)) ∧
        FootEq N T (L.mem s) (L.mem r.1) ∧ WritesIn st s r.1 (SFoot st T c s) ∧ SchedRel st N T C c r.1 σ' ⦄ := fun h =>
      WP.spec_bind h fun s1 h1 => by simp only [WP.spec_ok]; exact ⟨trivial, h1.2⟩
    have hpp : ¬(Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd x) = true ∧
        Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd x) = true) →
        sched.postpone st s sc ⦃ s1 => (s1, a).2 = a ∧ ∃ σ', Fl4Spec.schedContextResume (Z := Unit) sc.bv σ =
        ({((), σ')}, False) ∧ σ'.kheap = σ.kheap ∧ σ'.schedulerAction = σ.schedulerAction ∧
        σ'.curTime = σ.curTime ∧ (∀ u, u ∈ σ.releaseQueue → u ∈ σ'.releaseQueue) ∧
        (Fl4Spec.schedulable i.bv σ' = true → σ' = σ ∧
          Fl4Spec.getScRefillSufficient (Z := Unit) sc.bv 0 σ = ({(true, σ)}, False) ∧
          Fl4Spec.getScRefillReady (Z := Unit) sc.bv σ = ({(true, σ)}, False)) ∧
        FootEq N T (L.mem s) (L.mem (s1, a).1) ∧ WritesIn st s (s1, a).1 (SFoot st T c s) ∧ SchedRel st N T C c (s1, a).1 σ' ⦄ := by
      intro hnr
      refine WP.spec_mono (postpone_refines s σ hS hRel hsc ht htw (by rw [hts]; exact hsc0) hr0) ?_
      rintro s1 ⟨σ', hp, hk', ha', hct', hrq', hf, hw, hS'⟩
      refine ⟨rfl, σ', by rw [hspec, ite_t ⟨hsb, hnr⟩]; exact hp, hk', ha', hct',
        fun u hu => (hrq' u).2 (Or.inr hu), fun h => ?_, hf, hw, hS'⟩
      rw [schedulable_rel ((hrq' _).2 (Or.inl rfl))] at h; cases h
    refine WP.spec_bind (ready_refines s σ hS hsc hk) ?_
    intro b3 hb3
    rw [getScRefillReady_eq hk hne] at hb3
    have eb3 := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb3))).1
    by_cases h3 : b3 = true
    · simp only [h3, ↓reduceIte]
      refine WP.spec_bind (sufficient_refines s a σ hS hsc hk 0#u64 hmb) ?_
      intro b4 hb4
      rw [getScRefillSufficient_eq hk hne] at hb4
      have eb4 := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb4))).1
      by_cases h4 : b4 = true
      · simp only [h4, ↓reduceIte, WP.spec_ok]
        have hok : Fl4Spec.refillReady σ.curTime (Fl4Spec.refillHd x) = true ∧
            Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd x) = true := ⟨eb3.trans h3, eb4.trans h4⟩
        refine ⟨trivial, (fin σ s (by rw [hspec, ite_f (fun h => h.2 hok)]) rfl FootEq.rfl' (WritesIn.refl _ _) hS fun _ => ⟨?_, ?_⟩).2⟩
        · rw [getScRefillSufficient_eq hk hne, hok.2]
        · rw [getScRefillReady_eq hk hne, hok.1]
      · simp only [h4, Bool.false_eq_true, ↓reduceIte]
        exact hpost (hpp fun h => h4 (eb4.symm.trans h.2))
    · simp only [h3, Bool.false_eq_true, ↓reduceIte]
      exact hpost (hpp fun h => h3 (eb3.symm.trans h.1))
  · simp only [hsb, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨trivial, (fin σ s (by rw [hspec, ite_f (fun h => hsb h.1)]) rfl FootEq.rfl' (WritesIn.refl _ _) hS (fun h => absurd h hsb)).2⟩

end

end

end Fl4Proofs.P3.Sched
