/-
P3 (DESIGN.md §9), scheduling contexts: **SchedContext `Bind` (thread)**
against l4v `sched_context_bind_tcb`.

* `InvBut.unblock`: `refill_unblock_check` keeps `Inv` except `rd` for one
  thread (as `Inv.unblock`).
* `bind_tcb_refines`: `bind_tcb` of an unbound SC and a TCB with no SC
  (both links set, the migration a no-op on one core, the sporadic unblock
  check, `sched_context_resume`, then enqueue and reschedule if
  schedulable), ending in `Inv`; `ActIdle` when the action is
  `resume_cur_thread` at entry and the thread is not the idle thread. The
  decoder's check that a blocked thread gets a released SC is a hypothesis.
-/
import Fl4Proofs.P3.ScUnbind
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- **`refill_unblock_check` keeps `Inv` except `rd` for `t`**, if no
release-queue member is bound to the SC. -/
theorem InvBut.unblock {σ σ' : State Unit} {t : ObjRef} (h : InvBut σ t) {p : ObjRef} {y : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext y n)) (hne : y.scRefills ≠ [])
    (hnr : refillReady σ.curTime (refillHd y) = true → y.scPeriod ≠ 0 →
      ∀ u ∈ σ.releaseQueue, ∀ x, σ.kheap u = some (.tcb x) → x.tcbSchedContext ≠ some p)
    {r : Unit} (hm : (r, σ') ∈ (refillUnblockCheck (Z := Unit) p σ).1) : InvBut σ' t := by
  rcases unblock_result hk hne hm with ⟨rfl, -⟩ | ⟨z, rfl, hzR, hzt, hzy, hrdy, hzne, hper⟩
  · exact h
  have hnr' := hnr hrdy hper
  have hzper : z.scPeriod = y.scPeriod := by rw [hzy]
  have hkp : ∀ q, q ≠ p → (updSc { σ with reprogramTimer := true } p z n).kheap q = σ.kheap q := fun q hq => by
    simp [updK, hq]
  have hkz : (updSc { σ with reprogramTimer := true } p z n).kheap p = some (.schedContext z n) := by simp [updK]
  have hzact : scActive z = scActive y := by rw [hzy]
  have htcb : ∀ u x, (updSc { σ with reprogramTimer := true } p z n).kheap u = some (.tcb x) →
      σ.kheap u = some (.tcb x) := fun u x hx => by
    by_cases e : u = p
    · subst e; rw [hkz] at hx; cases hx
    · rw [hkp u e] at hx; exact hx
  refine ⟨fun d q u hu => ?_, fun u hu => ?_, ?_, fun u x hut hx hc => ?_, fun q w m hw => ?_,
    fun u x q hx hq => ?_, fun q x q' hx hq => ?_, fun q w m hw => ?_, fun q w m hw => ?_⟩
  · have h0 := h.rq d q u hu
    have : u ≠ p := by obtain ⟨x, -, -, -, h1, -⟩ := h0; rintro rfl; rw [hk] at h1; cases h1
    exact RqOK.upd h0 hkp (fun y' n' h => by rw [hk] at h; cases h; exact ⟨z, hkz, hzact⟩) this
  · obtain ⟨x, scp, w, m, h1, h2, h3, h4, h5⟩ := h.rel u hu
    have hup : u ≠ p := by rintro rfl; rw [hk] at h1; cases h1
    have hsp : scp ≠ p := fun e => hnr' u hu x h1 (e ▸ h2)
    exact ⟨x, scp, w, m, by rw [hkp u hup]; exact h1, h2, h3, by rw [hkp scp hsp]; exact h4, h5⟩
  · show σ.releaseQueue.Pairwise _
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h.sorted
    obtain ⟨xa, pa, ya, na, h1, h2, -, h4, h5⟩ := h.rel a ha
    obtain ⟨xb, pb, yb, nb, g1, g2, -, g4, g5⟩ := h.rel b hb
    have nea := h.ne _ _ _ h4 h5
    have neb := h.ne _ _ _ g4 g5
    have hap : a ≠ p := by rintro rfl; rw [hk] at h1; cases h1
    have hbp : b ≠ p := by rintro rfl; rw [hk] at g1; cases g1
    have hpa : pa ≠ p := fun e => hnr' a ha xa h1 (e ▸ h2)
    have hpb : pb ≠ p := fun e => hnr' b hb xb g1 (e ▸ g2)
    rw [specRt_eq (by rw [hkp a hap]; exact h1) h2 (by rw [hkp pa hpa]; exact h4) nea,
      specRt_eq (by rw [hkp b hbp]; exact g1) g2 (by rw [hkp pb hpb]; exact g4) neb]
    rw [specRt_eq h1 h2 h4 nea, specRt_eq g1 g2 g4 neb] at hab
    exact hab
  · have hx0 := htcb u x hx
    intro x' scp w m h1 h2 h3 h4 h5
    rw [hx] at h1; cases h1
    by_cases e : scp = p
    · subst e
      rw [hkz] at h3; cases h3
      exact ⟨ready_now _ _ hzt, sufficient_of_refOK (hzR (h.refills _ y n hk (hzact ▸ h4) hper))⟩
    · rw [hkp scp e] at h3
      exact h.rd u x hut hx0 hc x scp w m hx0 h2 h3 h4 h5
  · by_cases e : q = p
    · subst e; rw [hkz] at hw; cases hw; intro ha _; exact hzR (h.refills _ y n hk (hzact ▸ ha) hper)
    · rw [hkp q e] at hw; exact h.refills q w m hw
  · obtain ⟨w, m, h1, h2⟩ := h.back u x q (htcb u x hx) hq
    by_cases e : q = p
    · subst e; rw [hk] at h1; cases h1
      exact ⟨z, n, hkz, by rw [hzy]; exact h2⟩
    · exact ⟨w, m, by rw [hkp q e]; exact h1, h2⟩
  · have hx0 : σ.kheap q = some (.notification x) := by
      by_cases e : q = p
      · subst e; rw [hkz] at hx; cases hx
      · rw [hkp q e] at hx; exact hx
    obtain ⟨w, m, h1⟩ := h.ntfnSc q x q' hx0 hq
    by_cases e : q' = p
    · subst e; exact ⟨z, n, hkz⟩
    · exact ⟨w, m, by rw [hkp q' e]; exact h1⟩
  · by_cases e : q = p
    · subst e; rw [hkz] at hw; cases hw; exact fun _ => hzne
    · rw [hkp q e] at hw; exact h.ne q w m hw
  · by_cases e : q = p
    · subst e; rw [hkz] at hw; cases hw; intro _ hp0; exact absurd (hzper.symm.trans hp0) hper
    · rw [hkp q e] at hw; exact h.rr q w m hw


/-- The spec's sporadic-and-active unblock check of an SC. -/
theorem ifSporadicActive_some {σ : State Unit} {p : ObjRef} {x : SchedContext} {n : Nat}
    (hk : σ.kheap p = some (.schedContext x n)) :
    ifSporadicActiveCurScTestRefillUnblockCheck (Z := Unit) (some p) σ =
      (if x.scSporadic = true ∧ scActive x = true ∧ ¬ p = σ.curSc then refillUnblockCheck p σ
        else ({((), σ)}, False)) := by
  unfold ifSporadicActiveCurScTestRefillUnblockCheck ifCondRefillUnblockCheck
  simp only [NonDet.maybeM]
  rw [nd_bind_one (getSchedContext_eq hk), nd_gets_bind, nd_pure_bind']
  simp only [NonDet.when]
  by_cases e : x.scSporadic = true ∧ scActive x = true ∧ ¬ p = σ.curSc
  · obtain ⟨e1, e2, e3⟩ := e
    simp [e1, e2, e3]
  · rw [ite_f (c := x.scSporadic = true ∧ scActive x = true ∧ ¬ p = σ.curSc) e]
    have : ¬ ((x.scSporadic = true ∧ scActive x = true) ∧ (True → p ≠ σ.curSc)) :=
      fun h => e ⟨h.1.1, h.1.2, h.2 trivial⟩
    rw [ite_f this]; rfl

theorem updSc_updK_comm (σ : State Unit) {p t : ObjRef} (hpt : p ≠ t) (A : KernelObject) (B : SchedContext)
    (n : Nat) : updSc (updK σ t A) p B n = updK (updSc σ p B n) t A := by
  cases σ; simp only [updSc, updK]; rw [Function.update_comm (Ne.symm hpt)]

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- `NSC` holds if only an SC changed. -/
theorem NSC.of_off {N C : Set U64} {σ σ' : Fl4Spec.State Unit} (h : NSC N C σ) {p : Fl4Spec.ObjRef}
    (hq : ∀ q, q ≠ p → σ'.kheap q = σ.kheap q) (hp : ∃ y n, σ'.kheap p = some (.schedContext y n)) :
    NSC N C σ' := by
  intro m hm x q hx hq'
  by_cases e : m.bv = p
  · subst e; obtain ⟨y, n, hy⟩ := hp; rw [hy] at hx; cases hx
  · rw [hq _ e] at hx; exact h m hm x q hx hq'

/-- **`bind_tcb` refines `sched_context_bind_tcb`**, for an unbound SC `p`
and a thread `t` with no SC; a blocked thread's SC is released (the
decoder's check). -/
theorem bind_tcb_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    {p : U64} (hp : p ∈ C) (hp0 : p ≠ 0#u64) {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap p.bv = some (.schedContext y n)) (hy0 : y.scTcb = none)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt)) (hxt0 : xt.tcbSchedContext = none)
    (hblk : Fl4Spec.runnable xt.tcbState = false → inClass xt.tcbState → Fl4Spec.scActive y = true → released σ y)
    (hT : TimeAgree ar) :
    schedcontext.bind_tcb st ar s a p t ⦃ r => ∃ σ',
      Fl4Spec.schedContextBindTcb (Z := Unit) p.bv t.bv σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ.schedulerAction = .resumeCurThread → IdleOK σ → t.bv ≠ σ.idleThread → ActIdle σ') ∧
      WritesIn st s r.1 (KFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hS0 := hS
  have hal24 : Aligned (scW p 24#u64) := by
    obtain ⟨x0, n0, -, hx0⟩ := hs.scs p hp; exact (hx0.hdr (K := 24#u64) (by simp) (by simp)).1
  have hsw24 := sw_hdr hS hp (K := 24#u64) (by simp) (by simp) (by decide)
  have hP := hS.placed
  have ht0 : t ≠ 0#u64 := fun e => (hc.tcbs t ht).ne0 (by rw [e]; rfl)
  have hpt : p.bv ≠ t.bv := fun e => by rw [e, hkt] at hk; cases hk
  have hnq0 : NotQueued σ t.bv := by
    refine ⟨fun d q hm => ?_, fun hm => ?_⟩
    · obtain ⟨x, _, _, _, h1, h2, -⟩ := hI.rq d q _ hm; rw [hkt] at h1; cases h1; rw [hxt0] at h2; cases h2
    · obtain ⟨x, _, _, _, h1, h2, -⟩ := hI.rel _ hm; rw [hkt] at h1; cases h1; rw [hxt0] at h2; cases h2
  unfold schedcontext.bind_tcb
  -- the two links
  refine WP.spec_bind (obj.Tcb.set_sc.spec' s t p) ?_
  rintro s1 rfl
  obtain ⟨hS1, hf1, hK1⟩ := hS.set_tcb_sc ht hkt (v := p) (Or.inr hp)
  rw [optRef_ne hp0] at hS1 hK1
  have hka : (updK σ t.bv (.tcb { xt with tcbSchedContext := some p.bv })).kheap p.bv =
      some (.schedContext y n) := by simp only [updK_kheap, Function.update_of_ne hpt]; exact hk
  have w1 : WritesIn st s (L.wr s (scA t) p) (SFoot st T c s) :=
    writesIn_tcb (K := 3464#u64) hc.tcbs ht (by unfold SOff SOffL; decide) (by simp) p
  refine WP.spec_bind (obj.Sc.set_tcb.spec' _ p t) ?_
  rintro s2 rfl
  have w2 : WritesIn st s (L.wr (L.wr s (scA t) p) (scW p 24#u64) t) (KFoot st T N C c s σ) :=
    WritesIn.kfoot_sw (WritesIn.kfoot_of_sfoot w1) ((writesIn_wr hal24).mono fun b hb => hb ▸ hsw24)
  obtain ⟨hS2, hf2, hK2⟩ := hS1.set_sc_tcb hp hka t
  rw [optRef_ne ht0] at hS2 hK2
  set σd := updSc (updK σ t.bv (.tcb { xt with tcbSchedContext := some p.bv })) p.bv
    { y with scTcb := some t.bv } n with hσd
  have hR2 : NtfnStateRel N T (L.mem (L.wr (L.wr s (scA t) p) (scW p 24#u64) t)) σd :=
    (hR.frame hP hf1 hK1).frame hS1.placed hf2 hK2
  have hN2 : NSC N C σd := hN.updTcb.updSc
  have hId : InvBut σd t.bv := by
    rw [hσd, updSc_updK_comm σ hpt]; exact hI.donated hk hy0 hkt hpt hnq0
  have hkd : σd.kheap p.bv = some (.schedContext { y with scTcb := some t.bv } n) := by simp [σd, updK]
  have hktd : σd.kheap t.bv = some (.tcb { xt with tcbSchedContext := some p.bv }) := by
    simp [σd, updK, Ne.symm hpt]
  -- the migration (one core)
  step with obj.Sc.cpu.spec as ⟨i, hi⟩
  have hic : i = c := by rw [hi, scCoreA_eq]; exact hS2.core p hp
  subst hic
  unfold smp.migrate_tcb
  step with obj.Tcb.affinity.spec as ⟨j, hj⟩
  obtain ⟨Q2, R2, hc2, hs2⟩ := hS2.lists
  have hji : j = i := by rw [hj]; exact hc2.aff t ht
  subst hji
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
  have hS3 := hS2
  have w3 := w2
  have hR3 := hR2
  obtain ⟨Q3, R3, hc3, hs3⟩ := hS3.lists
  obtain ⟨x3, n3, hk3', hx3⟩ := hs3.scs p hp
  rw [hkd] at hk3'; cases hk3'
  have hne : Fl4Spec.scActive y = true → y.scRefills ≠ [] := hI.ne p.bv y n hk
  -- the unblock check
  step with sporadic.sc_sporadic.spec' as ⟨b, hb⟩
  have hbb : b = y.scSporadic := by
    rw [hb, show y.scSporadic = _ from hx3.sporadic]; simp [hp0] <;> exact Iff.rfl
  subst hbb
  -- the unblock check
  have P2 : ∀ s3 : S, SchedRel st N T C j s3 σd → NtfnStateRel N T (L.mem s3) σd →
      ScRelW st s3 p { y with scTcb := some t.bv } n →
      (if y.scSporadic = true then do
          let b1 ← sporadic.sc_active st s3 p
          if b1 = true then do
              let s5 ← sched.cur_sc st s3
              let b2 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc p s5
              if b2 = true then sporadic.unblock_check st s3 p else ok s3
            else ok s3
        else ok s3) ⦃ s4 => ∃ σu,
        Fl4Spec.ifSporadicActiveCurScTestRefillUnblockCheck (Z := Unit) (some p.bv) σd = ({((), σu)}, False) ∧
        SchedRel st N T C j s4 σu ∧ NtfnStateRel N T (L.mem s4) σu ∧
        (σu = σd ∨ Fl4Spec.scActive y = true ∧ Fl4Spec.refillUnblockCheck (Z := Unit) p.bv σd = ({((), σu)}, False)) ∧
        WritesIn st s3 s4 (KFoot st T N C j s3 σd) ⦄ := by
    intro s3 hS3 hR3 hx3
    obtain ⟨Q3, R3, hc3, hs3⟩ := hS3.lists
    have hsp0 := ifSporadicActive_some hkd
    by_cases hsp : y.scSporadic = true
    · rw [if_pos hsp]
      step with sc_active_spec as ⟨b1, hb1⟩
      have hab : b1 = Fl4Spec.scActive y := by
        rw [hb1]; show _ = decide (0 < y.scRefillMax)
        apply decide_eq_decide.2; rw [← hx3.max]; rfl
      subst hab
      by_cases hact : Fl4Spec.scActive y = true
      · rw [if_pos hact]
        step with sched.cur_sc.spec' as ⟨v, hv⟩
        rw [hc3.cur] at hv
        subst hv
        rw [sc_ne_eq]
        simp only [bind_ok]
        by_cases hcs : p = nodeW st s3 j layout.node.CUR_SC
        · have hd : decide (p ≠ nodeW st s3 j layout.node.CUR_SC) = false :=
            decide_eq_false (fun h => h hcs)
          rw [hd]; simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
          exact ⟨σd, hsp0.trans (if_neg (fun h => h.2.2 (by rw [hs3.curSc, ← hcs]))), hS3, hR3, Or.inl rfl,
            WritesIn.refl _ _⟩
        · have hd : decide (p ≠ nodeW st s3 j layout.node.CUR_SC) = true := decide_eq_true hcs
          rw [hd]; simp only [↓reduceIte]
          refine WP.spec_mono (WP.spec_and (unblock_check_refines s3 σd hS3 hp (hx3.rmax_ne hact))
            (unblock_check_kfoot hS3 hp (hx3.rmax_ne hact))) ?_
          rintro s4 ⟨⟨σu, he, hf, hK, hS4⟩, hw⟩
          exact ⟨σu, (hsp0.trans (if_pos ⟨hsp, hact, fun e => hcs (eq_of_bv (by rw [e, hs3.curSc]))⟩)).trans he,
            hS4, hR3.frame hS3.placed hf hK, Or.inr ⟨hact, he⟩, hw⟩
      · rw [if_neg hact, WP.spec_ok]
        exact ⟨σd, hsp0.trans (if_neg (fun h => hact h.2.1)), hS3, hR3, Or.inl rfl, WritesIn.refl _ _⟩
    · rw [if_neg hsp, WP.spec_ok]
      exact ⟨σd, hsp0.trans (if_neg (fun h => hsp h.1)), hS3, hR3, Or.inl rfl, WritesIn.refl _ _⟩
  -- what the unblock check keeps
  have U : ∀ σu, (σu = σd ∨ Fl4Spec.scActive y = true ∧ Fl4Spec.refillUnblockCheck (Z := Unit) p.bv σd = ({((), σu)}, False)) →
      ∃ yu, σu.kheap p.bv = some (.schedContext yu n) ∧ yu.scTcb = some t.bv ∧
        (∀ q, q ≠ p.bv → σu.kheap q = σd.kheap q) ∧ σu.releaseQueue = σd.releaseQueue ∧
        σu.readyQueues = σd.readyQueues ∧ σu.schedulerAction = σd.schedulerAction ∧
        σu.idleThread = σd.idleThread ∧
        (Fl4Spec.runnable xt.tcbState = false → inClass xt.tcbState → Fl4Spec.scActive yu = true →
          released σu yu) ∧ InvBut σu t.bv := by
    rintro σu (rfl | ⟨hya, he⟩)
    · exact ⟨_, hkd, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, fun h1 h2 h3 => hblk h1 h2 h3, hId⟩
    · have hm : ((), σu) ∈ (Fl4Spec.refillUnblockCheck (Z := Unit) p.bv σd).1 := by rw [he]; rfl
      have hnr : Fl4Spec.refillReady σd.curTime (Fl4Spec.refillHd { y with scTcb := some t.bv }) = true →
          ({ y with scTcb := some t.bv } : Fl4Spec.SchedContext).scPeriod ≠ 0 →
          ∀ u ∈ σd.releaseQueue, ∀ x, σd.kheap u = some (.tcb x) → x.tcbSchedContext ≠ some p.bv := by
        intro _ _ u hu x hx hxp
        by_cases e : u = t.bv
        · exact hnq0.2 (e ▸ hu)
        · have hup : u ≠ p.bv := by rintro rfl; rw [hkd] at hx; cases hx
          have hx0 : σ.kheap u = some (.tcb x) := by
            simp only [σd, updSc, updK_kheap, Function.update_of_ne hup, Function.update_of_ne e] at hx; exact hx
          obtain ⟨y', n', h1, h2⟩ := hI.back u x p.bv hx0 hxp
          rw [hk] at h1; cases h1; rw [hy0] at h2; cases h2
      have hIu := hId.unblock hkd (hne hya) hnr hm
      rcases unblock_result hkd (hne hya) hm with ⟨rfl, -⟩ | ⟨z, rfl, hzR, hzt, hzy, hrdy, hzne, hper⟩
      · exact ⟨_, hkd, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, fun h1 h2 h3 => hblk h1 h2 h3, hIu⟩
      · refine ⟨z, by simp [updK], by rw [hzy], fun q hq => by simp [updK, hq], rfl, rfl, rfl, rfl,
          fun _ _ ha => ?_, hIu⟩
        have hact' : Fl4Spec.scActive ({ y with scTcb := some t.bv } : Fl4Spec.SchedContext) = true := by
          rw [← ha, hzy]
        exact ⟨ready_now _ _ hzt, sufficient_of_refOK (hzR (hId.refills p.bv _ n hkd hact' hper))⟩
  refine WP.spec_bind (P2 _ hS3 hR3 hx3) ?_
  rintro s4 ⟨σu, hun, hS4, hR4, hor, hw4⟩
  obtain ⟨yu, hku, hyu, hqu, hrqu, hrdu, hactu, hidu, hrelu, hIu⟩ := U σu hor
  have hzd : SzKeep σ σd := by
    rw [hσd]; exact (SzKeep.updK hkt fun _ _ e => by cases e).trans
      (SzKeep.updK hka fun x m e => by cases e; exact ⟨y, rfl⟩)
  have hzu : SzKeep σ σu := hzd.trans fun q x m hq => by
    by_cases e : q = p.bv
    · subst e; rw [hku] at hq; cases hq; exact ⟨_, hkd⟩
    · exact ⟨x, by rw [← hqu q e]; exact hq⟩
  have w4 := WritesIn.kfoot_trans w3 (SzKeepC.of hzd) hw4
  have hktu : σu.kheap t.bv = some (.tcb { xt with tcbSchedContext := some p.bv }) := by
    rw [hqu _ (Ne.symm hpt)]; exact hktd
  have hnqu : NotQueued σu t.bv :=
    ⟨fun d q => by rw [hrdu]; exact hnq0.1 d q, by rw [hrqu]; exact hnq0.2⟩
  have hRel : RelOK σu :=
    ⟨fun u hu => by obtain ⟨x, p, -, -, h1, h2, -⟩ := hIu.rel u hu; exact ⟨x, p, h1, h2⟩, hIu.sorted,
      fun u hu x' p' hx hp => by
        obtain ⟨x, p, y, n, h1, h2, -, h4, h5⟩ := hIu.rel u hu
        rw [hx] at h1; cases h1; rw [hp] at h2; cases h2; exact ⟨y, n, h4, h5⟩⟩
  -- `resume`
  refine WP.spec_bind (resume_refines s4 a σu hR4 hS4 hRel (hT.mb a) hp hp0 ht (word24_of hS4 hp hku hyu)
    (scA_of hS4 ht hktu rfl) (fun x hx => by rw [hktu] at hx; cases hx; exact hnqu.1 _ _)) ?_
  rintro ⟨s5, a5⟩ ⟨rfl, σr, hrs, hkr, har, htr, -, -, hf5, hw5, hS5⟩
  have w5 := WritesIn.kfoot_sfoot w4 hw5
  have hR5 : NtfnStateRel N T (L.mem s5) σr := hR4.frame hP hf5 (KView.of_kheap hkr)
  have hIr : Inv σr := hIu.resume hku hyu hktu rfl hnqu hrelu hrs
  have hkeep := resume_keep hIu hku hyu hktu rfl hnqu hrs
  have hNr : NSC N C σr := NSC.of_off hN2 (p := p.bv) (fun q hq => by rw [hkr, hqu q hq])
    ⟨yu, n, by rw [hkr]; exact hku⟩
  -- the idle thread through the steps
  have hIdr : σ.schedulerAction = .resumeCurThread → IdleOK σ → t.bv ≠ σ.idleThread →
      IdleOK σr ∧ σr.schedulerAction = .resumeCurThread := by
    intro ha0 hId0 hti
    have hip : σ.idleThread ≠ p.bv := by
      obtain ⟨xi, h1, -⟩ := hId0; intro e; rw [e, hk] at h1; cases h1
    have hIdd : IdleOK σd := IdleOK.of hId0 rfl
      (by simp only [σd, updSc, updK_kheap, Function.update_of_ne hip, Function.update_of_ne (Ne.symm hti)]) id
    have hIdu : IdleOK σu := IdleOK.of hIdd hidu (hqu _ hip) (by rw [hrqu]; exact id)
    refine ⟨IdleOK.of hIdu hkeep.1.2.2.2.2.2.1 (by rw [hkr]) (fun hm => (hkeep.2.2 _ hm).resolve_left
      (fun e => hti (by rw [← e]; exact hidu))), ?_⟩
    rw [hkeep.2.1, hactu]; exact ha0
  -- the spec up to the schedulable test
  have hsp : ∀ σ', (Fl4Spec.NonDet.gets (Fl4Spec.schedulable (Z := Unit) t.bv) >>= fun sched =>
      Fl4Spec.NonDet.when (sched = true) (do
        Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedEnqueue t.bv
        Fl4Spec.rescheduleRequired)) σr = ({((), σ')}, False) →
      Fl4Spec.schedContextBindTcb (Z := Unit) p.bv t.bv σ = ({((), σ')}, False) := by
    intro σ' h
    unfold Fl4Spec.schedContextBindTcb
    refine (nd_bind_one (threadSet_eq _ hkt) _).trans ?_
    refine (nd_bind_one (updateSchedContext_eq hka _) _).trans ?_
    refine (nd_bind_one hun _).trans ?_
    refine (nd_bind_one hrs _).trans ?_
    exact h
  step with sched.is_schedulable.spec' as ⟨b2, hb2⟩
  rw [schedulable_eq hR5 hS5 ht] at hb2
  subst hb2
  by_cases hsch : Fl4Spec.schedulable t.bv σr = true
  · rw [if_pos hsch]
    obtain ⟨x5, scp5, y5, n5, g1, g2, g3, g4, g5, g6⟩ := schedulable_inv hsch
    obtain ⟨Q5, R5, hc5, hs5⟩ := hS5.lists
    have hrel5 : (L.mem s5 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
      by_contra h
      exact g6 (by rw [hs5.rel]; exact List.mem_map_of_mem ((hc5.released t ht).1 h))
    refine WP.spec_bind (WP.spec_and (enqueue_refines s5 σr hS5 t ht (fun _ => hrel5)) (enqueue_sfoot hS5 ht)) ?_
    rintro s6 ⟨⟨σe, hen, hke, hre, hf6, hS6⟩, hw6⟩
    have e6 := pair_eq (hen.symm.trans (tcbSchedAction_gen g1 _))
    subst e6
    set σe := setQ σr x5.tcbDomain x5.tcbPriority
      (Fl4Spec.tcbSchedEnqueue t.bv (σr.readyQueues x5.tcbDomain x5.tcbPriority)) with hσe
    have hIe : Inv σe := hIr.qchange (qchange_enqueue g1 hsch)
    have hR6 : NtfnStateRel N T (L.mem s6) σe := hR5.frame hP hf6 (KView.of_kheap rfl)
    refine WP.spec_bind (WP.spec_and (reschedule_required_refines s6 _ hR6 hS6 hIe.actReady)
      (reschedule_required_sfoot hS6)) ?_
    rintro s7 ⟨⟨σf, hef, hkf, -, hf7, hS7⟩, hw7⟩
    obtain ⟨σ9, he9, hq9⟩ := rescheduleRequired_qchange hIe.actReady
    rw [he9] at hef
    have e7 := pair_eq hef
    subst e7
    rw [WP.spec_ok]
    refine ⟨σf, hsp σf ?_, hS7, hR6.frame hP hf7 (KView.of_kheap hkf), fun m hm x q hx hq => hNr m hm x q
      (by rw [hkf] at hx; exact hx) hq, hIe.qchange hq9, fun ha0 hId0 hti => ?_,
      WritesIn.kfoot_sfoot (WritesIn.kfoot_sfoot w5 hw6) hw7⟩
    · rw [nd_gets_bind]
      unfold Fl4Spec.NonDet.when
      rw [if_pos hsch]
      exact (nd_bind_one (tcbSchedAction_gen g1 _) _).trans he9
    · obtain ⟨hIdr', har'⟩ := hIdr ha0 hId0 hti
      have e := rescheduleRequired_noswitch (σ := σe)
        (fun u h => by
          have : σr.schedulerAction = .switchThread u := h
          rw [har'] at this; cases this)
      rw [he9] at e
      rw [← pair_eq e]
      exact ActIdle.of_noswitch hIdr' (fun _ h => by cases h)
  · rw [if_neg hsch, WP.spec_ok]
    refine ⟨σr, hsp σr ?_, hS5, hR5, hNr, hIr, fun ha0 hId0 hti => ?_, w5⟩
    · rw [nd_gets_bind]
      unfold Fl4Spec.NonDet.when
      rw [if_neg hsch]; rfl
    · obtain ⟨hIdr', har'⟩ := hIdr ha0 hId0 hti
      exact ActIdle.of_noswitch hIdr' (fun u h => by rw [har'] at h; cases h)

end

end

end Fl4Proofs.P3.Sched
