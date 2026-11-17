/-
P3 (DESIGN.md §9), scheduling contexts: **the donation branch of
`maybe_donate_sched_context`** (`maybe_donate_refines`).

When the thread has no SC and the notification's SC is bound to no TCB,
FL4 binds the SC to the thread (`schedcontext::donate`: SC's `TCB` word, the
thread's `SC` word, `migrate_tcb` to the SC's core, which on a single core
keeps the affinity), then `schedcontext::resume`; the spec does
`sched_context_donate` then `sched_context_resume`.

Hypotheses beyond the relations (`DonatePre`), all l4v invariants or
platform facts:
* the notification's SC is one of `C` (`SchedRel` relates the SCs of `C`);
* the thread is in no ready queue (l4v `valid_ready_qs`: a queued thread has
  an active SC, and this one has none);
* `RelOK` (l4v `valid_release_q`, `sorted_release_q`), for `postpone`;
* the platform's `MIN_BUDGET` is the spec's (`hmb`).

`ActReady` is preserved (`ActReady.donate`): the donation makes only the
thread schedulable, and `sched_context_resume` leaves it schedulable only
with a ready and sufficient head refill.
-/
import Fl4Proofs.P3.ScResume
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

theorem schedulable_mono {σ σ' : State Unit} {u : ObjRef} (h1 : tcbsOf σ' u = tcbsOf σ u)
    (h2 : ∀ p, Option.map scActive (scsOf σ' p) = Option.map scActive (scsOf σ p))
    (h3 : ∀ v ∈ σ.releaseQueue, v ∈ σ'.releaseQueue) (h : schedulable u σ' = true) : schedulable u σ = true := by
  have e : schedulable u { σ' with releaseQueue := σ.releaseQueue } = schedulable u σ :=
    schedulable_congr h1 h2 rfl
  rw [← e]
  simp only [schedulable, decide_eq_true_eq] at h ⊢
  exact ⟨h.1, h.2.1, fun hm => h.2.2 (h3 _ hm)⟩

/-- **`ActReady` survives a donation and `sched_context_resume`.** -/
theorem _root_.Fl4Proofs.P3.Notif.ActReady.donate {σ σr : State Unit} (h : ActReady σ) {t sc : ObjRef} {xs xs' : SchedContext} {ns : Nat}
    {xt xt' : Tcb}
    (hkd : ∀ p, p ≠ t → p ≠ sc → σr.kheap p = σ.kheap p)
    (hksc : σ.kheap sc = some (.schedContext xs ns)) (hksc' : σr.kheap sc = some (.schedContext xs' ns))
    (hrf : xs'.scRefills = xs.scRefills) (hmx : xs'.scRefillMax = xs.scRefillMax)
    (hkt : σ.kheap t = some (.tcb xt)) (hxt0 : xt.tcbSchedContext = none)
    (hkt' : σr.kheap t = some (.tcb xt')) (hxt' : xt'.tcbSchedContext = some sc)
    (hact : σr.schedulerAction = σ.schedulerAction) (hct : σr.curTime = σ.curTime)
    (hrq : ∀ u ∈ σ.releaseQueue, u ∈ σr.releaseQueue)
    (hts : schedulable t σr = true → getScRefillSufficient (Z := Unit) sc 0 σr = ({(true, σr)}, False) ∧
      getScRefillReady (Z := Unit) sc σr = ({(true, σr)}, False)) :
    ActReady σr := by
  have hst : sc ≠ t := by rintro rfl; rw [hksc] at hkt; cases hkt
  intro u hu hs
  by_cases eu : u = t
  · subst eu
    obtain ⟨h1, h2⟩ := hts hs
    exact ⟨xt', sc, hkt', hxt', h1, h2⟩
  -- another thread: its TCB and the SCs' refills are unchanged
  have htcb : tcbsOf σr u = tcbsOf σ u := by
    rw [tcbsOf_eq, tcbsOf_eq]
    by_cases es : u = sc
    · subst es; rw [hksc, hksc']
    · rw [hkd u eu es]
  have hscm : ∀ p, Option.map scActive (scsOf σr p) = Option.map scActive (scsOf σ p) := by
    intro p
    rw [scsOf_eq, scsOf_eq]
    by_cases ep : p = sc
    · subst ep; rw [hksc, hksc']; simp [scActive, hmx]
    · by_cases et : p = t
      · subst et; rw [hkt, hkt']
      · rw [hkd p et ep]
  have hs0 := schedulable_mono htcb hscm hrq hs
  obtain ⟨x, scp, hkx, hsc, h1, h2⟩ := h u (by rw [← hact]; exact hu) hs0
  obtain ⟨y, n, hky, hne, hsuff⟩ := suff_inv h1
  have hrdy := ready_inv h2 hky hne
  have hkx' : σr.kheap u = some (.tcb x) := by
    by_cases es : u = sc
    · subst es; rw [hksc] at hkx; cases hkx
    · rw [hkd u eu es]; exact hkx
  obtain ⟨y', hky', hrf'⟩ : ∃ y', σr.kheap scp = some (.schedContext y' n) ∧ y'.scRefills = y.scRefills := by
    by_cases ep : scp = sc
    · subst ep; rw [hksc] at hky; cases hky; exact ⟨xs', hksc', hrf⟩
    · have et : scp ≠ t := by rintro rfl; rw [hkt] at hky; cases hky
      exact ⟨y, by rw [hkd scp et ep]; exact hky, rfl⟩
  have hne' : y'.scRefills ≠ [] := by rw [hrf']; exact hne
  have hd : refillHd y' = refillHd y := by unfold refillHd; rw [hrf']
  refine ⟨x, scp, hkx', hsc, ?_, ?_⟩
  · rw [getScRefillSufficient_eq hky' hne', hd, hsuff]
  · rw [getScRefillReady_eq hky' hne', hd, hct, hrdy]

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

@[step] theorem obj.Tcb.set_affinity.spec' (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_affinity st t s v ⦃ s' => s' = L.wr s (affA t) v ⦄ := by
  unfold obj.Tcb.set_affinity; step*; simp_all [affA]

/-- Writing a word with the value it has keeps the relation. -/
theorem SchedRel.wr_same {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {a v : U64} (ha : Aligned a) (hv : L.mem s a = v) :
    SchedRel st N T C c (L.wr s a v) σ ∧ FootEq N T (L.mem s) (L.mem (L.wr s a v)) := by
  have hw : WritesIn st s (L.wr s a v) (fun _ => False) := by
    refine ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb _ => ?_⟩
    by_cases e : b = a
    · subst e; rw [rd_wr_eq ha, hv]
    · exact rd_wr_ne ha hb (Ne.symm e)
  exact ⟨hS.stable (hw.mono fun _ h => h.elim) (NtfnStep.refl σ), fun b hb _ => hw.2.2 b hb id⟩

/-- The spec's state after `sched_context_donate` of an unbound SC. -/
def donSt (σ : Fl4Spec.State Unit) (sc t : Fl4Spec.ObjRef) (xs : Fl4Spec.SchedContext) (ns : Nat) (xt : Fl4Spec.Tcb) :
    Fl4Spec.State Unit :=
  updK (updSc σ sc { xs with scTcb := some t } ns) t (.tcb { xt with tcbSchedContext := some sc })

/-- **`donate` of an SC bound to no TCB refines `sched_context_donate`.** -/
theorem donate_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) {sc : U64} (hsc : sc ∈ C) (hsc0 : sc ≠ 0#u64) {t : U64} (ht : t ∈ T)
    (htw0 : L.mem s (scW sc 24#u64) = 0#u64) :
    schedcontext.donate st ar s a sc t ⦃ r => r.2 = a ∧ ∃ xs ns xt, σ.kheap sc.bv = some (.schedContext xs ns) ∧
      σ.kheap t.bv = some (.tcb xt) ∧
      Fl4Spec.schedContextDonate (Z := Unit) sc.bv t.bv σ = ({((), donSt σ sc.bv t.bv xs ns xt)}, False) ∧
      FootEq N T (L.mem s) (L.mem r.1) ∧ KView σ (donSt σ sc.bv t.bv xs ns xt) ∧
      SchedRel st N T C c r.1 (donSt σ sc.bv t.bv xs ns xt) ∧ WritesIn st s r.1 (KFoot st T N C c s σ) ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xs, ns, hks, hxs⟩ := hs.scs sc hsc
  obtain ⟨xt, hkt, -, -, -, -⟩ := hs.tcb t ht
  have ht0 : t ≠ 0#u64 := fun e => (hc.tcbs t ht).ne0 (by rw [e]; rfl)
  have hst : sc.bv ≠ t.bv := by intro e; rw [e, hkt] at hks; cases hks
  unfold schedcontext.donate
  step as ⟨i, i_post⟩
  rw [scTcbA_eq, htw0] at i_post
  subst i_post
  step as ⟨b, b_post⟩
  simp only [b_post, decide_true, ↓reduceIte, bind_ok]
  step as ⟨s2, s2_post⟩
  subst s2_post
  have hal24 : Aligned (scW sc 24#u64) := (hxs.hdr (K := 24#u64) (by simp) (by simp)).1
  have w1 : WritesIn st s (L.wr s (scW sc 24#u64) t) (KFoot st T N C c s σ) :=
    (writesIn_wr hal24).mono fun b hb => Or.inr (Or.inr (hb ▸ sw_hdr hS hsc (K := 24#u64) (by simp) (by simp) (by decide)))
  obtain ⟨hS1, hf1, hv1⟩ := hS.set_sc_tcb hsc hks t
  rw [optRef_ne ht0] at hS1 hv1
  have hkt1 : (updSc σ sc.bv { xs with scTcb := some t.bv } ns).kheap t.bv = some (.tcb xt) := by
    simp [updK, Ne.symm hst, hkt]
  step as ⟨s3, s3_post⟩
  subst s3_post
  have w2 := WritesIn.kfoot_sfoot w1 (writesIn_tcb (K := 3464#u64) (c := c) hc.tcbs ht (by unfold SOff SOffL; decide) (by simp) sc)
  obtain ⟨hS2, hf2, hv2⟩ := hS1.set_tcb_sc ht hkt1 (v := sc) (Or.inr hsc)
  rw [optRef_ne hsc0] at hS2 hv2
  step as ⟨cpu, cpu_post⟩
  have hcpu : cpu = c := by rw [cpu_post, scCoreA_eq]; exact hS2.core sc hsc
  subst hcpu
  unfold smp.migrate_tcb
  step as ⟨i, i_post⟩
  obtain ⟨Q2, R2, hc2, hs2⟩ := hS2.lists
  have hi : i = cpu := by rw [i_post]; exact hc2.aff t ht
  subst hi
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
  refine ⟨xs, ns, xt, hks, hkt, ?_, FootEq.trans' hf1 hf2, KView.trans hv1 hv2, hS2, w2⟩
  -- the spec
  have hg : Fl4Spec.getScObjRef (Z := Unit) Fl4Spec.SchedContext.scTcb sc.bv σ = ({(xs.scTcb, σ)}, False) := by
    unfold Fl4Spec.getScObjRef; rw [nd_bind_one (getSchedContext_eq hks)]; rfl
  unfold Fl4Spec.schedContextDonate
  rw [nd_bind_one hg, hxs.tcb, htw0, optRef_zero]
  simp only [Fl4Spec.NonDet.when, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [nd_bind_one (show Fl4Spec.NonDet.pure (σ := Fl4Spec.State Unit) () σ = ({((), σ)}, False) from rfl)]
  show (Fl4Spec.updateSchedContext sc.bv _ >>= _) σ = _
  rw [nd_bind_one (updateSchedContext_eq hks _)]
  rw [show Fl4Spec.scTcbUpdate (fun _ => some t.bv) xs = { xs with scTcb := some t.bv } from rfl]
  show Fl4Spec.threadSet _ t.bv _ = _
  rw [threadSet_eq _ hkt1]
  rfl

set_option maxHeartbeats 1000000 in
/-- **`maybe_donate_sched_context` refines `maybe_donate_sc`**, given
`DonatePre`'s facts (see the module docstring); it keeps `ActReady`. -/
theorem maybe_donate_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : NtfnStateRel N T (L.mem s) σ) (hS : SchedRel st N T C c s σ) (hRel : RelOK σ)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (t n : U64) (ht : t ∈ T) (hn : n ∈ N)
    (hnC : L.mem s (nScA n) ≠ 0#u64 → L.mem s (nScA n) ∈ C)
    (hnq : L.mem s (scA t) = 0#u64 → ∀ x, σ.kheap t.bv = some (.tcb x) →
      t.bv ∉ σ.readyQueues x.tcbDomain x.tcbPriority) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ r => ∃ σ1,
      Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σ = ({((), σ1)}, False) ∧ FootEq N T (L.mem s) (L.mem r.1) ∧
      KView σ σ1 ∧ SchedRel st N T C c r.1 σ1 ∧ WritesIn st s r.1 (KFoot st T N C c s σ) ∧
      (ActReady σ → ActReady σ1) ⦄ := by
  have hP := hS.placed
  by_cases hd : L.mem s (scA t) = 0#u64 ∧ L.mem s (nScA n) ≠ 0#u64 ∧
      L.mem s (scW (L.mem s (nScA n)) 24#u64) = 0#u64
  swap
  · have hno : L.mem s (scA t) ≠ 0#u64 ∨ L.mem s (nScA n) = 0#u64 ∨
        (L.mem s (nScA n) ∈ C ∧ L.mem s (scW (L.mem s (nScA n)) 24#u64) ≠ 0#u64) := by
      by_cases h1 : L.mem s (scA t) = 0#u64
      · by_cases h2 : L.mem s (nScA n) = 0#u64
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr ⟨hnC h2, fun h3 => hd ⟨h1, h2, h3⟩⟩)
      · exact Or.inl h1
    refine WP.spec_mono (maybe_donate_nodonate s a σ hR hS t n ht hn hno) ?_
    rintro r ⟨rfl, he⟩
    exact ⟨σ, he, FootEq.rfl', KView.refl σ, hS, WritesIn.refl _ _, id⟩
  obtain ⟨h0, hsc0, htw0⟩ := hd
  set sc := L.mem s (nScA n) with hscdef
  have hscC := hnC hsc0
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨xn, hkn, hxn⟩ := hR.ntfn n hn
  obtain ⟨xt0, hkt0, -, -, hsct0, -⟩ := hs.tcb t ht
  unfold notification.maybe_donate_sched_context
  step as ⟨i, i_post⟩
  rw [i_post]
  simp only [h0, ↓reduceIte]
  step as ⟨i1, i1_post⟩
  step as ⟨b, b_post⟩
  rw [i1_post, ← hscdef] at b_post
  simp only [b_post, hsc0, decide_false, Bool.false_eq_true, ↓reduceIte]
  step as ⟨i2, i2_post⟩
  have hi2 : i2 = 0#u64 := by rw [i2_post, i1_post, ← hscdef, scTcbA_eq]; exact htw0
  simp only [hi2, ↓reduceIte]
  rw [i1_post, ← hscdef]
  refine WP.spec_bind (donate_refines s a σ hS hscC hsc0 ht htw0) ?_
  rintro ⟨s1, a1⟩ ⟨ha1, xs, ns, xt, hks, hkt, hdon, hf1, hv1, hS1, hw1⟩
  simp only at ha1
  subst ha1
  rw [hkt0] at hkt; cases hkt
  have hst : sc.bv ≠ t.bv := by intro e; rw [e, hkt0] at hks; cases hks
  set σd := donSt σ sc.bv t.bv xs ns xt0 with hσd
  have hR1 : NtfnStateRel N T (L.mem s1) σd := hR.frame hP hf1 hv1
  obtain ⟨Q1, R1, hc1, hs1⟩ := hS1.lists
  have hkd_sc : σd.kheap sc.bv = some (.schedContext { xs with scTcb := some t.bv } ns) := by
    simp [σd, donSt, updK, hst]
  have hkd_t : σd.kheap t.bv = some (.tcb { xt0 with tcbSchedContext := some sc.bv }) := by
    simp [σd, donSt, updK]
  have hkd_o : ∀ p, p ≠ t.bv → p ≠ sc.bv → σd.kheap p = σ.kheap p := by
    intro p h1 h2; simp [σd, donSt, updK, h1, h2]
  -- the SC's and the thread's words after the donation
  have htw1 : L.mem s1 (scW sc 24#u64) = t := by
    obtain ⟨x', n', hk', hx'⟩ := hs1.scs sc hscC
    rw [hkd_sc] at hk'; cases hk'
    have := hx'.tcb; simp only at this
    exact eq_of_bv (optRef_some this.symm).2
  have hts1 : L.mem s1 (scA t) = sc := by
    obtain ⟨x', hk', -, -, hsc', -⟩ := hs1.tcb t ht
    rw [hkd_t] at hk'; cases hk'
    simp only at hsc'
    exact eq_of_bv (optRef_some hsc'.symm).2
  have hnq1 : ∀ x, σd.kheap t.bv = some (.tcb x) → t.bv ∉ σd.readyQueues x.tcbDomain x.tcbPriority := by
    intro x hx; rw [hkd_t] at hx; cases hx; exact hnq h0 xt0 hkt0
  have htR : t.bv ∉ σ.releaseQueue := fun hm => by
    obtain ⟨x, p, hx, hp⟩ := hRel.sc _ hm
    rw [hkt0] at hx; cases hx
    rw [hsct0, h0, optRef_zero] at hp; cases hp
  have hRel1 : RelOK σd := hRel.transfer' hS rfl (fun u hu x hx => by
      have h1 : u ≠ t.bv := fun e => htR (e ▸ hu)
      have h2 : u ≠ sc.bv := by rintro rfl; rw [hks] at hx; cases hx
      rw [hkd_o u h1 h2]; exact hx)
    (fun p y m hy => by
      by_cases e : p = sc.bv
      · subst e; rw [hks] at hy; cases hy; exact ⟨_, hkd_sc, rfl, rfl⟩
      · have et : p ≠ t.bv := by rintro rfl; rw [hkt0] at hy; cases hy
        exact ⟨y, by rw [hkd_o p et e]; exact hy, rfl, rfl⟩)
    (fun u hu x' hx => by
      have h1 : u ≠ t.bv := fun e => htR (e ▸ hu)
      have h2 : u ≠ sc.bv := by rintro rfl; rw [hkd_sc] at hx; cases hx
      exact ⟨x', by rw [← hkd_o u h1 h2]; exact hx, rfl⟩)
    (fun p y' m hy => by
      by_cases e : p = sc.bv
      · subst e; rw [hkd_sc] at hy; cases hy; exact ⟨xs, hks, rfl⟩
      · have et : p ≠ t.bv := by rintro rfl; rw [hkd_t] at hy; cases hy
        exact ⟨y', by rw [← hkd_o p et e]; exact hy, rfl⟩)
  refine WP.spec_mono (resume_refines s1 a1 σd hR1 hS1 hRel1 hmb hscC hsc0 ht htw1 hts1 hnq1) ?_
  rintro ⟨s2, a2⟩ ⟨-, σr, hres, hkr, har, hctr, hrqr, htsr, hf2, hw2, hS2⟩
  obtain ⟨xs', ns', hks', hxs⟩ := hs.scs sc hscC
  rw [hks] at hks'; cases hks'
  have hspec : Fl4Spec.maybeDonateSc (Z := Unit) t.bv n.bv σ = Fl4Spec.schedContextResume (Z := Unit) sc.bv σd := by
    unfold Fl4Spec.maybeDonateSc Fl4Spec.getTcbObjRef
    rw [nd_bind_one (threadGet_eq _ hkt0), hsct0, h0, optRef_zero]
    simp only [Fl4Spec.NonDet.when, ↓reduceIte]
    rw [nd_bind_one' (getNtfnSc_eq hkn), hxn.sc, ← hscdef, optRef_ne hsc0]
    simp only [Fl4Spec.NonDet.maybeM]
    have hg : Fl4Spec.getScObjRef (Z := Unit) Fl4Spec.SchedContext.scTcb sc.bv σ = ({(xs.scTcb, σ)}, False) := by
      unfold Fl4Spec.getScObjRef; rw [nd_bind_one (getSchedContext_eq hks)]; rfl
    rw [nd_bind_one hg, hxs.tcb, htw0, optRef_zero]
    simp only [Fl4Spec.NonDet.when, ↓reduceIte]
    rw [nd_bind_one hdon]
  refine ⟨σr, by rw [hspec]; exact hres, FootEq.trans' hf1 hf2, KView.trans hv1 (KView.of_kheap hkr), hS2,
    WritesIn.kfoot_sfoot hw1 hw2, fun hA => ?_⟩
  refine hA.donate (t := t.bv) (sc := sc.bv) (xs := xs) (xs' := { xs with scTcb := some t.bv }) (xt := xt0)
    (xt' := { xt0 with tcbSchedContext := some sc.bv }) (fun p h1 h2 => by rw [hkr, hkd_o p h1 h2]) hks
    (by rw [hkr]; exact hkd_sc) rfl rfl hkt0 (by rw [hsct0, h0, optRef_zero]) (by rw [hkr]; exact hkd_t) rfl
    (by rw [har]; rfl) (by rw [hctr]; rfl) (fun u hu => hrqr u hu) (fun h => ?_)
  obtain ⟨e, h1, h2⟩ := htsr h
  subst e
  exact ⟨h1, h2⟩

end

end

end Fl4Proofs.P3.Sched
