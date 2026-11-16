/-
P3 (DESIGN.md §9), IPC: **the notification wake-up's donation with its
footprint**: `donate_refines` and `maybe_donate_refines` (ScDonateRef) with
FL4's writes (`KFoot`), for the IPC proofs' lift (IpcDonate's `tk_lift`).
-/
import Fl4Proofs.P3.ScDonateRef
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

/-! ## The donation with its footprint

`donate_refines` and `maybe_donate_refines` (ScDonateRef) with FL4's writes
(`KFoot`): the SC's `TCB` word, the thread's `SC` and affinity words, and
`resume`'s (`resume_refines`). -/

variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`donate` of an SC bound to no TCB refines `sched_context_donate`.** -/
theorem donate_refinesW {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
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
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step as ⟨s4, s4_post⟩
  subst s4_post
  have w3 := WritesIn.kfoot_sfoot w2 (writesIn_tcb (K := 3520#u64) hc.tcbs ht (by unfold SOff SOffL; decide) (by simp) i)
  obtain ⟨hS3, hf3⟩ := hS2.wr_same (field_aligned (hc.tcbs t ht) (K := 3520#u64) (by simp) (by simp))
    (hc2.aff t ht)
  refine ⟨xs, ns, xt, hks, hkt, ?_, FootEq.trans' (FootEq.trans' hf1 hf2) hf3, KView.trans hv1 hv2, hS3, w3⟩
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
theorem maybe_donate_refinesW {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
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
  refine WP.spec_bind (donate_refinesW s a σ hS hscC hsc0 ht htw0) ?_
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
      · subst e; rw [hks] at hy; cases hy; exact ⟨_, hkd_sc, rfl⟩
      · have et : p ≠ t.bv := by rintro rfl; rw [hkt0] at hy; cases hy
        exact ⟨y, by rw [hkd_o p et e]; exact hy, rfl⟩)
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

end Fl4Proofs.P3.Sched
