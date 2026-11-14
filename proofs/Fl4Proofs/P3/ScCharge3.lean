/-
P3 (DESIGN.md §9), scheduling contexts: **the tail of `end_timeslice`**
(`rap_refines`): a ready and sufficient current thread is appended to its
ready queue, otherwise its SC is postponed; either way `Inv` is restored
(from `InvBut` for the current thread).
-/
import Fl4Proofs.P3.ScCharge2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

theorem qchange_append {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hs : schedulable t σ = true) :
    QChange σ (setQ σ x.tcbDomain x.tcbPriority (tcbSchedAppend t (σ.readyQueues x.tcbDomain x.tcbPriority))) :=
  qchange_tcbSchedAction hk _ fun u hu => by
    unfold tcbSchedAppend at hu
    split at hu
    · rcases List.mem_append.1 hu with hu | hu
      · exact Or.inl hu
      · simp only [List.mem_singleton] at hu; subst hu; exact Or.inr hs
    · exact Or.inl hu

end Spec

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **`end_timeslice`'s requeue-or-postpone tail.** -/
theorem rap_refines {N T C : Set U64} {c : U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) {sc ct : U64} (hI : InvBut σ ct.bv) (hsc : sc ∈ C) (hct : ct ∈ T)
    (htw : L.mem s (scW sc 24#u64) = ct) (hts : L.mem s (scA ct) = sc) (hsc0 : sc ≠ 0#u64)
    (hsch : Fl4Spec.schedulable ct.bv σ = true)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    (do
      let b ← sporadic.ready st s sc
      if b then do
        let b1 ← sporadic.sufficient st ar s a sc 0#u64
        if b1 then do
          let s1 ← sched.append st s ct
          ok (s1, a)
        else do
          let s1 ← sched.postpone st s sc
          ok (s1, a)
      else do
        let s1 ← sched.postpone st s sc
        ok (s1, a)) ⦃ r => r.2 = a ∧ ∃ σ', (do
          let ready ← Fl4Spec.getScRefillReady (Z := Unit) sc.bv
          let sufficient ← Fl4Spec.getScRefillSufficient sc.bv 0
          if ready = true ∧ sufficient = true then Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedAppend ct.bv
          else Fl4Spec.postpone sc.bv) σ = ({((), σ')}, False) ∧ SchedRel st N T C c r.1 σ' ∧ Inv σ' ∧
          KView σ σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ σ'.consumedTime = σ.consumedTime ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
  obtain ⟨xt, hkt, -, -, hsct, -⟩ := hs.tcb ct hct
  have hsct' : xt.tcbSchedContext = some sc.bv := by rw [hsct, hts, optRef_ne hsc0]
  obtain ⟨xt', scp, y, m, hkt', hsc', hrun, hky, hact, hnr⟩ := schedulable_inv hsch
  rw [hkt] at hkt'; cases hkt'
  rw [hsct'] at hsc'; cases hsc'
  rw [hk] at hky; cases hky
  have hne : x.scRefills ≠ [] := hI.ne _ _ _ hk
  have hct0 : ct ≠ 0#u64 := fun e => (hc.tcbs ct hct).ne0 (by rw [e]; rfl)
  have hr0 : (L.mem s (inqA ct) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra h
    exact hnr (by rw [hs.rel]; exact List.mem_map_of_mem ((hc.released ct hct).1 h))
  have hRel : RelOK σ :=
    ⟨fun u hu => by obtain ⟨x, p, -, -, h1, h2, -⟩ := hI.rel u hu; exact ⟨x, p, h1, h2⟩, hI.sorted⟩
  have hpp : (do let s1 ← sched.postpone st s sc; ok (s1, a)) ⦃ r => r.2 = a ∧ ∃ σ',
      Fl4Spec.postpone (Z := Unit) sc.bv σ = ({((), σ')}, False) ∧ SchedRel st N T C c r.1 σ' ∧ Inv σ' ∧
      KView σ σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ σ'.consumedTime = σ.consumedTime ⦄ := by
    refine WP.spec_bind (postpone_refines s σ hS hRel hsc hct htw (by rw [hts]; exact hsc0) hr0) ?_
    rintro s1 ⟨σ', hp, hk', -, -, -, hf, hS'⟩
    simp only [WP.spec_ok]
    refine ⟨trivial, σ', hp, hS', ?_, KView.of_kheap hk', hR.frame hS.placed hf (KView.of_kheap hk'), ?_⟩
    all_goals obtain ⟨b0, hp2⟩ := postpone_eq hk (by rw [hx.tcb, htw, optRef_ne hct0]) hkt (specRt σ) (fun u hu => by
      rcases hu with rfl | hu
      · exact ⟨xt, sc.bv, x, n, hkt, hsct', hk, hne, specRt_eq hkt hsct' hk hne⟩
      · obtain ⟨xu, pu, yu, nu, h1, h2, -, h4, -⟩ := hI.rel u hu
        exact ⟨xu, pu, yu, nu, h1, h2, h4, hI.ne _ _ _ h4, specRt_eq h1 h2 h4 (hI.ne _ _ _ h4)⟩)
    all_goals rw [hp2] at hp
    all_goals rw [pair_eq hp]
    · exact hI.postponed hkt hsct' hrun hk hact b0
    · rfl
  refine WP.spec_bind (ready_refines s σ hS hsc hk) ?_
  intro b hb
  rw [getScRefillReady_eq hk hne] at hb
  have eb := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb))).1
  have hsp1 : ∀ m : Fl4Spec.SMonad Unit Unit, (do
      let ready ← Fl4Spec.getScRefillReady (Z := Unit) sc.bv
      let sufficient ← Fl4Spec.getScRefillSufficient sc.bv 0
      if ready = true ∧ sufficient = true then Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedAppend ct.bv
      else Fl4Spec.postpone sc.bv) σ =
      (if b = true ∧ Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd x) = true then
        Fl4Spec.tcbSchedAction Fl4Spec.tcbSchedAppend ct.bv σ else Fl4Spec.postpone sc.bv σ) := by
    intro _
    rw [nd_bind_one (getScRefillReady_eq hk hne), nd_bind_one (getScRefillSufficient_eq hk hne 0), eb]
    split_ifs <;> rfl
  have hsp := hsp1 (pure ())
  by_cases hb' : b = true
  · simp only [hb', ↓reduceIte]
    refine WP.spec_bind (sufficient_refines s a σ hS hsc hk 0#u64 hmb) ?_
    intro b1 hb1
    rw [getScRefillSufficient_eq hk hne] at hb1
    have eb1 := (Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst hb1))).1
    replace eb1 : Fl4Spec.refillSufficient 0 (Fl4Spec.refillHd x) = b1 := eb1
    by_cases hb1' : b1 = true
    · simp only [hb1', ↓reduceIte]
      refine WP.spec_bind (append_refines s σ hS ct hct (fun _ => hr0)) ?_
      rintro s1 ⟨σ', ha, hk', -, hf, hS'⟩
      simp only [WP.spec_ok]
      have hrel : released σ x := ⟨eb.trans hb', eb1.trans hb1'⟩
      have hInv : Inv σ := hI.inv fun x' hx' _ => by
        intro x'' scp' y' m' h1 h2 h3 _ _
        rw [hkt] at h1; cases h1; rw [hsct'] at h2; cases h2; rw [hk] at h3; cases h3; exact hrel
      refine ⟨trivial, σ', ?_, hS', ?_, KView.of_kheap hk', hR.frame hS.placed hf (KView.of_kheap hk'), ?_⟩
      · rw [hsp, ite_t ⟨hb', eb1.trans hb1'⟩]; exact ha
      · rw [tcbSchedAction_gen hkt] at ha
        rw [pair_eq ha]
        exact hInv.qchange (qchange_append hkt hsch)
      · rw [tcbSchedAction_gen hkt] at ha
        rw [pair_eq ha]; rfl
    · simp only [hb1', Bool.false_eq_true, ↓reduceIte]
      refine WP.spec_mono hpp ?_
      rintro r ⟨h1, σ', hp, h2, h3, h4⟩
      refine ⟨h1, σ', ?_, h2, h3, h4⟩
      rw [hsp, ite_f (fun h => hb1' (eb1.symm.trans h.2))]; exact hp
  · simp only [hb', Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_mono hpp ?_
    rintro r ⟨h1, σ', hp, h2, h3, h4⟩
    refine ⟨h1, σ', ?_, h2, h3, h4⟩
    rw [hsp, ite_f (fun h => hb' h.1)]; exact hp
end

end

end Fl4Proofs.P3.Sched
