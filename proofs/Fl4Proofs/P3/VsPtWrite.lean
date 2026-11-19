/-
P3 (DESIGN.md §9), VSpace: **writing a page-table entry** (FL4
`vspace::write_mapping`) against l4v `store_pte` followed by the TLB flush
of `perform_page_invocation` (`invalidate_page_structure_cache_asid`).

* `PtRel.upd_l1`: the relation after an entry of a PT of `L1` is written
  with a word related to the new `PTE`;
* `storePte_at`: l4v's `store_pte` at entry `i` of a PT;
* `write_mapping_rel`: FL4 writes the entry, then flushes (nothing, a page,
  or the ASID, depending on the old and new entries); l4v stores the entry
  and flushes the ASID's paging-structure cache. The flushes are arch
  effects (`VsMapHyps`): each of FL4's is matched by one outcome of l4v's,
  which does not fail.
-/
import Fl4Proofs.P3.VsPte
import Fl4Proofs.P0.Auto
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

/-- The entry words of the page tables of `L1`. -/
def PtW (L1 : Set U64) (b : U64) : Prop := ∃ p ∈ L1, ∃ i : U64, i.val < 512 ∧ b = peA p i

/-- The spec change of a PTE write. -/
def PtStep (σ σ' : Fl4Spec.State Unit) : Prop :=
  ∃ p f f', σ.kheap p = some (.archObj (.pageTable f)) ∧ σ' = updK σ p (.archObj (.pageTable f'))

section Hyps
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- The TLB flushes of a mapping, and `SR` (see the module docstring). -/
structure VsMapHyps (A : Type) (ar : machine.Arch A) (L1 : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop) :
    Prop where
  stable : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (PtW L1) → PtStep σ σ' → SR s' a σ'
  flushOK : ∀ (vs : Fl4Spec.ObjRef) (asid : Fl4Spec.Asid) (σ : Fl4Spec.State Unit),
    ¬ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid σ).2
  noFlush : ∀ s a σ (vs : Fl4Spec.ObjRef) (asid : U64), SR s a σ →
    ∃ σ', ((), σ') ∈ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid.bv σ).1 ∧ SR s a σ'
  flushPage : ∀ s a σ (vs : Fl4Spec.ObjRef) (asid vaddr : U64), SR s a σ → ar.invalidate_page a asid vaddr ⦃ a' =>
    ∃ σ', ((), σ') ∈ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid.bv σ).1 ∧ SR s a' σ' ⦄
  flushAsid : ∀ s a σ (vs : Fl4Spec.ObjRef) (asid : U64), SR s a σ → ar.invalidate_asid a asid ⦃ a' =>
    ∃ σ', ((), σ') ∈ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid.bv σ).1 ∧ SR s a' σ' ⦄

end Hyps

section Spec
open Fl4Spec

theorem storePte_at {σ : State Unit} {q : U64} (hq : q.val % 4096 = 0) {f : BitVec 9 → PTE}
    (hk : σ.kheap q.bv = some (.archObj (.pageTable f))) {j : U64} (hj : j.val < 512) (pte : PTE) :
    storePte (Z := Unit) (q.bv + (j.bv <<< wordSizeBits)) pte σ =
      ({((), updK σ q.bv (.archObj (.pageTable (Function.update f (ucast 9 j.bv) pte))))}, False) := by
  obtain ⟨h1, h2⟩ := split_slot q.bv j.bv hq hj
  unfold storePte
  rw [nd_pure_bind', nd_pure_bind']
  simp only [ptBits, tableSize, ptTranslationBits, wordSizeBits] at h1 h2 ⊢
  rw [h1, h2, nd_bind_one (show getPt (Z := Unit) q.bv σ = ({(f, σ)}, False) by
    unfold getPt; rw [nd_bind_one (getObject_eq hk)]; rfl), nd_pure_bind']
  exact setObject_eq hk rfl

end Spec

/-- Distinct 4K-aligned tables have distinct entry words. -/
theorem peA_ne {p q i j : U64} (hp : p.val % 4096 = 0) (hq : q.val % 4096 = 0) (hpq : p ≠ q) (hi : i.val < 512)
    (hj : j.val < 512) : peA p i ≠ peA q j := by
  intro e
  have := congrArg UScalar.val e
  rw [peA_val (tbl_fit hp) hi, peA_val (tbl_fit hq) hj] at this
  have : p.val ≠ q.val := fun h => hpq (UScalar.eq_of_val_eq h)
  omega

/-- **The relation after writing entry `i` of the PT at `p`.** -/
theorem PtRel.upd_l1 {L4 L3 L2 L1 : Set U64} {m m' : U64 → U64} {σ : Fl4Spec.State Unit} (hP : PtPlaced L4 L3 L2 L1)
    (hR : PtRel L4 L3 L2 L1 m σ) {p : U64} (hp : p ∈ L1) {f : BitVec 9 → Fl4Spec.PTE}
    (hk : σ.kheap p.bv = some (.archObj (.pageTable f))) {i : U64} (hi : i.val < 512) (v : U64) (pte : Fl4Spec.PTE)
    (hv : PTERel v pte) (hm : ∀ b, Aligned b → b ≠ peA p i → m' b = m b) (hme : m' (peA p i) = v) :
    PtRel L4 L3 L2 L1 m' (updK σ p.bv (.archObj (.pageTable (Function.update f (Fl4Spec.ucast 9 i.bv) pte)))) := by
  have hpa := hP p (Or.inr (Or.inr (Or.inr hp)))
  have hal : ∀ q j : U64, q.val % 4096 = 0 → j.val < 512 → Aligned (peA q j) := fun q j hq hj => by
    show _ % 8 = 0; rw [peA_val (tbl_fit hq) hj]; omega
  have hoth : ∀ q j : U64, q.val % 4096 = 0 → q ≠ p → j.val < 512 → m' (peA q j) = m (peA q j) :=
    fun q j hq hqp hj => hm _ (hal q j hq hj) (peA_ne hq hpa hqp hj hi)
  have hkq : ∀ q : U64, ∀ o, σ.kheap q.bv = some o → (∀ g, o ≠ .archObj (.pageTable g)) →
      (updK σ p.bv (.archObj (.pageTable (Function.update f (Fl4Spec.ucast 9 i.bv) pte)))).kheap q.bv = some o ∧ q ≠ p := by
    intro q o hq hno
    have hqp : q ≠ p := fun e => by subst e; rw [hk] at hq; injection hq with hq; exact hno f hq.symm
    exact ⟨by simp [show q.bv ≠ p.bv from fun h => hqp (eq_of_bv h), hq], hqp⟩
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · obtain ⟨g, hg, hgf⟩ := hR.l4 q hq
    obtain ⟨hk', hqp⟩ := hkq q _ hg (fun _ h => by cases h)
    have hqa := hP q (Or.inl hq)
    exact ⟨g, hk', fun j hj => by rw [hoth q j hqa hqp (by omega)]; exact hgf j hj⟩
  · obtain ⟨g, hg, hgf⟩ := hR.l3 q hq
    obtain ⟨hk', hqp⟩ := hkq q _ hg (fun _ h => by cases h)
    have hqa := hP q (Or.inr (Or.inl hq))
    exact ⟨g, hk', fun j hj => by rw [hoth q j hqa hqp hj]; exact hgf j hj⟩
  · obtain ⟨g, hg, hgf⟩ := hR.l2 q hq
    obtain ⟨hk', hqp⟩ := hkq q _ hg (fun _ h => by cases h)
    have hqa := hP q (Or.inr (Or.inr (Or.inl hq)))
    exact ⟨g, hk', fun j hj => by rw [hoth q j hqa hqp hj]; exact hgf j hj⟩
  · obtain ⟨g, hg, hgf⟩ := hR.l1 q hq
    have hqa := hP q (Or.inr (Or.inr (Or.inr hq)))
    by_cases e : q = p
    · subst e
      rw [hk] at hg; injection hg with hg; injection hg with hg; injection hg with hg; subst hg
      refine ⟨Function.update f (Fl4Spec.ucast 9 i.bv) pte, by simp, fun j hj => ?_⟩
      by_cases ej : j = i
      · subst ej; rw [Function.update_self, hme]; exact hv
      · rw [Function.update_of_ne (fun h => ej (ucast_inj 9 hj hi h)),
          hm _ (hal q j hqa hj) (fun h => ej (by
            have := congrArg UScalar.val h
            rw [peA_val (tbl_fit hqa) hj, peA_val (tbl_fit hqa) hi] at this
            exact UScalar.eq_of_val_eq (by omega)))]
        exact hgf j hj
    · exact ⟨g, by simp [show q.bv ≠ p.bv from fun h => e (eq_of_bv h), hg], fun j hj => by rw [hoth q j hqa e hj]; exact hgf j hj⟩

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`write_mapping`** of entry `i` of a PT of `L1` refines l4v's
`store_pte` and flush: the spec does not fail, FL4 writes the entry, and
one of the spec's outcomes is related again. -/
theorem write_mapping_rel {A : Type} {ar : machine.Arch A} {L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsMapHyps st A ar L1 SR) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : PtRel L4 L3 L2 L1 (L.mem s) σ) (hP : PtPlaced L4 L3 L2 L1) (hS : SR s a σ) {p : U64} (hp : p ∈ L1)
    {i : U64} (hi : i.val < 512) (e : U64) (pte : Fl4Spec.PTE) (he : PTERel e pte) (asid vaddr : U64)
    (defer : Bool) (vs : Fl4Spec.ObjRef) :
    vspace.write_mapping st ar s a (peA p i) e asid vaddr defer ⦃ r =>
      r.1 = L.wr s (peA p i) e ∧
      ¬ ((Fl4Spec.storePte (Z := Unit) (peA p i).bv pte >>= fun _ =>
          Fl4Spec.invalidatePageStructureCacheAsid vs asid.bv) σ).2 ∧
      ∃ σ', ((), σ') ∈ ((Fl4Spec.storePte (Z := Unit) (peA p i).bv pte >>= fun _ =>
          Fl4Spec.invalidatePageStructureCacheAsid vs asid.bv) σ).1 ∧
        PtRel L4 L3 L2 L1 (L.mem r.1) σ' ∧ SR r.1 r.2 σ' ⦄ := by
  obtain ⟨f, hk, -⟩ := hR.l1 p hp
  have hpa := hP p (Or.inr (Or.inr (Or.inr hp)))
  have hea : Aligned (peA p i) := by show _ % 8 = 0; rw [peA_val (tbl_fit hpa) hi]; omega
  set σ1 := updK σ p.bv (.archObj (.pageTable (Function.update f (Fl4Spec.ucast 9 i.bv) pte)))
  have hst : Fl4Spec.storePte (Z := Unit) (peA p i).bv pte σ = ({((), σ1)}, False) := by
    rw [peA_bv _ _ hi (tbl_fit hpa)]; exact storePte_at hpa hk hi pte
  have hR1 : PtRel L4 L3 L2 L1 (L.mem (L.wr s (peA p i) e)) σ1 :=
    hR.upd_l1 hP hp hk hi e pte he (fun b hb hne => L.mem_wr_ne hea hb (fun h => hne (UScalar.eq_of_val_eq h).symm))
      (L.mem_wr_same hea)
  have hW : WritesIn st s (L.wr s (peA p i) e) (PtW L1) :=
    ⟨by simp, by simp, fun b hb hn => L.mem_wr_ne hea hb (fun h => hn ⟨p, hp, i, hi, (UScalar.eq_of_val_eq h).symm⟩)⟩
  have hS1 := hH.stable _ _ a σ σ1 hS hW ⟨p.bv, f, _, hk, rfl⟩
  have hnf : ¬ ((Fl4Spec.storePte (Z := Unit) (peA p i).bv pte >>= fun _ =>
      Fl4Spec.invalidatePageStructureCacheAsid vs asid.bv) σ).2 := by
    rw [nd_bind_one hst]; exact hH.flushOK _ _ _
  have hmem : ∀ σ', ((), σ') ∈ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid.bv σ1).1 →
      ((), σ') ∈ ((Fl4Spec.storePte (Z := Unit) (peA p i).bv pte >>= fun _ =>
        Fl4Spec.invalidatePageStructureCacheAsid vs asid.bv) σ).1 := fun σ' h => by rw [nd_bind_one hst]; exact h
  have hPt' : ∀ σ', ((), σ') ∈ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid.bv σ1).1 →
      PtRel L4 L3 L2 L1 (L.mem (L.wr s (peA p i) e)) σ' := fun σ' h => by
    obtain ⟨ms, rfl⟩ := doMachineOp_mem h
    exact ⟨hR1.l4, hR1.l3, hR1.l2, hR1.l1⟩
  unfold vspace.write_mapping
  rw [L.read_eq]
  apply ok_bind_spec
  rw [L.write_eq]
  apply ok_bind_spec
  rw [P_PRESENT_eq]
  apply ok_bind_spec
  unfold lift
  apply ok_bind_spec
  split
  · obtain ⟨σ', h1, h2⟩ := hH.noFlush _ a σ1 vs asid hS1
    exact (WP.spec_ok _).2 ⟨rfl, hnf, σ', hmem σ' h1, hPt' σ' h1, h2⟩
  · refine WP.spec_bind (Fl4Proofs.P0.vspace.rights_raised.p0 _ _) ?_
    rintro b -
    split
    · refine WP.spec_bind (hH.flushPage _ a σ1 vs asid vaddr hS1) ?_
      rintro a1 ⟨σ', h1, h2⟩
      exact (WP.spec_ok _).2 ⟨rfl, hnf, σ', hmem σ' h1, hPt' σ' h1, h2⟩
    · split
      · refine WP.spec_bind (Fl4Proofs.P0.vspace.rights_lowered.p0 _ _) ?_
        rintro b1 -
        split
        · obtain ⟨σ', h1, h2⟩ := hH.noFlush _ a σ1 vs asid hS1
          exact (WP.spec_ok _).2 ⟨rfl, hnf, σ', hmem σ' h1, hPt' σ' h1, h2⟩
        · refine WP.spec_bind (hH.flushAsid _ a σ1 vs asid hS1) ?_
          rintro a1 ⟨σ', h1, h2⟩
          exact (WP.spec_ok _).2 ⟨rfl, hnf, σ', hmem σ' h1, hPt' σ' h1, h2⟩
      · refine WP.spec_bind (hH.flushAsid _ a σ1 vs asid hS1) ?_
        rintro a1 ⟨σ', h1, h2⟩
        exact (WP.spec_ok _).2 ⟨rfl, hnf, σ', hmem σ' h1, hPt' σ' h1, h2⟩

end

end

end Fl4Proofs.P3.Vs
