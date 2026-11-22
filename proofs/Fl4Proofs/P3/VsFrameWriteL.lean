/-
P3 (DESIGN.md §9), VSpace: **writing a large or huge page entry**
(`write_mapping` at the PD and PDPT level: `write_mapping_rel_pd`,
`write_mapping_rel_pdpt`, VsPtWrite's `write_mapping_rel` one and two levels
up), with the hypotheses for every level (`VsMapHypsAll`) and their lift to
the CSpace and ASID relations (`VsMapHypsAll.ext`).
-/
import Fl4Proofs.P3.VsFrameMapL
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section Hyps
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- The TLB flushes of a mapping, and `SR` stable under the entry writes at
every level (VsPtWrite's `VsMapHyps`, for PTs, PDs and PDPTs). -/
structure VsMapHypsAll (A : Type) (ar : machine.Arch A) (L1 L2 L3 : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop) :
    Prop where
  stable1 : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (PtW L1) → PtStep σ σ' → SR s' a σ'
  stable2 : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (PdW L2) → PdStep σ σ' → SR s' a σ'
  stable3 : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (PdptW L3) → PdptStep σ σ' → SR s' a σ'
  flushOK : ∀ (vs : Fl4Spec.ObjRef) (asid : Fl4Spec.Asid) (σ : Fl4Spec.State Unit),
    ¬ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid σ).2
  noFlush : ∀ s a σ (vs : Fl4Spec.ObjRef) (asid : U64), SR s a σ →
    ∃ σ', ((), σ') ∈ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid.bv σ).1 ∧ SR s a σ'
  flushPage : ∀ s a σ (vs : Fl4Spec.ObjRef) (asid vaddr : U64), SR s a σ → ar.invalidate_page a asid vaddr ⦃ a' =>
    ∃ σ', ((), σ') ∈ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid.bv σ).1 ∧ SR s a' σ' ⦄
  flushAsid : ∀ s a σ (vs : Fl4Spec.ObjRef) (asid : U64), SR s a σ → ar.invalidate_asid a asid ⦃ a' =>
    ∃ σ', ((), σ') ∈ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid.bv σ).1 ∧ SR s a' σ' ⦄

/-- `SR` with the CSpace and ASID relations, for every table level. -/
def MapRelA {A : Type} (th : TypedHeap) (P L4 L3 L2 L1 : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop) (s : S)
    (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  SR s a σ ∧ StateRel th (L.mem s) σ ∧ SlotsValid th (L.mem s) ∧ VsRel P (L.mem s) (L.ksb s) σ ∧
    VsPlaced P (L.ksb s) ∧ ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b

/-- The hypotheses of the large and huge frame maps. -/
structure VsFrameHypsL (A : Type) (ar : machine.Arch A) (th : TypedHeap) (P L4 L3 L2 L1 : Set U64)
    (SR : S → A → Fl4Spec.State Unit → Prop) : Prop where
  restart : ∀ s a σ (ct : U64) (x : Fl4Spec.Tcb), StateRel th (L.mem s) σ → SlotsValid th (L.mem s) →
    VsRel P (L.mem s) (L.ksb s) σ → PtRel L4 L3 L2 L1 (L.mem s) σ → SR s a σ → ct.bv = σ.curThread →
    σ.kheap ct.bv = some (.tcb x) → th ct = some .tcb →
    OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) →
    Fl4Spec.runnable x.tcbState = true →
    sched.set_thread_state st s ct sched.TS_RESTART ⦃ s' =>
      StateRel th (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SlotsValid th (L.mem s') ∧
      VsRel P (L.mem s') (L.ksb s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      PtRel L4 L3 L2 L1 (L.mem s') (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧
      SR s' a (stsAct (updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ∧ L.ksb s' = L.ksb s ⦄
  capStable : ∀ s s' a σ σ', SR s a σ → WritesIn st s s' (SlotW th) → CapStep σ σ' → SR s' a σ'
  map : VsMapHypsAll st A ar L1 L2 L3 SR
  /-- #65: `SR` relates FL4's 1 GiB-page feature bit to the spec's flag. -/
  huge : ∀ s a σ, SR s a σ → HugeRel (L.mem s) (L.ksb s) σ

end Hyps

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem VsMapHypsAll.ext {A : Type} {ar : machine.Arch A} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsMapHypsAll st A ar L1 L2 L3 SR) (hPl : Placed th)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) : VsMapHypsAll st A ar L1 L2 L3 (MapRelA st th P L4 L3 L2 L1 SR) where
  stable1 s s' a σ σ' := by
    rintro ⟨hS, hSt, hSV, hR, hVP, hPV⟩ hW hst
    have hS' := hH.stable1 s s' a σ σ' hS hW hst
    obtain ⟨p, f, f', hk, rfl⟩ := hst
    have hcap := capAt_of_writes hPl hW (fun b h => hPS b (by obtain ⟨p, hp, i, hi, hb⟩ := h; exact ⟨p, Or.inr (Or.inr (Or.inr hp)), i, hi, hb⟩))
    refine ⟨hS', Vs.StateRel.upd_other (StateRel.of_caps hSt hcap) hk _, Vs.SlotsValid.of_caps hSV hcap, ?_,
      by rw [hW.1]; exact hVP, by rw [hW.1]; exact hPV⟩
    rw [hW.1]
    refine hR.frame (fun b hb => hW.2.2 b (hb.aligned hVP) (fun h => hPV b (by obtain ⟨p, hp, i, hi, hb⟩ := h; exact ⟨p, Or.inr (Or.inr (Or.inr hp)), i, hi, hb⟩) hb)) rfl (fun q hq => ?_)
    obtain ⟨g, hg, -⟩ := hR.pool q hq
    have : q.bv ≠ p := kheap_ne hg hk (fun _ h1 h2 => by subst h1; cases h2)
    simp [updK, this]
  stable2 s s' a σ σ' := by
    rintro ⟨hS, hSt, hSV, hR, hVP, hPV⟩ hW hst
    have hS' := hH.stable2 s s' a σ σ' hS hW hst
    obtain ⟨p, f, f', hk, rfl⟩ := hst
    have hcap := capAt_of_writes hPl hW (fun b h => hPS b (by obtain ⟨p, hp, i, hi, hb⟩ := h; exact ⟨p, Or.inr (Or.inr (Or.inl hp)), i, hi, hb⟩))
    refine ⟨hS', Vs.StateRel.upd_other (StateRel.of_caps hSt hcap) hk _, Vs.SlotsValid.of_caps hSV hcap, ?_,
      by rw [hW.1]; exact hVP, by rw [hW.1]; exact hPV⟩
    rw [hW.1]
    refine hR.frame (fun b hb => hW.2.2 b (hb.aligned hVP) (fun h => hPV b (by obtain ⟨p, hp, i, hi, hb⟩ := h; exact ⟨p, Or.inr (Or.inr (Or.inl hp)), i, hi, hb⟩) hb)) rfl (fun q hq => ?_)
    obtain ⟨g, hg, -⟩ := hR.pool q hq
    have : q.bv ≠ p := kheap_ne hg hk (fun _ h1 h2 => by subst h1; cases h2)
    simp [updK, this]
  stable3 s s' a σ σ' := by
    rintro ⟨hS, hSt, hSV, hR, hVP, hPV⟩ hW hst
    have hS' := hH.stable3 s s' a σ σ' hS hW hst
    obtain ⟨p, f, f', hk, rfl⟩ := hst
    have hcap := capAt_of_writes hPl hW (fun b h => hPS b (by obtain ⟨p, hp, i, hi, hb⟩ := h; exact ⟨p, Or.inr (Or.inl hp), i, hi, hb⟩))
    refine ⟨hS', Vs.StateRel.upd_other (StateRel.of_caps hSt hcap) hk _, Vs.SlotsValid.of_caps hSV hcap, ?_,
      by rw [hW.1]; exact hVP, by rw [hW.1]; exact hPV⟩
    rw [hW.1]
    refine hR.frame (fun b hb => hW.2.2 b (hb.aligned hVP) (fun h => hPV b (by obtain ⟨p, hp, i, hi, hb⟩ := h; exact ⟨p, Or.inr (Or.inl hp), i, hi, hb⟩) hb)) rfl (fun q hq => ?_)
    obtain ⟨g, hg, -⟩ := hR.pool q hq
    have : q.bv ≠ p := kheap_ne hg hk (fun _ h1 h2 => by subst h1; cases h2)
    simp [updK, this]
  flushOK := hH.flushOK
  noFlush s a σ vs asid := by
    rintro ⟨hS, hSt, hSV, hR, hVP, hPV⟩
    obtain ⟨σ', h1, h2⟩ := hH.noFlush s a σ vs asid hS
    obtain ⟨ms, rfl⟩ := doMachineOp_mem h1
    exact ⟨_, h1, h2, Vs.StateRel.ms hSt ms, hSV, ⟨hR.1, hR.2, hR.3⟩, hVP, hPV⟩
  flushPage s a σ vs asid vaddr := by
    rintro ⟨hS, hSt, hSV, hR, hVP, hPV⟩
    refine WP.spec_mono (hH.flushPage s a σ vs asid vaddr hS) ?_
    rintro a' ⟨σ', h1, h2⟩
    obtain ⟨ms, rfl⟩ := doMachineOp_mem h1
    exact ⟨_, h1, h2, Vs.StateRel.ms hSt ms, hSV, ⟨hR.1, hR.2, hR.3⟩, hVP, hPV⟩
  flushAsid s a σ vs asid := by
    rintro ⟨hS, hSt, hSV, hR, hVP, hPV⟩
    refine WP.spec_mono (hH.flushAsid s a σ vs asid hS) ?_
    rintro a' ⟨σ', h1, h2⟩
    obtain ⟨ms, rfl⟩ := doMachineOp_mem h1
    exact ⟨_, h1, h2, Vs.StateRel.ms hSt ms, hSV, ⟨hR.1, hR.2, hR.3⟩, hVP, hPV⟩


theorem write_mapping_rel_pd {A : Type} {ar : machine.Arch A} {L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsMapHypsAll st A ar L1 L2 L3 SR) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : PtRel L4 L3 L2 L1 (L.mem s) σ) (hP : PtPlaced L4 L3 L2 L1) (hS : SR s a σ) {p : U64} (hp : p ∈ L2)
    {i : U64} (hi : i.val < 512) (e : U64) (pte : Fl4Spec.PDE) (he : PDERel L1 e pte) (asid vaddr : U64)
    (defer : Bool) (vs : Fl4Spec.ObjRef) :
    vspace.write_mapping st ar s a (peA p i) e asid vaddr defer ⦃ r =>
      r.1 = L.wr s (peA p i) e ∧
      ¬ ((Fl4Spec.storePde (Z := Unit) (peA p i).bv pte >>= fun _ =>
          Fl4Spec.invalidatePageStructureCacheAsid vs asid.bv) σ).2 ∧
      ∃ σ', ((), σ') ∈ ((Fl4Spec.storePde (Z := Unit) (peA p i).bv pte >>= fun _ =>
          Fl4Spec.invalidatePageStructureCacheAsid vs asid.bv) σ).1 ∧
        PtRel L4 L3 L2 L1 (L.mem r.1) σ' ∧ SR r.1 r.2 σ' ⦄ := by
  obtain ⟨f, hk, -⟩ := hR.l2 p hp
  have hpa := hP p (Or.inr (Or.inr (Or.inl hp)))
  have hea : Aligned (peA p i) := by show _ % 8 = 0; rw [peA_val (tbl_fit hpa) hi]; omega
  set σ1 := updK σ p.bv (.archObj (.pageDirectory (Function.update f (Fl4Spec.ucast 9 i.bv) pte)))
  have hst : Fl4Spec.storePde (Z := Unit) (peA p i).bv pte σ = ({((), σ1)}, False) := by
    rw [peA_bv _ _ hi (tbl_fit hpa)]; exact storePde_at hpa hk hi pte
  have hR1 : PtRel L4 L3 L2 L1 (L.mem (L.wr s (peA p i) e)) σ1 :=
    hR.upd_l2 hP hp hk hi e pte he (fun b hb hne => L.mem_wr_ne hea hb (fun h => hne (UScalar.eq_of_val_eq h).symm))
      (L.mem_wr_same hea)
  have hW : WritesIn st s (L.wr s (peA p i) e) (PdW L2) :=
    ⟨by simp, by simp, fun b hb hn => L.mem_wr_ne hea hb (fun h => hn ⟨p, hp, i, hi, (UScalar.eq_of_val_eq h).symm⟩)⟩
  have hS1 := hH.stable2 _ _ a σ σ1 hS hW ⟨p.bv, f, _, hk, rfl⟩
  have hnf : ¬ ((Fl4Spec.storePde (Z := Unit) (peA p i).bv pte >>= fun _ =>
      Fl4Spec.invalidatePageStructureCacheAsid vs asid.bv) σ).2 := by
    rw [nd_bind_one hst]; exact hH.flushOK _ _ _
  have hmem : ∀ σ', ((), σ') ∈ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid.bv σ1).1 →
      ((), σ') ∈ ((Fl4Spec.storePde (Z := Unit) (peA p i).bv pte >>= fun _ =>
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


theorem write_mapping_rel_pdpt {A : Type} {ar : machine.Arch A} {L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsMapHypsAll st A ar L1 L2 L3 SR) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hR : PtRel L4 L3 L2 L1 (L.mem s) σ) (hP : PtPlaced L4 L3 L2 L1) (hS : SR s a σ) {p : U64} (hp : p ∈ L3)
    {i : U64} (hi : i.val < 512) (e : U64) (pte : Fl4Spec.PDPTE) (he : PDPTERel L2 e pte) (asid vaddr : U64)
    (defer : Bool) (vs : Fl4Spec.ObjRef) :
    vspace.write_mapping st ar s a (peA p i) e asid vaddr defer ⦃ r =>
      r.1 = L.wr s (peA p i) e ∧
      ¬ ((Fl4Spec.storePdpte (Z := Unit) (peA p i).bv pte >>= fun _ =>
          Fl4Spec.invalidatePageStructureCacheAsid vs asid.bv) σ).2 ∧
      ∃ σ', ((), σ') ∈ ((Fl4Spec.storePdpte (Z := Unit) (peA p i).bv pte >>= fun _ =>
          Fl4Spec.invalidatePageStructureCacheAsid vs asid.bv) σ).1 ∧
        PtRel L4 L3 L2 L1 (L.mem r.1) σ' ∧ SR r.1 r.2 σ' ⦄ := by
  obtain ⟨f, hk, -⟩ := hR.l3 p hp
  have hpa := hP p (Or.inr (Or.inl hp))
  have hea : Aligned (peA p i) := by show _ % 8 = 0; rw [peA_val (tbl_fit hpa) hi]; omega
  set σ1 := updK σ p.bv (.archObj (.pdPointerTable (Function.update f (Fl4Spec.ucast 9 i.bv) pte)))
  have hst : Fl4Spec.storePdpte (Z := Unit) (peA p i).bv pte σ = ({((), σ1)}, False) := by
    rw [peA_bv _ _ hi (tbl_fit hpa)]; exact storePdpte_at hpa hk hi pte
  have hR1 : PtRel L4 L3 L2 L1 (L.mem (L.wr s (peA p i) e)) σ1 :=
    hR.upd_l3 hP hp hk hi e pte he (fun b hb hne => L.mem_wr_ne hea hb (fun h => hne (UScalar.eq_of_val_eq h).symm))
      (L.mem_wr_same hea)
  have hW : WritesIn st s (L.wr s (peA p i) e) (PdptW L3) :=
    ⟨by simp, by simp, fun b hb hn => L.mem_wr_ne hea hb (fun h => hn ⟨p, hp, i, hi, (UScalar.eq_of_val_eq h).symm⟩)⟩
  have hS1 := hH.stable3 _ _ a σ σ1 hS hW ⟨p.bv, f, _, hk, rfl⟩
  have hnf : ¬ ((Fl4Spec.storePdpte (Z := Unit) (peA p i).bv pte >>= fun _ =>
      Fl4Spec.invalidatePageStructureCacheAsid vs asid.bv) σ).2 := by
    rw [nd_bind_one hst]; exact hH.flushOK _ _ _
  have hmem : ∀ σ', ((), σ') ∈ (Fl4Spec.invalidatePageStructureCacheAsid (Z := Unit) vs asid.bv σ1).1 →
      ((), σ') ∈ ((Fl4Spec.storePdpte (Z := Unit) (peA p i).bv pte >>= fun _ =>
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
