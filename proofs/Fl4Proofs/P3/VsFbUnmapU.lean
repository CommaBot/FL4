/-
P3 (issue #16, FL4 #71), VSpace FrameBatch (KENTRY-PLAN fb3l): **FL4's
`unmap_page_unflushed` refines the spec's `unmapPageUnflushed`** (a DELETE
entry's deferred unmap): VsFrameUnmapRel's `unmap_page_rel` without the ASID
lookup (the batch's root given) and without the flush; the Boolean (whether
an entry was cleared) is the spec's.

* `uU_{s,l,h}_{noSlot,other,match}`: the spec's outcomes.
* `unmap_unflushed_rel`: the outcome, `UR` after (any `SR` stable under the
  entry writes, `VsUnmapPageHyps`' stability fields), the writes in the page
  tables, `KFoot`, the non-arch objects kept.
-/
import Fl4Proofs.P3.XTopJointFbMapRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3

noncomputable section

section Spec
open Fl4Spec

theorem uU_s_noSlot {v : VSpaceRef} {pp vs : ObjRef} {σ : State Unit} {e : LookupFailure}
    (hl : ExceptT.run (lookupPtSlot (Z := Unit) vs v) σ = ({(.error e, σ)}, False)) :
    unmapPageUnflushed (Z := Unit) .x64SmallPage vs v pp σ = ({(false, σ)}, False) := by
  unfold unmapPageUnflushed
  refine (catch_err (e := e) ?_).trans rfl
  exact runE_bind_err hl

theorem uU_s_other {v : VSpaceRef} {pp vs slot : ObjRef} {σ : State Unit} {x : PTE}
    (hl : ExceptT.run (lookupPtSlot (Z := Unit) vs v) σ = ({(.ok slot, σ)}, False))
    (hg : getPte (Z := Unit) slot σ = ({(x, σ)}, False)) (hc : checkMappingPptr pp (.vmPTE x) = false) :
    unmapPageUnflushed (Z := Unit) .x64SmallPage vs v pp σ = ({(false, σ)}, False) := by
  unfold unmapPageUnflushed
  refine (catch_err (e := .invalidRoot) ?_).trans rfl
  rw [runE_bind_ok hl, runE_bind_ok (runE_liftE hg)]
  exact runE_bind_err (by rw [runE_unlessE_false (by simp [hc])]; rfl)

theorem uU_s_match {v : VSpaceRef} {pp vs slot : ObjRef} {σ σ1 : State Unit} {x : PTE}
    (hl : ExceptT.run (lookupPtSlot (Z := Unit) vs v) σ = ({(.ok slot, σ)}, False))
    (hg : getPte (Z := Unit) slot σ = ({(x, σ)}, False)) (hc : checkMappingPptr pp (.vmPTE x) = true)
    (hs : storePte (Z := Unit) slot .invalidPTE σ = ({((), σ1)}, False)) :
    unmapPageUnflushed (Z := Unit) .x64SmallPage vs v pp σ = ({(true, σ1)}, False) := by
  unfold unmapPageUnflushed
  refine catch_ok ?_
  rw [runE_bind_ok hl, runE_bind_ok (runE_liftE hg), runE_bind_ok (runE_unlessE_true (by simp [hc]) _ σ),
    runE_bind_ok (runE_liftE hs)]
  rfl

theorem uU_l_noSlot {v : VSpaceRef} {pp vs : ObjRef} {σ : State Unit} {e : LookupFailure}
    (hl : ExceptT.run (lookupPdSlot (Z := Unit) vs v) σ = ({(.error e, σ)}, False)) :
    unmapPageUnflushed (Z := Unit) .x64LargePage vs v pp σ = ({(false, σ)}, False) := by
  unfold unmapPageUnflushed
  refine (catch_err (e := e) ?_).trans rfl
  exact runE_bind_err hl

theorem uU_l_other {v : VSpaceRef} {pp vs slot : ObjRef} {σ : State Unit} {x : PDE}
    (hl : ExceptT.run (lookupPdSlot (Z := Unit) vs v) σ = ({(.ok slot, σ)}, False))
    (hg : getPde (Z := Unit) slot σ = ({(x, σ)}, False)) (hc : checkMappingPptr pp (.vmPDE x) = false) :
    unmapPageUnflushed (Z := Unit) .x64LargePage vs v pp σ = ({(false, σ)}, False) := by
  unfold unmapPageUnflushed
  refine (catch_err (e := .invalidRoot) ?_).trans rfl
  rw [runE_bind_ok hl, runE_bind_ok (runE_liftE hg)]
  exact runE_bind_err (by rw [runE_unlessE_false (by simp [hc])]; rfl)

theorem uU_l_match {v : VSpaceRef} {pp vs slot : ObjRef} {σ σ1 : State Unit} {x : PDE}
    (hl : ExceptT.run (lookupPdSlot (Z := Unit) vs v) σ = ({(.ok slot, σ)}, False))
    (hg : getPde (Z := Unit) slot σ = ({(x, σ)}, False)) (hc : checkMappingPptr pp (.vmPDE x) = true)
    (hs : storePde (Z := Unit) slot .invalidPDE σ = ({((), σ1)}, False)) :
    unmapPageUnflushed (Z := Unit) .x64LargePage vs v pp σ = ({(true, σ1)}, False) := by
  unfold unmapPageUnflushed
  refine catch_ok ?_
  rw [runE_bind_ok hl, runE_bind_ok (runE_liftE hg), runE_bind_ok (runE_unlessE_true (by simp [hc]) _ σ),
    runE_bind_ok (runE_liftE hs)]
  rfl

theorem uU_h_noSlot {v : VSpaceRef} {pp vs : ObjRef} {σ : State Unit} {e : LookupFailure}
    (hl : ExceptT.run (lookupPdptSlot (Z := Unit) vs v) σ = ({(.error e, σ)}, False)) :
    unmapPageUnflushed (Z := Unit) .x64HugePage vs v pp σ = ({(false, σ)}, False) := by
  unfold unmapPageUnflushed
  refine (catch_err (e := e) ?_).trans rfl
  exact runE_bind_err hl

theorem uU_h_other {v : VSpaceRef} {pp vs slot : ObjRef} {σ : State Unit} {x : PDPTE}
    (hl : ExceptT.run (lookupPdptSlot (Z := Unit) vs v) σ = ({(.ok slot, σ)}, False))
    (hg : getPdpte (Z := Unit) slot σ = ({(x, σ)}, False)) (hc : checkMappingPptr pp (.vmPDPTE x) = false) :
    unmapPageUnflushed (Z := Unit) .x64HugePage vs v pp σ = ({(false, σ)}, False) := by
  unfold unmapPageUnflushed
  refine (catch_err (e := .invalidRoot) ?_).trans rfl
  rw [runE_bind_ok hl, runE_bind_ok (runE_liftE hg)]
  exact runE_bind_err (by rw [runE_unlessE_false (by simp [hc])]; rfl)

theorem uU_h_match {v : VSpaceRef} {pp vs slot : ObjRef} {σ σ1 : State Unit} {x : PDPTE}
    (hl : ExceptT.run (lookupPdptSlot (Z := Unit) vs v) σ = ({(.ok slot, σ)}, False))
    (hg : getPdpte (Z := Unit) slot σ = ({(x, σ)}, False)) (hc : checkMappingPptr pp (.vmPDPTE x) = true)
    (hs : storePdpte (Z := Unit) slot .invalidPDPTE σ = ({((), σ1)}, False)) :
    unmapPageUnflushed (Z := Unit) .x64HugePage vs v pp σ = ({(true, σ1)}, False) := by
  unfold unmapPageUnflushed
  refine catch_ok ?_
  rw [runE_bind_ok hl, runE_bind_ok (runE_liftE hg), runE_bind_ok (runE_unlessE_true (by simp [hc]) _ σ),
    runE_bind_ok (runE_liftE hs)]
  rfl

end Spec

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- **`unmap_page_unflushed`** refines `unmapPageUnflushed` (module docstring). -/
theorem unmap_unflushed_rel [Fl4Proofs.P1.PlainStore st] {A : Type} {ar : machine.Arch A} {th : TypedHeap}
    {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} (hH : VsUnmapPageHyps st A ar L3 L2 L1 SR)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hPl : Placed th) (hPP : PtPlaced L4 L3 L2 L1)
    (hPS : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ SlotW th b) (hVP : VsPlaced P (L.ksb s))
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b)
    (hU : UR st th P L4 L3 L2 L1 SR s a σ) (sz : capability.FrameSize) (r1 vaddr pp : U64) (hr1 : r1 ∈ L4)
    (hv : UserV vaddr) :
    vspace.unmap_page_unflushed st s r1 sz vaddr pp ⦃ r =>
      ∃ σ', (r.1, σ') ∈ (Fl4Spec.unmapPageUnflushed (Z := Unit) (frameSizeOf sz) r1.bv vaddr.bv pp.bv σ).1 ∧
        (σ' = σ ∨ ∃ q ao ao', σ.kheap q = some (.archObj ao) ∧ Fl4Spec.aaType ao' = Fl4Spec.aaType ao ∧
          Fl4Spec.aaType ao ≠ .aASIDPool ∧ σ' = Notif.updK σ q (.archObj ao')) ∧
        UR st th P L4 L3 L2 L1 SR r.2 a σ' ∧ L.ksb r.2 = L.ksb s ∧ KFoot σ σ' ∧ ArchShr σ σ' ∧
        WritesIn st s r.2 (PtWAll L4 L3 L2 L1) ⦄ := by
  obtain ⟨hS, hSt, hSV, hR, hPt⟩ := hU
  have hskip : Fl4Spec.unmapPageUnflushed (Z := Unit) (frameSizeOf sz) r1.bv vaddr.bv pp.bv σ = ({(false, σ)}, False) →
      (ok (false, s) : Result (Bool × S)) ⦃ r =>
        ∃ σ', (r.1, σ') ∈ (Fl4Spec.unmapPageUnflushed (Z := Unit) (frameSizeOf sz) r1.bv vaddr.bv pp.bv σ).1 ∧
          (σ' = σ ∨ ∃ q ao ao', σ.kheap q = some (.archObj ao) ∧ Fl4Spec.aaType ao' = Fl4Spec.aaType ao ∧
            Fl4Spec.aaType ao ≠ .aASIDPool ∧ σ' = Notif.updK σ q (.archObj ao')) ∧
          UR st th P L4 L3 L2 L1 SR r.2 a σ' ∧ L.ksb r.2 = L.ksb s ∧ KFoot σ σ' ∧ ArchShr σ σ' ∧
          WritesIn st s r.2 (PtWAll L4 L3 L2 L1) ⦄ := by
    intro h
    refine (WP.spec_ok _).2 ⟨σ, by rw [h]; exact Set.mem_singleton _, Or.inl rfl, ⟨hS, hSt, hSV, hR, hPt⟩, rfl,
      KFoot.refl _, ArchShr.refl σ, WritesIn.refl _ _⟩
  have hAM : vspace.ADDR_MASK = 4503599627366400#u64 := by unfold vspace.ADDR_MASK; rfl
  unfold vspace.unmap_page_unflushed
  simp only [layout.paddr, bind_ok]
  cases sz with
  | Small =>
    refine WP.spec_bind (lookup_pt_slot_rel s σ hPt hPP hr1 vaddr hv) ?_
    rintro r2 ⟨hsp, hsl, hse⟩
    cases r2 with
    | Err lf =>
      obtain ⟨n, rfl⟩ := hse _ rfl
      exact hskip (uU_s_noSlot hsp)
    | Ok x =>
      obtain ⟨q, hq, rfl⟩ := hsl _ rfl
      obtain ⟨f, hk, hf2⟩ := hPt.l1 q hq
      have hqa := hPP q (Or.inr (Or.inr (Or.inr hq)))
      have hj := vIdx_lt vaddr 12
      have hfe2 := hf2 _ hj
      have hg : Fl4Spec.getPte (Z := Unit) (peA q (vIdx vaddr 12)).bv σ =
          ({(f (Fl4Spec.ucast 9 (vIdx vaddr 12).bv), σ)}, False) := by
        rw [peA_bv _ _ hj (tbl_fit hqa)]; exact getPte_at hqa hk hj
      dsimp only
      rw [L.read_eq]
      apply ok_bind_spec
      apply ok_bind_spec
      rw [P_PRESENT_eq]
      apply ok_bind_spec
      unfold lift
      apply ok_bind_spec
      by_cases hp0 : (L.mem s (peA q (vIdx vaddr 12)) &&& 1#u64) = 0#u64
      · rw [if_pos hp0]
        refine hskip (uU_s_other hsp hg ?_)
        revert hfe2
        cases f (Fl4Spec.ucast 9 (vIdx vaddr 12).bv) with
        | invalidPTE => intro; rfl
        | smallPagePTE _ _ _ => intro h; exact absurd hp0 h.1
      rw [if_neg hp0]
      simp only [not_true_eq_false, ↓reduceIte, vspace.frame_base, frame_gpa_plain, bind_ok]
      rw [hAM]
      obtain ⟨fb, fa, fr, hfx⟩ : ∃ fb fa fr, f (Fl4Spec.ucast 9 (vIdx vaddr 12).bv) = .smallPagePTE fb fa fr := by
        revert hfe2
        cases f (Fl4Spec.ucast 9 (vIdx vaddr 12).bv) with
        | invalidPTE => intro h; exact absurd hp0 h
        | smallPagePTE a b c => intro; exact ⟨a, b, c, rfl⟩
      rw [hfx] at hfe2 hg
      have hfb : (eA (L.mem s (peA q (vIdx vaddr 12)))).bv = fb := hfe2.2.1
      by_cases hadr : ((L.mem s (peA q (vIdx vaddr 12)) &&& 4503599627366400#u64) !=
          core.num.U64.wrapping_sub pp layout.PPTR_BASE) = true
      · rw [if_pos hadr]
        refine hskip (uU_s_other hsp hg ?_)
        show decide (fb = Fl4Spec.addrFromPPtr pp.bv) = false
        rw [decide_eq_false_iff_not, ← hfb, ← paddr_bv]
        exact fun h => (bne_iff_ne.1 hadr) (eq_of_bv h)
      rw [if_neg hadr]
      have hadrE : eA (L.mem s (peA q (vIdx vaddr 12))) = core.num.U64.wrapping_sub pp layout.PPTR_BASE :=
        Classical.byContradiction fun hne => hadr (bne_iff_ne.2 hne)
      have hc : Fl4Spec.checkMappingPptr pp.bv (.vmPTE (.smallPagePTE fb fa fr)) = true := by
        show decide (fb = Fl4Spec.addrFromPPtr pp.bv) = true
        rw [decide_eq_true_iff, ← hfb, ← paddr_bv, hadrE]
      set σs := updK σ q.bv (.archObj (.pageTable (Function.update f (Fl4Spec.ucast 9 (vIdx vaddr 12).bv) .invalidPTE)))
        with hσs
      have hstore : Fl4Spec.storePte (Z := Unit) (peA q (vIdx vaddr 12)).bv .invalidPTE σ = ({((), σs)}, False) := by
        rw [peA_bv _ _ hj (tbl_fit hqa)]; exact storePte_at hqa hk hj _
      have hun := uU_s_match hsp hg hc hstore
      rw [L.write_eq]
      apply ok_bind_spec
      have hea : Aligned (peA q (vIdx vaddr 12)) := by
        show _ % 8 = 0; rw [peA_val (tbl_fit hqa) hj]; omega
      set s1 := L.wr s (peA q (vIdx vaddr 12)) 0#u64 with hs1
      have hPts : PtRel L4 L3 L2 L1 (L.mem s1) σs :=
        hPt.upd_l1 hPP hq hk hj 0#u64 .invalidPTE (by show ¬ (0#u64 &&& 1#u64) ≠ 0#u64; decide)
          (fun b hb hne => L.mem_wr_ne hea hb (fun h => hne (UScalar.eq_of_val_eq h).symm)) (L.mem_wr_same hea)
      have hW : WritesIn st s s1 (PtW L1) :=
        ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => L.mem_wr_ne hea hb
          (fun h => hn ⟨q, hq, _, hj, (UScalar.eq_of_val_eq h).symm⟩)⟩
      have hSs := hH.ptStable _ _ a _ σs hS hW ⟨q.bv, f, _, hk, rfl⟩
      have hWA : ∀ b, PtW L1 b → PtWAll L4 L3 L2 L1 b := by
        rintro b ⟨p, hp, i, hi, hb⟩; exact ⟨p, Or.inr (Or.inr (Or.inr hp)), i, hi, hb⟩
      have hcap := capAt_of_writes hPl hW (fun b hb => hPS b (hWA b hb))
      have hSts : StateRel th (L.mem s1) σs := Vs.StateRel.upd_other (StateRel.of_caps hSt hcap) hk _
      have hSVs : SlotsValid th (L.mem s1) := Vs.SlotsValid.of_caps hSV hcap
      have hRs : VsRel P (L.mem s1) (L.ksb s1) σs := by
        rw [hW.1]
        refine hR.frame (fun b hb => hW.2.2 b (hb.aligned hVP) (fun h => hPV b (hWA b h) hb)) rfl (fun p hp => ?_)
        obtain ⟨g, hg', -⟩ := hR.pool p hp
        have : p.bv ≠ q.bv := kheap_ne hg' hk (fun _ h1 h2 => by subst h1; cases h2)
        simp [hσs, updK, this]
      refine (WP.spec_ok _).2 ⟨σs, ?_, Or.inr ⟨q.bv, _, _, hk, by simp [Fl4Spec.aaType], by simp [Fl4Spec.aaType], rfl⟩, ⟨hSs, hSts, hSVs, ⟨hRs.1, hRs.2, hRs.3⟩,
        ⟨hPts.l4, hPts.l3, hPts.l2, hPts.l1⟩⟩, L.ksb_wr _ _ _, KFoot.arch hk _, ArchShr.upd_pt hk _, hW.mono hWA⟩
      · exact (congrArg (fun m => ((true, σs) ∈ m.1)) hun).mpr (Set.mem_singleton _)
  | Large =>
    refine WP.spec_bind (lookup_pd_slot_rel s σ hPt hPP hr1 vaddr hv) ?_
    rintro r2 ⟨hsp, hsl, hse⟩
    cases r2 with
    | Err lf =>
      obtain ⟨n, rfl⟩ := hse _ rfl
      exact hskip (uU_l_noSlot hsp)
    | Ok x =>
      obtain ⟨q, hq, rfl⟩ := hsl _ rfl
      obtain ⟨f, hk, hf2⟩ := hPt.l2 q hq
      have hqa := hPP q (Or.inr (Or.inr (Or.inl hq)))
      have hj := vIdx_lt vaddr 21
      have hfe2 := hf2 _ hj
      have hg : Fl4Spec.getPde (Z := Unit) (peA q (vIdx vaddr 21)).bv σ =
          ({(f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv), σ)}, False) := by
        rw [peA_bv _ _ hj (tbl_fit hqa)]; exact getPde_at hqa hk hj
      dsimp only
      rw [L.read_eq]
      apply ok_bind_spec
      apply ok_bind_spec
      rw [P_PRESENT_eq]
      apply ok_bind_spec
      unfold lift
      apply ok_bind_spec
      by_cases hp0 : (L.mem s (peA q (vIdx vaddr 21)) &&& 1#u64) = 0#u64
      · rw [if_pos hp0]
        refine hskip (uU_l_other hsp hg ?_)
        revert hfe2
        cases f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) with
        | invalidPDE => intro; rfl
        | pageTablePDE _ _ _ => intro h; exact absurd hp0 h.1
        | largePagePDE _ _ _ => intro h; exact absurd hp0 h.1
      rw [if_neg hp0]
      simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
      rw [P_PS_eq]
      apply ok_bind_spec
      apply ok_bind_spec
      by_cases hps : (L.mem s (peA q (vIdx vaddr 21)) &&& 128#u64) = 0#u64
      · rw [if_pos hps]
        refine hskip (uU_l_other hsp hg ?_)
        revert hfe2
        cases f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) with
        | invalidPDE => intro; rfl
        | pageTablePDE _ _ _ => intro; rfl
        | largePagePDE _ _ _ => intro h; exact absurd hps h.2.1
      rw [if_neg hps]
      simp only [vspace.frame_base, frame_gpa_plain, bind_ok]
      obtain ⟨fb, fa, fr, hfx⟩ : ∃ fb fa fr, f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) = .largePagePDE fb fa fr := by
        revert hfe2
        cases f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) with
        | invalidPDE => intro h; exact absurd hp0 h
        | pageTablePDE _ _ _ => intro h; exact absurd ((eS_iff _).1 (by simpa using hps)) h.2.1
        | largePagePDE a b c => intro; exact ⟨a, b, c, rfl⟩
      rw [hfx] at hfe2 hg
      have hfb : (lA (L.mem s (peA q (vIdx vaddr 21)))).bv = fb := hfe2.2.2.1
      by_cases hadr : ((L.mem s (peA q (vIdx vaddr 21)) &&& 4503599625273344#u64) !=
          core.num.U64.wrapping_sub pp layout.PPTR_BASE) = true
      · rw [if_pos hadr]
        refine hskip (uU_l_other hsp hg ?_)
        show decide (fb = Fl4Spec.addrFromPPtr pp.bv) = false
        rw [decide_eq_false_iff_not, ← hfb, ← paddr_bv]
        exact fun h => (bne_iff_ne.1 hadr) (eq_of_bv h)
      rw [if_neg hadr]
      have hadrE : lA (L.mem s (peA q (vIdx vaddr 21))) = core.num.U64.wrapping_sub pp layout.PPTR_BASE :=
        Classical.byContradiction fun hne => hadr (bne_iff_ne.2 hne)
      have hc : Fl4Spec.checkMappingPptr pp.bv (.vmPDE (.largePagePDE fb fa fr)) = true := by
        show decide (fb = Fl4Spec.addrFromPPtr pp.bv) = true
        rw [decide_eq_true_iff, ← hfb, ← paddr_bv, hadrE]
      set σs := updK σ q.bv (.archObj (.pageDirectory (Function.update f (Fl4Spec.ucast 9 (vIdx vaddr 21).bv) .invalidPDE)))
        with hσs
      have hstore : Fl4Spec.storePde (Z := Unit) (peA q (vIdx vaddr 21)).bv .invalidPDE σ = ({((), σs)}, False) := by
        rw [peA_bv _ _ hj (tbl_fit hqa)]; exact storePde_at hqa hk hj _
      have hun := uU_l_match hsp hg hc hstore
      rw [L.write_eq]
      apply ok_bind_spec
      have hea : Aligned (peA q (vIdx vaddr 21)) := by
        show _ % 8 = 0; rw [peA_val (tbl_fit hqa) hj]; omega
      set s1 := L.wr s (peA q (vIdx vaddr 21)) 0#u64 with hs1
      have hPts : PtRel L4 L3 L2 L1 (L.mem s1) σs :=
        hPt.upd_l2 hPP hq hk hj 0#u64 .invalidPDE (by show ¬ (0#u64 &&& 1#u64) ≠ 0#u64; decide)
          (fun b hb hne => L.mem_wr_ne hea hb (fun h => hne (UScalar.eq_of_val_eq h).symm)) (L.mem_wr_same hea)
      have hW : WritesIn st s s1 (PdW L2) :=
        ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => L.mem_wr_ne hea hb
          (fun h => hn ⟨q, hq, _, hj, (UScalar.eq_of_val_eq h).symm⟩)⟩
      have hSs := hH.pdStable _ _ a _ σs hS hW ⟨q.bv, f, _, hk, rfl⟩
      have hWA : ∀ b, PdW L2 b → PtWAll L4 L3 L2 L1 b := by
        rintro b ⟨p, hp, i, hi, hb⟩; exact ⟨p, Or.inr (Or.inr (Or.inl hp)), i, hi, hb⟩
      have hcap := capAt_of_writes hPl hW (fun b hb => hPS b (hWA b hb))
      have hSts : StateRel th (L.mem s1) σs := Vs.StateRel.upd_other (StateRel.of_caps hSt hcap) hk _
      have hSVs : SlotsValid th (L.mem s1) := Vs.SlotsValid.of_caps hSV hcap
      have hRs : VsRel P (L.mem s1) (L.ksb s1) σs := by
        rw [hW.1]
        refine hR.frame (fun b hb => hW.2.2 b (hb.aligned hVP) (fun h => hPV b (hWA b h) hb)) rfl (fun p hp => ?_)
        obtain ⟨g, hg', -⟩ := hR.pool p hp
        have : p.bv ≠ q.bv := kheap_ne hg' hk (fun _ h1 h2 => by subst h1; cases h2)
        simp [hσs, updK, this]
      refine (WP.spec_ok _).2 ⟨σs, ?_, Or.inr ⟨q.bv, _, _, hk, by simp [Fl4Spec.aaType], by simp [Fl4Spec.aaType], rfl⟩, ⟨hSs, hSts, hSVs, ⟨hRs.1, hRs.2, hRs.3⟩,
        ⟨hPts.l4, hPts.l3, hPts.l2, hPts.l1⟩⟩, L.ksb_wr _ _ _, KFoot.arch hk _, ArchShr.upd_pd hk _, hW.mono hWA⟩
      · exact (congrArg (fun m => ((true, σs) ∈ m.1)) hun).mpr (Set.mem_singleton _)
  | Huge =>
    refine WP.spec_bind (lookup_pdpt_slot_rel s σ hPt hPP hr1 vaddr hv) ?_
    rintro r2 ⟨hsp, hsl, hse⟩
    cases r2 with
    | Err lf =>
      obtain ⟨n, rfl⟩ := hse _ rfl
      exact hskip (uU_h_noSlot hsp)
    | Ok x =>
      obtain ⟨q, hq, rfl⟩ := hsl _ rfl
      obtain ⟨f, hk, hf2⟩ := hPt.l3 q hq
      have hqa := hPP q (Or.inr (Or.inl hq))
      have hj := vIdx_lt vaddr 30
      have hfe2 := hf2 _ hj
      have hg : Fl4Spec.getPdpte (Z := Unit) (peA q (vIdx vaddr 30)).bv σ =
          ({(f (Fl4Spec.ucast 9 (vIdx vaddr 30).bv), σ)}, False) := by
        rw [peA_bv _ _ hj (tbl_fit hqa)]; exact getPdpte_at hqa hk hj
      dsimp only
      rw [L.read_eq]
      apply ok_bind_spec
      apply ok_bind_spec
      rw [P_PRESENT_eq]
      apply ok_bind_spec
      unfold lift
      apply ok_bind_spec
      by_cases hp0 : (L.mem s (peA q (vIdx vaddr 30)) &&& 1#u64) = 0#u64
      · rw [if_pos hp0]
        refine hskip (uU_h_other hsp hg ?_)
        revert hfe2
        cases f (Fl4Spec.ucast 9 (vIdx vaddr 30).bv) with
        | invalidPDPTE => intro; rfl
        | pageDirectoryPDPTE _ _ _ => intro h; exact absurd hp0 h.1
        | hugePagePDPTE _ _ _ => intro h; exact absurd hp0 h.1
      rw [if_neg hp0]
      simp only [Bool.false_eq_true, not_false_eq_true, ↓reduceIte]
      rw [P_PS_eq]
      apply ok_bind_spec
      apply ok_bind_spec
      by_cases hps : (L.mem s (peA q (vIdx vaddr 30)) &&& 128#u64) = 0#u64
      · rw [if_pos hps]
        refine hskip (uU_h_other hsp hg ?_)
        revert hfe2
        cases f (Fl4Spec.ucast 9 (vIdx vaddr 30).bv) with
        | invalidPDPTE => intro; rfl
        | pageDirectoryPDPTE _ _ _ => intro; rfl
        | hugePagePDPTE _ _ _ => intro h; exact absurd hps h.2.1
      rw [if_neg hps]
      simp only [vspace.frame_base, frame_gpa_plain, bind_ok]
      obtain ⟨fb, fa, fr, hfx⟩ : ∃ fb fa fr, f (Fl4Spec.ucast 9 (vIdx vaddr 30).bv) = .hugePagePDPTE fb fa fr := by
        revert hfe2
        cases f (Fl4Spec.ucast 9 (vIdx vaddr 30).bv) with
        | invalidPDPTE => intro h; exact absurd hp0 h
        | pageDirectoryPDPTE _ _ _ => intro h; exact absurd ((eS_iff _).1 (by simpa using hps)) h.2.1
        | hugePagePDPTE a b c => intro; exact ⟨a, b, c, rfl⟩
      rw [hfx] at hfe2 hg
      have hfb : (hA (L.mem s (peA q (vIdx vaddr 30)))).bv = fb := hfe2.2.2.1
      by_cases hadr : ((L.mem s (peA q (vIdx vaddr 30)) &&& 4503598553628672#u64) !=
          core.num.U64.wrapping_sub pp layout.PPTR_BASE) = true
      · rw [if_pos hadr]
        refine hskip (uU_h_other hsp hg ?_)
        show decide (fb = Fl4Spec.addrFromPPtr pp.bv) = false
        rw [decide_eq_false_iff_not, ← hfb, ← paddr_bv]
        exact fun h => (bne_iff_ne.1 hadr) (eq_of_bv h)
      rw [if_neg hadr]
      have hadrE : hA (L.mem s (peA q (vIdx vaddr 30))) = core.num.U64.wrapping_sub pp layout.PPTR_BASE :=
        Classical.byContradiction fun hne => hadr (bne_iff_ne.2 hne)
      have hc : Fl4Spec.checkMappingPptr pp.bv (.vmPDPTE (.hugePagePDPTE fb fa fr)) = true := by
        show decide (fb = Fl4Spec.addrFromPPtr pp.bv) = true
        rw [decide_eq_true_iff, ← hfb, ← paddr_bv, hadrE]
      set σs := updK σ q.bv (.archObj (.pdPointerTable (Function.update f (Fl4Spec.ucast 9 (vIdx vaddr 30).bv) .invalidPDPTE)))
        with hσs
      have hstore : Fl4Spec.storePdpte (Z := Unit) (peA q (vIdx vaddr 30)).bv .invalidPDPTE σ = ({((), σs)}, False) := by
        rw [peA_bv _ _ hj (tbl_fit hqa)]; exact storePdpte_at hqa hk hj _
      have hun := uU_h_match hsp hg hc hstore
      rw [L.write_eq]
      apply ok_bind_spec
      have hea : Aligned (peA q (vIdx vaddr 30)) := by
        show _ % 8 = 0; rw [peA_val (tbl_fit hqa) hj]; omega
      set s1 := L.wr s (peA q (vIdx vaddr 30)) 0#u64 with hs1
      have hPts : PtRel L4 L3 L2 L1 (L.mem s1) σs :=
        hPt.upd_l3 hPP hq hk hj 0#u64 .invalidPDPTE (by show ¬ (0#u64 &&& 1#u64) ≠ 0#u64; decide)
          (fun b hb hne => L.mem_wr_ne hea hb (fun h => hne (UScalar.eq_of_val_eq h).symm)) (L.mem_wr_same hea)
      have hW : WritesIn st s s1 (PdptW L3) :=
        ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun b hb hn => L.mem_wr_ne hea hb
          (fun h => hn ⟨q, hq, _, hj, (UScalar.eq_of_val_eq h).symm⟩)⟩
      have hSs := hH.pdptStable _ _ a _ σs hS hW ⟨q.bv, f, _, hk, rfl⟩
      have hWA : ∀ b, PdptW L3 b → PtWAll L4 L3 L2 L1 b := by
        rintro b ⟨p, hp, i, hi, hb⟩; exact ⟨p, Or.inr (Or.inl hp), i, hi, hb⟩
      have hcap := capAt_of_writes hPl hW (fun b hb => hPS b (hWA b hb))
      have hSts : StateRel th (L.mem s1) σs := Vs.StateRel.upd_other (StateRel.of_caps hSt hcap) hk _
      have hSVs : SlotsValid th (L.mem s1) := Vs.SlotsValid.of_caps hSV hcap
      have hRs : VsRel P (L.mem s1) (L.ksb s1) σs := by
        rw [hW.1]
        refine hR.frame (fun b hb => hW.2.2 b (hb.aligned hVP) (fun h => hPV b (hWA b h) hb)) rfl (fun p hp => ?_)
        obtain ⟨g, hg', -⟩ := hR.pool p hp
        have : p.bv ≠ q.bv := kheap_ne hg' hk (fun _ h1 h2 => by subst h1; cases h2)
        simp [hσs, updK, this]
      refine (WP.spec_ok _).2 ⟨σs, ?_, Or.inr ⟨q.bv, _, _, hk, by simp [Fl4Spec.aaType], by simp [Fl4Spec.aaType], rfl⟩, ⟨hSs, hSts, hSVs, ⟨hRs.1, hRs.2, hRs.3⟩,
        ⟨hPts.l4, hPts.l3, hPts.l2, hPts.l1⟩⟩, L.ksb_wr _ _ _, KFoot.arch hk _, ArchShr.upd_pdpt hk _, hW.mono hWA⟩
      · exact (congrArg (fun m => ((true, σs) ∈ m.1)) hun).mpr (Set.mem_singleton _)



end

end

end Fl4Proofs.P3.Vs
