/-
P3 (DESIGN.md §9), Untyped: **`XTopAt` with fresh page tables added to the
VSpace sets** (`XTopAt.addTab`), for the retype of PDPTs, page directories
and page tables at `J` (UtEpRet's `JAtZ.utEpJ`): the weakened VSpace cap
field (`JAtZ.vsc`, VsCapW) asks an unmapped table cap's table in its set, and
a retype's new table caps are unmapped, so the retype grows `L3`, `L2` or
`L1` by the window's tables (UtEpXTop's `XTopAt.addE` for endpoints).

The sets enter `XTopAt` only through the VSpace part of `TopPlaced` (`pt`,
`disj`, `po`, `ps`, `pv`) and `PtRel`: a new table is 4 KiB-aligned, its
words are zero in FL4's memory and it is an empty table of its kind in the
spec (`PtRel`'s entries `invalid`), and its range holds no word of the other
objects (`OObj`), of the old VSpace objects (`VObj`) or of a typed-heap
object. The entry relations are monotone in the sets they name.
-/
import Fl4Proofs.P3.UtEpXTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs

noncomputable section

theorem Vs.not_eP_zero : ¬ eP 0#u64 := by simp [eP]

theorem Vs.PML4ERel.mono {L3 L3' : Set U64} (h3 : L3 ⊆ L3') {w : U64} {e : Fl4Spec.PML4E}
    (h : PML4ERel L3 w e) : PML4ERel L3' w e := by
  cases e with
  | invalidPML4E => exact h
  | pdPointerTablePML4E t a r => exact ⟨h.1, h.2.1, h3 h.2.2⟩

theorem Vs.PDPTERel.mono {L2 L2' : Set U64} (h2 : L2 ⊆ L2') {w : U64} {e : Fl4Spec.PDPTE}
    (h : PDPTERel L2 w e) : PDPTERel L2' w e := by
  cases e with
  | invalidPDPTE => exact h
  | pageDirectoryPDPTE t a r => exact ⟨h.1, h.2.1, h.2.2.1, h2 h.2.2.2⟩
  | hugePagePDPTE f a r => exact h

theorem Vs.PDERel.mono {L1 L1' : Set U64} (h1 : L1 ⊆ L1') {w : U64} {e : Fl4Spec.PDE}
    (h : PDERel L1 w e) : PDERel L1' w e := by
  cases e with
  | invalidPDE => exact h
  | pageTablePDE t a r => exact ⟨h.1, h.2.1, h.2.2.1, h1 h.2.2.2⟩
  | largePagePDE f a r => exact h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`XTopAt` with fresh tables added** (module docstring). -/
theorem XTopAt.addTab {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) {W3 W2 W1 : Set U64}
    (hk3 : ∀ q ∈ W3, σ.kheap q.bv = some (.archObj (.pdPointerTable fun _ => .invalidPDPTE)))
    (hk2 : ∀ q ∈ W2, σ.kheap q.bv = some (.archObj (.pageDirectory fun _ => .invalidPDE)))
    (hk1 : ∀ q ∈ W1, σ.kheap q.bv = some (.archObj (.pageTable fun _ => .invalidPTE)))
    (hal : ∀ q, (q ∈ W3 ∨ q ∈ W2 ∨ q ∈ W1) → q.val % 4096 = 0)
    (hz : ∀ q, (q ∈ W3 ∨ q ∈ W2 ∨ q ∈ W1) → ∀ i : U64, i.val < 512 → L.mem s (peA q i) = 0#u64)
    (hfr : ∀ q, (q ∈ W3 ∨ q ∈ W2 ∨ q ∈ W1) → ∀ b : U64, q.val ≤ b.val → b.val < q.val + 4096 →
      ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b ∧ ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b ∧
      ∀ p k, Z.th p = some k → ¬ (p.val ≤ b.val ∧ b.val < p.val + objSize k)) :
    XTopAt (L := L) AR { Z with L3 := Z.L3 ∪ W3, L2 := Z.L2 ∪ W2, L1 := Z.L1 ∪ W1 } s a σ := by
  obtain ⟨⟨⟨hO, hP⟩, hR, hPt, hPI, hCO⟩, hRel, hIpc, hE⟩ := hX
  have hPl := hP.pl
  -- a word of a new table
  have hin : ∀ q, (q ∈ W3 ∨ q ∈ W2 ∨ q ∈ W1) → ∀ i : U64, i.val < 512 →
      q.val ≤ (peA q i).val ∧ (peA q i).val < q.val + 4096 := by
    intro q hq i hi
    have hv := peA_val (tbl_fit (hal q hq)) hi
    omega
  -- the table words of the enlarged sets: an old one's, or a new table's
  have hW : ∀ b, PtWAll Z.L4 (Z.L3 ∪ W3) (Z.L2 ∪ W2) (Z.L1 ∪ W1) b →
      PtWAll Z.L4 Z.L3 Z.L2 Z.L1 b ∨ ∃ q, (q ∈ W3 ∨ q ∈ W2 ∨ q ∈ W1) ∧ ∃ i : U64, i.val < 512 ∧ b = peA q i := by
    rintro b ⟨q, hq, i, hi, rfl⟩
    rcases hq with hq | (hq | hq) | (hq | hq) | (hq | hq)
    · exact Or.inl ⟨q, Or.inl hq, i, hi, rfl⟩
    · exact Or.inl ⟨q, Or.inr (Or.inl hq), i, hi, rfl⟩
    · exact Or.inr ⟨q, Or.inl hq, i, hi, rfl⟩
    · exact Or.inl ⟨q, Or.inr (Or.inr (Or.inl hq)), i, hi, rfl⟩
    · exact Or.inr ⟨q, Or.inr (Or.inl hq), i, hi, rfl⟩
    · exact Or.inl ⟨q, Or.inr (Or.inr (Or.inr hq)), i, hi, rfl⟩
    · exact Or.inr ⟨q, Or.inr (Or.inr hq), i, hi, rfl⟩
  have hP' : TopPlaced st Z.th Z.P Z.L4 (Z.L3 ∪ W3) (Z.L2 ∪ W2) (Z.L1 ∪ W1) Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ := by
    refine ⟨hP.ep, hP.vs, ?_, hP.pl, ?_, hP.nodeE, ?_, ?_, ?_, hP.vo, hP.sd, hP.tko⟩
    · intro q hq
      rcases hq with hq | (hq | hq) | (hq | hq) | (hq | hq)
      · exact hP.pt q (Or.inl hq)
      · exact hP.pt q (Or.inr (Or.inl hq))
      · exact hal q (Or.inl hq)
      · exact hP.pt q (Or.inr (Or.inr (Or.inl hq)))
      · exact hal q (Or.inr (Or.inl hq))
      · exact hP.pt q (Or.inr (Or.inr (Or.inr hq)))
      · exact hal q (Or.inr (Or.inr hq))
    · intro b hb hv
      rcases hv with h | h | ⟨q, hq, h1, h2⟩ | h
      · exact hP.disj b hb (Or.inl h)
      · exact hP.disj b hb (Or.inr (Or.inl h))
      · rcases hq with hq | hq | (hq | hq) | (hq | hq) | (hq | hq)
        · exact hP.disj b hb (Or.inr (Or.inr (Or.inl ⟨q, Or.inl hq, h1, h2⟩)))
        · exact hP.disj b hb (Or.inr (Or.inr (Or.inl ⟨q, Or.inr (Or.inl hq), h1, h2⟩)))
        · exact hP.disj b hb (Or.inr (Or.inr (Or.inl ⟨q, Or.inr (Or.inr (Or.inl hq)), h1, h2⟩)))
        · exact (hfr q (Or.inl hq) b h1 h2).1 hb
        · exact hP.disj b hb (Or.inr (Or.inr (Or.inl ⟨q, Or.inr (Or.inr (Or.inr (Or.inl hq))), h1, h2⟩)))
        · exact (hfr q (Or.inr (Or.inl hq)) b h1 h2).1 hb
        · exact hP.disj b hb (Or.inr (Or.inr (Or.inl ⟨q, Or.inr (Or.inr (Or.inr (Or.inr hq))), h1, h2⟩)))
        · exact (hfr q (Or.inr (Or.inr hq)) b h1 h2).1 hb
      · exact hP.disj b hb (Or.inr (Or.inr (Or.inr h)))
    · intro b hb
      rcases hW b hb with h | ⟨q, hq, i, hi, rfl⟩
      · exact hP.po b h
      · have hv := peA_val (tbl_fit (hal q hq)) hi
        obtain ⟨g1, g2⟩ := hin q hq i hi
        refine ⟨?_, fun p k hp hpk => (hfr q hq _ g1 g2).2.2 p k hp hpk⟩
        unfold P1.Aligned; rw [hv]; have := hal q hq; omega
    · intro b hb
      rcases hW b hb with h | ⟨q, hq, i, hi, rfl⟩
      · exact hP.ps b h
      · intro hs
        obtain ⟨g1, g2⟩ := hin q hq i hi
        exact (hfr q hq _ g1 g2).2.1 (slotW_vobj hPl hs (L.ksb s))
    · intro b hb
      rcases hW b hb with h | ⟨q, hq, i, hi, rfl⟩
      · exact hP.pv b h
      · intro hs
        obtain ⟨g1, g2⟩ := hin q hq i hi
        exact (hfr q hq _ g1 g2).2.1 (vsWrite_vobj hP.vs hs)
  have hPt' : PtRel Z.L4 (Z.L3 ∪ W3) (Z.L2 ∪ W2) (Z.L1 ∪ W1) (L.mem s) σ := by
    refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
    · obtain ⟨f, hf, he⟩ := hPt.l4 q hq
      exact ⟨f, hf, fun i hi => (he i hi).mono Set.subset_union_left⟩
    · rcases hq with hq | hq
      · obtain ⟨f, hf, he⟩ := hPt.l3 q hq
        exact ⟨f, hf, fun i hi => (he i hi).mono Set.subset_union_left⟩
      · refine ⟨_, hk3 q hq, fun i hi => ?_⟩
        show ¬ eP _
        rw [hz q (Or.inl hq) i hi]; exact not_eP_zero
    · rcases hq with hq | hq
      · obtain ⟨f, hf, he⟩ := hPt.l2 q hq
        exact ⟨f, hf, fun i hi => (he i hi).mono Set.subset_union_left⟩
      · refine ⟨_, hk2 q hq, fun i hi => ?_⟩
        show ¬ eP _
        rw [hz q (Or.inr (Or.inl hq)) i hi]; exact not_eP_zero
    · rcases hq with hq | hq
      · exact hPt.l1 q hq
      · refine ⟨_, hk1 q hq, fun i hi => ?_⟩
        show ¬ eP _
        rw [hz q (Or.inr (Or.inr hq)) i hi]; exact not_eP_zero
  exact ⟨⟨⟨hO, hP'⟩, hR, hPt', hPI, hCO⟩, hRel, hIpc, hE⟩

/-- **`XTopAt` with fresh PML4s added to `L4`** (as `XTopAt.addTab`): a new
PML4's user half (entries below 256, the only ones `PtRel` relates) is zero in
FL4's memory and empty in the spec; its kernel half (the copied global
mappings) is related by nothing. -/
theorem XTopAt.addPml4 {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) {W4 : Set U64}
    (hk4 : ∀ q ∈ W4, ∃ f, σ.kheap q.bv = some (.archObj (.pageMapL4 f)) ∧
      ∀ i : U64, i.val < 256 → f (Fl4Spec.ucast 9 i.bv) = .invalidPML4E)
    (hal : ∀ q ∈ W4, q.val % 4096 = 0)
    (hz : ∀ q ∈ W4, ∀ i : U64, i.val < 256 → L.mem s (peA q i) = 0#u64)
    (hfr : ∀ q ∈ W4, ∀ b : U64, q.val ≤ b.val → b.val < q.val + 4096 →
      ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b ∧ ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b ∧
      ∀ p k, Z.th p = some k → ¬ (p.val ≤ b.val ∧ b.val < p.val + objSize k)) :
    XTopAt (L := L) AR { Z with L4 := Z.L4 ∪ W4 } s a σ := by
  obtain ⟨⟨⟨hO, hP⟩, hR, hPt, hPI, hCO⟩, hRel, hIpc, hE⟩ := hX
  have hPl := hP.pl
  have hin : ∀ q ∈ W4, ∀ i : U64, i.val < 512 → q.val ≤ (peA q i).val ∧ (peA q i).val < q.val + 4096 := by
    intro q hq i hi
    have hv := peA_val (tbl_fit (hal q hq)) hi
    omega
  have hW : ∀ b, PtWAll (Z.L4 ∪ W4) Z.L3 Z.L2 Z.L1 b →
      PtWAll Z.L4 Z.L3 Z.L2 Z.L1 b ∨ ∃ q ∈ W4, ∃ i : U64, i.val < 512 ∧ b = peA q i := by
    rintro b ⟨q, hq, i, hi, rfl⟩
    rcases hq with (hq | hq) | hq
    · exact Or.inl ⟨q, Or.inl hq, i, hi, rfl⟩
    · exact Or.inr ⟨q, hq, i, hi, rfl⟩
    · exact Or.inl ⟨q, Or.inr hq, i, hi, rfl⟩
  have hP' : TopPlaced st Z.th Z.P (Z.L4 ∪ W4) Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ := by
    refine ⟨hP.ep, hP.vs, ?_, hP.pl, ?_, hP.nodeE, ?_, ?_, ?_, hP.vo, hP.sd, hP.tko⟩
    · intro q hq
      rcases hq with (hq | hq) | hq
      · exact hP.pt q (Or.inl hq)
      · exact hal q hq
      · exact hP.pt q (Or.inr hq)
    · intro b hb hv
      rcases hv with h | h | ⟨q, hq, h1, h2⟩ | h
      · exact hP.disj b hb (Or.inl h)
      · exact hP.disj b hb (Or.inr (Or.inl h))
      · rcases hq with hq | (hq | hq) | hq
        · exact hP.disj b hb (Or.inr (Or.inr (Or.inl ⟨q, Or.inl hq, h1, h2⟩)))
        · exact hP.disj b hb (Or.inr (Or.inr (Or.inl ⟨q, Or.inr (Or.inl hq), h1, h2⟩)))
        · exact (hfr q hq b h1 h2).1 hb
        · exact hP.disj b hb (Or.inr (Or.inr (Or.inl ⟨q, Or.inr (Or.inr hq), h1, h2⟩)))
      · exact hP.disj b hb (Or.inr (Or.inr (Or.inr h)))
    · intro b hb
      rcases hW b hb with h | ⟨q, hq, i, hi, rfl⟩
      · exact hP.po b h
      · have hv := peA_val (tbl_fit (hal q hq)) hi
        obtain ⟨g1, g2⟩ := hin q hq i hi
        refine ⟨?_, fun p k hp hpk => (hfr q hq _ g1 g2).2.2 p k hp hpk⟩
        unfold P1.Aligned; rw [hv]; have := hal q hq; omega
    · intro b hb
      rcases hW b hb with h | ⟨q, hq, i, hi, rfl⟩
      · exact hP.ps b h
      · intro hs
        obtain ⟨g1, g2⟩ := hin q hq i hi
        exact (hfr q hq _ g1 g2).2.1 (slotW_vobj hPl hs (L.ksb s))
    · intro b hb
      rcases hW b hb with h | ⟨q, hq, i, hi, rfl⟩
      · exact hP.pv b h
      · intro hs
        obtain ⟨g1, g2⟩ := hin q hq i hi
        exact (hfr q hq _ g1 g2).2.1 (vsWrite_vobj hP.vs hs)
  have hPt' : PtRel (Z.L4 ∪ W4) Z.L3 Z.L2 Z.L1 (L.mem s) σ := by
    refine ⟨fun q hq => ?_, hPt.l3, hPt.l2, hPt.l1⟩
    rcases hq with hq | hq
    · exact hPt.l4 q hq
    · obtain ⟨f, hf, he⟩ := hk4 q hq
      refine ⟨f, hf, fun i hi => ?_⟩
      rw [he i hi]
      show ¬ eP _
      rw [hz q hq i hi]; exact not_eP_zero
  exact ⟨⟨⟨hO, hP'⟩, hR, hPt', fun p hp lo hl h1 h2 => Set.mem_union_left _ (hPI p hp lo hl h1 h2), hCO⟩, hRel, hIpc, hE⟩

end

end

end Fl4Proofs.P3
