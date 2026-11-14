/-
P3 (DESIGN.md §9), CSpace: `delete(slot, true)` of an empty or trivially
finalised slot (`delete_refines`) **keeps `FinInv`** (`delete_refines_fin`).
-/
import Fl4Proofs.P3.Delete
import Fl4Proofs.P3.FinOps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem delete_refines_fin (th : TypedHeap) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hFI : FinInv th (L.mem s) σ G)
    {px : U64} {rx : Nat} (hpx : th px = some (.cnode rx)) {idx : List Bool} (hl : idx.length = rx)
    {c : capability.Cap} (hc : capAt (L.mem s) (cslotAddr (px.bv, idx)) = ok c)
    (ht : c = .Null ∨ ∃ fin, cdt.is_final_capability st s (cslotAddr (px.bv, idx)) = ok fin ∧ TrivKind σ c fin) :
    cdt.delete st arI s a (cslotAddr (px.bv, idx)) true ⦃ r => r.1 = .Ok () ∧
      ∃ σ' G', (Fl4Spec.capDelete (Z := Unit) (px.bv, idx)).run σ = ({(.ok (), σ')}, False) ∧
        StateRel th (L.mem r.2.1) σ' ∧ SlotsValid th (L.mem r.2.1) ∧ MdbLinks th (L.mem r.2.1) G' ∧
        CdtRel th (L.mem r.2.1) σ' G' ∧ MdbInv (L.mem r.2.1) G' ∧ FinInv th (L.mem r.2.1) σ' G' ∧
        MdbStep (L.mem s) G (L.mem r.2.1) G' ⦄ := by
  obtain ⟨c', a', hc', hca, hg⟩ := hR.slot_cap (Z := Unit) (sl := (px.bv, idx)) rfl (by rw [hl]; exact hpx)
  rw [hc] at hc'
  have : c' = c := by simpa using hc'.symm
  subst this
  rw [hca.abs] at hg
  unfold cdt.delete
  simp only [↓reduceIte]
  rw [finalise_imm_triv arI σ s a _ c' hc ht]
  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, uncurry_apply_pair]
  rcases ht with rfl | ⟨fin, hfin, htk⟩
  · rw [empty_slot_null arI s a _ hc]
    simp only [bind_ok, uncurry_apply_pair]
    rw [WP.spec_ok]
    have he : Fl4Spec.emptySlot (Z := Unit) (px.bv, idx) .nullCap σ = ({((), σ)}, False) := by
      unfold Fl4Spec.emptySlot
      rw [nd_bind_single hg]; simp [absCap]
    exact ⟨rfl, σ, G, capDelete_triv _ σ σ hg (Or.inl rfl) he, hR, hV, hM, hC, hI, hFI, MdbStep.refl hM⟩
  · have hcn : c' ≠ .Null := by intro e; subst e; simp [TrivKind] at htk
    obtain ⟨⟨s2, a2⟩, he2, ha2, σ', G', hes, hR', hV', hM', hC', hI', hFI', hSt⟩ :=
      spec_exists (empty_full_fin (ar := arI) th s a σ G hR hV hP hM hC hI hFI hpx hl hc hcn)
    simp only at ha2 hR' hV' hM' hC' hI' hFI' hSt
    rw [he2]
    simp only [bind_ok, uncurry_apply_pair]
    rw [WP.spec_ok]
    exact ⟨rfl, σ', G', capDelete_triv _ σ σ' hg (Or.inr ⟨c', fin, rfl, hcn, htk⟩) hes, hR', hV', hM', hC', hI',
      hFI', hSt⟩

end

end

end Fl4Proofs.P3
