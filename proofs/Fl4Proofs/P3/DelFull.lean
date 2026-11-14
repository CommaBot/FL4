/-
P3 (DESIGN.md §9), CSpace: **FL4's `delete(slot, true)` refines l4v's
`cap_delete`** (`rec_del (CTEDeleteCall slot True)`): `finalise_slot
_immediate`, then `empty_slot` with the cleanup cap, for any cap, with
zombies, given the hypotheses of `DelRound` (`FinalHyp`, `FinObjHyp`,
`PPHypD`, `PostDelHyp`) and a bound `K` on CNode sizes with
`(psiD + 1) * (K + 1) < 2 ^ 64` (the fuel then suffices).

When it succeeds, the measure `psiD` is strictly smaller. The number of
MDB slots need not be: deleting a zombie stored in its own CNode can move
it to the CNode's first slot and leave every other slot as it was.
-/
import Fl4Proofs.P3.DelImm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`delete(slot, true)` refines `cap_delete`.** -/
theorem delete_full (th : TypedHeap) (hP : Placed th) (hF : FinalHyp (L := L) th)
    (hO : FinObjHyp (L := L) arI th) (hPP : PPHypD (L := L) arI th) (hPD : PostDelHyp (L := L) arI th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK5 : 5 ≤ K)
    (sl : Fl4Spec.CslotPtr) (hA : AbsSlot th sl) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hDS : DState (L := L) th s σ G) (hxn : capV (L.mem s) (cslotAddr sl) ≠ .Null)
    (hbound : psiD (L.mem s) G * (K + 1) + K < 2 ^ 64 - 1) :
    cdt.delete st arI s a (cslotAddr sl) true ⦃ r => ∃ σ' G', DState (L := L) th r.2.1 σ' G' ∧
      psiD (L.mem r.2.1) G' ≤ psiD (L.mem s) G ∧ (nnS G').card ≤ (nnS G).card ∧
      ((r.1 = .Ok () ∧ (.ok (), σ') ∈ ((Fl4Spec.capDelete (Z := Unit) sl).run σ).1 ∧
          psiD (L.mem r.2.1) G' < psiD (L.mem s) G) ∨
        (r.1 = .Err .Preempted ∧ (.error (), σ') ∈ ((Fl4Spec.capDelete (Z := Unit) sl).run σ).1)) ⦄ := by
  unfold cdt.delete cdt.finalise_slot_immediate
  simp only [↓reduceIte]
  have hW : layout.WALK_FUEL.val = 2 ^ 64 - 1 := by simp [layout.WALK_FUEL, U64.rMax]
  have hnu := nuX_le hK hK5 hDS.2 hA.isSlot (K := K)
  apply WP.spec_bind (immediate_loop arI th hP hF hO hPP hPD K hK hK5 sl hA s σ G s a layout.WALK_FUEL
    ⟨σ, G, hDS, by simp only; rw [hW]; omega, le_refl _, le_refl _, fun h => absurd h hxn, fun _ h => h⟩
    (by rw [hW]))
  rintro ⟨r, s1, a1⟩ ⟨σ1, G1, hDS1, hcd1, hps1, hnul1, hres⟩
  simp only [uncurry_apply_pair] at hDS1 hcd1 hps1 hnul1 hres ⊢
  rcases hres with ⟨f, rfl, hcl, hclw, hrd⟩ | ⟨rfl, hrd⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply WP.spec_bind (empty_step arI th hP hPD s1 a1 σ1 G1 hDS1 hA f.cleanup hcl hclw)
    rintro ⟨s2, a2⟩ ⟨σ2, G2, hes, hDS2, hx2, hoth2, hps2, hcd2, hlt2⟩
    simp only [uncurry_apply_pair] at hes hDS2 hx2 hoth2 hps2 hcd2 hlt2 ⊢
    rw [WP.spec_ok]
    obtain ⟨v, hv⟩ := rd_cte_ok (σ2 := σ2) hrd (by simp only [true_or, Fl4Spec.NonDet.when, ↓reduceIte]; exact hes)
    refine ⟨σ2, G2, hDS2, le_trans hps2 hps1, le_trans hcd2 hcd1, Or.inl ⟨rfl, capDelete_ok hv, ?_⟩⟩
    by_cases hn : capV (L.mem s1) (cslotAddr sl) = .Null
    · exact lt_of_le_of_lt hps2 (hnul1 hn)
    · exact lt_of_lt_of_le (hlt2 hn).2 hps1
  · simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_ok, bind_tc_ok, WP.spec_ok]
    exact ⟨σ1, G1, hDS1, hps1, hcd1, Or.inr ⟨by trivial, capDelete_err (rd_cte_err hrd)⟩⟩

/-! ## `DelHyp` discharged -/

theorem psiD_links_eq {th : TypedHeap} {m : U64 → U64} {G1 G2 : MdbGhost} (h1 : MdbLinks th m G1)
    (h2 : MdbLinks th m G2) : psiD m G1 = psiD m G2 :=
  le_antisymm (psiD_le h2 h1 (fun _ _ h => h) (fun _ _ _ h => h)) (psiD_le h1 h2 (fun _ _ h => h) (fun _ _ _ h => h))

/-- The invariant `DelHyp` needs: `DelInv`, and the bound on `psiD` for the
fuel. -/
def DelE (th : TypedHeap) (K : Nat) (s : S) (_σ : Fl4Spec.State Unit) : Prop :=
  DelInv th (L.mem s) ∧ ∀ G, MdbLinks th (L.mem s) G → psiD (L.mem s) G * (K + 1) + K < 2 ^ 64 - 1

theorem psiD_slotsSame {th : TypedHeap} : ∀ m m' G, MdbLinks th m G → SlotsSame th m m' → psiD m' G = psiD m G :=
  fun _ _ _ hM hS => psiD_same hM (hM.of_same hS) hS

/-- **`DelHyp` holds** for the measure `psiD` and the invariant `DelE`,
from the hypotheses on finality, the object-specific finalisations, the
preemption points and `post_cap_deletion`. -/
theorem delHyp_full (th : TypedHeap) (hP : Placed th) (hF : FinalHyp (L := L) th)
    (hO : FinObjHyp (L := L) arI th) (hPP : PPHypD (L := L) arI th) (hPD : PostDelHyp (L := L) arI th)
    (K : Nat) (hK : ∀ p r, th p = some (.cnode r) → 2 ^ r ≤ K) (hK5 : 5 ≤ K) :
    DelHyp (L := L) arI psiD th (DelE (L := L) th K) := by
  intro s a σ G c hCR ⟨hD, hB⟩ hA hxm
  have hxn : capV (L.mem s) (cslotAddr c) ≠ .Null := ((mem_nnS hCR.2.2.1 _).1 (List.mem_toFinset.2 hxm)).2
  refine WP.spec_mono (delete_full arI th hP hF hO hPP hPD K hK hK5 c hA s a σ G ⟨hCR, hD⟩ hxn
    (hB G hCR.2.2.1)) ?_
  rintro r ⟨σ', G', ⟨hCR', hD'⟩, hps', -, hcase⟩
  refine ⟨σ', G', ?_, hCR', hD', fun G'' hM'' => ?_⟩
  · rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr ⟨h1, h2⟩
  · have := hB G hCR.2.2.1
    rw [psiD_links_eq hM'' hCR'.2.2.1]
    have := Nat.mul_le_mul_right (K + 1) hps'
    omega

/-- The preemption point keeps `DelE`. -/
theorem rppHyp_full (th : TypedHeap) (K : Nat) (hPP : PPHypD (L := L) arI th) :
    RPPHyp (L := L) arI th (DelE (L := L) th K) := by
  intro s a σ G hCR ⟨hD, hB⟩
  refine WP.spec_mono (hPP s a σ G ⟨hCR, hD⟩) ?_
  rintro r ⟨hS, σ', hcase, hCR'⟩
  refine ⟨hS, σ', hcase, hCR', hD.of_same hS, fun G'' hM'' => ?_⟩
  rw [psiD_links_eq hM'' (hCR.2.2.1.of_same hS), psiD_same hCR.2.2.1 (hCR.2.2.1.of_same hS) hS]
  exact hB G hCR.2.2.1

end

end

end Fl4Proofs.P3
