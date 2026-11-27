/-
P3 (issue #16, F1 stage 3; F1-PLAN §4, KENTRY-PLAN f2): **`VsNamed` across the
slot steps** (the CSpace class: frame steps, inserts, moves, swaps).

* `VsKeep th th' m m'`: the keyed caps (`VKey`: table, PML4 and pool caps) across
  a step: every keyed cap before has a slot after with its key and ref (`fwd`),
  every keyed cap after one before (`back`), and two distinct slots after with
  one key, the first unmapped, have distinct preimages (`inj`; l4v
  `unique_table_caps`: an unmapped cap is never duplicated).
* `VsNamed.step`: `VsKeep` with the walk words kept (`TblSame`, `SetWSame` at
  the pre-state's sets) keeps `VsNamed` (`VsSlotsW` and the relations at the
  pre-state). The frame class is `VsKeep.of_eq` (or VsNamed's `VsNamed.frame`).
* `VsKeep.of_pre`: a slot map `f` (each keyed slot after holds the cap of its
  `f`-preimage, every keyed slot before is hit, `f` separates an unmapped slot
  from the others); `vsKeep_insert` (`cdt::insert` of a derived cap: never an
  unmapped table cap, `derive_tabun`; a keyed copy is its source,
  `other => other` in `derive_cap` / `mask_cap_rights` / `update_cap_data`),
  `vsKeep_move`, `vsKeep_swap` (as CnodeVsW's `vsSlotsT_insert` / `move` /
  `swap`).
-/
import Fl4Proofs.P3.VsNamed
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

noncomputable section

section
variable {m m' : U64 → U64} {ksb : U64}

section St
variable {P L4 L3 L2 L1 : Set U64} {σ : Fl4Spec.State Unit}
  (hR : VsRel P m ksb σ) (hPt : PtRel L4 L3 L2 L1 m σ) (hPI : PoolsIn P L4 m)
  (hWt : TblSame ksb m m') (hWp : SetWSame P L4 L3 L2 L1 m m')
include hR hPt hPI hWt hWp

/-- **(F1 stage 3) `VsNamed` across a step keeping the walk words and the keyed
caps** (`VsKeep`). -/
theorem VsNamed.step {th th' : TypedHeap} (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hK : VsKeep th th' m m') : VsNamed th' m' ksb where
  named k q a v h := by
    obtain ⟨y, hy, hk, hr⟩ := hN.named k q a v (h.frame hR hPt hPI hWt hWp)
    obtain ⟨y', hy', e1, e2⟩ := hK.fwd y hy (by rw [hk]; simp)
    exact ⟨y', hy', by rw [e1]; exact hk, by rw [e2]; exact hr⟩
  uref y1 y2 hy1 hy2 hk hn := by
    obtain ⟨z1, hz1, a1, b1⟩ := hK.back y1 hy1 hn
    obtain ⟨z2, hz2, a2, b2⟩ := hK.back y2 hy2 (by rw [← hk]; exact hn)
    rw [← b1, ← b2]
    exact hN.uref z1 z2 hz1 hz2 (by rw [a1, a2, hk]) (by rw [a1]; exact hn)
  uun y1 y2 hy1 hy2 hk hu := by
    by_contra hne
    obtain ⟨z1, z2, hz1, hz2, hz, a1, b1, a2⟩ := hK.inj y1 y2 hy1 hy2 hne hk hu
    exact hz (hN.uun z1 z2 hz1 hz2 (by rw [a1, a2]) (TabUn.of_ref a1 b1 hu))
  empty y' hy' hu k q hk i hi := by
    obtain ⟨z, hz, a1, b1⟩ := hK.back y' hy' (tabUn_key hu)
    have hu' := TabUn.of_ref a1 b1 hu
    have hk' : VKey (capV m z) = some (k, q) := a1.trans hk
    have hq := lvl_mem (hS.need hz (vneed_of_un hu' hk'))
    rw [hWp _ hq _ (by split_ifs at hi <;> omega)]
    exact hN.empty z hz hu' k q hk' i hi
  poolT y' hy' q b hb hi hib := by
    have hk0 : VKey (capV m' y') = some (5, q) := by rw [hb]; rfl
    obtain ⟨z, hz, a1, b1⟩ := hK.back y' hy' (by rw [hk0]; simp)
    obtain ⟨b', hb'⟩ := pool_of_key (a1.trans hk0)
    rw [hb', hb] at b1
    simp only [VRefOf, Option.some.injEq, Prod.mk.injEq, true_and, and_true] at b1
    have hcw := hS z hz
    rw [hb'] at hcw
    simp only [VCapW, VCapOK] at hcw
    rw [hWt _ (by omega)]
    exact hN.poolT z hz q b' hb' hi (by omega)

/-- **(F1 stage 3, retypes) `VsNamed` across a step adding fresh unmapped
caps**: the old slots kept with their keyed caps, every keyed cap after old or
new, a new one unmapped, the only cap of its object, its table empty (a retype:
the new objects in the untyped's free part, apart from every old cap's object,
`UtInv.drange`, zeroed, a PML4's user half too). -/
theorem VsNamed.grow {th th' : TypedHeap} (hN : VsNamed th m ksb) (hS : VsSlotsW th P L4 L3 L2 L1 m)
    (hth : ∀ y, IsSlot th y → IsSlot th' y)
    (hold : ∀ y, IsSlot th y → VKey (capV m y) ≠ none → capV m' y = capV m y)
    (hnew : ∀ y, IsSlot th' y → VKey (capV m' y) ≠ none → (IsSlot th y ∧ capV m' y = capV m y) ∨
      (TabUn (capV m' y) ∧ (∀ z, IsSlot th' z → z ≠ y → VKey (capV m' z) ≠ VKey (capV m' y)) ∧
        ∀ k q, VKey (capV m' y) = some (k, q) → ∀ i : U64, i.val < (if k = 4 then 256 else 512) →
          ¬ eP (m' (peA q i)))) :
    VsNamed th' m' ksb where
  named k q a v h := by
    obtain ⟨y, hy, hk, hr⟩ := hN.named k q a v (h.frame hR hPt hPI hWt hWp)
    have hc := hold y hy (by rw [hk]; simp)
    exact ⟨y, hth y hy, by rw [hc]; exact hk, by rw [hc]; exact hr⟩
  uref y1 y2 hy1 hy2 hk hn := by
    rcases hnew y1 hy1 hn with ⟨o1, c1⟩ | ⟨-, f1, -⟩
    · rcases hnew y2 hy2 (by rw [← hk]; exact hn) with ⟨o2, c2⟩ | ⟨-, f2, -⟩
      · rw [c1, c2] at hk; rw [c1] at hn; rw [c1, c2]; exact hN.uref y1 y2 o1 o2 hk hn
      · by_cases e : y1 = y2
        · rw [e]
        · exact absurd hk (f2 y1 hy1 e)
    · by_cases e : y2 = y1
      · rw [e]
      · exact absurd hk.symm (f1 y2 hy2 e)
  uun y1 y2 hy1 hy2 hk hu := by
    have hn := tabUn_key hu
    rcases hnew y1 hy1 hn with ⟨o1, c1⟩ | ⟨-, f1, -⟩
    · rcases hnew y2 hy2 (by rw [← hk]; exact hn) with ⟨o2, c2⟩ | ⟨-, f2, -⟩
      · rw [c1, c2] at hk; rw [c1] at hu; exact hN.uun y1 y2 o1 o2 hk hu
      · by_contra e; exact f2 y1 hy1 e hk
    · by_contra e; exact f1 y2 hy2 (Ne.symm e) hk.symm
  empty y hy hu k q hk i hi := by
    rcases hnew y hy (tabUn_key hu) with ⟨o, c⟩ | ⟨-, -, he⟩
    · rw [c] at hu hk
      have hq := lvl_mem (hS.need o (vneed_of_un hu hk))
      rw [hWp _ hq _ (by split_ifs at hi <;> omega)]
      exact hN.empty y o hu k q hk i hi
    · exact he k q hk i hi
  poolT y hy q b hb hi hib := by
    have hk0 : VKey (capV m' y) = some (5, q) := by rw [hb]; rfl
    rcases hnew y hy (by rw [hk0]; simp) with ⟨o, c⟩ | ⟨hu, -, -⟩
    · rw [c] at hb
      have hcw := hS y o
      rw [hb] at hcw
      simp only [VCapW, VCapOK] at hcw
      rw [hWt _ (by omega)]
      exact hN.poolT y o q b hb hi hib
    · rw [hb] at hu; exact hu.elim

end St

/-- **(F1 stage 3, drops) Fewer slots**: a slot of `th'` is one of `th`, and
every keyed slot of `th` is one of `th'` (the drop's `restrictTh`: a non-null
slot is an MDB slot, off the region, `UtCapP3.ns`). -/
theorem VsNamed.sub {th th' : TypedHeap} (hN : VsNamed th m ksb) (hsub : ∀ y, IsSlot th' y → IsSlot th y)
    (hk : ∀ y, IsSlot th y → VKey (capV m y) ≠ none → IsSlot th' y) : VsNamed th' m ksb where
  named k q a v h := by
    obtain ⟨y, hy, hr⟩ := hN.named k q a v h
    exact ⟨y, hk y hy (by rw [hr.1]; simp), hr⟩
  uref y y' hy hy' := hN.uref y y' (hsub y hy) (hsub y' hy')
  uun y y' hy hy' := hN.uun y y' (hsub y hy) (hsub y' hy')
  empty y hy := hN.empty y (hsub y hy)
  poolT y hy := hN.poolT y (hsub y hy)

end

end



end Fl4Proofs.P3.Vs
