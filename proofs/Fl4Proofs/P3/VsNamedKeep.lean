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

/-! ## Cap facts -/

theorem tabUn_key {c : capability.Cap} (h : TabUn c) : VKey c ≠ none := by
  cases c <;> simp_all [TabUn, VKey]

theorem tabUn_iff {c : capability.Cap} : TabUn c ↔ VKey c ≠ none ∧ ∃ a v, VRefOf c = some (false, a, v) := by
  cases c <;> simp [TabUn, VKey, VRefOf]

/-- Unmapped is read off the key and the ref. -/
theorem TabUn.of_ref {c c' : capability.Cap} (hk : VKey c' = VKey c) (hr : VRefOf c' = VRefOf c) (h : TabUn c) :
    TabUn c' := by
  rw [tabUn_iff] at h ⊢; rw [hk, hr]; exact h

theorem pool_of_key {c : capability.Cap} {q : U64} (h : VKey c = some (5, q)) : ∃ b, c = .AsidPool q b := by
  cases c <;> simp [VKey] at h
  subst h; exact ⟨_, rfl⟩

/-- `fullF`'s cap and source are untyped caps. -/
theorem fullF_key_none {c0 c u : capability.Cap} (h : fullF c0 c = some u) : VKey u = none ∧ VKey c0 = none := by
  unfold fullF at h
  split at h
  · split_ifs at h; cases h; exact ⟨rfl, rfl⟩
  · cases h

/-- The swap of two slots is injective. -/
theorem swapF_inj {a b x y : U64} (hab : a ≠ b)
    (h : (if x = a then b else if x = b then a else x) = (if y = a then b else if y = b then a else y)) : x = y := by
  split_ifs at h <;> subst_vars <;> first | rfl | contradiction

/-! ## The vehicle -/

/-- (F1 stage 3) **The keyed caps across a step** (module docstring). -/
structure VsKeep (th th' : TypedHeap) (m m' : U64 → U64) : Prop where
  fwd : ∀ y, IsSlot th y → VKey (capV m y) ≠ none → ∃ y', IsSlot th' y' ∧
    VKey (capV m' y') = VKey (capV m y) ∧ VRefOf (capV m' y') = VRefOf (capV m y)
  back : ∀ y', IsSlot th' y' → VKey (capV m' y') ≠ none → ∃ y, IsSlot th y ∧
    VKey (capV m y) = VKey (capV m' y') ∧ VRefOf (capV m y) = VRefOf (capV m' y')
  inj : ∀ y1 y2, IsSlot th' y1 → IsSlot th' y2 → y1 ≠ y2 → VKey (capV m' y1) = VKey (capV m' y2) →
    TabUn (capV m' y1) → ∃ z1 z2, IsSlot th z1 ∧ IsSlot th z2 ∧ z1 ≠ z2 ∧
      VKey (capV m z1) = VKey (capV m' y1) ∧ VRefOf (capV m z1) = VRefOf (capV m' y1) ∧
      VKey (capV m z2) = VKey (capV m' y1)

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

/-- The slots' caps kept. -/
theorem VsKeep.of_eq {th : TypedHeap} (hc : ∀ y, IsSlot th y → capV m' y = capV m y) : VsKeep th th m m' where
  fwd y hy _ := ⟨y, hy, by rw [hc y hy], by rw [hc y hy]⟩
  back y hy _ := ⟨y, hy, by rw [hc y hy], by rw [hc y hy]⟩
  inj y1 y2 hy1 hy2 hne hk _ := ⟨y1, y2, hy1, hy2, hne, by rw [hc y1 hy1], by rw [hc y1 hy1],
    by rw [← hc y2 hy2]; exact hk.symm⟩

/-- **A slot map**: each keyed slot after holds its `f`-preimage's cap, every
keyed slot before is an image, and `f` separates an unmapped slot after from
the other slots of its key. -/
theorem VsKeep.of_pre {th : TypedHeap} (f : U64 → U64) (hf : ∀ y', IsSlot th y' → IsSlot th (f y'))
    (hcap : ∀ y', IsSlot th y' → (VKey (capV m' y') ≠ none ∨ VKey (capV m (f y')) ≠ none) →
      capV m' y' = capV m (f y'))
    (hsurj : ∀ y, IsSlot th y → VKey (capV m y) ≠ none → ∃ y', IsSlot th y' ∧ f y' = y)
    (hinj : ∀ y1 y2, IsSlot th y1 → IsSlot th y2 → y1 ≠ y2 → TabUn (capV m' y1) →
      VKey (capV m' y1) = VKey (capV m' y2) → f y1 ≠ f y2) :
    VsKeep th th m m' where
  fwd y hy hk := by
    obtain ⟨y', hy', e⟩ := hsurj y hy hk
    have hc := hcap y' hy' (.inr (by rw [e]; exact hk))
    exact ⟨y', hy', by rw [hc, e], by rw [hc, e]⟩
  back y' hy' hk := by
    have hc := hcap y' hy' (.inl hk)
    exact ⟨f y', hf y' hy', by rw [hc], by rw [hc]⟩
  inj y1 y2 hy1 hy2 hne hk hu := by
    have k1 : VKey (capV m' y1) ≠ none := tabUn_key hu
    have hc1 := hcap y1 hy1 (.inl k1)
    have hc2 := hcap y2 hy2 (.inl (by rw [← hk]; exact k1))
    exact ⟨f y1, f y2, hf y1 hy1, hf y2 hy2, hinj y1 y2 hy1 hy2 hne hu hk, by rw [hc1], by rw [hc1],
      by rw [← hc2, hk]⟩

/-- **An insert** (`cdt::insert`): the destination, empty before, gets `c`, a
copy of the source when either is keyed, never an unmapped table cap; the
source set full if untyped (`fullF`). -/
theorem vsKeep_insert {th : TypedHeap} {src dest : U64} (hs : IsSlot th src) {c : capability.Cap}
    (hc : ∀ y, IsSlot th y → y ≠ src → y ≠ dest → capV m' y = capV m y) (hd : capV m' dest = c)
    (hsC : capV m' src = (fullF (capV m src) c).getD (capV m src)) (hd0 : VKey (capV m dest) = none)
    (hr : VKey c ≠ none ∨ VKey (capV m src) ≠ none → c = capV m src) (hu : ¬ TabUn c) :
    VsKeep th th m m' := by
  have hsK : VKey (capV m' src) ≠ none ∨ VKey (capV m src) ≠ none → capV m' src = capV m src := by
    intro h
    rw [hsC] at h ⊢
    cases hf : fullF (capV m src) c with
    | none => rfl
    | some u =>
      rw [hf, Option.getD_some] at h
      obtain ⟨h1, h2⟩ := fullF_key_none hf
      rcases h with h | h
      · exact absurd h1 h
      · exact absurd h2 h
  refine VsKeep.of_pre (fun y => if y = dest then src else y) (fun y hy => ?_) (fun y hy h => ?_)
    (fun y hy hk => ?_) (fun y1 y2 hy1 hy2 hne hu1 hk => ?_)
  · split_ifs
    · exact hs
    · exact hy
  · by_cases e : y = dest
    · rw [if_pos e] at h ⊢; rw [e, hd] at h ⊢; exact hr h
    · rw [if_neg e] at h ⊢
      by_cases e2 : y = src
      · rw [e2] at h ⊢; exact hsK h
      · exact hc y hy e2 e
  · have hyd : y ≠ dest := by rintro rfl; exact hk hd0
    exact ⟨y, hy, by simp only [if_neg hyd]⟩
  · have h1d : y1 ≠ dest := by rintro rfl; rw [hd] at hu1; exact hu hu1
    rw [if_neg h1d]
    by_cases e : y2 = dest
    · rw [if_pos e]
      rintro rfl
      have hk1 : VKey (capV m' y1) ≠ none := tabUn_key hu1
      have hs1 := hsK (.inl hk1)
      have hcs := hr (.inr (by rw [← hs1]; exact hk1))
      rw [hs1, ← hcs] at hu1
      exact hu hu1
    · rw [if_neg e]; exact hne

/-- **A move** (`cte_move`): the destination, empty before, gets `c`, the
source's cap when either is keyed; the source emptied. -/
theorem vsKeep_move {th : TypedHeap} {src dest : U64} (hs : IsSlot th src) (hdS : IsSlot th dest)
    (hne : src ≠ dest) {c : capability.Cap}
    (hc : ∀ y, IsSlot th y → y ≠ src → y ≠ dest → capV m' y = capV m y) (hd : capV m' dest = c)
    (hsC : capV m' src = .Null) (hd0 : VKey (capV m dest) = none)
    (hr : VKey c ≠ none ∨ VKey (capV m src) ≠ none → c = capV m src) : VsKeep th th m m' := by
  refine VsKeep.of_pre (fun y => if y = dest then src else if y = src then dest else y) (fun y hy => ?_)
    (fun y hy h => ?_) (fun y hy hk => ?_) (fun y1 y2 _ _ hne' _ _ heq => hne' (swapF_inj hne.symm heq))
  · split_ifs
    · exact hs
    · exact hdS
    · exact hy
  · by_cases e : y = dest
    · rw [if_pos e] at h ⊢; rw [e, hd] at h ⊢; exact hr h
    · rw [if_neg e] at h ⊢
      by_cases e2 : y = src
      · rw [if_pos e2] at h; rw [e2, hsC] at h
        exfalso; rcases h with h | h
        · exact h rfl
        · exact h hd0
      · rw [if_neg e2]; exact hc y hy e2 e
  · by_cases e : y = src
    · exact ⟨dest, hdS, by simp [e]⟩
    · have hyd : y ≠ dest := by rintro rfl; exact hk hd0
      exact ⟨y, hy, by simp only [if_neg hyd, if_neg e]⟩

/-- **A swap** (`cte_swap`): `s2` gets `c1`, `s1` gets `c2`, each its source's
cap when either is keyed. -/
theorem vsKeep_swap {th : TypedHeap} {s1 s2 : U64} (hs1 : IsSlot th s1) (hs2 : IsSlot th s2) (hne : s1 ≠ s2)
    {c1 c2 : capability.Cap} (hc : ∀ y, IsSlot th y → y ≠ s1 → y ≠ s2 → capV m' y = capV m y)
    (hd2 : capV m' s2 = c1) (hd1 : capV m' s1 = c2)
    (hr1 : VKey c1 ≠ none ∨ VKey (capV m s1) ≠ none → c1 = capV m s1)
    (hr2 : VKey c2 ≠ none ∨ VKey (capV m s2) ≠ none → c2 = capV m s2) : VsKeep th th m m' := by
  refine VsKeep.of_pre (fun y => if y = s1 then s2 else if y = s2 then s1 else y) (fun y hy => ?_)
    (fun y hy h => ?_) (fun y hy _ => ?_) (fun y1 y2 _ _ hne' _ _ heq => hne' (swapF_inj hne heq))
  · split_ifs
    · exact hs2
    · exact hs1
    · exact hy
  · by_cases e : y = s1
    · rw [if_pos e] at h ⊢; rw [e, hd1] at h ⊢; exact hr2 h
    · rw [if_neg e] at h ⊢
      by_cases e2 : y = s2
      · rw [if_pos e2] at h ⊢; rw [e2, hd2] at h ⊢; exact hr1 h
      · rw [if_neg e2]; exact hc y hy e e2
  · by_cases e : y = s1
    · exact ⟨s2, hs2, by simp [e, Ne.symm hne]⟩
    · by_cases e2 : y = s2
      · exact ⟨s1, hs1, by simp [e2]⟩
      · exact ⟨y, hy, by simp only [if_neg e, if_neg e2]⟩

end

end


/-! ## Copies of keyed caps are their sources (`other => other`) -/

section Copy
variable {S : Type} {st : machine.Store S}

/-- Either of two caps keyed. -/
abbrev Keyed2 (a b : capability.Cap) : Prop := VKey a ≠ none ∨ VKey b ≠ none

theorem keyChain {a b c : capability.Cap} (e1 : Keyed2 a b → a = b) (e2 : Keyed2 b c → b = c)
    (hk : Keyed2 a c) : a = c := by
  rcases hk with hk | hk
  · have h1 := e1 (.inl hk); rw [h1] at hk; rw [h1]; exact e2 (.inl hk)
  · have h2 := e2 (.inr hk); rw [← h2] at hk; rw [← h2]; exact e1 (.inr hk)

theorem vkey_mask {r : capability.Rights} {c c' : capability.Cap} (h : capability.mask_cap_rights r c = ok c')
    (hk : Keyed2 c' c) : c' = c := by
  cases c <;> simp only [capability.mask_cap_rights] at h
  case Frame p sz v dev m ept a va =>
    unfold capability.mask_vm_rights at h
    repeat' split at h
    all_goals (simp at h; subst h; first | rfl | simp [Keyed2, VKey] at hk)
  all_goals (repeat' split at h) <;> (simp at h; subst h; first | rfl | simp [Keyed2, VKey] at hk)

theorem vkey_update {pr : Bool} {d : U64} {c c' : capability.Cap} (h : objects.update_cap_data pr d c = ok c')
    (hk : Keyed2 c' c) : c' = c := by
  cases c <;> simp only [objects.update_cap_data] at h
  case CNode p r gs g =>
    simp only [lift, bind_ok] at h
    split at h
    · simp at h; subst h; first | rfl | simp [Keyed2, VKey] at hk
    · revert h; generalize d >>> 6#i32 = x; cases x <;> simp
      generalize objects.mask (d &&& 63#u64) = y; cases y <;> simp
      intro h; subst h; simp [Keyed2, VKey] at hk
  all_goals (repeat' split at h) <;> (simp at h; subst h; first | rfl | simp [Keyed2, VKey] at hk)

theorem vkey_derive {s : S} {slot : obj.Slot} {c c' : capability.Cap}
    (h : objects.derive_cap st s slot c = ok (.Ok c')) (hk : Keyed2 c' c) : c' = c := by
  cases c
  case Untyped p sb fi dev =>
    unfold objects.derive_cap at h
    revert h; generalize cdt.ensure_no_children st s slot = r
    cases r with
    | ret v =>
      cases v <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      intro h; subst h; rfl
    | _ => simp
  case Frame p sz r dv m ept a va =>
    simp only [objects.derive_cap] at h; simp at h; subst h; simp [Keyed2, VKey] at hk
  all_goals simp only [objects.derive_cap] at h
  all_goals (repeat' split at h) <;> (simp at h; try subst h) <;> first | rfl | simp_all [Keyed2, VKey]

/-- **A keyed cap `copied_cap` produces is its source** (Copy / Mint: mask,
update and derive keep a VSpace cap; Move: the source; Mutate: update). -/
theorem vkey_copied {s : S} {lbl length buf src : U64} {srcC nc : capability.Cap} {mv : Bool}
    (h : cnode.copied_cap st s lbl length buf src srcC = ok (.Ok (nc, mv))) (hk : Keyed2 nc srcC) :
    nc = srcC := by
  unfold cnode.copied_cap at h
  obtain ⟨ct, -, h⟩ := bind_ok_inv h
  split at h
  · split at h
    · simp [error.truncated] at h
    obtain ⟨i, -, h⟩ := bind_ok_inv h
    obtain ⟨r, -, h⟩ := bind_ok_inv h
    obtain ⟨c1, hc1, h⟩ := bind_ok_inv h
    obtain ⟨r1, hr1, h⟩ := bind_ok_inv h
    cases r1 with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from] at h
    | Ok v =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at h
      obtain ⟨rfl, rfl⟩ := h
      exact keyChain (vkey_derive hr1) (vkey_mask hc1) hk
  · split at h
    · split at h
      · simp [error.truncated] at h
      obtain ⟨i, -, h⟩ := bind_ok_inv h
      obtain ⟨r, -, h⟩ := bind_ok_inv h
      obtain ⟨d, -, h⟩ := bind_ok_inv h
      obtain ⟨c1, hc1, h⟩ := bind_ok_inv h
      obtain ⟨c2, hc2, h⟩ := bind_ok_inv h
      obtain ⟨r1, hr1, h⟩ := bind_ok_inv h
      cases r1 with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from] at h
      | Ok v =>
        simp [core.result.Result.Insts.CoreOpsTry.branch] at h
        obtain ⟨rfl, rfl⟩ := h
        exact keyChain (vkey_derive hr1) (fun h2 => keyChain (vkey_update hc2) (vkey_mask hc1) h2) hk
    · split at h
      · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
      · split at h
        · simp [error.truncated] at h
        obtain ⟨d, -, h⟩ := bind_ok_inv h
        obtain ⟨c1, hc1, h⟩ := bind_ok_inv h
        simp at h; obtain ⟨rfl, rfl⟩ := h
        exact vkey_update hc1 hk

end Copy

/-! ## The drop at `JAtZ` -/

section
open Fl4Proofs.P3.Sched
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **(F1 stage 3) `VsNamed` at the drop's typed heap** (`JAtZ.drop`'s
`restrictTh`, same memory): the MDB's slots miss the region (`UtCapP3.ns`). -/
theorem _root_.Fl4Proofs.P3.JAtZ.vsNamedDrop (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hN : VsNamed Z.th (L.mem s) (L.ksb s)) {lo hi : Nat} (hNS : NoStraddle Z.th lo hi)
    (hns : ∀ a ∈ Z.G.chains.flatten, a.val < lo ∨ hi ≤ a.val) :
    VsNamed (restrictTh Z.th lo hi) (L.mem s) (L.ksb s) := by
  obtain ⟨hPl, ⟨-, -, hML, -, -⟩, -⟩ := J.xtop.rel
  refine hN.sub (fun y hy => hy.of_restrict) fun y hy hk => ?_
  have hne : capV (L.mem s) y ≠ .Null := fun h => hk (by rw [h]; rfl)
  have hyG : y ∈ Z.G.chains.flatten := (hML.members y).2 ⟨hy, _, capAt_capV _ _, hne⟩
  exact hy.restrict hPl hNS (hns y hyG)

/-- **(F1 stage 3, frame class) `VsNamed` across the caller's restart**
(`set_thread_state Restart`: the slots and the `VObj` words kept,
`restart_top`), the frame `JAtZ.restartJ` makes. -/
theorem _root_.Fl4Proofs.P3.JAtZ.vsNamedRestart (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hN : VsNamed Z.th (L.mem s) (L.ksb s)) (hni : Entered σ) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) :
    ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 → VsNamed Z.th (L.mem s1) (L.ksb s1) := by
  intro s1 hs1
  obtain ⟨hcur, x0, hk, hrun⟩ := J.curRunnable hni hct
  have hF := J.xtop.fin
  have h := restart_top s a σ ct x0 hF.1 hF.2.1 hcur.symm hk hrun
  rw [hs1, WP.spec_ok] at h
  obtain ⟨-, -, -, hks, hmV⟩ := h
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) := slotsSame_of_vobj J.xtop.rel.1 hmV
  obtain ⟨hWt, hWp⟩ := walk_of_vobj hF.1.2.vs hF.1.2.pt hmV
  rw [hks]
  exact hN.frame hF.2.1 hF.2.2.1 hF.2.2.2.1 hWt hWp J.vsc fun y hy => hSS.capV hy

end

end Fl4Proofs.P3.Vs
