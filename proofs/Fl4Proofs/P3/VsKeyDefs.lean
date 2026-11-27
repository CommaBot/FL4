/-
P3 (issue #16, F1 stage 5; KENTRY-PLAN f4c): **the VSpace key of a cap and the
keyed caps across a slot step** (moved from VsNamed / VsNamedKeep so that the
CSpace refinements upstream of StepSem, e.g. CnodeCopy, can export `VsKeep`).

* `VKey` / `VRefOf`: a cap's VSpace key (level, object) and the ref it carries.
* `VsKeep th th' m m'` with `of_eq`, `of_pre`, `trans`, `vsKeep_insert`,
  `vsKeep_move`, `vsKeep_swap`; `vkey_mask` … `vkey_copied` (see VsNamedKeep).
-/
import Fl4Proofs.P3.CnodeVsW
import Fl4Proofs.P3.Insert
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

noncomputable section

/-- The VSpace key of a cap: level and object (PT 1 … PML4 4, pool 5). -/
def VKey : capability.Cap → Option (Nat × U64)
  | .PageTable q _ _ _ => some (1, q)
  | .PageDirectory q _ _ _ => some (2, q)
  | .Pdpt q _ _ _ => some (3, q)
  | .Pml4 q _ _ => some (4, q)
  | .AsidPool q _ => some (5, q)
  | _ => none

/-- The ref a cap carries (l4v `vs_cap_ref`): mapped flag, ASID / pool base,
vaddr. -/
def VRefOf : capability.Cap → Option (Bool × Nat × Nat)
  | .PageTable _ mp a v => some (mp, a.val, v.val)
  | .PageDirectory _ mp a v => some (mp, a.val, v.val)
  | .Pdpt _ mp a v => some (mp, a.val, v.val)
  | .Pml4 _ mp a => some (mp, a.val, 0)
  | .AsidPool _ b => some (true, b.val, 0)
  | _ => none


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
variable {m m' : U64 → U64}

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

/-- (F1 stage 5) **Unkeyed slots changed** (an insert of an IRQ / IO port cap, a
CNode step writing only unkeyed caps): every slot outside `W` kept, every slot of
`W` unkeyed before and after. -/
theorem VsKeep.of_nokey {th : TypedHeap} {W : U64 → Prop}
    (hc : ∀ y, IsSlot th y → ¬ W y → capV m' y = capV m y)
    (h0 : ∀ y, IsSlot th y → W y → VKey (capV m y) = none)
    (h1 : ∀ y, IsSlot th y → W y → VKey (capV m' y) = none) : VsKeep th th m m' :=
  VsKeep.of_pre id (fun _ h => h)
    (fun y hy hk => by
      by_cases e : W y
      · rcases hk with hk | hk
        · exact absurd (h1 y hy e) hk
        · exact absurd (h0 y hy e) hk
      · exact hc y hy e)
    (fun y hy _ => ⟨y, hy, rfl⟩) (fun _ _ _ _ hne _ _ => hne)

/-- (F1 stage 5) **Two keeping steps compose** (CNode Rotate's two moves). -/
theorem VsKeep.trans {th th1 th2 : TypedHeap} {m0 m1 m2 : U64 → U64} (h1 : VsKeep th th1 m0 m1)
    (h2 : VsKeep th1 th2 m1 m2) : VsKeep th th2 m0 m2 where
  fwd y hy hk := by
    obtain ⟨y1, hy1, e1, r1⟩ := h1.fwd y hy hk
    obtain ⟨y2, hy2, e2, r2⟩ := h2.fwd y1 hy1 (by rw [e1]; exact hk)
    exact ⟨y2, hy2, e2.trans e1, r2.trans r1⟩
  back y2 hy2 hk := by
    obtain ⟨y1, hy1, e1, r1⟩ := h2.back y2 hy2 hk
    obtain ⟨y, hy, e, r⟩ := h1.back y1 hy1 (by rw [e1]; exact hk)
    exact ⟨y, hy, e.trans e1, r.trans r1⟩
  inj y1 y2 hy1 hy2 hne hk hu := by
    obtain ⟨w1, w2, hw1, hw2, hw, a1, b1, a2⟩ := h2.inj y1 y2 hy1 hy2 hne hk hu
    have hu1 : TabUn (capV m1 w1) := TabUn.of_ref a1 b1 hu
    obtain ⟨z1, z2, hz1, hz2, hz, c1, d1, c2⟩ := h1.inj w1 w2 hw1 hw2 hw (a1.trans a2.symm) hu1
    exact ⟨z1, z2, hz1, hz2, hz, c1.trans a1, d1.trans b1, c2.trans a1⟩

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

/-- (F1 stage 5) **A copy into an empty slot** (TCB install): every slot but
`dest` kept, `dest` unkeyed before, and after either unkeyed or holding, not
unmapped, the cap of another slot. -/
theorem vsKeep_copy {th : TypedHeap} {dest : U64}
    (hc : ∀ y, IsSlot th y → y ≠ dest → capV m' y = capV m y) (hd0 : VKey (capV m dest) = none)
    (hr : VKey (capV m' dest) ≠ none → ∃ y0, IsSlot th y0 ∧ y0 ≠ dest ∧ capV m' dest = capV m y0)
    (hu : ¬ TabUn (capV m' dest)) : VsKeep th th m m' := by
  by_cases hk : VKey (capV m' dest) = none
  · exact VsKeep.of_nokey (W := (· = dest)) (fun y hy h => hc y hy h) (fun y _ e => by rw [e]; exact hd0)
      (fun y _ e => by rw [e]; exact hk)
  · obtain ⟨y0, hy0, hne, he⟩ := hr hk
    refine VsKeep.of_pre (fun y => if y = dest then y0 else y) (fun y hy => ?_) (fun y hy _ => ?_)
      (fun y hy hk' => ?_) (fun y1 y2 hy1 hy2 hne' hu1 _ => ?_)
    · split_ifs
      · exact hy0
      · exact hy
    · by_cases e : y = dest
      · rw [if_pos e, e]; exact he
      · rw [if_neg e]; exact hc y hy e
    · have hyd : y ≠ dest := by rintro rfl; exact hk' hd0
      exact ⟨y, hy, by simp only [if_neg hyd]⟩
    · have h1d : y1 ≠ dest := by rintro rfl; exact hu hu1
      rw [if_neg h1d]
      by_cases e : y2 = dest
      · rw [if_pos e]
        rintro rfl
        exact hu (by rw [he, ← hc y1 hy1 h1d]; exact hu1)
      · rw [if_neg e]; exact hne'

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

section CopyU
variable {S : Type} {st : machine.Store S}

/-- (F1 stage 5) **A copied (derived, not moved) cap is no unmapped table
cap** (`vsKeep_insert`'s `hu` for CNode Copy / Mint). -/
theorem copied_untab {s : S} {lbl length buf src : U64} {srcC nc : capability.Cap}
    (h : cnode.copied_cap st s lbl length buf src srcC = ok (.Ok (nc, false))) : ¬ TabUn nc := by
  intro hT
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
      first | (obtain ⟨rfl, -⟩ := h) | subst h
      exact derive_tabun hr1 hT
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
        first | (obtain ⟨rfl, -⟩ := h) | subst h
        exact derive_tabun hr1 hT
    · split at h
      · simp at h
      · split at h
        · simp [error.truncated] at h
        obtain ⟨d, -, h⟩ := bind_ok_inv h
        obtain ⟨c1, hc1, h⟩ := bind_ok_inv h
        simp at h

end CopyU

end Fl4Proofs.P3.Vs
