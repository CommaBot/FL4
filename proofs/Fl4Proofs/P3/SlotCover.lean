/-
P3 (DESIGN.md §9), CSpace: **the covering caps survive a cap move**
(`CoverKept`, `UtKept`), from the slot changes of `cdt::insert`
(`coverUt_ins`), `cdt::move_cap` (`coverUt_mov`) and `cdt::swap`
(`coverUt_swap`); `JAtZ.jcov_cover` (DeadKeep) reads them.
-/
import Fl4Proofs.P3.CapRange
import Fl4Proofs.P3.Insert
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem physF_null : physF capability.Cap.Null = false := by
  have h := phys_eq capability.Cap.Null
  unfold objects.cap_is_physical at h
  simp at h
  exact h

theorem shl_one_val {b : U64} (h : b.val < 64) : (1#64 <<< (b.val % 64)).toNat = 2 ^ b.val := by
  rw [Nat.mod_eq_of_lt h, BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by norm_num), one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (show 1 < 2 by norm_num) h)

/-- **The covering caps survive**: each physical non-untyped cap of a slot
has one of a slot after over the same range. -/
def CoverKept (th : TypedHeap) (m m' : U64 → U64) : Prop :=
  ∀ y, IsSlot th y → physF (capV m y) = true → isUt (capV m y) = false →
    ∃ y', IsSlot th y' ∧ physF (capV m' y') = true ∧ isUt (capV m' y') = false ∧
      baseF (capV m' y') = baseF (capV m y) ∧ topF (capV m' y') = topF (capV m y)

/-- **No new untyped region**: each untyped cap of a slot after has one of a
slot before over the same region and with the same device flag, its free
index then no larger (or the new one full). -/
def UtKept (th : TypedHeap) (m m' : U64 → U64) : Prop :=
  ∀ x, IsSlot th x → ∀ p sb fi d, capV m' x = .Untyped p sb fi d →
    ∃ y, IsSlot th y ∧ ∃ fi', capV m y = .Untyped p sb fi' d ∧ (fi'.val ≤ fi.val ∨ 2 ^ sb.val ≤ fi.val)

variable {th : TypedHeap} {m m1 m' : U64 → U64}

theorem CoverKept.refl (th : TypedHeap) (m : U64 → U64) : CoverKept th m m :=
  fun y hy hp hu => ⟨y, hy, hp, hu, rfl, rfl⟩

theorem UtKept.refl (th : TypedHeap) (m : U64 → U64) : UtKept th m m :=
  fun x hx _ _ fi _ h => ⟨x, hx, fi, h, Or.inl le_rfl⟩

theorem CoverKept.trans (h1 : CoverKept th m m1) (h2 : CoverKept th m1 m') : CoverKept th m m' := by
  intro y hy hp hu
  obtain ⟨y1, hy1, hp1, hu1, hb1, ht1⟩ := h1 y hy hp hu
  obtain ⟨y2, hy2, hp2, hu2, hb2, ht2⟩ := h2 y1 hy1 hp1 hu1
  exact ⟨y2, hy2, hp2, hu2, hb2.trans hb1, ht2.trans ht1⟩

theorem UtKept.trans (h1 : UtKept th m m1) (h2 : UtKept th m1 m') : UtKept th m m' := by
  intro x hx p sb fi d h
  obtain ⟨y1, hy1, fi1, h1', e1⟩ := h2 x hx p sb fi d h
  obtain ⟨y2, hy2, fi2, h2', e2⟩ := h1 y1 hy1 p sb fi1 d h1'
  refine ⟨y2, hy2, fi2, h2', ?_⟩
  omega

/-- Slots whose caps are kept keep both. -/
theorem coverUt_same (ho : ∀ y, IsSlot th y → capV m' y = capV m y) : CoverKept th m m' ∧ UtKept th m m' :=
  ⟨fun y hy hp hu => ⟨y, hy, by rw [ho y hy]; exact hp, by rw [ho y hy]; exact hu, by rw [ho y hy],
    by rw [ho y hy]⟩, fun x hx p sb fi d h => ⟨x, hx, fi, by rw [← ho x hx]; exact h, Or.inl le_rfl⟩⟩

/-- **`cdt::insert`'s slot changes** (a derived cap `c` of `src`'s `srcC`
into the null `dest`, `src` set full if untyped). -/
theorem coverUt_ins {src dest : U64} {c srcC : capability.Cap} (hs : IsSlot th src) (hne : src ≠ dest)
    (hsc : capV m src = srcC) (hdn : capV m dest = .Null) (hc' : capV m' dest = c)
    (hs' : capV m' src = (fullF srcC c).getD srcC)
    (ho : ∀ y, IsSlot th y → y ≠ src → y ≠ dest → capV m' y = capV m y)
    (hsh : shape c = shape srcC) (hut : isUt srcC = true → c = srcC)
    (hsb : ∀ p sb fi d, srcC = .Untyped p sb fi d → sb.val < 64) : CoverKept th m m' ∧ UtKept th m m' := by
  refine ⟨fun y hy hp hu => ?_, fun x hx p sb fi d h => ?_⟩
  · by_cases ed : y = dest
    · subst ed; rw [hdn, physF_null] at hp; cases hp
    by_cases es : y = src
    · subst es
      rw [hsc] at hp hu
      have hf : fullF srcC c = none := by
        cases srcC <;> simp_all [isUt, fullF]
      refine ⟨y, hy, ?_, ?_, ?_, ?_⟩ <;> rw [hs', hf, Option.getD_none, ← hsc] <;> simp_all
    · have e := ho y hy es ed
      exact ⟨y, hy, by rw [e]; exact hp, by rw [e]; exact hu, by rw [e], by rw [e]⟩
  · by_cases ed : x = dest
    · subst ed
      rw [hc'] at h
      have hu : isUt srcC = true := by rw [← isUt_of_shape hsh, h]; rfl
      exact ⟨src, hs, fi, by rw [hsc, ← hut hu, h], Or.inl le_rfl⟩
    by_cases es : x = src
    · subst es
      rw [hs'] at h
      cases hf : fullF srcC c with
      | none => rw [hf, Option.getD_none] at h; exact ⟨x, hx, fi, by rw [hsc]; exact h, Or.inl le_rfl⟩
      | some v =>
        rw [hf, Option.getD_some] at h
        subst h
        cases srcC <;> cases c <;> simp only [fullF, reduceCtorEq] at hf
        split_ifs at hf with hpb
        cases hf
        have h64 := hsb _ _ _ _ rfl
        refine ⟨x, hx, _, by rw [hsc], Or.inr ?_⟩
        show 2 ^ _ ≤ (1#64 <<< (_ % 64)).toNat
        rw [shl_one_val h64]
    · exact ⟨x, hx, fi, by rw [← ho x hx es ed]; exact h, Or.inl le_rfl⟩

/-- **`cdt::move_cap`'s slot changes** (`src`'s cap, as `c` of its shape, into
the null `dest`; `src` nulled). -/
theorem coverUt_mov {src dest : U64} {c srcC : capability.Cap} (hd : IsSlot th dest) (hne : src ≠ dest)
    (hsc : capV m src = srcC) (hdn : capV m dest = .Null) (hc' : capV m' dest = c) (hs' : capV m' src = .Null)
    (ho : ∀ y, IsSlot th y → y ≠ src → y ≠ dest → capV m' y = capV m y)
    (hsh : shape c = shape srcC) (hs : IsSlot th src)
    (hfi : ∀ p sb fi d, c = .Untyped p sb fi d → ∀ fi' d', srcC = .Untyped p sb fi' d' → d' = d ∧ (fi'.val ≤ fi.val ∨ 2 ^ sb.val ≤ fi.val)) :
    CoverKept th m m' ∧ UtKept th m m' := by
  obtain ⟨hb, ht, hph⟩ := range_of_shape hsh
  refine ⟨fun y hy hp hu => ?_, fun x hx p sb fi d h => ?_⟩
  · by_cases ed : y = dest
    · subst ed; rw [hdn, physF_null] at hp; cases hp
    by_cases es : y = src
    · subst es
      rw [hsc] at hp hu ⊢
      exact ⟨dest, hd, by rw [hc', hph]; exact hp, by rw [hc', isUt_of_shape hsh]; exact hu, by rw [hc', hb],
        by rw [hc', ht]⟩
    · have e := ho y hy es ed
      exact ⟨y, hy, by rw [e]; exact hp, by rw [e]; exact hu, by rw [e], by rw [e]⟩
  · by_cases ed : x = dest
    · subst ed
      rw [hc'] at h
      subst h
      cases srcC <;> simp only [shape, reduceCtorEq, capability.Cap.Untyped.injEq] at hsh
      obtain ⟨rfl, rfl, -, -⟩ := hsh
      obtain ⟨e, h'⟩ := hfi _ _ _ _ rfl _ _ rfl
      subst e
      exact ⟨src, hs, _, hsc, h'⟩
    by_cases es : x = src
    · subst es; rw [hs'] at h; cases h
    · exact ⟨x, hx, fi, by rw [← ho x hx es ed]; exact h, Or.inl le_rfl⟩

/-- **`cdt::swap`'s slot changes** (`s1`'s cap, as `c1` of its shape, into
`s2`, and `s2`'s, as `c2`, into `s1`). -/
theorem coverUt_swap {s1 s2 : U64} {c1 c2 o1 o2 : capability.Cap} (h1 : IsSlot th s1) (h2 : IsSlot th s2)
    (hne : s1 ≠ s2) (ho1 : capV m s1 = o1) (ho2 : capV m s2 = o2) (hc2' : capV m' s2 = c1)
    (hc1' : capV m' s1 = c2) (ho : ∀ y, IsSlot th y → y ≠ s1 → y ≠ s2 → capV m' y = capV m y)
    (hsh1 : shape c1 = shape o1) (hsh2 : shape c2 = shape o2)
    (hfi1 : ∀ p sb fi d, c1 = .Untyped p sb fi d → ∀ fi' d', o1 = .Untyped p sb fi' d' → d' = d ∧ (fi'.val ≤ fi.val ∨ 2 ^ sb.val ≤ fi.val))
    (hfi2 : ∀ p sb fi d, c2 = .Untyped p sb fi d → ∀ fi' d', o2 = .Untyped p sb fi' d' → d' = d ∧ (fi'.val ≤ fi.val ∨ 2 ^ sb.val ≤ fi.val)) :
    CoverKept th m m' ∧ UtKept th m m' := by
  obtain ⟨hb1, ht1, hph1⟩ := range_of_shape hsh1
  obtain ⟨hb2, ht2, hph2⟩ := range_of_shape hsh2
  have ut : ∀ {c o : capability.Cap}, shape c = shape o → ∀ {p sb fi d}, c = .Untyped p sb fi d →
      ∃ fi' d', o = .Untyped p sb fi' d' := by
    intro c o hsh p sb fi d h
    subst h
    cases o <;> simp only [shape, reduceCtorEq, capability.Cap.Untyped.injEq] at hsh
    obtain ⟨rfl, rfl, -, -⟩ := hsh
    exact ⟨_, _, rfl⟩
  refine ⟨fun y hy hp hu => ?_, fun x hx p sb fi d h => ?_⟩
  · by_cases e1 : y = s1
    · subst e1
      rw [ho1] at hp hu ⊢
      exact ⟨s2, h2, by rw [hc2', hph1]; exact hp, by rw [hc2', isUt_of_shape hsh1]; exact hu, by rw [hc2', hb1],
        by rw [hc2', ht1]⟩
    by_cases e2 : y = s2
    · subst e2
      rw [ho2] at hp hu ⊢
      exact ⟨s1, h1, by rw [hc1', hph2]; exact hp, by rw [hc1', isUt_of_shape hsh2]; exact hu, by rw [hc1', hb2],
        by rw [hc1', ht2]⟩
    · have e := ho y hy e1 e2
      exact ⟨y, hy, by rw [e]; exact hp, by rw [e]; exact hu, by rw [e], by rw [e]⟩
  · by_cases e2 : x = s2
    · subst e2
      rw [hc2'] at h
      obtain ⟨fi', d', e⟩ := ut hsh1 h
      obtain ⟨ed, h'⟩ := hfi1 _ _ _ _ h _ _ e
      subst ed
      exact ⟨s1, h1, fi', by rw [ho1, e], h'⟩
    by_cases e1 : x = s1
    · subst e1
      rw [hc1'] at h
      obtain ⟨fi', d', e⟩ := ut hsh2 h
      obtain ⟨ed, h'⟩ := hfi2 _ _ _ _ h _ _ e
      subst ed
      exact ⟨s2, h2, fi', by rw [ho2, e], h'⟩
    · exact ⟨x, hx, fi, by rw [← ho x hx e1 e2]; exact h, Or.inl le_rfl⟩

end

end Fl4Proofs.P3
