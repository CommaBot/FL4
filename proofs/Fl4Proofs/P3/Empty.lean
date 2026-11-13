/-
P3 (DESIGN.md §9), CSpace: `cdt::empty_slot` (seL4 `emptySlot`) on the store.
-/
import Fl4Proofs.P3.Move
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section
set_option linter.unusedSimpArgs false

section EmptyMem
variable {th : TypedHeap} {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st]
  {ar : machine.Arch A}

/-- The slot words after `cdt::empty_slot x` from `s` (`x` holding a cap). -/
def EmpWords (th : TypedHeap) (s s' : S) (x : U64) : Prop :=
  ∀ a, IsSlot th a → ∀ k, Off k →
    L.mem s' (wordOf a k) =
      if a = x then 0#u64
      else if prevOf (L.mem s) x ≠ 0#u64 ∧ a = prevOf (L.mem s) x ∧ k = 24#u64 then
        ⟨setNextF (L.mem s (wordOf a 24#u64)).bv (nextOf (L.mem s) x).bv⟩
      else if nextOf (L.mem s) x ≠ 0#u64 ∧ a = nextOf (L.mem s) x ∧ k = 16#u64 then prevOf (L.mem s) x
      else if nextOf (L.mem s) x ≠ 0#u64 ∧ a = nextOf (L.mem s) x ∧ k = 24#u64 then
        ⟨setBitF (L.mem s (wordOf a 24#u64)).bv 49 (fbOf (L.mem s) a || fbOf (L.mem s) x)⟩
      else L.mem s (wordOf a k)

def isNullB : capability.Cap → Bool
  | .Null => true
  | _ => false

theorem cap_is_null_eq (c : capability.Cap) : capability.Cap.is_null c = ok (isNullB c) := by
  cases c <;> rfl

theorem isNullB_false {c : capability.Cap} (h : c ≠ .Null) : isNullB c = false := by
  cases c <;> simp_all [isNullB]

theorem slot_first_badged_eq (sl : obj.Slot) (s : S) :
    obj.Slot.first_badged st sl s = ok (fbOf (L.mem s) sl) := by
  have := slot_first_badged_spec (L := L) sl s
  revert this; cases obj.Slot.first_badged st sl s <;> simp [WP.spec_vis, WP.spec_div]

theorem ite_set_fb (b fb : Bool) (n : obj.Slot) (s : S) :
    (if b = true then obj.Slot.set_first_badged st n s true else obj.Slot.set_first_badged st n s fb) =
      obj.Slot.set_first_badged st n s (b || fb) := by
  cases b <;> rfl

theorem post_null (s : S) (a : A) : objects.post_cap_deletion st ar s a .Null = ok (s, a) := rfl

@[step] theorem post_null_spec (s : S) (a : A) :
    objects.post_cap_deletion st ar s a .Null ⦃ r => r = (s, a) ⦄ := by rw [post_null]; simp

set_option maxRecDepth 8000 in
/-- What `cdt::empty_slot` does to the slots, word by word (with no cleanup
cap: `post_cap_deletion Null` does nothing). -/
theorem empty_slot_mem (hP : Placed th) (s : S) (a : A) (xs : U64) (hx : IsSlot th xs)
    (c : capability.Cap) (hc : capAt (L.mem s) xs = ok c) (hcn : c ≠ .Null)
    (hpv : prevOf (L.mem s) xs = 0#u64 ∨ (IsSlot th (prevOf (L.mem s) xs) ∧ prevOf (L.mem s) xs ≠ xs))
    (hnx : nextOf (L.mem s) xs = 0#u64 ∨ (IsSlot th (nextOf (L.mem s) xs) ∧ nextOf (L.mem s) xs ≠ xs))
    (hPN : prevOf (L.mem s) xs ≠ 0#u64 → nextOf (L.mem s) xs ≠ 0#u64 → prevOf (L.mem s) xs ≠ nextOf (L.mem s) xs) :
    cdt.empty_slot st ar s a xs .Null ⦃ r => EmpWords (L := L) th s r.1 xs ∧ r.2 = a ⦄ := by
  unfold cdt.empty_slot
  rw [slot_cap_eq, hc]
  simp only [bind_ok, cap_is_null_eq, isNullB_false hcn, Bool.false_eq_true, ↓reduceIte, slot_prev_eq,
    slot_next_eq]
  by_cases hp0 : prevOf (L.mem s) xs = 0#u64 <;> by_cases hn0 : nextOf (L.mem s) xs = 0#u64 <;>
    simp only [is_null_eq, hp0, hn0, decide_true, decide_false, ↓reduceIte, bind_ok, Bool.false_eq_true,
      slot_first_badged_eq, ite_set_fb] <;>
    step* <;> subst_vars <;> refine ⟨?_, rfl⟩ <;> unfold EmpWords <;> intro b hb k hk
  · clear * - hP hb hx hk hp0 hn0
    simp only [mem_wr_slot hP, hb, hx, hk, off0, off8, off16, off24, ne_eq, not_true_eq_false,
        false_and, ↓reduceIte, hp0, hn0, not_false_eq_true, fbOf] <;>
      rcases hk with rfl | rfl | rfl | rfl <;> by_cases h1 : b = xs <;> (try subst h1) <;>
      simp only [lit_ne, true_and, and_true, and_false, false_and, ↓reduceIte, and_self,
          not_false_eq_true, *]
  · obtain ⟨hNsl, hNx⟩ := hnx.resolve_left hn0
    have hPN' : True := trivial
    have hPx : True := trivial
    generalize hN : nextOf (L.mem s) xs = N at *
    clear * - hP hb hx hk hp0 hn0 hNsl hNx hPN' hPx
    simp only [mem_wr_slot hP, hb, hx, hNsl, hk, off0, off8, off16, off24, ne_eq, not_true_eq_false,
        false_and, ↓reduceIte, hp0, hn0, not_false_eq_true, fbOf] <;>
      rcases hk with rfl | rfl | rfl | rfl <;> by_cases h1 : b = xs <;> by_cases h3 : b = N <;>
      (try subst h1) <;> (try subst h3) <;>
      first
      | exact absurd rfl hPx
      | exact absurd rfl hNx
      | exact absurd rfl hPN'
      | simp only [lit_ne, true_and, and_true, and_false, false_and, ↓reduceIte, and_self,
          not_false_eq_true, Bool.false_or, Bool.true_or, ne_eq, *]
  · obtain ⟨hPsl, hPx⟩ := hpv.resolve_left hp0
    have hPN' : True := trivial
    have hNx : True := trivial
    generalize hPv : prevOf (L.mem s) xs = P at *
    clear * - hP hb hx hk hp0 hn0 hPsl hPx hPN' hNx
    simp only [mem_wr_slot hP, hb, hx, hPsl, hk, off0, off8, off16, off24, ne_eq, not_true_eq_false,
        false_and, ↓reduceIte, hp0, hn0, not_false_eq_true, fbOf] <;>
      rcases hk with rfl | rfl | rfl | rfl <;> by_cases h1 : b = xs <;> by_cases h3 : b = P <;>
      (try subst h1) <;> (try subst h3) <;>
      first
      | exact absurd rfl hPx
      | exact absurd rfl hNx
      | exact absurd rfl hPN'
      | simp only [lit_ne, true_and, and_true, and_false, false_and, ↓reduceIte, and_self,
          not_false_eq_true, Bool.false_or, Bool.true_or, ne_eq, *]
  · obtain ⟨hPsl, hPx⟩ := hpv.resolve_left hp0
    obtain ⟨hNsl, hNx⟩ := hnx.resolve_left hn0
    have hPN' := hPN hp0 hn0
    generalize hPv : prevOf (L.mem s) xs = P at *
    generalize hN : nextOf (L.mem s) xs = N at *
    clear * - hP hb hx hk hp0 hn0 hPsl hPx hNsl hNx hPN'
    simp only [mem_wr_slot hP, hb, hx, hPsl, hNsl, hk, off0, off8, off16, off24, ne_eq, not_true_eq_false,
        false_and, ↓reduceIte, hp0, hn0, not_false_eq_true, fbOf] <;>
      rcases hk with rfl | rfl | rfl | rfl <;> by_cases h1 : b = xs <;> by_cases h3 : b = P <;>
      by_cases h4 : b = N <;>
      (try subst h1) <;> (try subst h3) <;> (try subst h4) <;>
      first
      | exact absurd rfl hPx
      | exact absurd rfl hNx
      | exact absurd rfl hPN'
      | simp only [lit_ne, true_and, and_true, and_false, false_and, ↓reduceIte, and_self,
          not_false_eq_true, Bool.false_or, Bool.true_or, ne_eq, *]

section Fields
variable {s s' : S} {xs : U64}

theorem EmpWords.capAt' (hW : EmpWords (L := L) th s s' xs) {a : U64} (ha : IsSlot th a) :
    capAt (L.mem s') a = if a = xs then ok .Null else capAt (L.mem s) a := by
  rw [capAt_words, hW a ha _ off0, hW a ha _ off8]
  by_cases h1 : a = xs
  · simp only [h1, ↓reduceIte]; exact decode_encode_null.2
  · simp [h1, lit_ne]; rw [← capAt_words]

theorem EmpWords.prevOf' (hW : EmpWords (L := L) th s s' xs) {a : U64} (ha : IsSlot th a) :
    prevOf (L.mem s') a = if a = xs then 0#u64
      else if nextOf (L.mem s) xs ≠ 0#u64 ∧ a = nextOf (L.mem s) xs then prevOf (L.mem s) xs
      else prevOf (L.mem s) a := by
  rw [show prevOf (L.mem s') a = L.mem s' (wordOf a 16#u64) from rfl, hW a ha _ off16]
  by_cases h1 : a = xs
  · simp [h1]
  · simp only [h1, ↓reduceIte, lit_ne, and_false, and_true]; rfl

theorem EmpWords.nextOf' (hW : EmpWords (L := L) th s s' xs) {a : U64} (ha : IsSlot th a)
    (hN : Canonical (nextOf (L.mem s) xs))
    (hPN : prevOf (L.mem s) xs ≠ 0#u64 → nextOf (L.mem s) xs ≠ 0#u64 → prevOf (L.mem s) xs ≠ nextOf (L.mem s) xs) :
    nextOf (L.mem s') a = if a = xs then 0#u64
      else if prevOf (L.mem s) xs ≠ 0#u64 ∧ a = prevOf (L.mem s) xs then nextOf (L.mem s) xs
      else nextOf (L.mem s) a := by
  rw [show nextOf (L.mem s') a = ⟨sextF (L.mem s' (wordOf a 24#u64)).bv⟩ from rfl, hW a ha _ off24]
  by_cases h1 : a = xs
  · simp only [h1, ↓reduceIte]; rw [sextF_canonical _ canonical_zero]
  · rw [if_neg h1, if_neg h1]
    by_cases h3 : prevOf (L.mem s) xs ≠ 0#u64 ∧ a = prevOf (L.mem s) xs
    · rw [if_pos ⟨h3.1, h3.2, rfl⟩, if_pos h3]
      show (⟨sextF (setNextF _ _)⟩ : U64) = _
      rw [sextF_setNextF, sextF_canonical _ hN]
    · rw [if_neg (fun h => h3 ⟨h.1, h.2.1⟩), if_neg h3]
      have h4 : ¬ (nextOf (L.mem s) xs ≠ 0#u64 ∧ a = nextOf (L.mem s) xs ∧ (24#u64 : U64) = 16#u64) := by
        rintro ⟨-, -, h⟩; exact absurd h (by decide)
      rw [if_neg h4]
      by_cases h5 : nextOf (L.mem s) xs ≠ 0#u64 ∧ a = nextOf (L.mem s) xs
      · rw [if_pos ⟨h5.1, h5.2, rfl⟩]
        show (⟨sextF (setBitF _ 49 _)⟩ : U64) = _
        rw [sextF_setBitF _ _ (Or.inr rfl)]; rfl
      · rw [if_neg (fun h => h5 ⟨h.1, h.2.1⟩)]; rfl

theorem EmpWords.revOf' (hW : EmpWords (L := L) th s s' xs) {a : U64} (ha : IsSlot th a) :
    revOf (L.mem s') a = if a = xs then false else revOf (L.mem s) a := by
  rw [show revOf (L.mem s') a = (L.mem s' (wordOf a 24#u64)).bv.getLsbD 48 from rfl, hW a ha _ off24]
  by_cases h1 : a = xs
  · simp [h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h3 : prevOf (L.mem s) xs ≠ 0#u64 ∧ a = prevOf (L.mem s) xs
    · rw [if_pos ⟨h3.1, h3.2, rfl⟩]
      show (setNextF _ _).getLsbD 48 = _
      rw [getLsbD_setNextF _ _ 48 (le_refl _) (by decide)]; rfl
    · rw [if_neg (fun h => h3 ⟨h.1, h.2.1⟩)]
      have h4 : ¬ (nextOf (L.mem s) xs ≠ 0#u64 ∧ a = nextOf (L.mem s) xs ∧ (24#u64 : U64) = 16#u64) := by
        rintro ⟨-, -, h⟩; exact absurd h (by decide)
      rw [if_neg h4]
      by_cases h5 : nextOf (L.mem s) xs ≠ 0#u64 ∧ a = nextOf (L.mem s) xs
      · rw [if_pos ⟨h5.1, h5.2, rfl⟩]
        show (setBitF _ 49 _).getLsbD 48 = _
        rw [getLsbD_setBitF _ _ _ (Or.inr rfl) (Or.inl rfl)]; simp; rfl
      · rw [if_neg (fun h => h5 ⟨h.1, h.2.1⟩)]; rfl

end Fields

end EmptyMem

end

end Fl4Proofs.P3
