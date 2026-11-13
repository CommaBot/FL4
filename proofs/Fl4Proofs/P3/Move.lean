/-
P3 (DESIGN.md §9), CSpace: `cdt::move_cap` (seL4 `cteMove`) on the store.
-/
import Fl4Proofs.P3.Insert
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section
set_option linter.unusedSimpArgs false

section MoveMem
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

@[step] theorem slot_clear_spec (sl : obj.Slot) (s : S) :
    obj.Slot.clear st sl s ⦃ s' =>
      s' = L.wr (L.wr (L.wr (L.wr s (wordOf sl 0#u64) 0#u64) (wordOf sl 8#u64) 0#u64) (wordOf sl 16#u64) 0#u64)
        (wordOf sl 24#u64) 0#u64 ⦄ := by
  unfold obj.Slot.clear; simp [L.write_eq, lift, wordOf_zero]

attribute [local step] set_cap_spec

theorem slot_prev_eq (sl : obj.Slot) (s : S) : obj.Slot.prev st sl s = ok (prevOf (L.mem s) sl) := by
  unfold obj.Slot.prev; simp [lift, L.read_eq, prevOf, layout.cte.PREV]

theorem slot_next_eq (sl : obj.Slot) (s : S) : obj.Slot.next st sl s = ok (nextOf (L.mem s) sl) := by
  unfold obj.Slot.next; simp [next_word_eq, sext48_eq, nextOf]

theorem is_null_eq (sl : obj.Slot) : obj.Slot.is_null sl = ok (decide (sl = 0#u64)) := rfl

/-- The slot words after `cdt::move_cap c src dest` from `s`. -/
def MovWords (th : TypedHeap) (s s' : S) (c : capability.Cap) (src dest : U64) : Prop :=
  ∀ a, IsSlot th a → ∀ k, Off k →
    L.mem s' (wordOf a k) =
      if a = dest then
        (if k = 0#u64 then ⟨(encodeF c).1⟩ else if k = 8#u64 then ⟨(encodeF c).2⟩ else
         if k = 16#u64 then prevOf (L.mem s) src else
         ⟨setBitF (setBitF (setNextF (L.mem s (wordOf dest 24#u64)).bv (nextOf (L.mem s) src).bv) 48
            (revOf (L.mem s) src)) 49 (fbOf (L.mem s) src)⟩)
      else if a = src then 0#u64
      else if prevOf (L.mem s) src ≠ 0#u64 ∧ a = prevOf (L.mem s) src ∧ k = 24#u64 then
        ⟨setNextF (L.mem s (wordOf a 24#u64)).bv dest.bv⟩
      else if nextOf (L.mem s) src ≠ 0#u64 ∧ a = nextOf (L.mem s) src ∧ k = 16#u64 then dest
      else L.mem s (wordOf a k)

set_option maxRecDepth 8000 in
/-- What `cdt::move_cap` does to the slots, word by word. -/
theorem move_mem (hP : Placed th) (s : S) (c : capability.Cap) (src dest : U64)
    (hs : IsSlot th src) (hd : IsSlot th dest) (hne : src ≠ dest)
    (hpv : prevOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (prevOf (L.mem s) src) ∧ prevOf (L.mem s) src ≠ dest ∧ prevOf (L.mem s) src ≠ src))
    (hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src)) :
    cdt.move_cap st s c src dest ⦃ s' => MovWords (L := L) th s s' c src dest ⦄ := by
  unfold cdt.move_cap
  rw [slot_prev_eq, slot_next_eq]
  simp only [bind_ok]
  have hne' := Ne.symm hne
  have e2 : ∀ s1 : S, L.wr (L.wr s1 dest ⟨(encodeF c).1⟩) (core.num.U64.wrapping_add dest 8#u64) ⟨(encodeF c).2⟩ =
      wrCap (L := L) s1 dest c := fun _ => rfl
  by_cases hp0 : prevOf (L.mem s) src = 0#u64 <;> by_cases hn0 : nextOf (L.mem s) src = 0#u64 <;>
    simp only [is_null_eq, hp0, hn0, decide_true, decide_false, ↓reduceIte, bind_ok, Bool.false_eq_true] <;>
    step* <;>
    unfold MovWords <;> intro a ha k hk <;> subst_vars <;> rw [e2, wrCap_eq]
  · -- no neighbours
    clear * - hP ha hs hd hne hne' hk hp0 hn0
    simp only [mem_wr_slot hP, ha, hs, hd, hk, off0, off8, off16, off24, ne_eq, not_true_eq_false,
        false_and, ↓reduceIte, hp0, hn0, not_false_eq_true] <;>
      rcases hk with rfl | rfl | rfl | rfl <;> by_cases h1 : a = dest <;> by_cases h2 : a = src <;>
      (try subst h1) <;> (try subst h2) <;>
      first
      | exact absurd rfl hne
      | simp only [lit_ne, true_and, and_true, and_false, false_and, ↓reduceIte, and_self,
          not_false_eq_true, *]
  · -- only a next
    obtain ⟨hNsl, hNd, hNs⟩ := hnx.resolve_left hn0
    generalize hN : nextOf (L.mem s) src = N at *
    clear * - hP ha hs hd hne hne' hk hp0 hn0 hNsl hNd hNs
    simp only [mem_wr_slot hP, ha, hs, hd, hNsl, hk, off0, off8, off16, off24, ne_eq, not_true_eq_false,
        false_and, ↓reduceIte, hp0, hn0, not_false_eq_true] <;>
      rcases hk with rfl | rfl | rfl | rfl <;> by_cases h1 : a = dest <;> by_cases h2 : a = src <;>
      by_cases h3 : a = N <;>
      (try subst h1) <;> (try subst h2) <;> (try subst h3) <;>
      first
      | exact absurd rfl hne
      | exact absurd rfl hNd
      | exact absurd rfl hNs
      | simp only [lit_ne, true_and, and_true, and_false, false_and, ↓reduceIte, and_self,
          not_false_eq_true, *]
  · -- only a prev
    obtain ⟨hPsl, hPd, hPs⟩ := hpv.resolve_left hp0
    generalize hPv : prevOf (L.mem s) src = P at *
    clear * - hP ha hs hd hne hne' hk hp0 hn0 hPsl hPd hPs
    simp only [mem_wr_slot hP, ha, hs, hd, hPsl, hk, off0, off8, off16, off24, ne_eq, not_true_eq_false,
        false_and, ↓reduceIte, hp0, hn0, not_false_eq_true] <;>
      rcases hk with rfl | rfl | rfl | rfl <;> by_cases h1 : a = dest <;> by_cases h2 : a = src <;>
      by_cases h3 : a = P <;>
      (try subst h1) <;> (try subst h2) <;> (try subst h3) <;>
      first
      | exact absurd rfl hne
      | exact absurd rfl hPd
      | exact absurd rfl hPs
      | simp only [lit_ne, true_and, and_true, and_false, false_and, ↓reduceIte, and_self,
          not_false_eq_true, *]
  · -- both
    obtain ⟨hPsl, hPd, hPs⟩ := hpv.resolve_left hp0
    obtain ⟨hNsl, hNd, hNs⟩ := hnx.resolve_left hn0
    generalize hPv : prevOf (L.mem s) src = P at *
    generalize hN : nextOf (L.mem s) src = N at *
    clear * - hP ha hs hd hne hne' hk hp0 hn0 hPsl hPd hPs hNsl hNd hNs
    simp only [mem_wr_slot hP, ha, hs, hd, hPsl, hNsl, hk, off0, off8, off16, off24, ne_eq, not_true_eq_false,
        false_and, ↓reduceIte, hp0, hn0, not_false_eq_true] <;>
      rcases hk with rfl | rfl | rfl | rfl <;> by_cases h1 : a = dest <;> by_cases h2 : a = src <;>
      by_cases h3 : a = P <;> by_cases h4 : a = N <;>
      (try subst h1) <;> (try subst h2) <;> (try subst h3) <;> (try subst h4) <;>
      first
      | exact absurd rfl hne
      | exact absurd rfl hPd
      | exact absurd rfl hPs
      | exact absurd rfl hNd
      | exact absurd rfl hNs
      | simp only [lit_ne, true_and, and_true, and_false, false_and, ↓reduceIte, and_self,
          not_false_eq_true, *]

section Fields
variable {s s' : S} {c : capability.Cap} {src dest : U64}

theorem MovWords.capAt' (hW : MovWords (L := L) th s s' c src dest) {a : U64} (ha : IsSlot th a)
    (he : EncWf c) (hne : src ≠ dest) :
    capAt (L.mem s') a = if a = dest then ok c else if a = src then ok .Null else capAt (L.mem s) a := by
  rw [capAt_words, hW a ha _ off0, hW a ha _ off8]
  by_cases h1 : a = dest
  · simp [h1, decode_enc c he]
  · by_cases h2 : a = src
    · subst h2; simp only [h1, ↓reduceIte]; exact decode_encode_null.2
    · simp [h1, h2, lit_ne]; rw [← capAt_words]

theorem MovWords.prevOf' (hW : MovWords (L := L) th s s' c src dest) {a : U64} (ha : IsSlot th a)
    (hne : src ≠ dest) :
    prevOf (L.mem s') a = if a = dest then prevOf (L.mem s) src else if a = src then 0#u64
      else if nextOf (L.mem s) src ≠ 0#u64 ∧ a = nextOf (L.mem s) src then dest else prevOf (L.mem s) a := by
  rw [show prevOf (L.mem s') a = L.mem s' (wordOf a 16#u64) from rfl, hW a ha _ off16]
  by_cases h1 : a = dest
  · simp [h1, lit_ne]
  · by_cases h2 : a = src
    · subst h2; simp [h1]
    · simp only [h1, h2, ↓reduceIte, lit_ne, and_false, and_true]; rfl

theorem MovWords.nextOf' (hW : MovWords (L := L) th s s' c src dest) (hP : Placed th) {a : U64}
    (ha : IsSlot th a) (hd : IsSlot th dest) (hne : src ≠ dest) (hN : Canonical (nextOf (L.mem s) src)) :
    nextOf (L.mem s') a = if a = dest then nextOf (L.mem s) src else if a = src then 0#u64
      else if prevOf (L.mem s) src ≠ 0#u64 ∧ a = prevOf (L.mem s) src then dest else nextOf (L.mem s) a := by
  rw [show nextOf (L.mem s') a = ⟨sextF (L.mem s' (wordOf a 24#u64)).bv⟩ from rfl, hW a ha _ off24]
  by_cases h1 : a = dest
  · simp only [h1, ↓reduceIte, lit_ne]
    rw [sextF_setBitF _ _ (Or.inr rfl), sextF_setBitF _ _ (Or.inl rfl), sextF_setNextF, sextF_canonical _ hN]
  · by_cases h2 : a = src
    · subst h2; simp only [h1, ↓reduceIte]
      rw [sextF_canonical _ canonical_zero]
    · by_cases h3 : prevOf (L.mem s) src ≠ 0#u64 ∧ a = prevOf (L.mem s) src
      · obtain ⟨h3a, h3b⟩ := h3
        subst h3b
        have h3a' : ¬ (prevOf (L.mem s) src = 0#u64) := h3a
        simp only [h1, h2, ↓reduceIte, h3a', not_false_eq_true, and_self, and_true, ne_eq]
        rw [sextF_setNextF, sextF_canonical _ (hd.canonical hP)]
      · simp only [h1, h2, ↓reduceIte, lit_ne, and_false, false_and]
        rw [if_neg (by tauto), if_neg h3]; rfl

theorem MovWords.revOf' (hW : MovWords (L := L) th s s' c src dest) {a : U64} (ha : IsSlot th a)
    (hne : src ≠ dest) :
    revOf (L.mem s') a = if a = dest then revOf (L.mem s) src else if a = src then false else revOf (L.mem s) a := by
  rw [show revOf (L.mem s') a = (L.mem s' (wordOf a 24#u64)).bv.getLsbD 48 from rfl, hW a ha _ off24]
  by_cases h1 : a = dest
  · rw [if_pos h1, if_pos h1, if_neg (by decide), if_neg (by decide), if_neg (by decide)]
    show (setBitF (setBitF _ 48 _) 49 _).getLsbD 48 = _
    rw [getLsbD_setBitF _ _ _ (Or.inr rfl) (Or.inl rfl), getLsbD_setBitF _ _ _ (Or.inl rfl) (Or.inl rfl)]
    simp
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : a = src
    · rw [if_pos h2, if_pos h2]; rfl
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : prevOf (L.mem s) src ≠ 0#u64 ∧ a = prevOf (L.mem s) src ∧ (24#u64 : U64) = 24#u64
      · rw [if_pos h3]
        show (setNextF _ _).getLsbD 48 = _
        rw [getLsbD_setNextF _ _ 48 (le_refl _) (by decide)]; rfl
      · rw [if_neg h3]
        have h4 : ¬ (nextOf (L.mem s) src ≠ 0#u64 ∧ a = nextOf (L.mem s) src ∧ (24#u64 : U64) = 16#u64) := by
          rintro ⟨-, -, h⟩; exact absurd h (by decide)
        rw [if_neg h4]; rfl

end Fields

end MoveMem

end

end Fl4Proofs.P3
