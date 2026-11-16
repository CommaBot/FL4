/-
P3 (DESIGN.md §9), CSpace: the slot fields (cap, `prev`, `next`,
`revocable`, `first_badged`) after each slot setter, field by field.
-/
import Fl4Proofs.P3.Insert
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section
set_option linter.unusedSimpArgs false

section
variable {th : TypedHeap} (hP : Placed th) {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
include hP

variable {a b : U64} (ha : IsSlot th a) (hb : IsSlot th b) (s : S)
include ha hb

/-! `set_prev b v` -/

theorem prevOf_setPrev (v : U64) :
    prevOf (L.mem (L.wr s (wordOf b 16#u64) v)) a = if a = b then v else prevOf (L.mem s) a :=
  prevOf_wr16 hP ha hb s v

theorem nextOf_setPrev (v : U64) : nextOf (L.mem (L.wr s (wordOf b 16#u64) v)) a = nextOf (L.mem s) a := by
  unfold nextOf; rw [word24_wr16 hP ha hb]

theorem revOf_setPrev (v : U64) : revOf (L.mem (L.wr s (wordOf b 16#u64) v)) a = revOf (L.mem s) a := by
  unfold revOf; rw [word24_wr16 hP ha hb]

theorem fbOf_setPrev (v : U64) : fbOf (L.mem (L.wr s (wordOf b 16#u64) v)) a = fbOf (L.mem s) a := by
  unfold fbOf; rw [word24_wr16 hP ha hb]

theorem capAt_setPrev (v : U64) : capAt (L.mem (L.wr s (wordOf b 16#u64) v)) a = capAt (L.mem s) a :=
  capAt_wr_link hP ha hb (Or.inl rfl) s v

/-! `set_next b n` -/

theorem prevOf_setNext (n : U64) :
    prevOf (L.mem (L.wr s (wordOf b 24#u64) ⟨setNextF (L.mem s (wordOf b 24#u64)).bv n.bv⟩)) a =
      prevOf (L.mem s) a := prevOf_wr24 hP ha hb s _

theorem nextOf_setNext (n : U64) (hn : Canonical n) :
    nextOf (L.mem (L.wr s (wordOf b 24#u64) ⟨setNextF (L.mem s (wordOf b 24#u64)).bv n.bv⟩)) a =
      if a = b then n else nextOf (L.mem s) a := by
  unfold nextOf; rw [word24_wr24 hP ha hb]
  by_cases h : a = b
  · subst h; simp only [↓reduceIte]; rw [sextF_setNextF, sextF_canonical _ hn]
  · simp [h]

theorem revOf_setNext (n : U64) :
    revOf (L.mem (L.wr s (wordOf b 24#u64) ⟨setNextF (L.mem s (wordOf b 24#u64)).bv n.bv⟩)) a =
      revOf (L.mem s) a := by
  unfold revOf; rw [word24_wr24 hP ha hb]
  by_cases h : a = b
  · subst h; simp only [↓reduceIte]
    show (setNextF _ _).getLsbD 48 = _
    rw [getLsbD_setNextF _ _ 48 (le_refl _) (by decide)]
  · simp [h]

theorem fbOf_setNext (n : U64) :
    fbOf (L.mem (L.wr s (wordOf b 24#u64) ⟨setNextF (L.mem s (wordOf b 24#u64)).bv n.bv⟩)) a =
      fbOf (L.mem s) a := by
  unfold fbOf; rw [word24_wr24 hP ha hb]
  by_cases h : a = b
  · subst h; simp only [↓reduceIte]
    show (setNextF _ _).getLsbD 49 = _
    rw [getLsbD_setNextF _ _ 49 (by decide) (by decide)]
  · simp [h]

theorem capAt_setNext (n : U64) :
    capAt (L.mem (L.wr s (wordOf b 24#u64) ⟨setNextF (L.mem s (wordOf b 24#u64)).bv n.bv⟩)) a =
      capAt (L.mem s) a := capAt_wr_link hP ha hb (Or.inr rfl) s _

/-! `set_revocable b v` (bit 48) and `set_first_badged b v` (bit 49) -/

theorem prevOf_setBit (k : Nat) (v : Bool) :
    prevOf (L.mem (L.wr s (wordOf b 24#u64) ⟨setBitF (L.mem s (wordOf b 24#u64)).bv k v⟩)) a =
      prevOf (L.mem s) a := prevOf_wr24 hP ha hb s _

theorem nextOf_setBit (k : Nat) (hk : k = 48 ∨ k = 49) (v : Bool) :
    nextOf (L.mem (L.wr s (wordOf b 24#u64) ⟨setBitF (L.mem s (wordOf b 24#u64)).bv k v⟩)) a =
      nextOf (L.mem s) a := by
  unfold nextOf; rw [word24_wr24 hP ha hb]
  by_cases h : a = b
  · subst h; simp only [↓reduceIte]; rw [sextF_setBitF _ _ hk]
  · simp [h]

theorem revOf_setBit (k : Nat) (hk : k = 48 ∨ k = 49) (v : Bool) :
    revOf (L.mem (L.wr s (wordOf b 24#u64) ⟨setBitF (L.mem s (wordOf b 24#u64)).bv k v⟩)) a =
      if a = b ∧ k = 48 then v else revOf (L.mem s) a := by
  unfold revOf; rw [word24_wr24 hP ha hb]
  by_cases h : a = b
  · subst h; simp only [↓reduceIte, true_and]
    show (setBitF _ _ _).getLsbD 48 = _
    rw [getLsbD_setBitF _ _ _ hk (Or.inl rfl)]
    rcases hk with rfl | rfl <;> simp
  · simp [h]

theorem fbOf_setBit (k : Nat) (hk : k = 48 ∨ k = 49) (v : Bool) :
    fbOf (L.mem (L.wr s (wordOf b 24#u64) ⟨setBitF (L.mem s (wordOf b 24#u64)).bv k v⟩)) a =
      if a = b ∧ k = 49 then v else fbOf (L.mem s) a := by
  unfold fbOf; rw [word24_wr24 hP ha hb]
  by_cases h : a = b
  · subst h; simp only [↓reduceIte, true_and]
    show (setBitF _ _ _).getLsbD 49 = _
    rw [getLsbD_setBitF _ _ _ hk (Or.inr rfl)]
    rcases hk with rfl | rfl <;> simp
  · simp [h]

theorem capAt_setBit (k : Nat) (v : Bool) :
    capAt (L.mem (L.wr s (wordOf b 24#u64) ⟨setBitF (L.mem s (wordOf b 24#u64)).bv k v⟩)) a =
      capAt (L.mem s) a := capAt_wr_link hP ha hb (Or.inr rfl) s _

/-! `set_next_flags b n r f` -/

theorem prevOf_setNextFlags (n : U64) (r f : Bool) :
    prevOf (L.mem (L.wr s (wordOf b 24#u64)
      ⟨setBitF (setBitF (setNextF (L.mem s (wordOf b 24#u64)).bv n.bv) 48 r) 49 f⟩)) a =
      prevOf (L.mem s) a := prevOf_wr24 hP ha hb s _

theorem nextOf_setNextFlags (n : U64) (hn : Canonical n) (r f : Bool) :
    nextOf (L.mem (L.wr s (wordOf b 24#u64)
      ⟨setBitF (setBitF (setNextF (L.mem s (wordOf b 24#u64)).bv n.bv) 48 r) 49 f⟩)) a =
      if a = b then n else nextOf (L.mem s) a := by
  unfold nextOf; rw [word24_wr24 hP ha hb]
  by_cases h : a = b
  · subst h; simp only [↓reduceIte]
    rw [sextF_setBitF _ _ (Or.inr rfl), sextF_setBitF _ _ (Or.inl rfl),
      sextF_setNextF, sextF_canonical _ hn]
  · simp [h]

theorem revOf_setNextFlags (n : U64) (r f : Bool) :
    revOf (L.mem (L.wr s (wordOf b 24#u64)
      ⟨setBitF (setBitF (setNextF (L.mem s (wordOf b 24#u64)).bv n.bv) 48 r) 49 f⟩)) a =
      if a = b then r else revOf (L.mem s) a := by
  unfold revOf; rw [word24_wr24 hP ha hb]
  by_cases h : a = b
  · subst h; simp only [↓reduceIte]
    show (setBitF (setBitF _ 48 r) 49 f).getLsbD 48 = r
    rw [getLsbD_setBitF _ _ _ (Or.inr rfl) (Or.inl rfl)]
    simp only [show (48 : Nat) ≠ 49 by decide, ↓reduceIte]
    rw [getLsbD_setBitF _ _ _ (Or.inl rfl) (Or.inl rfl)]
    simp
  · simp [h]

theorem fbOf_setNextFlags (n : U64) (r f : Bool) :
    fbOf (L.mem (L.wr s (wordOf b 24#u64)
      ⟨setBitF (setBitF (setNextF (L.mem s (wordOf b 24#u64)).bv n.bv) 48 r) 49 f⟩)) a =
      if a = b then f else fbOf (L.mem s) a := by
  unfold fbOf; rw [word24_wr24 hP ha hb]
  by_cases h : a = b
  · subst h; simp only [↓reduceIte]
    show (setBitF _ 49 f).getLsbD 49 = f
    rw [getLsbD_setBitF _ _ _ (Or.inr rfl) (Or.inr rfl)]
    simp
  · simp [h]

theorem capAt_setNextFlags (n : U64) (r f : Bool) :
    capAt (L.mem (L.wr s (wordOf b 24#u64)
      ⟨setBitF (setBitF (setNextF (L.mem s (wordOf b 24#u64)).bv n.bv) 48 r) 49 f⟩)) a =
      capAt (L.mem s) a := capAt_wr_link hP ha hb (Or.inr rfl) s _

/-! `set_cap b c` -/

theorem link_wrCap {k : U64} (hk : k = 16#u64 ∨ k = 24#u64) (c : capability.Cap) :
    L.mem (wrCap (L := L) s b c) (wordOf a k) = L.mem s (wordOf a k) := by
  rw [wrCap_eq, link_wr_cap hP ha hb hk (Or.inr rfl), link_wr_cap hP ha hb hk (Or.inl rfl)]

theorem prevOf_wrCap (c : capability.Cap) : prevOf (L.mem (wrCap (L := L) s b c)) a = prevOf (L.mem s) a := by
  unfold prevOf; exact link_wrCap hP ha hb s (Or.inl rfl) c
theorem nextOf_wrCap (c : capability.Cap) : nextOf (L.mem (wrCap (L := L) s b c)) a = nextOf (L.mem s) a := by
  unfold nextOf; rw [link_wrCap hP ha hb s (Or.inr rfl) c]
theorem revOf_wrCap (c : capability.Cap) : revOf (L.mem (wrCap (L := L) s b c)) a = revOf (L.mem s) a := by
  unfold revOf; rw [link_wrCap hP ha hb s (Or.inr rfl) c]
theorem fbOf_wrCap (c : capability.Cap) : fbOf (L.mem (wrCap (L := L) s b c)) a = fbOf (L.mem s) a := by
  unfold fbOf; rw [link_wrCap hP ha hb s (Or.inr rfl) c]

end

end

end Fl4Proofs.P3
