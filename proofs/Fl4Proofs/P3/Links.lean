/-
P3 (DESIGN.md §9), CSpace: the derivation-tree words of a slot.

A slot (obj.rs, layout.rs `cte`) is four words: the cap (two words), `prev`
(word 2, a slot address or 0) and the `next` word (word 3): bits 0..47 the
next slot address (sign-extended when read, `sext48`), bit 48 `revocable`
(seL4 `mdbRevocable`), bit 49 `first_badged` (`mdbFirstBadged`).

This file gives the slot accessors as functions of the memory view
(`prevOf`, `nextOf`, `revOf`, `fbOf`) and specs of the extracted getters and
setters, and the bit facts the CDT proofs use: setting one field of the
`next` word leaves the others alone, and a canonical address written with
`set_next` reads back unchanged.
-/
import Fl4Proofs.P3.SetCap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section
set_option linter.unusedSimpArgs false

/-! ## The `next` word on bits -/

/-- `sext48`. -/
def sextF (w : BitVec 64) : BitVec 64 :=
  if (w &&& M48) &&& 0x800000000000#64 = 0#64 then w &&& M48 else (w &&& M48) ||| 0xffff000000000000#64

/-- `set_next`: replace the address bits. -/
def setNextF (w n : BitVec 64) : BitVec 64 := (w &&& ~~~M48) ||| (n &&& M48)

/-- `set_revocable` / `set_first_badged`: set bit `k`. -/
def setBitF (w : BitVec 64) (k : Nat) (v : Bool) : BitVec 64 :=
  (w &&& ~~~(1#64 <<< k)) ||| (if v then 1#64 <<< k else 0#64)

theorem sextF_eq_unpackF (w : BitVec 64) : sextF w = unpackF w := rfl

theorem sextF_setNextF (w n : BitVec 64) : sextF (setNextF w n) = sextF n := by
  have : setNextF w n &&& M48 = n &&& M48 := by
    apply BitVec.eq_of_getElem_eq; intro i hi
    simp only [setNextF, M48, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not]
    interval_cases i <;> simp
  simp only [sextF, this]

theorem sextF_canonical (p : U64) (hp : Canonical p) : sextF p.bv = p.bv := by
  rw [sextF_eq_unpackF]
  exact unpack_gen p.bv p hp (fun _ _ _ => rfl)

theorem getLsbD_setNextF (w n : BitVec 64) (k : Nat) (hk : 48 ≤ k) (hk' : k < 64) :
    (setNextF w n).getLsbD k = w.getLsbD k := by
  simp only [setNextF, M48, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not]
  interval_cases k <;> simp

theorem setBitF_low (w : BitVec 64) (k : Nat) (hk : k = 48 ∨ k = 49) (v : Bool) :
    setBitF w k v &&& M48 = w &&& M48 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  rcases hk with rfl | rfl <;> cases v <;>
    simp only [setBitF, M48, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, ite_true,
      Bool.false_eq_true, ite_false, BitVec.getElem_shiftLeft] <;>
    interval_cases i <;> simp

theorem sextF_setBitF (w : BitVec 64) (k : Nat) (hk : k = 48 ∨ k = 49) (v : Bool) :
    sextF (setBitF w k v) = sextF w := by
  simp only [sextF, setBitF_low w k hk v]

theorem getLsbD_setBitF (w : BitVec 64) (k j : Nat) (hk : k = 48 ∨ k = 49) (hj : j = 48 ∨ j = 49) (v : Bool) :
    (setBitF w k v).getLsbD j = if j = k then v else w.getLsbD j := by
  rcases hk with rfl | rfl <;> rcases hj with rfl | rfl <;> cases v <;>
    simp [setBitF, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]

theorem bit_ne_zero (x : BitVec 64) (k : Nat) (hk : k = 48 ∨ k = 49) :
    ¬ (x &&& 1#64 <<< k = 0#64) ↔ x.getLsbD k = true := by
  constructor
  · intro h
    by_contra hb
    apply h
    apply BitVec.eq_of_getElem_eq; intro i hi
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft]
    rcases hk with rfl | rfl <;> interval_cases i <;> simp_all [BitVec.getLsbD_eq_getElem]
  · intro hb h
    have := congrArg (fun y : BitVec 64 => y.getLsbD k) h
    simp only [BitVec.getLsbD_and, hb, BitVec.getLsbD_shiftLeft, Bool.true_and, BitVec.getLsbD_zero] at this
    rcases hk with rfl | rfl <;> simp at this

/-! ## Slot fields as functions of the memory -/

/-- Address of word `k` of a slot. -/
abbrev wordOf (a : U64) (k : U64) : U64 := core.num.U64.wrapping_add a k

def prevOf (mem : U64 → U64) (a : U64) : U64 := mem (wordOf a 16#u64)
def nextOf (mem : U64 → U64) (a : U64) : U64 := ⟨sextF (mem (wordOf a 24#u64)).bv⟩
def revOf (mem : U64 → U64) (a : U64) : Bool := (mem (wordOf a 24#u64)).bv.getLsbD 48
def fbOf (mem : U64 → U64) (a : U64) : Bool := (mem (wordOf a 24#u64)).bv.getLsbD 49

section Specs
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem mdb_revocable_eq : obj.MDB_REVOCABLE = ok ⟨1#64 <<< 48⟩ := by
  unfold obj.MDB_REVOCABLE; rw [shl_eq _ 48#i32 (by decide) (by decide)]; rfl
theorem mdb_first_badged_eq : obj.MDB_FIRST_BADGED = ok ⟨1#64 <<< 49⟩ := by
  unfold obj.MDB_FIRST_BADGED; rw [shl_eq _ 49#i32 (by decide) (by decide)]; rfl

@[step] theorem slot_prev_spec (sl : obj.Slot) (s : S) :
    obj.Slot.prev st sl s ⦃ r => r = prevOf (L.mem s) sl ⦄ := by
  unfold obj.Slot.prev; simp [lift, L.read_eq, prevOf, layout.cte.PREV]

theorem next_word_eq (sl : obj.Slot) (s : S) :
    obj.Slot.next_word st sl s = ok (L.mem s (wordOf sl 24#u64)) := by
  unfold obj.Slot.next_word; simp [lift, L.read_eq, layout.cte.NEXT]

theorem sext48_eq (w : U64) : obj.sext48 w = ok ⟨sextF w.bv⟩ := by
  unfold obj.sext48 sextF
  simp only [lift, bind_ok, obj.MDB_PTR_MASK, M48]
  by_cases hc : w.bv &&& 281474976710655#64 &&& 140737488355328#64 = 0#64
  · have : (w &&& 281474976710655#u64 &&& 140737488355328#u64 != 0#u64) = false := by
      simp only [bne_eq_false_iff_eq, UScalar.eq_equiv_bv_eq]; exact hc
    simp only [this, hc, Bool.false_eq_true, ↓reduceIte]; rfl
  · have : (w &&& 281474976710655#u64 &&& 140737488355328#u64 != 0#u64) = true := by
      simp only [bne_iff_ne, ne_eq, UScalar.eq_equiv_bv_eq]; exact hc
    simp only [this, hc, ↓reduceIte]; rfl

@[step] theorem slot_next_spec (sl : obj.Slot) (s : S) :
    obj.Slot.next st sl s ⦃ r => r = nextOf (L.mem s) sl ⦄ := by
  unfold obj.Slot.next; simp [next_word_eq, sext48_eq, nextOf]

@[step] theorem slot_revocable_spec (sl : obj.Slot) (s : S) :
    obj.Slot.revocable st sl s ⦃ r => r = revOf (L.mem s) sl ⦄ := by
  unfold obj.Slot.revocable
  simp only [next_word_eq, mdb_revocable_eq, lift, bind_ok, WP.spec_ok, revOf]
  generalize L.mem s (wordOf sl 24#u64) = x
  rw [Bool.eq_iff_iff, bne_iff_ne, ne_eq, UScalar.eq_equiv_bv_eq]
  show ¬ (x.bv &&& 1#64 <<< 48 = 0#64) ↔ _
  exact (bit_ne_zero x.bv 48 (Or.inl rfl))

@[step] theorem slot_set_prev_spec (sl : obj.Slot) (s : S) (p : obj.Slot) :
    obj.Slot.set_prev st sl s p ⦃ s' => s' = L.wr s (wordOf sl 16#u64) p ⦄ := by
  unfold obj.Slot.set_prev; simp [lift, L.write_eq, layout.cte.PREV]

@[step] theorem slot_set_next_spec (sl : obj.Slot) (s : S) (n : obj.Slot) :
    obj.Slot.set_next st sl s n ⦃ s' =>
      s' = L.wr s (wordOf sl 24#u64) ⟨setNextF (L.mem s (wordOf sl 24#u64)).bv n.bv⟩ ⦄ := by
  unfold obj.Slot.set_next
  simp [next_word_eq, lift, L.write_eq, layout.cte.NEXT, obj.MDB_PTR_MASK, setNextF, M48]
  rfl

@[step] theorem slot_set_revocable_spec (sl : obj.Slot) (s : S) (v : Bool) :
    obj.Slot.set_revocable st sl s v ⦃ s' =>
      s' = L.wr s (wordOf sl 24#u64) ⟨setBitF (L.mem s (wordOf sl 24#u64)).bv 48 v⟩ ⦄ := by
  unfold obj.Slot.set_revocable
  simp only [next_word_eq, mdb_revocable_eq, lift, bind_ok, layout.cte.NEXT]
  cases v <;> simp [L.write_eq, setBitF] <;> rfl

@[step] theorem slot_set_first_badged_spec (sl : obj.Slot) (s : S) (v : Bool) :
    obj.Slot.set_first_badged st sl s v ⦃ s' =>
      s' = L.wr s (wordOf sl 24#u64) ⟨setBitF (L.mem s (wordOf sl 24#u64)).bv 49 v⟩ ⦄ := by
  unfold obj.Slot.set_first_badged
  simp only [next_word_eq, mdb_first_badged_eq, lift, bind_ok, layout.cte.NEXT]
  cases v <;> simp [L.write_eq, setBitF] <;> rfl

@[step] theorem slot_first_badged_spec (sl : obj.Slot) (s : S) :
    obj.Slot.first_badged st sl s ⦃ r => r = fbOf (L.mem s) sl ⦄ := by
  unfold obj.Slot.first_badged
  simp only [next_word_eq, mdb_first_badged_eq, lift, bind_ok, WP.spec_ok, fbOf]
  generalize L.mem s (wordOf sl 24#u64) = x
  rw [Bool.eq_iff_iff, bne_iff_ne, ne_eq, UScalar.eq_equiv_bv_eq]
  show ¬ (x.bv &&& 1#64 <<< 49 = 0#64) ↔ _
  exact (bit_ne_zero x.bv 49 (Or.inr rfl))

@[step] theorem slot_set_next_flags_spec (sl : obj.Slot) (s : S) (n : obj.Slot) (r f : Bool) :
    obj.Slot.set_next_flags st sl s n r f ⦃ s' =>
      s' = L.wr s (wordOf sl 24#u64)
        ⟨setBitF (setBitF (setNextF (L.mem s (wordOf sl 24#u64)).bv n.bv) 48 r) 49 f⟩ ⦄ := by
  unfold obj.Slot.set_next_flags
  simp only [next_word_eq, mdb_revocable_eq, mdb_first_badged_eq, obj.MDB_PTR_MASK,
    lift, bind_ok, layout.cte.NEXT]
  cases r <;> cases f <;> simp only [Bool.false_eq_true, ↓reduceIte, L.write_eq, bind_ok, WP.spec_ok]
  all_goals
    congr 1
    rw [UScalar.eq_equiv_bv_eq]
    simp [setBitF, setNextF, M48]
    bv_decide

@[step] theorem slot_is_null_spec (sl : obj.Slot) : obj.Slot.is_null sl ⦃ b => b = decide (sl = 0#u64) ⦄ := by
  unfold obj.Slot.is_null; simp

end Specs

end

end Fl4Proofs.P3
