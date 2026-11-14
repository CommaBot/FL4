/-
P3 (DESIGN.md §9), endpoints: X64 `storeWord` / `loadWord` on the byte
memory: a stored word reads back (`load_store_same`), and a store leaves the
other aligned words alone (`load_store_other`).
-/
import Fl4Proofs.P3.EpRel
import Mathlib.Tactic.IntervalCases
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open Fl4Spec

noncomputable section

/-- The byte memory after X64 `storeWord p w`. -/
def storeMem (um : Word → Word8) (p w : Word) : Word → Word8 :=
  (intUpto 0 7).foldl
    (fun m i => Function.update m (p + BitVec.ofInt 64 i) ((wordRsplit w : List Word8).getD (7 - i.toNat) 0)) um

theorem intUpto_07 : intUpto 0 7 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide

theorem wordRsplit_eq (w : Word) : (wordRsplit w : List Word8) =
    [(w >>> 56).setWidth 8, (w >>> 48).setWidth 8, (w >>> 40).setWidth 8, (w >>> 32).setWidth 8,
     (w >>> 24).setWidth 8, (w >>> 16).setWidth 8, (w >>> 8).setWidth 8, (w >>> 0).setWidth 8] := by
  unfold wordRsplit
  rw [show (64 + 8 - 1) / 8 = 8 from rfl, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  rfl

theorem load_store_same (um : Word → Word8) (p w : Word) : loadWordAt (storeMem um p w) p = w := by
  unfold storeMem loadWordAt
  rw [intUpto_07, wordRsplit_eq]
  simp (config := { decide := true }) only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
    Function.update_apply, add_right_inj, ↓reduceIte]
  simp only [Int.reduceToNat, Nat.reduceSub, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some]
  unfold wordRcat
  simp only [List.foldl_cons, List.foldl_nil]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem addr_ne {p q x y : Word} (hp : p.toNat % 8 = 0) (hq : q.toNat % 8 = 0) (hne : q ≠ p)
    (hx : x.toNat < 8) (hy : y.toNat < 8) : q + x ≠ p + y := by
  intro e
  have h := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, BitVec.toNat_add] at h
  have h1 := p.isLt; have h2 := q.isLt
  have h3 : q.toNat + x.toNat < 2 ^ 64 := by omega
  have h4 : p.toNat + y.toNat < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4] at h
  exact hne (BitVec.eq_of_toNat_eq (by omega))

theorem storeMem_other (um : Word → Word8) (p w a : Word) (h : ∀ y : Word, y.toNat < 8 → a ≠ p + y) :
    storeMem um p w a = um a := by
  unfold storeMem
  rw [intUpto_07]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [Function.update_of_ne (h _ (by decide)), Function.update_of_ne (h _ (by decide)),
    Function.update_of_ne (h _ (by decide)), Function.update_of_ne (h _ (by decide)),
    Function.update_of_ne (h _ (by decide)), Function.update_of_ne (h _ (by decide)),
    Function.update_of_ne (h _ (by decide)), Function.update_of_ne (h _ (by decide))]

theorem load_store_other (um : Word → Word8) {p q : Word} (w : Word) (hp : p.toNat % 8 = 0) (hq : q.toNat % 8 = 0)
    (hne : q ≠ p) : loadWordAt (storeMem um p w) q = loadWordAt um q := by
  unfold loadWordAt
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [intUpto_07] at hi
  refine storeMem_other um p w _ fun y hy => addr_ne hp hq hne ?_ hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end

end Fl4Proofs.P3.Endp
