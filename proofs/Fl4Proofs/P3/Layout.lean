/-
P3 (DESIGN.md §9), CSpace: the layout of the typed heap, what writes to
slots need.

* `objSize k`: bytes of an object of kind `k` (a CNode of radix `r` is
  `2^r` 32-byte slots; a TCB is 4 KiB, layout.rs `tcb`, with its five cap
  slots first).
* `Placed th` (hypothesis on the ghost typed heap, a P1 invariant to come):
  every object is 32-byte aligned, lies in the kernel (upper) half of the
  address space without wrapping around, and distinct objects do not
  overlap.
* `IsSlot th a`: `a` is the address of a cap slot of an object of `th`.

Consequences: slot addresses are aligned words (`IsSlot.aligned`), distinct
slots are 32 bytes apart (`IsSlot.apart`), and the abstraction of slot
addresses is injective (`cslotAddr_inj`), so a write to one slot leaves the
caps and links of every other slot alone.
-/
import Fl4Proofs.P3.StateRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- Bytes of an object of kind `k`. -/
def objSize : ObjKind → Nat
  | .cnode r => 32 * 2 ^ r
  | .tcb => 4096
  | .other n => n

/-- Hypothesis: objects are aligned, do not wrap and do not overlap. -/
structure Placed (th : TypedHeap) : Prop where
  align : ∀ p k, th p = some k → p.val % 32 = 0
  fits : ∀ p k, th p = some k → p.val + objSize k ≤ 2 ^ 64
  disj : ∀ p q kp kq, th p = some kp → th q = some kq → p ≠ q →
    p.val + objSize kp ≤ q.val ∨ q.val + objSize kq ≤ p.val
  /-- Objects are in the kernel half of the address space (layout.rs
  `PPTR_BASE`), so slot addresses are canonical. -/
  high : ∀ p k, th p = some k → 2 ^ 64 - 2 ^ 47 ≤ p.val

/-- Slot `i` of the object at `p`. -/
abbrev slotOf (p : U64) (i : Nat) : U64 := slotAddr p.bv (BitVec.ofNat 64 i)

/-- `a` is a cap slot of an object of `th`: slot `i < 2^r` of a CNode, or one
of the five slots of a TCB. -/
def IsSlotAt (th : TypedHeap) (p : U64) (i : Nat) : Prop :=
  (∃ r, th p = some (.cnode r) ∧ i < 2 ^ r) ∨ (th p = some .tcb ∧ i < tcbSlots)

def IsSlot (th : TypedHeap) (a : U64) : Prop := ∃ p i, IsSlotAt th p i ∧ a = slotOf p i

theorem IsSlotAt.size {th : TypedHeap} {p : U64} {i : Nat} (h : IsSlotAt th p i) :
    ∃ k, th p = some k ∧ 32 * (i + 1) ≤ objSize k := by
  rcases h with ⟨r, hp, hi⟩ | ⟨hp, hi⟩
  · exact ⟨_, hp, by simp [objSize]; omega⟩
  · exact ⟨_, hp, by simp [objSize, tcbSlots] at hi ⊢; omega⟩

theorem slotOf_val {p : U64} {i : Nat} (h : p.val + 32 * (i + 1) ≤ 2 ^ 64) :
    (slotOf p i).val = p.val + 32 * i := by
  show (p.bv + BitVec.ofNat 64 i * 32#64).toNat = p.val + 32 * i
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  show (p.val + i % 2 ^ 64 * (32 % 2 ^ 64) % 2 ^ 64) % 2 ^ 64 = p.val + 32 * i
  have h1 : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
  have h2 : (32 : Nat) % 2 ^ 64 = 32 := rfl
  rw [h1, h2, Nat.mod_eq_of_lt (a := i * 32) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem IsSlotAt.val {th : TypedHeap} (hP : Placed th) {p : U64} {i : Nat} (h : IsSlotAt th p i) :
    (slotOf p i).val = p.val + 32 * i := by
  obtain ⟨k, hk, hs⟩ := h.size
  exact slotOf_val (by have := hP.fits p k hk; omega)

theorem IsSlotAt.aligned {th : TypedHeap} (hP : Placed th) {p : U64} {i : Nat} (h : IsSlotAt th p i) :
    (slotOf p i).val % 32 = 0 := by
  obtain ⟨k, hk, -⟩ := h.size
  rw [h.val hP]; have := hP.align p k hk; omega

/-- Distinct slots are at least 32 bytes apart. -/
theorem IsSlotAt.apart {th : TypedHeap} (hP : Placed th) {p q : U64} {i j : Nat}
    (hi : IsSlotAt th p i) (hj : IsSlotAt th q j) (hne : ¬ (p = q ∧ i = j)) :
    (slotOf p i).val + 32 ≤ (slotOf q j).val ∨ (slotOf q j).val + 32 ≤ (slotOf p i).val := by
  rw [hi.val hP, hj.val hP]
  obtain ⟨kp, hkp, hsp⟩ := hi.size
  obtain ⟨kq, hkq, hsq⟩ := hj.size
  by_cases hpq : p = q
  · subst hpq
    have : i ≠ j := fun e => hne ⟨rfl, e⟩
    omega
  · rcases hP.disj p q kp kq hkp hkq hpq with h | h <;> omega

/-! ## Slots by address -/

theorem IsSlot.fit {th : TypedHeap} (hP : Placed th) {a : U64} (h : IsSlot th a) : a.val + 32 ≤ 2 ^ 64 := by
  obtain ⟨p, i, hi, rfl⟩ := h
  obtain ⟨k, hk, hs⟩ := hi.size
  rw [hi.val hP]; have := hP.fits p k hk; omega

theorem IsSlot.align {th : TypedHeap} (hP : Placed th) {a : U64} (h : IsSlot th a) : a.val % 32 = 0 := by
  obtain ⟨p, i, hi, rfl⟩ := h; exact hi.aligned hP

theorem IsSlot.high {th : TypedHeap} (hP : Placed th) {a : U64} (h : IsSlot th a) : 2 ^ 64 - 2 ^ 47 ≤ a.val := by
  obtain ⟨p, i, hi, rfl⟩ := h
  obtain ⟨k, hk, -⟩ := hi.size
  rw [hi.val hP]; have := hP.high p k hk; omega

theorem IsSlot.apart {th : TypedHeap} (hP : Placed th) {a b : U64} (ha : IsSlot th a) (hb : IsSlot th b)
    (hne : a ≠ b) : a.val + 32 ≤ b.val ∨ b.val + 32 ≤ a.val := by
  obtain ⟨p, i, hi, rfl⟩ := ha
  obtain ⟨q, j, hj, rfl⟩ := hb
  exact hi.apart hP hj (fun ⟨h1, h2⟩ => hne (h1 ▸ h2 ▸ rfl))

theorem IsSlot.ne_zero {th : TypedHeap} (hP : Placed th) {a : U64} (h : IsSlot th a) : a ≠ 0#u64 := by
  rintro rfl; have := h.high hP; simp at this

end

end Fl4Proofs.P3
