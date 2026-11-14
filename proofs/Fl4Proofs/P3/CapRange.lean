/-
P3 (DESIGN.md §9): **ranges of caps** (`baseF`, `topF`: first and last byte,
FL4's `u64` arithmetic), and `Within` / `Disj` / `DisjR`. Moved here from
UntypedMdb / UntypedLoop so that `MdbStep` (before CnodeCopy) can use them.
-/
import Fl4Proofs.P3.MdbSem
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## Ranges of caps -/

theorem ptr_total (c : capability.Cap) : ∃ v, capability.Cap.ptr c = ok v := by cases c <;> exact ⟨_, rfl⟩
theorem phys_total (c : capability.Cap) : ∃ v, objects.cap_is_physical c = ok v := by cases c <;> exact ⟨_, rfl⟩
theorem size_total (c : capability.Cap) : ∃ v, objects.cap_size_bits c = ok v := by
  cases c <;> simp only [objects.cap_size_bits, frame_bits_eq, ite_ok_eq] <;> exact ⟨_, rfl⟩

def ptrF (c : capability.Cap) : U64 := Classical.choose (ptr_total c)
def physF (c : capability.Cap) : Bool := Classical.choose (phys_total c)
def sizeF (c : capability.Cap) : U64 := Classical.choose (size_total c)
theorem ptr_eq (c : capability.Cap) : capability.Cap.ptr c = ok (ptrF c) := Classical.choose_spec (ptr_total c)
theorem phys_eq (c : capability.Cap) : objects.cap_is_physical c = ok (physF c) := Classical.choose_spec (phys_total c)
theorem size_eq (c : capability.Cap) : objects.cap_size_bits c = ok (sizeF c) := Classical.choose_spec (size_total c)

/-- First and last byte of a cap's range (`u64` arithmetic, as FL4). -/
def baseF (c : capability.Cap) : Nat := (ptrF c).val
def topF (c : capability.Cap) : Nat := (core.num.U64.wrapping_add (ptrF c) (maskF (sizeF c))).val

theorem ok_inj {α : Type} {a b : α} (h : (ok a : Result α) = ok b) : a = b := by simpa using h

theorem ptrF_shape (c : capability.Cap) : ptrF (shape c) = ptrF c := by
  have h : capability.Cap.ptr (shape c) = capability.Cap.ptr c := by cases c <;> rfl
  rw [ptr_eq, ptr_eq] at h; exact ok_inj h
theorem physF_shape (c : capability.Cap) : physF (shape c) = physF c := by
  have h : objects.cap_is_physical (shape c) = objects.cap_is_physical c := by cases c <;> rfl
  rw [phys_eq, phys_eq] at h; exact ok_inj h
theorem sizeF_shape (c : capability.Cap) : sizeF (shape c) = sizeF c := by
  have h : objects.cap_size_bits (shape c) = objects.cap_size_bits c := by cases c <;> rfl
  rw [size_eq, size_eq] at h; exact ok_inj h

theorem shape_shape (c : capability.Cap) : shape (shape c) = shape c := by cases c <;> rfl

theorem range_of_shape {c c' : capability.Cap} (h : shape c = shape c') :
    baseF c = baseF c' ∧ topF c = topF c' ∧ physF c = physF c' := by
  unfold baseF topF
  rw [← ptrF_shape c, ← sizeF_shape c, ← physF_shape c, h, ptrF_shape, sizeF_shape, physF_shape]
  exact ⟨rfl, rfl, rfl⟩

/-- `b`'s range is inside `a`'s. -/
def Within (b a : capability.Cap) : Prop := baseF a ≤ baseF b ∧ topF b ≤ topF a
/-- The ranges of `a` and `b` do not meet. -/
def Disj (a b : capability.Cap) : Prop := topF a < baseF b ∨ topF b < baseF a
/-- `c`'s range misses `lo .. hi`. -/
def DisjR (c : capability.Cap) (lo hi : Nat) : Prop := topF c < lo ∨ hi ≤ baseF c

end

end Fl4Proofs.P3
