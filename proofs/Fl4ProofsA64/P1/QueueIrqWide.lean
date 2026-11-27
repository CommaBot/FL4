/-
P1 (aarch64): groundwork for widening the x86-shaped "IRQ handler caps name IRQs below 128" bound of the A64
deletion forms (`DelCapOK`, `W7.DelCapOK`, `DelPlaceAt.irq`, `W7.DelPlaceAt.irq`, `R.DelPlaceAt.irq`). On AArch64 the
GIC has `layout::irq::COUNT` = 5376 IRQs, so an IrqHandler cap can name an IRQ up to 5375 and P3 cannot supply
the `< 128` facts there (they would be false). This module proves the A64 IRQ-node slot fact for the full range:

* `irq_slotW_a64`: for `i < 5376`, the IRQ's handler slot (`IRQ_NODE` 43232 + 32·i, below `IOPORT_BITMAP`
  215264 and the ks area 223488) is a cap-slot word (`SlotW`); QueueFinCur's `irq_slotW` text with the bound.

The IRQ-state word of `post_cap_deletion` (`IRQ_STATE` 224 + 8·i < 43232) is likewise in range for `i < 5376`.
The widened `DelCapOK` / `DelPlaceAt.irq` forms and the deletion chain over them are the next step (with
QueueDecIrq). No named premises.
-/
import Fl4ProofsA64.P1.QueueFinCur
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

theorem irq_slotW_a64 {s : S} {i : U64} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hi : i.val < 5376) :
    SlotW T Ω Sg (irqSlotA (L.ksb s) i) := by
  have q := h.1.choose_spec.choose_spec
  have hSg := h.2.2.2.1
  have e : ∀ o : U64, o.val < 32 → core.num.U64.wrapping_add (irqSlotA (L.ksb s) i) o =
      core.num.U64.wrapping_add (L.ksb s) (core.num.U64.wrapping_add 43232#u64  -- a64: 1248->43232
        (core.num.U64.wrapping_add (core.num.U64.wrapping_mul i 32#u64) o)) := fun o ho => by
    apply UScalar.eq_of_val_eq
    simp [irqSlotA, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def,
      U64.numBits]
    omega
  have hv : ∀ o : U64, o.val < 32 → (core.num.U64.wrapping_add 43232#u64  -- a64: 1248->43232
      (core.num.U64.wrapping_add (core.num.U64.wrapping_mul i 32#u64) o)).val = 43232 + 32 * i.val + o.val :=  -- a64: 1248->43232
    fun o ho => by
      simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
      omega
  refine ⟨?_, fun o ho h8 => ?_⟩
  · have := e 0#u64 (by simp)
    have h0 : core.num.U64.wrapping_add (irqSlotA (L.ksb s) i) 0#u64 = irqSlotA (L.ksb s) i := by
      apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    rw [← h0, this]
    exact ks_aligned q (by rw [hv 0#u64 (by simp)]; simp; omega) (by rw [hv 0#u64 (by simp)]; simp; omega)
  · rw [e o ho]
    have hl : (core.num.U64.wrapping_add 43232#u64  -- a64: 1248->43232
        (core.num.U64.wrapping_add (core.num.U64.wrapping_mul i 32#u64) o)).val < 223488 := by rw [hv o ho]; omega  -- a64: 13568->223488
    have h8' : (core.num.U64.wrapping_add 43232#u64  -- a64: 1248->43232
        (core.num.U64.wrapping_add (core.num.U64.wrapping_mul i 32#u64) o)).val % 8 = 0 := by rw [hv o ho]; omega
    exact Or.inr ⟨hSg.ksΩ _ hl h8', fun hb' => by
      have := hSg.ks _ hb'; rw [ks_val q hl] at this; omega⟩


end

end Fl4ProofsA64.P1
