/-
# P2 (line p3mc, gen 34): `JAtZ.jpl` (P3's `JPlaced`) at the boot state

**`jpl_B`**: `JPlaced thB HB {tiB} {sciB} sB σB` (so `JAtZ.jpl` with `Tr = {tiB}`, `Cq = {sciB}`): `HB` well formed,
`thB` placed, its TCB the heap's, its IRQ CNodes `other 5` objects of `HB` (P3's `ksH`), the idle SC `sc 7`
(`0 + minSchedContextBits`), the block placement (`JKern`'s), and every slot fact by the null cap (`slot_null`).

No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootMdbF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical

noncomputable section

theorem nodeA_slot (i : U64) (hi : i.val < 128) : IsSlot thB (nodeA (bsL.ksb sB) i) := by
  rw [sB_ksb]
  have hv := nodeA_val (kb := kbB) kbB_fit' hi
  rw [kbB_val] at hv
  refine ⟨nodeA kbB i, 0, Or.inl ⟨0, ?_, by norm_num⟩, ?_⟩
  · unfold thB; rw [if_neg (by omega), if_pos (by omega)]
  · apply UScalar.eq_of_val_eq
    rw [slotOf_val (by omega)]; simp

theorem jpl_B : JPlaced (L := bsL) thB HB {tiB} {sciB} sB (σB (Z := Unit)) where
  heap := heapB_ok
  pl := placed_B
  tcb t := by
    constructor
    · intro h
      rcases thB_cases h with ⟨e, -⟩ | ⟨e, -⟩
      · rw [show t = tiB from eq_of_val' (by rw [e, tiB_val])]; exact HB_ti
      · cases e
    · intro h
      rcases HB_cases h with ⟨e, -⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨e, -⟩ | ⟨e, -⟩
      · rw [show t = tiB from eq_of_val' (by rw [e, tiB_val])]; exact thB_ti
      all_goals cases e
  cnode p r h := by
    rcases thB_cases h with ⟨-, e⟩ | ⟨e, g1, g2, g3⟩
    · cases e
    · cases e
      unfold HB
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      unfold Sched.ksH
      rw [kbB_val, if_pos ⟨by omega, by omega, by omega⟩]
  tr t h := by
    rcases thB_cases h with ⟨e, -⟩ | ⟨e, -⟩
    · exact eq_of_val' (by rw [e, tiB_val])
    · cases e
  sc c y n hc h := by
    obtain ⟨e, -, rfl⟩ := kheapB_sc h
    have hcv : c = sciB := by
      apply UScalar.eq_of_val_eq
      show c.bv.toNat = _
      rw [e, sciB_val]; decide
    subst hcv
    exact ⟨rfl, HB_sci⟩
  ks := jKern_boot.hks
  ksIn := jKern_boot.hksIn
  typed a ha := by
    rw [slot_null ha]
    exact ⟨fun _ _ _ _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h), fun _ _ h => (by cases h)⟩
  irq i hi := by
    rw [slot_null (nodeA_slot i hi)]
    exact ⟨fun _ _ _ _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h), fun _ _ h => (by cases h)⟩
  fh t ht := by
    left
    rw [cslot_tcb3]
    exact slot_null ⟨t, 3, Or.inr ⟨ht, by simp [tcbSlots]⟩, rfl⟩
  bfs t ht := by
    left
    rw [cslot_tcb2]
    exact slot_null ⟨t, 2, Or.inr ⟨ht, by simp [tcbSlots]⟩, rfl⟩
  cobj a ha := by rw [slot_null ha]; trivial

end

end Fl4Proofs.P2.BootSt
