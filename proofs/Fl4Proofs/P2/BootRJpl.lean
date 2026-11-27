/-
# P2 (line p3mc, gen 39, unit B): `JAtZ.jpl` (P3's `JPlaced`) at the second boot start

**`jpl_R`**: `JPlaced thR HR {tiB, tRw} {sciB, scRw} sR σR` (so `JAtZ.jpl` with `Tr = {tiB, tRw}`,
`Cq = {sciB, scRw}`), as gen 34's `jpl_B` at `(sB, σB)`: `HR` well formed, `thR` placed (`placed_R`), its two TCBs
the heap's, its IRQ CNodes `other 5` objects of `HR`, the spec's two SCs (`scRp`, the idle SC) `sc 7` objects of
`HR` in `Cq`, the block placement (`jKern_R`'s), and every slot fact by `slotR_cases` (each slot holds the null cap
or, at the root slot, `Thread tRw`: no endpoint, notification, reply, frame or SC cap; slots 2 and 3 of a TCB are
not the root slot, so null).

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.BootRMdbF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical

noncomputable section

theorem uB_nodeA_slot (i : U64) (hi : i.val < 128) : IsSlot thR (nodeA (bsL.ksb sR) i) := by
  rw [sR_ksb]
  have hv := nodeA_val (kb := kbB) kbB_fit' hi
  rw [kbB_val] at hv
  refine ⟨nodeA kbB i, 0, Or.inl ⟨0, ?_, by norm_num⟩, ?_⟩
  · unfold thR thB; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  · apply UScalar.eq_of_val_eq
    rw [slotOf_val (by omega)]; simp

theorem uB_typed_R {a : U64} (ha : IsSlot thR a) :
    CapTyped HR (Heap.replies HR) (Heap.ntfns HR) (capV (bsL.mem sR) a) := by
  rcases slotR_cases ha with rfl | ⟨hn, -⟩
  · rw [capV_R_root]
    exact ⟨fun _ _ _ _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h), fun _ _ h => (by cases h)⟩
  · rw [hn]
    exact ⟨fun _ _ _ _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h), fun _ _ h => (by cases h)⟩

/-- A TCB slot of `thR` but slot 0 is not the root slot. -/
theorem uB_slot_ne {t : U64} (ht : thR t = some .tcb) {i : Nat} (h0 : 0 < i) (h6 : i < tcbSlots) :
    slotOf t i ≠ tRw := by
  simp only [tcbSlots] at h6
  intro e
  have := congrArg UScalar.val e
  rcases thR_cases ht with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [slotOf_val (by omega), tRw_val] at this; omega
  · rw [slotOf_val (by omega), tRw_val] at this; omega
  · cases h1

theorem jpl_R : JPlaced (L := bsL) thR HR {tiB, tRw} {sciB, scRw} sR (σR (Z := Unit)) where
  heap := heapR_ok
  pl := placed_R
  tcb t := by
    constructor
    · intro h
      rcases thR_cases h with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
      · rw [show t = tRw from eq_of_val'' (by rw [e, tRw_val])]; exact HR_tR
      · rw [show t = tiB from eq_of_val'' (by rw [e, tiB_val])]; exact HR_ti
      · cases e
    · intro h
      rcases HR_cases h with ⟨e, -⟩ | ⟨-, e⟩ | ⟨e, -⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨e, -⟩ | ⟨e, -⟩
      · rw [show t = tRw from eq_of_val'' (by rw [e, tRw_val])]; exact thR_tR
      · cases e
      · rw [show t = tiB from eq_of_val'' (by rw [e, tiB_val])]; exact thR_ti
      all_goals cases e
  cnode p r h := by
    rcases thR_cases h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨e, g1, g2, g3⟩
    · cases e
    · cases e
    · cases e
      unfold HR HB
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      unfold Sched.ksH
      rw [kbB_val, if_pos ⟨by omega, by omega, by omega⟩]
  tr t h := by
    rcases thR_cases h with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact Or.inr (eq_of_val'' (by rw [e, tRw_val]))
    · exact Or.inl (eq_of_val'' (by rw [e, tiB_val]))
    · cases e
  sc c y n hc h := by
    rcases kheapR_cases h with ⟨e, he⟩ | ⟨e, he⟩ | ⟨-, -, hB⟩
    · cases he
    · cases he
      have hcv : c = scRw := by
        apply UScalar.eq_of_val_eq
        show c.bv.toNat = _
        rw [e, scRw_val]; decide
      subst hcv
      exact ⟨Or.inr rfl, HR_scR⟩
    · obtain ⟨e, -, rfl⟩ := kheapB_sc hB
      have hcv : c = sciB := by
        apply UScalar.eq_of_val_eq
        show c.bv.toNat = _
        rw [e, sciB_val]; decide
      subst hcv
      exact ⟨Or.inl rfl, HR_sci⟩
  ks := jKern_R.hks
  ksIn := jKern_R.hksIn
  typed a ha := uB_typed_R ha
  irq i hi := uB_typed_R (uB_nodeA_slot i hi)
  fh t ht := by
    left
    rw [cslot_tcb3]
    exact uB_null ⟨t, 3, Or.inr ⟨ht, by simp [tcbSlots]⟩, rfl⟩ (uB_slot_ne ht (by decide) (by simp [tcbSlots]))
  bfs t ht := by
    left
    rw [cslot_tcb2]
    exact uB_null ⟨t, 2, Or.inr ⟨ht, by simp [tcbSlots]⟩, rfl⟩ (uB_slot_ne ht (by decide) (by simp [tcbSlots]))
  cobj a ha := by
    rcases slotR_cases ha with rfl | ⟨hn, -⟩
    · rw [capV_R_root]; trivial
    · rw [hn]; trivial

end

end Fl4Proofs.P2.BootSt
