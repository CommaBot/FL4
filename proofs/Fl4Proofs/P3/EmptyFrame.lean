/-
P3 (DESIGN.md §9), CSpace: **`cdt::empty_slot` writes only slot words**
(`SlotFrame`, IntFrame), for the frames of the decodes that delete
(DomKeep).
-/
import Fl4Proofs.P3.IntFrame
import Fl4Proofs.P3.Empty
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {th : TypedHeap} {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st] {ar : machine.Arch A}

set_option maxRecDepth 8000 in
/-- **`cdt::empty_slot` writes only slot words** (with no cleanup cap). -/
theorem empty_slot_frame (hP : Placed th) (s : S) (a : A) (xs : U64) (hx : IsSlot th xs)
    (c : capability.Cap) (hc : capAt (L.mem s) xs = ok c) (hcn : c ≠ .Null)
    (hpv : prevOf (L.mem s) xs = 0#u64 ∨ IsSlot th (prevOf (L.mem s) xs))
    (hnx : nextOf (L.mem s) xs = 0#u64 ∨ IsSlot th (nextOf (L.mem s) xs)) :
    cdt.empty_slot st ar s a xs .Null ⦃ r => SlotFrame (L := L) th s r.1 ⦄ := by
  unfold cdt.empty_slot
  rw [slot_cap_eq, hc]
  simp only [bind_ok, cap_is_null_eq, isNullB_false hcn, Bool.false_eq_true, ↓reduceIte, slot_prev_eq,
    slot_next_eq]
  by_cases hp0 : prevOf (L.mem s) xs = 0#u64 <;> by_cases hn0 : nextOf (L.mem s) xs = 0#u64 <;>
    simp only [is_null_eq, hp0, hn0, decide_true, decide_false, ↓reduceIte, bind_ok, Bool.false_eq_true,
      slot_first_badged_eq, ite_set_fb] <;>
    step* <;> subst_vars <;> try dsimp only
  all_goals
    have hpS : prevOf (L.mem s) xs ≠ 0#u64 → IsSlot th (prevOf (L.mem s) xs) := fun h => hpv.resolve_left h
    have hnS : nextOf (L.mem s) xs ≠ 0#u64 → IsSlot th (nextOf (L.mem s) xs) := fun h => hnx.resolve_left h
    first
      | (have hp1 := hpS ‹_›; have hn1 := hnS ‹_›)
      | (have hp1 := hpS ‹_›)
      | (have hn1 := hnS ‹_›)
      | skip
    repeat (first
      | exact P1.LawfulStore.total
      | exact SlotFrame.refl s
      | refine SlotFrame.wr' hP ?_ (by assumption) (by first | exact off0 | exact off8 | exact off16 | exact off24) _)

end

end

end Fl4Proofs.P3
