/-
P3 (DESIGN.md §9), VSpace: `cdt::insert` writes only slot words
(`insert_frame2`; IntFrame's `insert_frame` for the words outside every
object), with the kernel-state base and the core kept.
-/
import Fl4Proofs.P3.IntFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

noncomputable section

section IFrame
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- `s'` agrees with `s` but at slot words of the typed heap. -/
def SlotFrame2 (th : TypedHeap) (s s' : S) : Prop :=
  L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ∧
    ∀ b, Aligned b → (¬ ∃ x k, IsSlot th x ∧ Off k ∧ b = wordOf x k) → L.mem s' b = L.mem s b

theorem SlotFrame2.refl (s : S) : SlotFrame2 (L := L) th s s := ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem SlotFrame2.wr' (hP : Placed th) {s s1 : S} (h : SlotFrame2 (L := L) th s s1) {a k : U64} (ha : IsSlot th a)
    (hk : Off k) (v : U64) : SlotFrame2 (L := L) th s (L.wr s1 (wordOf a k) v) := by
  refine ⟨by rw [L.ksb_wr]; exact h.1, by rw [L.cpu_wr]; exact h.2.1, fun b hb hn => ?_⟩
  rw [L.mem_wr _ _ _ _ (slot_word_aligned hP ha hk) hb, if_neg (fun e => hn ⟨a, k, ha, hk, e.symm⟩),
    h.2.2 b hb hn]

attribute [local step] set_cap_spec set_untyped_spec

/-- **`cdt::insert` writes only slot words.** -/
theorem insert_frame2 (hP : Placed th) (s : S) (c : capability.Cap) (src dest : U64)
    (hs : IsSlot th src) (hd : IsSlot th dest)
    (srcC : capability.Cap) (hsrcC : capAt (L.mem s) src = ok srcC)
    (hnx : nextOf (L.mem s) src = 0#u64 ∨ IsSlot th (nextOf (L.mem s) src)) :
    cdt.insert st s c src dest ⦃ s' => SlotFrame2 (L := L) th s s' ⦄ := by
  unfold cdt.insert
  rw [slot_cap_eq, hsrcC]
  simp only [bind_ok, is_cap_revocable_eq]
  step*
  all_goals
    have e2 : ∀ s1 : S, L.wr (L.wr s1 dest ⟨(encodeF c).1⟩) (core.num.U64.wrapping_add dest 8#u64) ⟨(encodeF c).2⟩ =
        wrCap (L := L) s1 dest c := fun _ => rfl
    subst_vars
    rw [e2]
  · cases hf : fullF srcC c <;> simp only [hf, wrCap_eq] <;>
      repeat (first
        | exact SlotFrame2.refl s
        | refine SlotFrame2.wr' hP ?_ (by assumption) (by first | exact off0 | exact off8 | exact off16 | exact off24) _)
  · have hz : nextOf (L.mem s) src ≠ 0#u64 := by
      intro h; simp_all only [decide_true, not_true_eq_false]
    have hn := hnx.resolve_left hz
    cases hf : fullF srcC c <;> simp only [hf, wrCap_eq] <;>
      repeat (first
        | exact SlotFrame2.refl s
        | refine SlotFrame2.wr' hP ?_ (by assumption) (by first | exact off0 | exact off8 | exact off16 | exact off24) _)

end IFrame

end

end Fl4Proofs.P3.Vs
