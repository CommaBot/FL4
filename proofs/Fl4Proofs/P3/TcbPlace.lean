/-
P3 (DESIGN.md §9), TCBs: **what the TCB cap installs give `JPlaced.step`**
(ScPlace). An install's slot frame `InstFr` (TcbCaps: every other slot's cap
kept, emptied or a zombie at home; the TCB's slots so or derived from a
slot's cap at the start, the fault-handler slot then an endpoint cap) gives
`JPlaced.step`'s slot hypotheses (`InstFr.jplaced`): the slots outside the
TCB's `ChgZ`, the TCB's slots typed when the caps at the start are, every
TCB's fault-handler slot kept, empty or an endpoint cap. A fault-handler
slot never holds a zombie at home (`not_homeZ_fault`: no object starts
there).
-/
import Fl4Proofs.P3.ScPlace
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1

noncomputable section

/-- A cap of the shape of a typed cap is typed. -/
theorem capTyped_of_shape {H : Heap} {Rp Nt : Set U64} {c c0 : capability.Cap} (hs : shape c = shape c0)
    (h : CapTyped H Rp Nt c0) : CapTyped H Rp Nt c := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun p b x y z w e => ?_, fun p b x y e => ?_, fun p g e => ?_⟩ <;> subst e <;>
    cases c0 <;> simp only [shape, reduceCtorEq, capability.Cap.Endpoint.injEq,
      capability.Cap.Notification.injEq, capability.Cap.Reply.injEq] at hs
  · exact h1 _ _ _ _ _ _ (by rw [hs.1])
  · exact h2 _ _ _ _ (by rw [hs.1])
  · exact h3 _ _ (by rw [hs.1])

/-- The address of a TCB's slot. -/
theorem tcb_slot_val {th : TypedHeap} (hP : Placed th) {t : U64} (ht : th t = some .tcb) {i : Nat}
    (hi : i < tcbSlots) : (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i)).val = t.val + 32 * i := by
  have he : cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i) = slotOf t i := by
    show slotAddr t.bv (Fl4Spec.ofBl _) = _
    rw [slotAddr_ofBl, tcbCnodeIndex_blVal i hi]
  rw [he]
  have hf := hP.fits t _ ht
  simp only [objSize] at hf
  simp only [tcbSlots] at hi
  exact slotOf_val (by omega)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **No zombie at home in a fault-handler slot**: a zombie at home names an
object starting at its slot (`DelInv.zwf`), and none starts inside a TCB. -/
theorem not_homeZ_fault {th : TypedHeap} (hP : Placed th) {m : U64 → U64} (hD : DelInv th m) {t : U64}
    (ht : th t = some .tcb) : ¬ HomeZ m (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) := by
  rintro ⟨zt, n, h⟩
  have hy : IsSlot th (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) :=
    AbsSlot.isSlot ⟨t, rfl, Or.inr ⟨ht, 3, by decide, rfl⟩⟩
  have hz := hD.zwf _ hy _ zt n h
  have hv := tcb_slot_val hP ht (i := 3) (by decide)
  obtain ⟨k, hk⟩ : ∃ k, th (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)) = some k := by
    rcases hz with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;> exact ⟨_, h1⟩
  have hne : t ≠ cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3) := fun e => by
    have := congrArg UScalar.val e; omega
  rcases hP.disj _ _ _ _ ht hk hne with h1 | h1 <;> simp only [objSize] at h1 <;> omega

/-- **`JPlaced.step`'s slot hypotheses from an install's slot frame**, with
`X` the TCB's slots: the other slots `ChgZ`; the TCB's slots typed when
every slot's cap at the start is; every TCB's fault-handler slot kept,
empty or an endpoint cap. -/
theorem InstFr.jplaced {th : TypedHeap} (hP : Placed th) {t : U64} (ht : th t = some .tcb) {m0 m : U64 → U64}
    (h : InstFr th t m0 m) (hD : DelInv th m) {H : Heap} {Rp Nt : Set U64}
    (hT0 : ∀ y, IsSlot th y → CapTyped H Rp Nt (capV m0 y)) :
    (∀ y, IsSlot th y → ¬ (∃ i, i < tcbSlots ∧ y = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i)) → ChgZ m0 m y) ∧
    (∀ y, IsSlot th y → (∃ i, i < tcbSlots ∧ y = cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex i)) →
      CapTyped H Rp Nt (capV m y)) ∧
    (∀ t', th t' = some .tcb →
      capV m (cslotAddr (t'.bv, Fl4Spec.tcbCnodeIndex 3)) = capV m0 (cslotAddr (t'.bv, Fl4Spec.tcbCnodeIndex 3)) ∨
      capV m (cslotAddr (t'.bv, Fl4Spec.tcbCnodeIndex 3)) = .Null ∨
      ∃ ep b0 b1 b2 b3 b4, capV m (cslotAddr (t'.bv, Fl4Spec.tcbCnodeIndex 3)) = .Endpoint ep b0 b1 b2 b3 b4) := by
  refine ⟨fun y hy hx => h.1 y hy (fun i hi e => hx ⟨i, hi, e⟩), fun y hy ⟨i, hi, e⟩ => ?_, fun t' ht' => ?_⟩
  · subst e
    rcases h.2 i hi with hz | ⟨⟨y0, hy0, hsh⟩, -⟩
    · exact capTyped_of_chgZ (hT0 _ hy) hz
    · exact capTyped_of_shape hsh (hT0 y0 hy0)
  · have hs3 : IsSlot th (cslotAddr (t'.bv, Fl4Spec.tcbCnodeIndex 3)) :=
      AbsSlot.isSlot ⟨t', rfl, Or.inr ⟨ht', 3, by decide, rfl⟩⟩
    have hz : ChgZ m0 m (cslotAddr (t'.bv, Fl4Spec.tcbCnodeIndex 3)) ∨
        ∃ ep b0 b1 b2 b3 b4, capV m (cslotAddr (t'.bv, Fl4Spec.tcbCnodeIndex 3)) = .Endpoint ep b0 b1 b2 b3 b4 := by
      by_cases e : t' = t
      · subst e
        rcases h.2 3 (by decide) with hz | ⟨-, hep⟩
        · exact Or.inl hz
        · exact Or.inr (hep rfl)
      · refine Or.inl (h.1 _ hs3 fun i hi e' => e ?_)
        have hA1 : AbsSlot th (t'.bv, Fl4Spec.tcbCnodeIndex 3) := ⟨t', rfl, Or.inr ⟨ht', 3, by decide, rfl⟩⟩
        have hA2 : AbsSlot th (t.bv, Fl4Spec.tcbCnodeIndex i) := ⟨t, rfl, Or.inr ⟨ht, i, hi, rfl⟩⟩
        exact (UScalar.eq_equiv_bv_eq t' t).2 (congrArg Prod.fst (cslotAddr_inj hP hA1 hA2 e'))
    rcases hz with (e | e | e) | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact absurd e (not_homeZ_fault hP hD ht')
    · exact Or.inr (Or.inr e)

end

end

end Fl4Proofs.P3.Sched
