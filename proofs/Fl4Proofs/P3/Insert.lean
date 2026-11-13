/-
P3 (DESIGN.md §9), CSpace: `cdt::insert` (seL4 `cteInsert`) on the store:
`objects::is_cap_revocable` and `set_untyped_cap_as_full` as functions
(`revF`, `fullF`) against the spec's `is_cap_revocable` and
`set_untyped_cap_as_full` condition, and `insert_mem`: every word of every
slot after `insert`, with the cap, `prev`, `next` and `revocable` of each slot
(`InsWords.capAt'`, `prevOf'`, `nextOf'`, `revOf'`). The refinement theorem
is in InsertRefine.lean.
-/
import Fl4Proofs.P3.Mdb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section
set_option linter.unusedSimpArgs false

/-! ## The pure parts of `insert` -/

/-- `objects::is_cap_revocable`. -/
def revF : capability.Cap → capability.Cap → Bool
  | .Endpoint _ b _ _ _ _, .Endpoint _ b' _ _ _ _ => b != b'
  | .Endpoint .., _ => true
  | .Notification _ b _ _, .Notification _ b' _ _ => b != b'
  | .Notification .., _ => true
  | .IrqHandler _, .IrqControl => true
  | .Untyped .., _ => true
  | .IoPort .., .IoPortControl => true
  | _, _ => false

theorem is_cap_revocable_eq (d s : capability.Cap) : objects.is_cap_revocable d s = ok (revF d s) := by
  cases d <;> cases s <;> rfl

/-- The spec's `is_cap_revocable` on a badged cap reads the source cap's badge,
which is `undefined` unless the source is the same kind of cap; FL4 answers
`true`. Insert is only called with a derived cap of the source's kind. -/
def SameBadgeKind : capability.Cap → capability.Cap → Prop
  | .Endpoint .., .Endpoint .. => True
  | .Endpoint .., _ => False
  | .Notification .., .Notification .. => True
  | .Notification .., _ => False
  | _, _ => True

theorem revF_spec (d s : capability.Cap) (hk : SameBadgeKind d s) :
    (revF d s = true ↔ Fl4Spec.isCapRevocable (absCap d) (absCap s)) := by
  cases d <;> cases s <;> simp_all [SameBadgeKind, revF, Fl4Spec.isCapRevocable, absCap, Fl4Spec.archIsCapRevocable,
    Fl4Spec.capEpBadge, UScalar.eq_equiv_bv_eq, bne_iff_ne]

/-- `set_untyped_cap_as_full`: the new source cap, if any. -/
def fullF : capability.Cap → capability.Cap → Option capability.Cap
  | .Untyped p1 b1 _ dev, .Untyped p2 b2 _ _ =>
    if p1 = p2 ∧ b1 = b2 then some (.Untyped p1 b1 ⟨1#64 <<< (b1.val % 64)⟩ dev) else none
  | _, _ => none

section Store
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- The store after writing cap `c` into slot `sl` (`Slot::set_cap`). -/
def wrCap (s : S) (sl : U64) (c : capability.Cap) : S :=
  L.wr (L.wr s sl ⟨(encodeF c).1⟩) (core.num.U64.wrapping_add sl 8#u64) ⟨(encodeF c).2⟩

theorem set_untyped_spec (s : S) (srcC newC : capability.Cap) (src : obj.Slot) :
    cdt.set_untyped_cap_as_full st s srcC newC src ⦃ s' =>
      s' = match fullF srcC newC with
        | some c' => wrCap (L := L) s src c'
        | none => s ⦄ := by
  unfold cdt.set_untyped_cap_as_full
  cases srcC <;> cases newC <;> simp only [fullF, WP.spec_ok]
  case Untyped.Untyped p1 b1 f1 d1 p2 b2 f2 d2 =>
    by_cases h1 : p1 = p2
    · by_cases h2 : b1 = b2
      · subst h1 h2
        have : (b1 &&& 63#u64).val = b1.val % 64 := by simp; exact Nat.and_two_pow_sub_one_eq_mod b1.val 6
        simp only [↓reduceIte, and_self, lift, bind_ok]
        rw [shl_u64_eq _ _ (by omega), this]
        simp only [bind_ok]
        exact set_cap_spec (L := L) _ _ _
      · simp [h1, h2]
    · simp [h1]

end Store

/-- The spec's `set_untyped_cap_as_full` condition is FL4's. -/
theorem fullF_spec (srcC newC : capability.Cap) :
    (Fl4Spec.isUntypedCap (absCap srcC) = true ∧ Fl4Spec.isUntypedCap (absCap newC) = true ∧
      Fl4Spec.objRefOf (absCap srcC) = Fl4Spec.objRefOf (absCap newC) ∧
      Fl4Spec.capBitsUntyped (absCap srcC) = Fl4Spec.capBitsUntyped (absCap newC)) ↔
    (fullF srcC newC).isSome := by
  cases srcC <;> cases newC <;> simp [absCap, fullF, Fl4Spec.isUntypedCap, Fl4Spec.objRefOf,
    Fl4Spec.capBitsUntyped, UScalar.eq_equiv_bv_eq]
  intro _; rw [← UScalar.eq_equiv_bv_eq, UScalar.eq_equiv]

theorem fullF_some {srcC newC c' : capability.Cap} (h : fullF srcC newC = some c') (he : EncWf srcC) :
    CapRel c' (Fl4Spec.maxFreeIndexUpdate (absCap srcC)) ∧ EncWf c' ∧ c' ≠ .Null := by
  cases srcC <;> cases newC <;> simp [fullF] at h
  case Untyped.Untyped p1 b1 f1 d1 p2 b2 f2 d2 =>
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨hp, hb⟩ := he
    refine ⟨⟨trivial, ?_⟩, ⟨hp, hb⟩, by simp⟩
    simp only [absCap, Fl4Spec.maxFreeIndexUpdate, Fl4Spec.freeIndexUpdate, Fl4Spec.maxFreeIndex,
      Fl4Spec.untypedSzBits, Fl4Spec.Cap.untypedCap.injEq, true_and]
    show (1#64 <<< (b1.val % 64)).toNat = 2 ^ b1.val
    rw [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt hb]
    simp [Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_right (by decide) hb

/-! ## `insert` on the store -/

section InsertMem
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem wrCap_eq (s : S) (sl : U64) (c : capability.Cap) :
    wrCap (L := L) s sl c = L.wr (L.wr s (wordOf sl 0#u64) ⟨(encodeF c).1⟩) (wordOf sl 8#u64) ⟨(encodeF c).2⟩ := by
  rw [wordOf_zero]; rfl

theorem lit_ne : ((0#u64 = 8#u64) = False) ∧ ((0#u64 = 16#u64) = False) ∧ ((0#u64 = 24#u64) = False) ∧
    ((8#u64 = 0#u64) = False) ∧ ((8#u64 = 16#u64) = False) ∧ ((8#u64 = 24#u64) = False) ∧
    ((16#u64 = 0#u64) = False) ∧ ((16#u64 = 8#u64) = False) ∧ ((16#u64 = 24#u64) = False) ∧
    ((24#u64 = 0#u64) = False) ∧ ((24#u64 = 8#u64) = False) ∧ ((24#u64 = 16#u64) = False) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (apply eq_false; decide)

theorem off0 : Off 0#u64 := Or.inl rfl
theorem off8 : Off 8#u64 := Or.inr (Or.inl rfl)
theorem off16 : Off 16#u64 := Or.inr (Or.inr (Or.inl rfl))
theorem off24 : Off 24#u64 := Or.inr (Or.inr (Or.inr rfl))

attribute [local step] set_cap_spec set_untyped_spec

/-- The slot words after `cdt::insert c src dest` from `s`. -/
def InsWords (th : TypedHeap) (s s' : S) (c srcC : capability.Cap) (src dest : U64) : Prop :=
  ∀ a, IsSlot th a → ∀ k, Off k →
    L.mem s' (wordOf a k) =
      if a = dest then
        (if k = 0#u64 then ⟨(encodeF c).1⟩ else if k = 8#u64 then ⟨(encodeF c).2⟩ else
         if k = 16#u64 then src else
         ⟨setBitF (setBitF (setNextF (L.mem s (wordOf dest 24#u64)).bv (nextOf (L.mem s) src).bv) 48
            (revF c srcC)) 49 (revF c srcC)⟩)
      else if a = src then
        (if k = 24#u64 then ⟨setNextF (L.mem s (wordOf src 24#u64)).bv dest.bv⟩ else
         match fullF srcC c with
         | some c' => if k = 0#u64 then ⟨(encodeF c').1⟩ else if k = 8#u64 then ⟨(encodeF c').2⟩
                      else L.mem s (wordOf a k)
         | none => L.mem s (wordOf a k))
      else if nextOf (L.mem s) src ≠ 0#u64 ∧ a = nextOf (L.mem s) src ∧ k = 16#u64 then dest
      else L.mem s (wordOf a k)

set_option maxRecDepth 8000 in
/-- What `cdt::insert` does to the slots, word by word. -/
theorem insert_mem (hP : Placed th) (s : S) (c : capability.Cap) (src dest : U64)
    (hs : IsSlot th src) (hd : IsSlot th dest) (hne : src ≠ dest)
    (srcC : capability.Cap) (hsrcC : capAt (L.mem s) src = ok srcC)
    (hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src)) :
    cdt.insert st s c src dest ⦃ s' => InsWords (L := L) th s s' c srcC src dest ⦄ := by
  unfold cdt.insert
  rw [slot_cap_eq, hsrcC]
  simp only [bind_ok, is_cap_revocable_eq]
  step*
  all_goals
    unfold InsWords
    intro a ha k hk
    have e2 : ∀ s1 : S, L.wr (L.wr s1 dest ⟨(encodeF c).1⟩) (core.num.U64.wrapping_add dest 8#u64) ⟨(encodeF c).2⟩ =
        wrCap (L := L) s1 dest c := fun _ => rfl
    subst_vars
    rw [e2]
  · -- `next` is null
    have hz : nextOf (L.mem s) src = 0#u64 := of_decide_eq_true b_post.symm
    have hne' := Ne.symm hne
    clear * - hP ha hs hd hne hne' hz hk
    cases hf : fullF srcC c <;> simp only [hf, wrCap_eq] <;>
      simp only [mem_wr_slot hP, ha, hs, hd, hk, off0, off8, off16, off24, hz, ne_eq, not_true_eq_false,
        false_and, ↓reduceIte] <;>
      rcases hk with rfl | rfl | rfl | rfl <;> by_cases h1 : a = dest <;> by_cases h2 : a = src <;>
      (try subst h1) <;> (try subst h2) <;>
      first
      | exact absurd rfl hne
      | simp only [lit_ne, true_and, and_true, and_false, false_and, ↓reduceIte, and_self,
          not_false_eq_true, *]
  · have hz : nextOf (L.mem s) src ≠ 0#u64 := by
      intro h; simp_all only [decide_true, not_true_eq_false]
    obtain ⟨hn, hnd, hns⟩ := hnx.resolve_left hz
    have hne' := Ne.symm hne
    have hnd' := Ne.symm hnd
    have hns' := Ne.symm hns
    generalize hN : nextOf (L.mem s) src = N at *
    clear * - hP ha hs hd hn hne hne' hnd hns hnd' hns' hz hk
    cases hf : fullF srcC c <;> simp only [hf, wrCap_eq] <;>
      simp only [mem_wr_slot hP, ha, hs, hd, hn, hk, off0, off8, off16, off24, ne_eq, not_true_eq_false,
        false_and, ↓reduceIte] <;>
      rcases hk with rfl | rfl | rfl | rfl <;> by_cases h1 : a = dest <;> by_cases h2 : a = src <;>
      by_cases h3 : a = N <;>
      (try subst h1) <;> (try subst h2) <;> (try subst h3) <;>
      first
      | exact absurd rfl hne
      | exact absurd rfl hnd
      | exact absurd rfl hns
      | simp only [lit_ne, true_and, and_true, and_false, false_and, ↓reduceIte, and_self,
          not_false_eq_true, *]

section Fields
variable {s s' : S} {c srcC : capability.Cap} {src dest : U64}

theorem decode_enc (c : capability.Cap) (he : EncWf c) :
    capability.Cap.decode ⟨(encodeF c).1⟩ ⟨(encodeF c).2⟩ = ok c := by
  rw [decode_eq]; exact congrArg ok (decodeF_encodeF c he)

theorem InsWords.capAt' (hW : InsWords (L := L) th s s' c srcC src dest) {a : U64} (ha : IsSlot th a)
    (he : EncWf c) (hes : EncWf srcC) (hsrcC : capAt (L.mem s) src = ok srcC) :
    capAt (L.mem s') a =
      if a = dest then ok c else if a = src then ok ((fullF srcC c).getD srcC) else capAt (L.mem s) a := by
  rw [capAt_words, hW a ha _ off0, hW a ha _ off8]
  by_cases h1 : a = dest
  · simp [h1, decode_enc c he]
  · by_cases h2 : a = src
    · subst h2
      cases hf : fullF srcC c with
      | none => simp [h1, hf, lit_ne]; rw [← capAt_words]; exact hsrcC
      | some c' => simp [h1, hf, lit_ne, decode_enc c' (fullF_some hf hes).2.1]
    · simp [h1, h2, lit_ne]; rw [← capAt_words]

theorem InsWords.prevOf' (hW : InsWords (L := L) th s s' c srcC src dest) {a : U64} (ha : IsSlot th a)
    (hNs : nextOf (L.mem s) src ≠ src) :
    prevOf (L.mem s') a = if a = dest then src
      else if nextOf (L.mem s) src ≠ 0#u64 ∧ a = nextOf (L.mem s) src then dest else prevOf (L.mem s) a := by
  unfold prevOf; rw [hW a ha _ off16]
  by_cases h1 : a = dest
  · simp [h1, lit_ne]
  · by_cases h2 : a = src
    · subst h2
      have : a ≠ nextOf (L.mem s) a := Ne.symm hNs
      cases fullF srcC c <;> simp [h1, lit_ne, this]
    · simp [h1, h2]

theorem InsWords.nextOf' (hW : InsWords (L := L) th s s' c srcC src dest) (hP : Placed th) {a : U64} (ha : IsSlot th a)
    (hd : IsSlot th dest) (hne : src ≠ dest) (hN : Canonical (nextOf (L.mem s) src)) :
    nextOf (L.mem s') a = if a = dest then nextOf (L.mem s) src
      else if a = src then dest else nextOf (L.mem s) a := by
  rw [show nextOf (L.mem s') a = ⟨sextF (L.mem s' (wordOf a 24#u64)).bv⟩ from rfl, hW a ha _ off24]
  by_cases h1 : a = dest
  · simp only [h1, ↓reduceIte, lit_ne]
    rw [sextF_setBitF _ _ (Or.inr rfl), sextF_setBitF _ _ (Or.inl rfl), sextF_setNextF, sextF_canonical _ hN]
  · by_cases h2 : a = src
    · subst h2
      simp only [h1, ↓reduceIte]
      rw [sextF_setNextF, sextF_canonical _ (hd.canonical hP)]
    · simp only [h1, h2, ↓reduceIte, lit_ne, and_false]; rfl

theorem InsWords.revOf' (hW : InsWords (L := L) th s s' c srcC src dest) {a : U64} (ha : IsSlot th a)
    (hne : src ≠ dest) :
    revOf (L.mem s') a = if a = dest then revF c srcC else revOf (L.mem s) a := by
  rw [show revOf (L.mem s') a = (L.mem s' (wordOf a 24#u64)).bv.getLsbD 48 from rfl, hW a ha _ off24]
  by_cases h1 : a = dest
  · simp only [h1, ↓reduceIte, lit_ne]
    show (setBitF (setBitF _ 48 _) 49 _).getLsbD 48 = _
    rw [getLsbD_setBitF _ _ _ (Or.inr rfl) (Or.inl rfl), getLsbD_setBitF _ _ _ (Or.inl rfl) (Or.inl rfl)]
    simp
  · by_cases h2 : a = src
    · subst h2
      simp only [h1, ↓reduceIte]
      show (setNextF _ _).getLsbD 48 = _
      rw [getLsbD_setNextF _ _ 48 (le_refl _) (by decide)]; rfl
    · simp only [h1, h2, ↓reduceIte, lit_ne, and_false]; rfl

end Fields

end InsertMem

end

end Fl4Proofs.P3
