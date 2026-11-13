/-
P3 (DESIGN.md §9), CSpace: `cdt::swap` (seL4 `cteSwap`) on the store, field
by field.
-/
import Fl4Proofs.P3.Fields
import Fl4Proofs.P3.MoveRefine
import Fl4Proofs.P3.Empty
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section
set_option linter.unusedSimpArgs false

theorem spec_eq_ok {α : Type} {m : Result α} {v : α} (h : m ⦃ r => r = v ⦄) : m = ok v := by
  revert h; cases m <;> simp [WP.spec_vis, WP.spec_div]

theorem bind_ite_ok {α β : Type} (c : Prop) [Decidable c] (a b : α) (f : α → Result β) :
    Std.bind (if c then ok a else ok b) f = f (if c then a else b) := by
  split <;> simp

section
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem set_prev_eq (sl : obj.Slot) (s : S) (p : obj.Slot) :
    obj.Slot.set_prev st sl s p = ok (L.wr s (wordOf sl 16#u64) p) := spec_eq_ok (slot_set_prev_spec sl s p)
theorem set_next_eq (sl : obj.Slot) (s : S) (n : obj.Slot) :
    obj.Slot.set_next st sl s n = ok (L.wr s (wordOf sl 24#u64) ⟨setNextF (L.mem s (wordOf sl 24#u64)).bv n.bv⟩) :=
  spec_eq_ok (slot_set_next_spec sl s n)
theorem set_rev_eq (sl : obj.Slot) (s : S) (v : Bool) :
    obj.Slot.set_revocable st sl s v = ok (L.wr s (wordOf sl 24#u64) ⟨setBitF (L.mem s (wordOf sl 24#u64)).bv 48 v⟩) :=
  spec_eq_ok (slot_set_revocable_spec sl s v)
theorem set_fb_eq (sl : obj.Slot) (s : S) (v : Bool) :
    obj.Slot.set_first_badged st sl s v =
      ok (L.wr s (wordOf sl 24#u64) ⟨setBitF (L.mem s (wordOf sl 24#u64)).bv 49 v⟩) :=
  spec_eq_ok (slot_set_first_badged_spec sl s v)
theorem set_cap_eq (sl : obj.Slot) (s : S) (c : capability.Cap) :
    obj.Slot.set_cap st sl s c = ok (wrCap (L := L) s sl c) := spec_eq_ok (set_cap_spec sl s c)
theorem slot_rev_eq (sl : obj.Slot) (s : S) : obj.Slot.revocable st sl s = ok (revOf (L.mem s) sl) :=
  spec_eq_ok (slot_revocable_spec sl s)

theorem canonical_ite (c : Prop) [Decidable c] (a b : U64) :
    Canonical (if c then a else b) = if c then Canonical a else Canonical b := by split <;> rfl

theorem hk48 : (48 : Nat) = 48 ∨ (48 : Nat) = 49 := Or.inl rfl
theorem hk49 : (49 : Nat) = 48 ∨ (49 : Nat) = 49 := Or.inr rfl
theorem n4948 : ((49 : Nat) = 48) = False := by decide
theorem n4849 : ((48 : Nat) = 49) = False := by decide

theorem isSlot_ite (c : Prop) [Decidable c] (a b : U64) :
    IsSlot th (if c then a else b) = if c then IsSlot th a else IsSlot th b := by split <;> rfl

/-- The slot fields after `cdt::swap c1 s1 c2 s2` (cap `c2` goes to `s1`,
`c1` to `s2`), in terms of the fields before. -/
def SwapFields (th : TypedHeap) (s s' : S) (c1 : capability.Cap) (s1 : U64) (c2 : capability.Cap) (s2 : U64) :
    Prop :=
  let m := L.mem s
  let pB := fun x => if nextOf m s1 ≠ 0#u64 ∧ x = nextOf m s1 then s2 else prevOf m x
  let nB := fun x => if prevOf m s1 ≠ 0#u64 ∧ x = prevOf m s1 then s2 else nextOf m x
  ∀ x, IsSlot th x →
    capAt (L.mem s') x = (if x = s2 then ok c1 else if x = s1 then ok c2 else capAt m x) ∧
    prevOf (L.mem s') x = (if nB s2 ≠ 0#u64 ∧ x = nB s2 then s1 else if x = s2 then prevOf m s1
      else if x = s1 then pB s2 else pB x) ∧
    nextOf (L.mem s') x = (if pB s2 ≠ 0#u64 ∧ x = pB s2 then s1 else if x = s2 then nextOf m s1
      else if x = s1 then nB s2 else nB x) ∧
    revOf (L.mem s') x = (if x = s2 then revOf m s1 else if x = s1 then revOf m s2 else revOf m x) ∧
    fbOf (L.mem s') x = (if x = s2 then fbOf m s1 else if x = s1 then fbOf m s2 else fbOf m x)

set_option maxHeartbeats 16000000 in
theorem swap_fields (hP : Placed th) (s : S) (c1 c2 : capability.Cap) (s1 s2 : U64)
    (hs1 : IsSlot th s1) (hs2 : IsSlot th s2) (hne : s1 ≠ s2) (he1 : EncWf c1) (he2 : EncWf c2)
    (hP1 : prevOf (L.mem s) s1 = 0#u64 ∨ IsSlot th (prevOf (L.mem s) s1))
    (hN1 : nextOf (L.mem s) s1 = 0#u64 ∨ IsSlot th (nextOf (L.mem s) s1))
    (hP2 : prevOf (L.mem s) s2 = 0#u64 ∨ IsSlot th (prevOf (L.mem s) s2))
    (hN2 : nextOf (L.mem s) s2 = 0#u64 ∨ IsSlot th (nextOf (L.mem s) s2)) :
    cdt.swap st s c1 s1 c2 s2 ⦃ s' => SwapFields (L := L) th s s' c1 s1 c2 s2 ⦄ := by
  unfold cdt.swap
  simp only [set_cap_eq, slot_prev_eq, slot_next_eq, slot_rev_eq, slot_first_badged_eq, is_null_eq,
    set_prev_eq, set_next_eq, set_rev_eq, set_fb_eq, bind_ok, bind_tc_ok, bind_ite_ok]
  simp only [prevOf_wrCap hP, nextOf_wrCap hP, revOf_wrCap hP, fbOf_wrCap hP, hs1, hs2]
  unfold SwapFields
  generalize hP1d : prevOf (L.mem s) s1 = P1 at *
  generalize hN1d : nextOf (L.mem s) s1 = N1 at *
  generalize hP2d : prevOf (L.mem s) s2 = P2 at *
  generalize hN2d : nextOf (L.mem s) s2 = N2 at *
  have hcN1 : Canonical N1 := by rcases hN1 with rfl | h; exact canonical_zero; exact h.canonical hP
  have hcN2 : Canonical N2 := by rcases hN2 with rfl | h; exact canonical_zero; exact h.canonical hP
  have hc1 := hs1.canonical hP
  have hc2 := hs2.canonical hP
  have hne' := Ne.symm hne
  rcases hP1 with hP1e | hP1s <;> rcases hN1 with hN1e | hN1s <;> rcases hP2 with hP2e | hP2s <;>
    rcases hN2 with hN2e | hN2s
  all_goals have hs1z := hs1.ne_zero hP
  all_goals have hs2z := hs2.ne_zero hP
  all_goals try (have hP1z := hP1s.ne_zero hP)
  all_goals try (have hN1z := hN1s.ne_zero hP)
  all_goals try (have hP2z := hP2s.ne_zero hP)
  all_goals try (have hN2z := hN2s.ne_zero hP)
  all_goals try (have hcN1 := hN1s.canonical hP)
  all_goals try (have hcN2 := hN2s.canonical hP)
  all_goals by_cases ha1 : s2 = N1 <;> by_cases ha2 : s2 = P1
  all_goals try (exfalso; simp_all; done)
  all_goals try subst ha1
  all_goals try subst ha2
  all_goals
    simp only [prevOf_wrCap hP, nextOf_wrCap hP, revOf_wrCap hP, fbOf_wrCap hP, prevOf_setPrev hP,
      nextOf_setPrev hP, revOf_setPrev hP, fbOf_setPrev hP, prevOf_setNext hP, nextOf_setNext hP,
      revOf_setNext hP, fbOf_setNext hP, prevOf_setBit hP, nextOf_setBit hP, revOf_setBit hP, fbOf_setBit hP,
      capAt_setPrev hP, capAt_setNext hP, capAt_setBit hP, capAt_wrCap hP,
      hk48, hk49, n4948, n4849, and_false, false_and, and_true, false_or, or_false, eq_self_iff_true, or_true, true_or, true_and, ne_eq, not_false_eq_true, not_true_eq_false,
      isSlot_ite, canonical_ite, hs1, hs2, hc1, hc2, canonical_zero, hs1z, hs2z, hne, hne',
      decide_false, decide_true, Bool.false_eq_true, ↓reduceIte, ite_self, hP1d, hN1d, hP2d, hN2d, he1, he2, *]
  all_goals rw [WP.spec_ok]
  all_goals try intro x hx
  all_goals try refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [prevOf_wrCap hP, nextOf_wrCap hP, revOf_wrCap hP, fbOf_wrCap hP, prevOf_setPrev hP,
      nextOf_setPrev hP, revOf_setPrev hP, fbOf_setPrev hP, prevOf_setNext hP, nextOf_setNext hP,
      revOf_setNext hP, fbOf_setNext hP, prevOf_setBit hP, nextOf_setBit hP, revOf_setBit hP, fbOf_setBit hP,
      capAt_setPrev hP, capAt_setNext hP, capAt_setBit hP, capAt_wrCap hP,
      hk48, hk49, n4948, n4849, and_false, false_and, and_true, false_or, or_false, eq_self_iff_true, or_true, true_or, true_and, ne_eq, not_false_eq_true, not_true_eq_false,
      isSlot_ite, canonical_ite, hs1, hs2, hc1, hc2, canonical_zero, hs1z, hs2z, hne, hne',
      decide_false, decide_true, Bool.false_eq_true, ↓reduceIte, ite_self, hP1d, hN1d, hP2d, hN2d, he1, he2, hx, *]

/-- The links after a swap, as a renaming by the transposition. -/
theorem RenLinks.swap (hP : Placed th) {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    {s1 s2 : U64} (h1m : s1 ∈ G.chains.flatten) (h2m : s2 ∈ G.chains.flatten) (hne : s1 ≠ s2)
    {c1 c2 : capability.Cap} (hc1 : c1 ≠ .Null) (hc2 : c2 ≠ .Null)
    (hF : ∀ x, IsSlot th x →
      capAt mem' x = (if x = s2 then ok c1 else if x = s1 then ok c2 else capAt mem x) ∧
      prevOf mem' x = (if (if prevOf mem s1 ≠ 0#u64 ∧ s2 = prevOf mem s1 then s2 else nextOf mem s2) ≠ 0#u64 ∧
          x = (if prevOf mem s1 ≠ 0#u64 ∧ s2 = prevOf mem s1 then s2 else nextOf mem s2) then s1
        else if x = s2 then prevOf mem s1
        else if x = s1 then (if nextOf mem s1 ≠ 0#u64 ∧ s2 = nextOf mem s1 then s2 else prevOf mem s2)
        else (if nextOf mem s1 ≠ 0#u64 ∧ x = nextOf mem s1 then s2 else prevOf mem x)) ∧
      nextOf mem' x = (if (if nextOf mem s1 ≠ 0#u64 ∧ s2 = nextOf mem s1 then s2 else prevOf mem s2) ≠ 0#u64 ∧
          x = (if nextOf mem s1 ≠ 0#u64 ∧ s2 = nextOf mem s1 then s2 else prevOf mem s2) then s1
        else if x = s2 then nextOf mem s1
        else if x = s1 then (if prevOf mem s1 ≠ 0#u64 ∧ s2 = prevOf mem s1 then s2 else nextOf mem s2)
        else (if prevOf mem s1 ≠ 0#u64 ∧ x = prevOf mem s1 then s2 else nextOf mem x))) :
    RenLinks th mem mem' (Equiv.swap s1 s2) G := by
  have hslot : ∀ a, a ∈ G.chains.flatten → IsSlot th a := fun a h => ((hM.members a).1 h).1
  have hz : ∀ a, a ∈ G.chains.flatten → a ≠ 0#u64 := fun a h => (hslot a h).ne_zero hP
  have hz1 := hz s1 h1m
  have hz2 := hz s2 h2m
  -- link facts
  have nl : ∀ u v, u ∈ G.chains.flatten → nextOf mem u = v → v ≠ 0#u64 → prevOf mem v = u := by
    intro u v hu h hv; subst h; exact (hM.next_link hu hv).2
  have pl : ∀ u v, v ∈ G.chains.flatten → prevOf mem v = u → u ≠ 0#u64 → nextOf mem u = v := by
    intro u v hv h hu; subst h; exact (hM.prev_link hv hu).2
  have nself : ∀ u, u ∈ G.chains.flatten → nextOf mem u ≠ u := by
    intro u hu; rcases hM.next_mem hu with h | ⟨-, h⟩
    · rw [h]; exact (hz u hu).symm
    · exact h
  have pself : ∀ u, u ∈ G.chains.flatten → prevOf mem u ≠ u := by
    intro u hu h
    have := pl u u hu h (hz u hu)
    exact nself u hu this
  have nmem : ∀ u, u ∈ G.chains.flatten → nextOf mem u = 0#u64 ∨ nextOf mem u ∈ G.chains.flatten := by
    intro u hu; rcases hM.next_mem hu with h | ⟨h, -⟩ <;> [exact Or.inl h; exact Or.inr h]
  have pmem : ∀ u, u ∈ G.chains.flatten → prevOf mem u = 0#u64 ∨ prevOf mem u ∈ G.chains.flatten := by
    intro u hu; by_cases h : prevOf mem u = 0#u64
    · exact Or.inl h
    · exact Or.inr (hM.prev_link hu h).1
  have hsw : ∀ y, y ≠ s1 → y ≠ s2 → Equiv.swap s1 s2 y = y := fun y a b => Equiv.swap_apply_of_ne_of_ne a b
  have e0 : Equiv.swap s1 s2 0#u64 = 0#u64 := hsw _ hz1.symm hz2.symm
  have hne' := Ne.symm hne
  have hP2s := pself s2 h2m
  have hN1s := nself s1 h1m
  have hP1s := pself s1 h1m
  have hN2s := nself s2 h2m
  refine ⟨e0, ?_, ?_, ?_⟩
  · intro a ha
    have hF' := fun x hx => (hF x hx).2.2
    by_cases h1 : a = s1
    · subst h1
      rw [Equiv.swap_apply_left, hF' s2 (hslot s2 h2m)]
      by_cases hN : nextOf mem a = s2
      · simp [hN, hz2]
      · have : nextOf mem a ≠ a := hN1s
        simp only [Ne.symm hN, and_false, ↓reduceIte, Ne.symm hP2s, ite_true, hsw _ this hN]
    by_cases h2 : a = s2
    · subst h2
      rw [Equiv.swap_apply_right, hF' s1 (hslot s1 h1m)]
      -- the guard `s1 = p2'` never holds
      have hg : ¬ ((if nextOf mem s1 ≠ 0#u64 ∧ a = nextOf mem s1 then a else prevOf mem a) ≠ 0#u64 ∧
          s1 = (if nextOf mem s1 ≠ 0#u64 ∧ a = nextOf mem s1 then a else prevOf mem a)) := by
        rintro ⟨-, h⟩
        by_cases hN : nextOf mem s1 ≠ 0#u64 ∧ a = nextOf mem s1
        · rw [if_pos hN] at h; exact hne h
        · rw [if_neg hN] at h
          apply hN
          have := pl _ _ ha h.symm hz1
          exact ⟨by rw [this]; exact hz _ ha, this.symm⟩
      rw [if_neg hg, if_neg hne, if_pos rfl]
      by_cases hP1 : prevOf mem s1 ≠ 0#u64 ∧ a = prevOf mem s1
      · rw [if_pos hP1]
        have hN2 : nextOf mem a = s1 := pl _ _ h1m hP1.2.symm hz2
        rw [hN2, Equiv.swap_apply_left]
      · rw [if_neg hP1]
        have h3 : nextOf mem a ≠ s1 := by
          intro h
          apply hP1
          have := nl _ _ ha h hz1
          exact ⟨by rw [this]; exact hz2, this.symm⟩
        exact (hsw _ h3 hN2s).symm
    · rw [hsw a h1 h2, hF' a (hslot a ha), if_neg h2, if_neg h1]
      have hp2 : ∀ q, (if nextOf mem s1 ≠ 0#u64 ∧ s2 = nextOf mem s1 then s2 else prevOf mem s2) = q →
          q ≠ 0#u64 → q = s2 ∨ (prevOf mem s2 = q ∧ nextOf mem q = s2 ∧ nextOf mem s1 ≠ s2) := by
        intro q hq hq0
        by_cases hc : nextOf mem s1 ≠ 0#u64 ∧ s2 = nextOf mem s1
        · rw [if_pos hc] at hq; exact Or.inl hq.symm
        · rw [if_neg hc] at hq
          refine Or.inr ⟨hq, pl _ _ h2m hq hq0, fun h => hc ⟨by rw [h]; exact hz2, h.symm⟩⟩
      by_cases hn1 : nextOf mem a = s1
      · have hPa : prevOf mem s1 = a := nl _ _ ha hn1 hz1
        rw [if_neg, if_pos ⟨by rw [hPa]; exact hz a ha, hPa.symm⟩, hn1, Equiv.swap_apply_left]
        rintro ⟨hq0, hq⟩
        rcases hp2 _ hq.symm (hq ▸ hq0) with h | ⟨-, h, -⟩
        · exact h2 h
        · rw [hn1] at h; exact hne h
      · by_cases hn2 : nextOf mem a = s2
        · have hPa : prevOf mem s2 = a := nl _ _ ha hn2 hz2
          have hc : ¬ (nextOf mem s1 ≠ 0#u64 ∧ s2 = nextOf mem s1) := by
            rintro ⟨-, h⟩
            have := nl _ _ h1m h.symm hz2
            exact h1 (this.symm.trans hPa).symm
          rw [if_pos, hn2, Equiv.swap_apply_right]
          rw [if_neg hc, hPa]; exact ⟨hz a ha, rfl⟩
        · rw [if_neg, if_neg, hsw _ hn1 hn2]
          · rintro ⟨-, h⟩
            exact hn1 (pl _ _ h1m h.symm (hz a ha))
          · rintro ⟨hq0, hq⟩
            rcases hp2 _ hq.symm (hq ▸ hq0) with h | ⟨-, h, -⟩
            · exact h2 h
            · exact hn2 h
  · intro a ha
    have hF' := fun x hx => (hF x hx).2.1
    by_cases h1 : a = s1
    · subst h1
      rw [Equiv.swap_apply_left, hF' s2 (hslot s2 h2m)]
      by_cases hP : prevOf mem a = s2
      · simp [hP, hz2]
      · have : prevOf mem a ≠ a := hP1s
        simp only [Ne.symm hP, and_false, ↓reduceIte, Ne.symm hN2s, ite_true, hsw _ this hP]
    by_cases h2 : a = s2
    · subst h2
      rw [Equiv.swap_apply_right, hF' s1 (hslot s1 h1m)]
      have hg : ¬ ((if prevOf mem s1 ≠ 0#u64 ∧ a = prevOf mem s1 then a else nextOf mem a) ≠ 0#u64 ∧
          s1 = (if prevOf mem s1 ≠ 0#u64 ∧ a = prevOf mem s1 then a else nextOf mem a)) := by
        rintro ⟨-, h⟩
        by_cases hN : prevOf mem s1 ≠ 0#u64 ∧ a = prevOf mem s1
        · rw [if_pos hN] at h; exact hne h
        · rw [if_neg hN] at h
          apply hN
          have := nl _ _ ha h.symm hz1
          exact ⟨by rw [this]; exact hz _ ha, this.symm⟩
      rw [if_neg hg, if_neg hne, if_pos rfl]
      by_cases hN1 : nextOf mem s1 ≠ 0#u64 ∧ a = nextOf mem s1
      · rw [if_pos hN1]
        have hP2 : prevOf mem a = s1 := nl _ _ h1m hN1.2.symm hz2
        rw [hP2, Equiv.swap_apply_left]
      · rw [if_neg hN1]
        have h3 : prevOf mem a ≠ s1 := by
          intro h
          apply hN1
          have := pl _ _ ha h hz1
          exact ⟨by rw [this]; exact hz2, this.symm⟩
        exact (hsw _ h3 hP2s).symm
    · rw [hsw a h1 h2, hF' a (hslot a ha), if_neg h2, if_neg h1]
      have hn2 : ∀ q, (if prevOf mem s1 ≠ 0#u64 ∧ s2 = prevOf mem s1 then s2 else nextOf mem s2) = q →
          q ≠ 0#u64 → q = s2 ∨ (nextOf mem s2 = q ∧ prevOf mem q = s2 ∧ prevOf mem s1 ≠ s2) := by
        intro q hq hq0
        by_cases hc : prevOf mem s1 ≠ 0#u64 ∧ s2 = prevOf mem s1
        · rw [if_pos hc] at hq; exact Or.inl hq.symm
        · rw [if_neg hc] at hq
          refine Or.inr ⟨hq, nl _ _ h2m hq hq0, fun h => hc ⟨by rw [h]; exact hz2, h.symm⟩⟩
      by_cases hp1 : prevOf mem a = s1
      · have hNa : nextOf mem s1 = a := pl _ _ ha hp1 hz1
        rw [if_neg, if_pos ⟨by rw [hNa]; exact hz a ha, hNa.symm⟩, hp1, Equiv.swap_apply_left]
        rintro ⟨hq0, hq⟩
        rcases hn2 _ hq.symm (hq ▸ hq0) with h | ⟨-, h, -⟩
        · exact h2 h
        · rw [hp1] at h; exact hne h
      · by_cases hp2 : prevOf mem a = s2
        · have hNa : nextOf mem s2 = a := pl _ _ ha hp2 hz2
          have hc : ¬ (prevOf mem s1 ≠ 0#u64 ∧ s2 = prevOf mem s1) := by
            rintro ⟨-, h⟩
            have := pl _ _ h1m h.symm hz2
            exact h1 (this.symm.trans hNa).symm
          rw [if_pos, hp2, Equiv.swap_apply_right]
          rw [if_neg hc, hNa]; exact ⟨hz a ha, rfl⟩
        · rw [if_neg, if_neg, hsw _ hp1 hp2]
          · rintro ⟨-, h⟩
            exact hp1 (nl _ _ h1m h.symm (hz a ha))
          · rintro ⟨hq0, hq⟩
            rcases hn2 _ hq.symm (hq ▸ hq0) with h | ⟨-, h, -⟩
            · exact h2 h
            · exact hp2 h
  · intro x
    have hcap := fun x hx => (hF x hx).1
    simp only [List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hys := hslot y hy
      by_cases h1 : y = s1
      · subst h1; rw [Equiv.swap_apply_left]
        exact ⟨hslot s2 h2m, c1, by rw [hcap s2 (hslot s2 h2m)]; simp, hc1⟩
      by_cases h2 : y = s2
      · subst h2; rw [Equiv.swap_apply_right]
        exact ⟨hslot s1 h1m, c2, by rw [hcap s1 (hslot s1 h1m)]; simp [hne], hc2⟩
      rw [hsw y h1 h2]
      obtain ⟨-, c, hc, hcn⟩ := (hM.members y).1 hy
      exact ⟨hys, c, by rw [hcap y hys, if_neg h2, if_neg h1]; exact hc, hcn⟩
    · rintro ⟨hx, c, hc, hcn⟩
      by_cases h1 : x = s1
      · subst h1; exact ⟨s2, h2m, Equiv.swap_apply_right _ _⟩
      by_cases h2 : x = s2
      · subst h2; exact ⟨s1, h1m, Equiv.swap_apply_left _ _⟩
      rw [hcap x hx, if_neg h2, if_neg h1] at hc
      exact ⟨x, (hM.members x).2 ⟨hx, c, hc, hcn⟩, hsw x h1 h2⟩

end

/-- The spec's CDT after a swap, as a renaming of the ghost tree. -/
theorem CdtRel.swap {Z : Type} {th : TypedHeap} (hP : Placed th) {mem mem' : U64 → U64}
    {σ σ' : Fl4Spec.State Z} {G : MdbGhost} (hC : CdtRel th mem σ G) (chains' : List (List U64))
    {sl1 sl2 : Fl4Spec.CslotPtr} (h1 : AbsSlot th sl1) (h2 : AbsSlot th sl2) (hne : sl1 ≠ sl2)
    (hcdt : σ'.cdt = fun r => ((σ.cdt (Equiv.swap sl1 sl2 r)).map (Equiv.swap sl1 sl2)))
    (hio : σ'.isOriginalCap = fun r => σ.isOriginalCap (Equiv.swap sl1 sl2 r))
    (hrev : ∀ a, IsSlot th a → revOf mem' a = revOf mem (Equiv.swap (cslotAddr sl1) (cslotAddr sl2) a)) :
    CdtRel th mem' σ' ⟨chains', Mdb.conjPar (Equiv.swap (cslotAddr sl1) (cslotAddr sl2)) G.par⟩ := by
  have hA : ∀ q, AbsSlot th q → AbsSlot th (Equiv.swap sl1 sl2 q) := by
    intro q hq
    by_cases e1 : q = sl1
    · rw [e1, Equiv.swap_apply_left]; exact h2
    · by_cases e2 : q = sl2
      · rw [e2, Equiv.swap_apply_right]; exact h1
      · rw [Equiv.swap_apply_of_ne_of_ne e1 e2]; exact hq
  have haddr : ∀ q, AbsSlot th q →
      cslotAddr (Equiv.swap sl1 sl2 q) = Equiv.swap (cslotAddr sl1) (cslotAddr sl2) (cslotAddr q) := by
    intro q hq
    by_cases e1 : q = sl1
    · rw [e1, Equiv.swap_apply_left, Equiv.swap_apply_left]
    · by_cases e2 : q = sl2
      · rw [e2, Equiv.swap_apply_right, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne e1 e2, Equiv.swap_apply_of_ne_of_ne
          (fun h => e1 (cslotAddr_inj hP hq h1 h)) (fun h => e2 (cslotAddr_inj hP hq h2 h))]
  have hcp : ∀ x, Mdb.conjPar (Equiv.swap (cslotAddr sl1) (cslotAddr sl2)) G.par x =
      (G.par (Equiv.swap (cslotAddr sl1) (cslotAddr sl2) x)).map (Equiv.swap (cslotAddr sl1) (cslotAddr sl2)) := by
    intro x; simp [Mdb.conjPar, Equiv.symm_swap]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro sl hsl
    show Option.map cslotAddr (σ'.cdt sl) = Mdb.conjPar _ G.par (cslotAddr sl)
    rw [hcdt, hcp, ← haddr sl hsl, ← hC.cdt _ (hA sl hsl)]
    beta_reduce
    cases hq : σ.cdt (Equiv.swap sl1 sl2 sl) with
    | none => simp
    | some q =>
      have hq' := (hC.cdt_slot _ _ hq).2
      simp [haddr q hq']
  · intro sl q hq
    rw [hcdt] at hq
    simp only [Option.map_eq_some_iff] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    obtain ⟨ha, hb⟩ := hC.cdt_slot _ _ hq0
    refine ⟨?_, hA _ hb⟩
    have := hA _ ha; simpa using this
  · intro sl hsl
    rw [hio, hrev _ hsl.isSlot, ← haddr sl hsl]
    exact hC.orig _ (hA sl hsl)
  · intro a b hab
    change Mdb.conjPar _ G.par a = some b at hab
    rw [hcp] at hab
    simp only [Option.map_eq_some_iff] at hab
    obtain ⟨b0, hb0, -⟩ := hab
    obtain ⟨sl0, hsl0, he0⟩ := hC.par_slot _ _ hb0
    refine ⟨Equiv.swap sl1 sl2 sl0, hA _ hsl0, ?_⟩
    rw [haddr _ hsl0, he0]; simp

end

end Fl4Proofs.P3
