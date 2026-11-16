/-
P3 (DESIGN.md §9), CSpace: **the frames of the CNode copies, moves and
swaps**, for the decodes' primitive-step traces (StepSem's `cslot` kind).

* `move_frame2`: `cdt::move_cap` writes only slot words (as VsInsFrame's
  `insert_frame2` for `cdt::insert`).
* `swap_frame2`: `cdt::swap` writes only slot words.
* `empty_frame2`: `cdt::empty_slot` with no cleanup cap writes only slot
  words; `set_cap_frame2`: `set_cap` writes only the slot's cap words.
* `insert_trace`, `move_trace`, `swap_trace`, `swap_for_delete_trace`: the
  frame and every other slot's cap kept.
* `capMove_nkn`, `capSwap_nkn`: the spec's `cap_move` and `cap_swap` are
  `CnK` (only CNodes, TCBs' caps, the CDT and the original bits change).
-/
import Fl4Proofs.P3.VsInsFrame
import Fl4Proofs.P3.Move
import Fl4Proofs.P3.SpecCnK
import Fl4Proofs.P3.Swap
import Fl4Proofs.P3.Empty
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

noncomputable section

section
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : LawfulStore st]

attribute [local step] set_cap_spec

/-- **`cdt::move_cap` writes only slot words.** -/
theorem move_frame2 (hP : Placed th) (s : S) (c : capability.Cap) (src dest : U64)
    (hs : IsSlot th src) (hd : IsSlot th dest)
    (hpv : prevOf (L.mem s) src = 0#u64 ∨ IsSlot th (prevOf (L.mem s) src))
    (hnx : nextOf (L.mem s) src = 0#u64 ∨ IsSlot th (nextOf (L.mem s) src)) :
    cdt.move_cap st s c src dest ⦃ s' => SlotFrame2 (L := L) th s s' ⦄ := by
  unfold cdt.move_cap
  rw [slot_prev_eq, slot_next_eq]
  simp only [bind_ok]
  have e2 : ∀ s1 : S, L.wr (L.wr s1 dest ⟨(encodeF c).1⟩) (core.num.U64.wrapping_add dest 8#u64) ⟨(encodeF c).2⟩ =
      wrCap (L := L) s1 dest c := fun _ => rfl
  by_cases hp0 : prevOf (L.mem s) src = 0#u64 <;> by_cases hn0 : nextOf (L.mem s) src = 0#u64 <;>
    simp only [is_null_eq, hp0, hn0, decide_true, decide_false, ↓reduceIte, bind_ok, Bool.false_eq_true] <;>
    step* <;> subst_vars <;> rw [e2, wrCap_eq]
  all_goals
    first
      | have hP' := hpv.resolve_left hp0
      | skip
  all_goals
    first
      | have hN' := hnx.resolve_left hn0
      | skip
  all_goals
    repeat (first
      | exact SlotFrame2.refl s
      | refine SlotFrame2.wr' hP ?_ (by assumption) (by first | exact off0 | exact off8 | exact off16 | exact off24) _)

/-- **`cdt::empty_slot` (no cleanup cap) writes only slot words.** -/
theorem empty_frame2 {A : Type} {ar : machine.Arch A} (hP : Placed th) (s : S) (a : A) (xs : U64) (hx : IsSlot th xs)
    (c : capability.Cap) (hc : capAt (L.mem s) xs = ok c)
    (hpv : prevOf (L.mem s) xs = 0#u64 ∨ IsSlot th (prevOf (L.mem s) xs))
    (hnx : nextOf (L.mem s) xs = 0#u64 ∨ IsSlot th (nextOf (L.mem s) xs)) :
    cdt.empty_slot st ar s a xs .Null ⦃ r => SlotFrame2 (L := L) th s r.1 ∧ r.2 = a ⦄ := by
  unfold cdt.empty_slot
  rw [slot_cap_eq, hc]
  simp only [bind_ok, cap_is_null_eq]
  cases hn : isNullB c
  · simp only [Bool.false_eq_true, ↓reduceIte, slot_prev_eq, slot_next_eq]
    by_cases hp0 : prevOf (L.mem s) xs = 0#u64 <;> by_cases hn0 : nextOf (L.mem s) xs = 0#u64 <;>
      simp only [is_null_eq, hp0, hn0, decide_true, decide_false, ↓reduceIte, bind_ok, Bool.false_eq_true,
        slot_first_badged_eq, ite_set_fb] <;>
      step* <;> subst_vars <;> refine ⟨?_, rfl⟩
    all_goals
      first
        | have hP' := hpv.resolve_left hp0
        | skip
    all_goals
      first
        | have hN' := hnx.resolve_left hn0
        | skip
    all_goals
      repeat (first
        | exact SlotFrame2.refl s
        | refine SlotFrame2.wr' hP ?_ (by assumption) (by first | exact off0 | exact off8 | exact off16 | exact off24) _)
  · simp only [↓reduceIte, WP.spec_ok]
    exact ⟨SlotFrame2.refl s, trivial⟩

/-- **`cdt::insert`'s trace**: slot words only, every slot's cap but the
source's and the destination's kept. -/
theorem insert_trace (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    {src dest : U64} (hsrc : src ∈ G.chains.flatten) (hd : IsSlot th dest) (hdest : dest ∉ G.chains.flatten)
    {srcC : capability.Cap} (hsrcC : capAt (L.mem s) src = ok srcC) (c : capability.Cap) (he : EncWf c) :
    cdt.insert st s c src dest ⦃ s' => SlotFrame2 (L := L) th s s' ∧
      ∀ y, IsSlot th y → y ≠ src → y ≠ dest → capV (L.mem s') y = capV (L.mem s) y ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hs := hslot src hsrc
  have hne : src ≠ dest := fun e => hdest (e ▸ hsrc)
  have hes : EncWf srcC := by rw [capAt_words] at hsrcC; exact decode_encWf hsrcC
  have hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrc with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, fun e => hdest (e ▸ h1), h2⟩
  have hnx' : nextOf (L.mem s) src = 0#u64 ∨ IsSlot th (nextOf (L.mem s) src) := by
    rcases hnx with h | h
    · exact Or.inl h
    · exact Or.inr h.1
  refine WP.spec_mono (WP.spec_and (insert_frame2 hP s c src dest hs hd srcC hsrcC hnx')
    (insert_mem hP s c src dest hs hd hne srcC hsrcC hnx)) ?_
  rintro s' ⟨hF, hW⟩
  refine ⟨hF, fun y hy h1 h2 => ?_⟩
  have := hW.capAt' hy he hes hsrcC
  rw [if_neg h2, if_neg h1, capAt_capV, capAt_capV] at this
  exact eq_of_ok_eq this

/-- **`cdt::move_cap`'s trace**: slot words only, every slot's cap but the
source's and the destination's kept. -/
theorem move_trace (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    {src dest : U64} (hsrc : src ∈ G.chains.flatten) (hd : IsSlot th dest) (hdest : dest ∉ G.chains.flatten)
    (c : capability.Cap) (he : EncWf c) :
    cdt.move_cap st s c src dest ⦃ s' => SlotFrame2 (L := L) th s s' ∧
      ∀ y, IsSlot th y → y ≠ src → y ≠ dest → capV (L.mem s') y = capV (L.mem s) y ⦄ := by
  have hslot : ∀ x, x ∈ G.chains.flatten → IsSlot th x := fun x h => ((hM.members x).1 h).1
  have hs := hslot src hsrc
  have hne : src ≠ dest := fun e => hdest (e ▸ hsrc)
  have hnx : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrc with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, fun e => hdest (e ▸ h1), h2⟩
  have hpv : prevOf (L.mem s) src = 0#u64 ∨
      (IsSlot th (prevOf (L.mem s) src) ∧ prevOf (L.mem s) src ≠ dest ∧ prevOf (L.mem s) src ≠ src) := by
    by_cases h0 : prevOf (L.mem s) src = 0#u64
    · exact Or.inl h0
    · obtain ⟨h1, h2⟩ := hM.prev_link hsrc h0
      refine Or.inr ⟨hslot _ h1, fun e => hdest (e ▸ h1), fun e => ?_⟩
      rw [e] at h2
      rcases hM.next_mem hsrc with h | ⟨-, h⟩
      · rw [h] at h2; exact hs.ne_zero hP h2.symm
      · exact h h2
  have or1 : ∀ {x : U64}, (x = 0#u64 ∨ (IsSlot th x ∧ x ≠ dest ∧ x ≠ src)) → x = 0#u64 ∨ IsSlot th x := by
    intro x h; rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h.1
  refine WP.spec_mono (WP.spec_and (move_frame2 hP s c src dest hs hd (or1 hpv) (or1 hnx))
    (move_mem hP s c src dest hs hd hne hpv hnx)) ?_
  rintro s' ⟨hF, hW⟩
  refine ⟨hF, fun y hy h1 h2 => ?_⟩
  have := hW.capAt' hy he hne
  rw [if_neg h2, if_neg h1, capAt_capV, capAt_capV] at this
  exact eq_of_ok_eq this

end

end

end Fl4Proofs.P3.Vs

namespace Fl4Proofs.P3.Ipc

noncomputable section

section
open Fl4Spec

/-- **`cap_move` changes CNodes, TCBs' caps, the CDT and the original bits
only.** -/
theorem capMove_nkn (c : Cap) (src dest : CslotPtr) : NKN (capMove (Z := Unit) c src dest) := by
  unfold capMove setCdt setOriginal
  repeat (first | exact nkn_getCap _ | exact nkn_setCap _ _ | exact nkn_doExtendedOp _ |
    exact nkn_pure _ | exact nkn_pure' _ | exact nkn_fail | exact nkn_gets _ | exact nkn_get |
    exact nkn_assert _ | exact nkn_get_put (fun σ => ⟨rfl, fun _ => Or.inl rfl⟩) |
    exact nkn_modify (fun σ => ⟨rfl, fun _ => Or.inl rfl⟩) | (refine nkn_bind ?_ (fun _ => ?_)) |
    (apply nkn_ite) | split)

/-- **`cap_swap` changes CNodes, TCBs' caps, the CDT and the original bits
only.** -/
theorem capSwap_nkn (c1 : Cap) (s1 : CslotPtr) (c2 : Cap) (s2 : CslotPtr) :
    NKN (capSwap (Z := Unit) c1 s1 c2 s2) := by
  unfold capSwap setCdt setOriginal
  repeat (first | exact nkn_getCap _ | exact nkn_setCap _ _ | exact nkn_doExtendedOp _ |
    exact nkn_pure _ | exact nkn_pure' _ | exact nkn_fail | exact nkn_gets _ | exact nkn_get |
    exact nkn_assert _ | exact nkn_get_put (fun σ => ⟨rfl, fun _ => Or.inl rfl⟩) |
    exact nkn_modify (fun σ => ⟨rfl, fun _ => Or.inl rfl⟩) | (refine nkn_bind ?_ (fun _ => ?_)) |
    (apply nkn_ite) | split)

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

set_option maxHeartbeats 16000000 in
theorem swap_frame2 (hP : Placed th) (s : S) (c1 c2 : capability.Cap) (s1 s2 : U64)
    (hs1 : IsSlot th s1) (hs2 : IsSlot th s2) (hne : s1 ≠ s2)
    (hP1 : prevOf (L.mem s) s1 = 0#u64 ∨ IsSlot th (prevOf (L.mem s) s1))
    (hN1 : nextOf (L.mem s) s1 = 0#u64 ∨ IsSlot th (nextOf (L.mem s) s1))
    (hP2 : prevOf (L.mem s) s2 = 0#u64 ∨ IsSlot th (prevOf (L.mem s) s2))
    (hN2 : nextOf (L.mem s) s2 = 0#u64 ∨ IsSlot th (nextOf (L.mem s) s2)) (he1 : EncWf c1) (he2 : EncWf c2) :
    cdt.swap st s c1 s1 c2 s2 ⦃ s' => Vs.SlotFrame2 (L := L) th s s' ⦄ := by
  unfold cdt.swap
  simp only [set_cap_eq, slot_prev_eq, slot_next_eq, slot_rev_eq, slot_first_badged_eq, is_null_eq,
    set_prev_eq, set_next_eq, set_rev_eq, set_fb_eq, set_next_flags_eq, bind_ok, bind_tc_ok, bind_ite_ok]
  simp only [prevOf_wrCap hP, nextOf_wrCap hP, revOf_wrCap hP, fbOf_wrCap hP, hs1, hs2]
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
      prevOf_setNextFlags hP, nextOf_setNextFlags hP, revOf_setNextFlags hP, fbOf_setNextFlags hP,
      capAt_setNextFlags hP,
      hk48, hk49, n4948, n4849, and_false, false_and, and_true, false_or, or_false, eq_self_iff_true, or_true, true_or, true_and, ne_eq, not_false_eq_true, not_true_eq_false,
      isSlot_ite, canonical_ite, hs1, hs2, hc1, hc2, canonical_zero, hs1z, hs2z, hne, hne',
      decide_false, decide_true, Bool.false_eq_true, ↓reduceIte, ite_self, hP1d, hN1d, hP2d, hN2d, he1, he2, *]
  all_goals rw [WP.spec_ok]
  all_goals simp only [wrCap_eq]
  all_goals
    repeat (first
      | exact Vs.SlotFrame2.refl s
      | refine Vs.SlotFrame2.wr' hP ?_ (by assumption) (by first | exact off0 | exact off8 | exact off16 | exact off24) _)


omit L in
/-- A linked slot's neighbours are null or slots. -/
theorem MdbLinks.nb {G : MdbGhost} {m : U64 → U64} (hP : Placed th) (hM : MdbLinks th m G) {x : U64}
    (hx : x ∈ G.chains.flatten) :
    (prevOf m x = 0#u64 ∨ IsSlot th (prevOf m x)) ∧ (nextOf m x = 0#u64 ∨ IsSlot th (nextOf m x)) := by
  have hslot : ∀ y, y ∈ G.chains.flatten → IsSlot th y := fun y h => ((hM.members y).1 h).1
  refine ⟨?_, ?_⟩
  · by_cases h0 : prevOf m x = 0#u64
    · exact Or.inl h0
    · exact Or.inr (hslot _ (hM.prev_link hx h0).1)
  · rcases hM.next_mem hx with h | ⟨h1, -⟩
    · exact Or.inl h
    · exact Or.inr (hslot _ h1)

/-- **`cdt::swap`'s trace**: slot words only, every slot's cap but the two
swapped ones kept. -/
theorem swap_trace (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    {s1 s2 : U64} (h1m : s1 ∈ G.chains.flatten) (h2m : s2 ∈ G.chains.flatten) (hne : s1 ≠ s2)
    (c1 c2 : capability.Cap) (he1 : EncWf c1) (he2 : EncWf c2) :
    cdt.swap st s c1 s1 c2 s2 ⦃ s' => Vs.SlotFrame2 (L := L) th s s' ∧
      ∀ y, IsSlot th y → y ≠ s1 → y ≠ s2 → capV (L.mem s') y = capV (L.mem s) y ⦄ := by
  have hs1 : IsSlot th s1 := ((hM.members _).1 h1m).1
  have hs2 : IsSlot th s2 := ((hM.members _).1 h2m).1
  obtain ⟨hP1, hN1⟩ := hM.nb hP h1m
  obtain ⟨hP2, hN2⟩ := hM.nb hP h2m
  refine WP.spec_mono (WP.spec_and (swap_frame2 hP s c1 c2 s1 s2 hs1 hs2 hne hP1 hN1 hP2 hN2 he1 he2)
    (swap_fields hP s c1 c2 s1 s2 hs1 hs2 hne he1 he2 hP1 hN1 hP2 hN2)) ?_
  rintro s' ⟨hF, hW⟩
  refine ⟨hF, fun y hy h1 h2 => ?_⟩
  have := (hW y hy).1
  rw [if_neg h2, if_neg h1, capAt_capV, capAt_capV] at this
  exact eq_of_ok_eq this


/-- **`set_cap` writes only the slot's cap words.** -/
theorem set_cap_frame2 (hP : Placed th) (s : S) (x : U64) (hx : IsSlot th x) (c : capability.Cap) :
    obj.Slot.set_cap st x s c ⦃ s' => Vs.SlotFrame2 (L := L) th s s' ⦄ := by
  refine WP.spec_mono (set_cap_spec x s c) ?_
  rintro s' rfl
  have e : L.wr (L.wr s x ⟨(encodeF c).1⟩) (core.num.U64.wrapping_add x 8#u64) ⟨(encodeF c).2⟩ =
      wrCap (L := L) s x c := rfl
  rw [e, wrCap_eq]
  exact Vs.SlotFrame2.wr' hP (Vs.SlotFrame2.wr' hP (Vs.SlotFrame2.refl s) hx off0 _) hx off8 _

/-- **`cap_swap_for_delete`'s trace**: slot words only, every slot's cap but
the two swapped ones kept (nothing, for one slot). -/
theorem swap_for_delete_trace (hP : Placed th) (s : S) (G : MdbGhost) (hM : MdbLinks th (L.mem s) G)
    {s1 s2 : U64} (h1m : s1 ∈ G.chains.flatten) (h2m : s2 ∈ G.chains.flatten) :
    cdt.cap_swap_for_delete st s s1 s2 ⦃ s' => Vs.SlotFrame2 (L := L) th s s' ∧
      ∀ y, IsSlot th y → y ≠ s1 → y ≠ s2 → capV (L.mem s') y = capV (L.mem s) y ⦄ := by
  unfold cdt.cap_swap_for_delete
  have heq : obj.Slot.Insts.CoreCmpPartialEqSlot.eq s1 s2 = ok (decide (s1 = s2)) := rfl
  rw [heq]
  simp only [bind_ok]
  by_cases hne : s1 = s2
  · simp only [hne, decide_true, ↓reduceIte, WP.spec_ok]
    exact ⟨Vs.SlotFrame2.refl s, fun _ _ _ _ => trivial⟩
  · simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte, slot_cap_eq, capAt_capV, bind_ok]
    have he1 : EncWf (capV (L.mem s) s1) := by
      have h := capAt_capV (L.mem s) s1; rw [capAt_words] at h; exact decode_encWf h
    have he2 : EncWf (capV (L.mem s) s2) := by
      have h := capAt_capV (L.mem s) s2; rw [capAt_words] at h; exact decode_encWf h
    exact swap_trace hP s G hM h1m h2m hne _ _ he1 he2

end

end

end Fl4Proofs.P3
