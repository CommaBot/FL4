/-
P3 (DESIGN.md §9), IPC: **`cdt::insert` changes the caps of the source and
the destination only** (`insert_capfr`; VsInsFrame's `insert_frame2` with
the caps of the other slots kept), for the cap transfer (IpcGrant.lean).
-/
import Fl4Proofs.P3.VsInsFrame
import Fl4Proofs.P3.MoveRefine
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

noncomputable section

/-! ## `cdt::insert` changes the caps of the source and destination only -/

section CapFr
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- `s'` agrees with `s` but at slot words, and on every slot's cap but
`src`'s and `dest`'s. -/
def CapFr (th : TypedHeap) (src dest : U64) (s s' : S) : Prop :=
  Vs.SlotFrame2 (L := L) th s s' ∧
    ∀ x, IsSlot th x → x ≠ src → x ≠ dest → capAt (L.mem s') x = capAt (L.mem s) x

theorem CapFr.refl (src dest : U64) (s : S) : CapFr (L := L) th src dest s s :=
  ⟨Vs.SlotFrame2.refl s, fun _ _ _ _ => rfl⟩

theorem CapFr.wr (hP : Placed th) {src dest : U64} {s s1 : S} (h : CapFr (L := L) th src dest s s1) {a k : U64}
    (ha : IsSlot th a) (hk : Off k) (hc : a = src ∨ a = dest ∨ k = 16#u64 ∨ k = 24#u64) (v : U64) :
    CapFr (L := L) th src dest s (L.wr s1 (wordOf a k) v) := by
  refine ⟨h.1.wr' hP ha hk v, fun x hx h1 h2 => ?_⟩
  rcases hc with rfl | rfl | hl | hl
  · rw [capAt_words, capAt_words, mem_wr_slot hP hx ha off0 hk, mem_wr_slot hP hx ha off8 hk,
      if_neg (fun e => h1 e.1), if_neg (fun e => h1 e.1), ← capAt_words, ← capAt_words]
    exact h.2 x hx h1 h2
  · rw [capAt_words, capAt_words, mem_wr_slot hP hx ha off0 hk, mem_wr_slot hP hx ha off8 hk,
      if_neg (fun e => h2 e.1), if_neg (fun e => h2 e.1), ← capAt_words, ← capAt_words]
    exact h.2 x hx h1 h2
  · rw [capAt_wr_link hP hx ha (Or.inl hl)]; exact h.2 x hx h1 h2
  · rw [capAt_wr_link hP hx ha (Or.inr hl)]; exact h.2 x hx h1 h2

open Vs in
attribute [local step] set_cap_spec set_untyped_spec in
/-- **`cdt::insert` changes the caps of the source and destination only.** -/
theorem insert_capfr (hP : Placed th) (s : S) (c : capability.Cap) (src dest : U64)
    (hs : IsSlot th src) (hd : IsSlot th dest)
    (srcC : capability.Cap) (hsrcC : capAt (L.mem s) src = ok srcC)
    (hnx : nextOf (L.mem s) src = 0#u64 ∨ IsSlot th (nextOf (L.mem s) src)) :
    cdt.insert st s c src dest ⦃ s' => CapFr (L := L) th src dest s s' ⦄ := by
  unfold cdt.insert cdt.insert_with_cap
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
        | exact CapFr.refl _ _ s
        | refine CapFr.wr hP ?_ (by assumption) (by first | exact off0 | exact off8 | exact off16 | exact off24)
            (by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr (Or.inl rfl)) |
              exact Or.inr (Or.inr (Or.inr rfl))) _)
  · have hz : nextOf (L.mem s) src ≠ 0#u64 := by
      intro h; simp_all only [decide_true, not_true_eq_false]
    have hn := hnx.resolve_left hz
    cases hf : fullF srcC c <;> simp only [hf, wrCap_eq] <;>
      repeat (first
        | exact CapFr.refl _ _ s
        | refine CapFr.wr hP ?_ (by assumption) (by first | exact off0 | exact off8 | exact off16 | exact off24)
            (by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr (Or.inl rfl)) |
              exact Or.inr (Or.inr (Or.inr rfl))) _)

end CapFr


section CapFr2
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- `s'` agrees with `s` but at slot words; the destination holds `c`; every
other slot's cap is kept, but the source's, which may be made full
(`set_untyped_cap_as_full`). -/
def CapFr2 (th : TypedHeap) (src dest : U64) (srcC c : capability.Cap) (s s' : S) : Prop :=
  Vs.SlotFrame2 (L := L) th s s' ∧ capAt (L.mem s') dest = ok c ∧
    ∀ x, IsSlot th x → x ≠ dest → capAt (L.mem s') x = capAt (L.mem s) x ∨
      (x = src ∧ ∃ c'', fullF srcC c = some c'' ∧ capAt (L.mem s') x = ok c'')

theorem CapFr2.link (hP : Placed th) {src dest : U64} {srcC c : capability.Cap} {s s1 : S}
    (h : CapFr2 (L := L) th src dest srcC c s s1) (hd : IsSlot th dest) {a k : U64}
    (ha : IsSlot th a) (hk : Off k) (hl : k = 16#u64 ∨ k = 24#u64) (v : U64) :
    CapFr2 (L := L) th src dest srcC c s (L.wr s1 (wordOf a k) v) := by
  refine ⟨h.1.wr' hP ha hk v, by rw [capAt_wr_link hP hd ha hl]; exact h.2.1, fun x hx hne => ?_⟩
  rw [capAt_wr_link hP hx ha hl]; exact h.2.2 x hx hne

/-- The base: the source made full or not, then the destination's cap. -/
theorem CapFr2.base (hP : Placed th) {src dest : U64} (hs : IsSlot th src) (hd : IsSlot th dest)
    {srcC c : capability.Cap} (hes : EncWf srcC) (he : EncWf c) (s : S) :
    CapFr2 (L := L) th src dest srcC c s (wrCap (L := L) (match fullF srcC c with
      | some c' => wrCap (L := L) s src c'
      | none => s) dest c) := by
  cases hf : fullF srcC c with
  | none =>
    simp only
    refine ⟨?_, by rw [capAt_wrCap hP s hd he hd, if_pos rfl], fun x hx hne => Or.inl ?_⟩
    · rw [wrCap_eq]
      exact ((Vs.SlotFrame2.refl s).wr' hP hd off0 _).wr' hP hd off8 _
    · rw [capAt_wrCap hP s hd he hx, if_neg hne]
  | some c'' =>
    simp only
    have he'' := (fullF_some hf hes).2.1
    refine ⟨?_, by rw [capAt_wrCap hP _ hd he hd, if_pos rfl], fun x hx hne => ?_⟩
    · rw [wrCap_eq, wrCap_eq]
      exact (((((Vs.SlotFrame2.refl s).wr' hP hs off0 _).wr' hP hs off8 _).wr' hP hd off0 _).wr' hP hd off8 _)
    · rw [capAt_wrCap hP _ hd he hx, if_neg hne, capAt_wrCap hP s hs he'' hx]
      by_cases e : x = src
      · rw [if_pos e]; exact Or.inr ⟨e, c'', hf, rfl⟩
      · rw [if_neg e]; exact Or.inl rfl

open Vs in
attribute [local step] set_cap_spec set_untyped_spec in
/-- **`cdt::insert` writes the new cap into the destination and keeps the
other slots' caps, but the source's, which may be made full.** -/
theorem insert_capfr2 (hP : Placed th) (s : S) (c : capability.Cap) (src dest : U64)
    (hs : IsSlot th src) (hd : IsSlot th dest)
    (srcC : capability.Cap) (hsrcC : capAt (L.mem s) src = ok srcC) (hes : EncWf srcC) (he : EncWf c)
    (hnx : nextOf (L.mem s) src = 0#u64 ∨ IsSlot th (nextOf (L.mem s) src)) :
    cdt.insert st s c src dest ⦃ s' => CapFr2 (L := L) th src dest srcC c s s' ⦄ := by
  unfold cdt.insert cdt.insert_with_cap
  rw [slot_cap_eq, hsrcC]
  simp only [bind_ok, is_cap_revocable_eq]
  step*
  all_goals
    have e2 : ∀ s1 : S, L.wr (L.wr s1 dest ⟨(encodeF c).1⟩) (core.num.U64.wrapping_add dest 8#u64) ⟨(encodeF c).2⟩ =
        wrCap (L := L) s1 dest c := fun _ => rfl
    subst_vars
    rw [e2]
  · repeat (first
      | exact CapFr2.base hP hs hd hes he s
      | refine CapFr2.link hP ?_ hd (by assumption) (by first | exact off16 | exact off24)
          (by first | exact Or.inl rfl | exact Or.inr rfl) _)
  · have hz : nextOf (L.mem s) src ≠ 0#u64 := by
      intro h; simp_all only [decide_true, not_true_eq_false]
    have hn := hnx.resolve_left hz
    repeat (first
      | exact CapFr2.base hP hs hd hes he s
      | refine CapFr2.link hP ?_ hd (by assumption) (by first | exact off16 | exact off24)
          (by first | exact Or.inl rfl | exact Or.inr rfl) _)

end CapFr2

end

end Fl4Proofs.P3.Ipc
