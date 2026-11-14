/-
P3 (DESIGN.md §9), scheduling contexts: **the slot writes of the
fault-handler install** on the FL4 side, in P1's terms.

* `SlotWd`: the cap-slot words of the typed heap; `ws_wr`, a write to one keeps
  `WritesIn … (SlotWd th)`.
* `empty_ws`, `insert_ws`: `cdt::empty_slot` (no cleanup cap) and
  `cdt::insert` write only cap-slot words (given the MDB neighbours are
  slots).
* `SlotCapW`: the placement hypothesis that the cap-slot words are P1's
  `CapW` words (a TCB slot below offset 160 of a TCB of `T`, a CNode slot
  in `Ω` outside the SC words `Sg`; P1 QueueSlots' docstring).
* `inst_hslot`: the slot part `hslot` of P1's `install_tcb_cap.cai` /
  `thread_control_sched.blkE`, from the MDB links and the cap relation of
  the state before the install.
-/
import Fl4Proofs.P1.QueueDelete
import Fl4Proofs.P3.ScBindSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3

noncomputable section
set_option linter.unusedSimpArgs false

section
variable {th : TypedHeap} {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}
  {ar : machine.Arch A}

/-- The cap-slot words of the typed heap. -/
def SlotWd (th : TypedHeap) (b : U64) : Prop := ∃ a, IsSlot th a ∧ ∃ k, Off k ∧ b = wordOf a k

theorem ws_wr (hP : Placed th) {s s1 : S} (h : P1.WritesIn st s s1 (SlotWd th)) {a k : U64} (ha : IsSlot th a)
    (hk : Off k) (v : U64) : P1.WritesIn st s (L.wr s1 (wordOf a k) v) (SlotWd th) :=
  ⟨by rw [L.ksb_wr]; exact h.1, by rw [L.cpu_wr]; exact h.2.1, fun b hb hn => by
    rw [L.mem_wr _ _ _ _ (slot_word_aligned hP ha hk) hb, if_neg (fun e => hn ⟨a, ha, k, hk, e.symm⟩)]
    exact h.2.2 b hb hn⟩

/-- **`cdt::empty_slot` (no cleanup cap) writes only cap-slot words.** -/
theorem empty_ws (hP : Placed th) (s : S) (a : A) (xs : U64) (hx : IsSlot th xs)
    (hpv : prevOf (L.mem s) xs = 0#u64 ∨ IsSlot th (prevOf (L.mem s) xs))
    (hnx : nextOf (L.mem s) xs = 0#u64 ∨ IsSlot th (nextOf (L.mem s) xs)) :
    cdt.empty_slot st ar s a xs .Null ⦃ r => P1.WritesIn st s r.1 (SlotWd th) ⦄ := by
  unfold cdt.empty_slot
  rw [slot_cap_eq, capAt_capV]
  simp only [bind_ok, cap_is_null_eq]
  split
  · exact (WP.spec_ok _).2 (P1.WritesIn.refl _ _)
  simp only [slot_prev_eq, slot_next_eq, slot_first_badged_eq, is_null_eq, bind_ok]
  have hc : ∀ s3 : S, P1.WritesIn st s s3 (SlotWd th) →
      (do let s4 ← obj.Slot.clear st xs s3; objects.post_cap_deletion st ar s4 a .Null) ⦃ r =>
        P1.WritesIn st s r.1 (SlotWd th) ⦄ := by
    intro s3 h3
    refine WP.spec_bind (slot_clear_spec xs s3) fun s4 e4 => ?_
    subst e4
    rw [post_null]
    rw [← wordOf_zero xs] at *
    refine (WP.spec_ok _).2 ?_
    exact ws_wr hP (ws_wr hP (ws_wr hP (ws_wr hP h3 hx off0 _) hx off8 _) hx off16 _) hx off24 _
  have hn : ∀ s1 : S, P1.WritesIn st s s1 (SlotWd th) → ∀ {N : U64}, IsSlot th N → ∀ (P : U64) (fb : Bool),
      (do
        let s3 ← obj.Slot.set_prev st N s1 P
        if fbOf (L.mem s3) N = true then obj.Slot.set_first_badged st N s3 true
          else obj.Slot.set_first_badged st N s3 fb) ⦃ s5 => P1.WritesIn st s s5 (SlotWd th) ⦄ := by
    intro s1 h1 N hN P fb
    refine WP.spec_bind (slot_set_prev_spec _ _ _) fun s3 e3 => ?_
    subst e3
    split
    all_goals
      refine WP.spec_mono (slot_set_first_badged_spec _ _ _) ?_
      rintro s5 rfl
      exact ws_wr hP (ws_wr hP h1 hN off16 _) hN off24 _
  by_cases hp0 : prevOf (L.mem s) xs = 0#u64 <;> by_cases hn0 : nextOf (L.mem s) xs = 0#u64 <;>
    simp only [hp0, hn0, decide_true, decide_false, ↓reduceIte, bind_ok, Bool.false_eq_true]
  · exact hc s (P1.WritesIn.refl _ _)
  · have hN := hnx.resolve_left hn0
    refine WP.spec_bind (hn s (P1.WritesIn.refl _ _) hN _ _) hc
  · have hPv := hpv.resolve_left hp0
    refine WP.spec_bind (slot_set_next_spec _ s _) fun s1 e1 => ?_
    subst e1
    exact hc _ (ws_wr hP (P1.WritesIn.refl _ _) hPv off24 _)
  · have hPv := hpv.resolve_left hp0
    have hN := hnx.resolve_left hn0
    refine WP.spec_bind (slot_set_next_spec _ s _) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hn _ (ws_wr hP (P1.WritesIn.refl _ _) hPv off24 _) hN _ _) hc

attribute [local step] set_cap_spec set_untyped_spec

/-- **`cdt::insert` writes only cap-slot words** (`insert_frame`'s proof). -/
theorem insert_ws (hP : Placed th) (s : S) (c : capability.Cap) (src dest : U64)
    (hs : IsSlot th src) (hd : IsSlot th dest)
    (srcC : capability.Cap) (hsrcC : capAt (L.mem s) src = ok srcC)
    (hnx : nextOf (L.mem s) src = 0#u64 ∨ IsSlot th (nextOf (L.mem s) src)) :
    cdt.insert st s c src dest ⦃ s' => P1.WritesIn st s s' (SlotWd th) ⦄ := by
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
        | exact P1.WritesIn.refl _ _
        | refine ws_wr hP ?_ (by assumption) (by first | exact off0 | exact off8 | exact off16 | exact off24) _)
  · have hz : nextOf (L.mem s) src ≠ 0#u64 := by
      intro h; simp_all only [decide_true, not_true_eq_false]
    have hn := hnx.resolve_left hz
    cases hf : fullF srcC c <;> simp only [hf, wrCap_eq] <;>
      repeat (first
        | exact P1.WritesIn.refl _ _
        | refine ws_wr hP ?_ (by assumption) (by first | exact off0 | exact off8 | exact off16 | exact off24) _)


/-- **The cap-slot words are P1's `CapW` words** (a placement hypothesis of
the typed heap against P1's sets: a TCB slot lies below offset 160 of a TCB
of `T`, a CNode slot in `Ω` outside the SC words `Sg`). -/
def SlotCapW (th : TypedHeap) (T Ω Sg : Set U64) : Prop := ∀ b, SlotWd th b → P1.CapW T Ω Sg b

/-- **The slot part of P1's `install_tcb_cap.cai`** (`hslot`): from any
state agreeing with `s` on the `CapW` words, `cdt::empty_slot` of the TCB
slot and, when `still_valid` holds, `cdt::insert` write only `CapW` words
(`empty_ws`, `insert_ws`, the MDB neighbours by `MdbLinks`). -/
theorem inst_hslot (hP : Placed th) {T Ω Sg : Set U64} (hSC : SlotCapW th T Ω Sg) {s : S} {G : MdbGhost}
    (hM : MdbLinks th (L.mem s) G) {root src : U64} (hr : IsSlot th root) (hs : IsSlot th src)
    (target slot : U64) (nc : capability.Cap) :
    ∀ (s1 : S) (a1 : A), (∀ b, P1.Aligned b → P1.CapW T Ω Sg b → L.mem s1 b = L.mem s b) →
      cdt.empty_slot st ar s1 a1 root .Null ⦃ r => P1.WritesIn st s1 r.1 (P1.CapW T Ω Sg) ∧
        tcb.still_valid st r.1 target slot nc src ⦃ b1 => b1 = true →
          cdt.insert st r.1 nc src root ⦃ s3 => P1.WritesIn st r.1 s3 (P1.CapW T Ω Sg) ⦄ ⦄ ⦄ := by
  intro s1 a1 hag
  have hSS : SlotsSame th (L.mem s) (L.mem s1) := fun a ha => by
    have w : ∀ k, Off k → L.mem s1 (wordOf a k) = L.mem s (wordOf a k) := fun k hk =>
      hag _ (slot_word_aligned hP ha hk) (hSC _ ⟨a, ha, k, hk, rfl⟩)
    refine ⟨by have := w _ off0; rwa [wordOf_zero] at this, w _ off8, w _ off16, w _ off24⟩
  have hM1 := hM.of_same hSS
  have hslot : ∀ y, y ∈ G.chains.flatten → IsSlot th y := fun y h => ((hM1.members y).1 h).1
  have hWm : ∀ {s' s'' : S}, P1.WritesIn st s' s'' (SlotWd th) → P1.WritesIn st s' s'' (P1.CapW T Ω Sg) :=
    fun h => h.mono hSC
  have hnm : ∀ y, IsSlot th y → capV (L.mem s1) y ≠ .Null →
      nextOf (L.mem s1) y = 0#u64 ∨ IsSlot th (nextOf (L.mem s1) y) := fun y hy hyn => by
    have hm := (hM1.members y).2 ⟨hy, _, capAt_capV _ _, hyn⟩
    rcases hM1.next_mem hm with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr (hslot _ h)
  have hins : ∀ s2 : S, (soB nc (capV (L.mem s2) src) = true →
      nextOf (L.mem s2) src = 0#u64 ∨ IsSlot th (nextOf (L.mem s2) src)) →
      tcb.still_valid st s2 target slot nc src ⦃ b1 => b1 = true →
        cdt.insert st s2 nc src root ⦃ s3 => P1.WritesIn st s2 s3 (P1.CapW T Ω Sg) ⦄ ⦄ := by
    intro s2 hn
    rw [still_valid_eq _ _ _ _ nc (hs.ne_zero hP)]
    refine (WP.spec_ok _).2 fun hb => ?_
    have h1 : soB nc (capV (L.mem s2) src) = true := by
      simp only [Bool.and_eq_true] at hb; exact hb.1
    exact WP.spec_mono (insert_ws hP s2 nc src root hs hr _ (capAt_capV _ _) (hn h1)) fun s3 h => hWm h
  by_cases hcn : capV (L.mem s1) root = .Null
  · rw [empty_slot_null ar s1 a1 root (by rw [capAt_capV, hcn]) .Null]
    refine (WP.spec_ok _).2 ⟨P1.WritesIn.refl _ _, hins s1 fun h1 => hnm src hs fun e => ?_⟩
    rw [e, soB_null_right] at h1; cases h1
  have hxm := (hM1.members root).2 ⟨hr, _, capAt_capV _ _, hcn⟩
  have hnx : nextOf (L.mem s1) root = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s1) root) ∧ nextOf (L.mem s1) root ≠ root) := by
    rcases hM1.next_mem hxm with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, h2⟩
  have hpv : prevOf (L.mem s1) root = 0#u64 ∨
      (IsSlot th (prevOf (L.mem s1) root) ∧ prevOf (L.mem s1) root ≠ root) := by
    by_cases h0 : prevOf (L.mem s1) root = 0#u64
    · exact Or.inl h0
    · obtain ⟨h1, h2⟩ := hM1.prev_link hxm h0
      refine Or.inr ⟨hslot _ h1, fun e => ?_⟩
      rw [e] at h2
      rcases hM1.next_mem hxm with h | ⟨-, h⟩
      · rw [h] at h2; exact hr.ne_zero hP h2.symm
      · exact h h2
  have hPN := hM1.prev_ne_next hP hxm
  have hNc : Canonical (nextOf (L.mem s1) root) := by
    rcases hnx with h | ⟨h, -⟩
    · rw [h]; exact canonical_zero
    · exact h.canonical hP
  refine WP.spec_mono (WP.spec_and (empty_ws hP s1 a1 root hr (hpv.imp_right And.left) (hnx.imp_right And.left))
    (empty_slot_mem hP s1 a1 root hr _ (capAt_capV _ _) hcn hpv hnx hPN)) ?_
  rintro r ⟨hw, hW, -⟩
  refine ⟨hWm hw, hins r.1 fun h1 => ?_⟩
  rw [hW.nextOf' hs hNc hPN]
  by_cases e1 : src = root
  · rw [if_pos e1]; exact Or.inl rfl
  rw [if_neg e1]
  split
  · exact hnx.imp_right And.left
  · refine hnm src hs fun e => ?_
    have hc := hW.capAt' hs
    rw [if_neg e1, capAt_capV, capAt_capV, e] at hc
    rw [Result.ok_injective hc, soB_null_right] at h1; cases h1

end

end

end Fl4Proofs.P3.Sched
