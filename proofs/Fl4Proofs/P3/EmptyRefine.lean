/-
P3 (DESIGN.md §9), CSpace: **`cdt::empty_slot` refines l4v `empty_slot`**
(nondeterministic spec, `Z = Unit`), for a CNode slot of the typed heap and
no cleanup cap.

`empty_slot_refines`: from related states and a slot holding a non-null cap,
FL4's `empty_slot slot Null` ends in a state related to the spec's single
outcome of `empty_slot slot NullCap`; the ghost tree loses the slot, whose
children get its parent (`Mdb.removePar`), as in the spec. A cleanup cap
other than `Null` (IRQ handler, IO port) runs `post_cap_deletion`, which
changes interrupt and arch state not related yet; it is not covered.
-/
import Fl4Proofs.P3.Empty
import Fl4Proofs.P3.MdbRemove
import Fl4Proofs.P3.InsertRefine
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- In a chain, the `next` of a slot is its successor (or 0 at the end). -/
theorem MdbLinks.next_eq_succ {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    {pre post : List U64} {a : U64} (hch : pre ++ a :: post ∈ G.chains) :
    nextOf mem a = (post.head?).getD 0#u64 := by
  have hc := hM.chain _ hch
  cases post with
  | nil => simpa using hM.last _ hch (by simp)
  | cons b post' =>
    rw [List.isChain_append] at hc
    simpa using (List.isChain_cons_cons.1 hc.2.1).1.1

theorem MdbLinks.prev_ne_next {th : TypedHeap} (hP : Placed th) {mem : U64 → U64} {G : MdbGhost}
    (hM : MdbLinks th mem G) {x : U64} (hx : x ∈ G.chains.flatten)
    (hp0 : prevOf mem x ≠ 0#u64) (hn0 : nextOf mem x ≠ 0#u64) : prevOf mem x ≠ nextOf mem x := by
  intro he
  obtain ⟨ch0, hch0, hxch⟩ := List.mem_flatten.1 hx
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hxch
  have hnd0 : (A ++ x :: B).Nodup := (List.nodup_flatten.1 hM.tree.nodup).1 _ hch0
  have hN := hM.next_eq_succ hch0
  cases B with
  | nil => exact hn0 (by simpa using hN)
  | cons b B' =>
    simp at hN
    -- `b`'s next is `x` (it is `x`'s prev)
    have h1 := (hM.prev_link hx hp0).2
    rw [he, hN] at h1
    have hb := hM.next_eq_succ (pre := A ++ [x]) (a := b) (post := B') (by simpa using hch0)
    rw [h1] at hb
    have hxs : x ≠ 0#u64 := (((hM.members x).1 hx).1).ne_zero hP
    cases B' with
    | nil => exact hxs (by simpa using hb)
    | cons y B'' =>
      simp at hb
      have := (Mdb.nodup_mid hnd0).2
      exact this (by simp [hb])

/-- The ghost tree after emptying `x`. -/
def remG (G : MdbGhost) (x : U64) : MdbGhost := ⟨Mdb.removeChains x G.chains, Mdb.removePar x G.par⟩

section
variable {S A : Type} {st : machine.Store S} [L : P1.LawfulStore st] {ar : machine.Arch A}

theorem empty_slot_refines (th : TypedHeap) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G)
    {px : U64} {rx : Nat} (hpx : th px = some (.cnode rx)) {idx : List Bool} (hl : idx.length = rx)
    {c : capability.Cap} (hc : capAt (L.mem s) (cslotAddr (px.bv, idx)) = ok c) (hcn : c ≠ .Null) :
    cdt.empty_slot st ar s a (cslotAddr (px.bv, idx)) .Null ⦃ r => r.2 = a ∧
      ∃ σ' G', Fl4Spec.emptySlot (Z := Unit) (px.bv, idx) .nullCap σ = ({((), σ')}, False) ∧
        StateRel th (L.mem r.1) σ' ∧ SlotsValid th (L.mem r.1) ∧ MdbLinks th (L.mem r.1) G' ∧
        CdtRel th (L.mem r.1) σ' G' ∧ G' = remG G (cslotAddr (px.bv, idx)) ⦄ := by
  have hAx : AbsSlot th (px.bv, idx) := ⟨px, rfl, Or.inl (by simpa [hl] using hpx)⟩
  have hx : IsSlot th (cslotAddr (px.bv, idx)) := hAx.isSlot
  have hxm : cslotAddr (px.bv, idx) ∈ G.chains.flatten := (hM.members _).2 ⟨hx, c, hc, hcn⟩
  have hslot : ∀ y, y ∈ G.chains.flatten → IsSlot th y := fun y h => ((hM.members y).1 h).1
  have hnx : nextOf (L.mem s) (cslotAddr (px.bv, idx)) = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s) (cslotAddr (px.bv, idx))) ∧
        nextOf (L.mem s) (cslotAddr (px.bv, idx)) ≠ cslotAddr (px.bv, idx)) := by
    rcases hM.next_mem hxm with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hslot _ h1, h2⟩
  have hpv : prevOf (L.mem s) (cslotAddr (px.bv, idx)) = 0#u64 ∨
      (IsSlot th (prevOf (L.mem s) (cslotAddr (px.bv, idx))) ∧
        prevOf (L.mem s) (cslotAddr (px.bv, idx)) ≠ cslotAddr (px.bv, idx)) := by
    by_cases h0 : prevOf (L.mem s) (cslotAddr (px.bv, idx)) = 0#u64
    · exact Or.inl h0
    · obtain ⟨h1, h2⟩ := hM.prev_link hxm h0
      refine Or.inr ⟨hslot _ h1, fun e => ?_⟩
      rw [e] at h2
      rcases hM.next_mem hxm with h | ⟨-, h⟩
      · rw [h] at h2; exact hx.ne_zero hP h2.symm
      · exact h h2
  have hPN := hM.prev_ne_next hP hxm
  have hNc : Canonical (nextOf (L.mem s) (cslotAddr (px.bv, idx))) := by
    rcases hnx with h | ⟨h, -⟩
    · rw [h]; exact canonical_zero
    · exact h.canonical hP
  obtain ⟨cs, hk, hwf, hs⟩ := hR.cnode px rx hpx
  obtain ⟨ac, hac, hrel⟩ := (hs idx hl).cap_eq hc
  have hget : Fl4Spec.getCap (Z := Unit) (px.bv, idx) σ = ({(ac, σ)}, False) := getCap_cnode hk hwf hac
  have hacn : ac ≠ .nullCap := fun h => hcn ((hrel.null_iff).1 h)
  apply WP.spec_mono (empty_slot_mem hP s a _ hx c hc hcn hpv hnx hPN)
  rintro r ⟨hW, hra⟩
  refine ⟨hra, ?_⟩
  -- the abstract state
  have hR1 : StateRel th (L.mem s) (emptySlotCdtState σ (px.bv, idx)) := StateRel.of_kheap hR rfl
  have hk1 : (emptySlotCdtState σ (px.bv, idx)).kheap px.bv = some (.cnode rx cs) := hk
  have hxEq : cslotAddr (px.bv, idx) = slotOf px (blVal 0 idx) := slotAddr_ofBl px idx
  have hcap' : ∀ y, IsSlot th y → capAt (L.mem r.1) y =
      if y = slotOf px (blVal 0 idx) then ok .Null else capAt (L.mem s) y := by
    intro y hy; rw [hW.capAt' hy, hxEq]
  obtain ⟨hR2, hV2⟩ := StateRel.update_cnode_slot hR1 hV hP hpx hk1 hwf hl
    (show CapRel .Null .nullCap from ⟨trivial, rfl⟩) trivial hcap'
  have h2 := setCap_cnode (Z := Unit) .nullCap hk1 hwf hl
  refine ⟨_, ⟨Mdb.removeChains (cslotAddr (px.bv, idx)) G.chains,
    Mdb.removePar (cslotAddr (px.bv, idx)) G.par⟩, emptySlot_eq hget hacn h2, hR2, hV2, ?_, ?_, rfl⟩
  · refine MdbLinks.remove hP hM hxm ⟨fun y hy => hW.prevOf' hy, fun y hy => hW.nextOf' hy hNc hPN, ?_, ?_⟩
    · rw [hW.capAt' hx]; simp
    · intro y hy hyx; rw [hW.capAt' hy]; simp [hyx]
  · exact CdtRel.remove hP hC _ hAx rfl rfl (fun y hy => hW.revOf' hy)

end

end

end Fl4Proofs.P3
