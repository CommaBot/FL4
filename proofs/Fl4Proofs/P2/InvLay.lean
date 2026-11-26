/-
# P2 (line hpzg, generation 8): layout premises of the frame-cap invocation path from P3 (`InvLay`)

stpost gen 13's `inv_pathsKF` (P2/InvBlk.lean) names three layout premises: [J] `hz` (`0 ∉ K.slots`), [J] `hcdt`
(`InvCdtJ`: a capability slot's CDT neighbours are capability slots) and [J] `hmap` (`InvMapJ`), besides `huf`.
From the bundled entry premise `SlJAt` (P3's `JAtZ` at the entry):

* **`slJAt_slot0`**: `0 ∉ K.slots`. `K.slots` is `{a | IsSlot Zx.th a}` (`SlJAtZ.slots`); a slot at address 0 would
  be slot 0 of an object at 0 (`IsSlotAt.val`, no wrap), and `JKern.h0` puts no object of `H` at 0 (a `Zx.th`
  object is one of `H`'s: `JPlaced.tcb` / `JPlaced.cnode`). **`hz_of`**: `inv_pathsKF`'s `hz`.
* **`slJAt_cdt`**: a capability slot's `PREV` word, when non-zero, and its `Slot.next`, when non-zero, are capability
  slots. An empty slot has null links (`DelInv.nc`); a non-empty one is in the MDB chains (`MdbLinks.members`,
  `JAtZ.mdbL`), whose neighbours are null or slots (`MdbLinks.nb`). **`invCdtJ_of`**: `InvCdtJ` for any `P`
  implying `SlJAt K`.

**`InvMapJ` is not derivable: it is false at P3's states** (finding, no lemma): a frame cap keeps its mapping
data (`mapped`, `asid`, `vaddr`) when the address space it was mapped in goes away. Deleting the last cap of the
VSpace root (`objects.finalise_cap` of a `Pml4` cap → `vspace.delete_asid`) clears the ASID pool entry, but
the frame caps that still name that ASID are not touched (seL4/l4v the same: `valid_cap` of a mapped page cap
asks only `asid ≤ mask asid_bits` and `vref < pptr_base`, not that the mapping exists; `unmap_page` checks
it). At such a state `localinv.small_page_entry` (via `find_vspace_for_asid`) is `none` for a mapped frame cap
with `asid ≠ 0`, so `InvMapJ`'s conclusion fails, while `JAtZ` holds. Fix (stpost's files): weaken `DelEnt`'s
`(mp = false ∨ asid = 0)` to `… ∨ localinv.small_page_entry st s asid va = ok none`. That is exactly what
`plan_with` leaves for a plan with `p.n ≤ p.pte`, since its `none` branch adds no PTE. Then show that the
decode's `unmap_page` writes nothing in that case: its re-walk is `find_vspace_for_asid` followed by
`lookup_pt_slot`, the same lookups `small_page_entry` makes, on the same gate-owned table words.

No named premise. No statement of an existing declaration changes; no `kernel_entry_reach*` is touched.
-/
import Fl4Proofs.P2.InvSeen
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **No capability slot at address 0** at a bundle state (module docstring). -/
theorem slJAt_slot0 {K : KLayout} {s : S} (h : SlJAt (L := L) K s) : (0#u64) ∉ K.slots := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  intro h0
  rw [B.slots] at h0
  obtain ⟨p, i, hsa, he⟩ := h0
  obtain ⟨Tr, Cq, hJ⟩ := B.j.jpl
  have hv := Fl4Proofs.P3.IsSlotAt.val hJ.pl hsa
  rw [← he] at hv
  have hp0 : p = 0#u64 := UScalar.eq_of_val_eq (by have h0v : (0#u64 : U64).val = 0 := rfl; omega)
  subst hp0
  have hH := B.j.kern.h0
  rcases hsa with ⟨r, hr, -⟩ | ⟨ht, -⟩
  · rw [hJ.cnode _ _ hr] at hH; cases hH
  · rw [(hJ.tcb _).1 ht] at hH; cases hH

/-- (hpzg gen 8) **`inv_pathsKF`'s `hz`** from the bundle. -/
theorem hz_of : ∀ (K : KLayout) (s : S), SlJAt (L := L) K s → (0#u64) ∉ K.slots :=
  fun _ _ h => slJAt_slot0 h

/-- **A capability slot's CDT neighbours are capability slots** at a bundle state (module docstring). -/
theorem slJAt_cdt {K : KLayout} {s : S} (h : SlJAt (L := L) K s) {sl : U64} (hsl : sl ∈ K.slots) :
    (L.mem s (core.num.U64.wrapping_add sl layout.cte.PREV) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add sl layout.cte.PREV) ∈ K.slots) ∧
    (∀ nx, obj.Slot.next st sl s = ok nx → nx ≠ 0#u64 → nx ∈ K.slots) := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  rw [B.slots] at hsl ⊢
  obtain ⟨Tr, Cq, hJ⟩ := B.j.jpl
  have hM := B.j.mdbL
  have ep : L.mem s (core.num.U64.wrapping_add sl layout.cte.PREV) = Fl4Proofs.P3.prevOf (L.mem s) sl := by
    unfold Fl4Proofs.P3.prevOf layout.cte.PREV; rfl
  rw [ep]
  by_cases hn : Fl4Proofs.P3.capV (L.mem s) sl = .Null
  · obtain ⟨hp0, hn0⟩ := B.j.del.nc sl hsl hn
    refine ⟨fun h => absurd hp0 h, fun nx hnx h => ?_⟩
    rw [Fl4Proofs.P3.slot_next_eq] at hnx
    rw [← ok_inj_ff hnx] at h
    exact absurd hn0 h
  · have hx : sl ∈ Zx.G.chains.flatten :=
      (hM.members sl).2 ⟨hsl, Fl4Proofs.P3.capV (L.mem s) sl, Fl4Proofs.P3.capAt_capV _ _, hn⟩
    obtain ⟨h1, h2⟩ := Fl4Proofs.P3.MdbLinks.nb hJ.pl hM hx
    refine ⟨fun h => h1.resolve_left h, fun nx hnx h => ?_⟩
    rw [Fl4Proofs.P3.slot_next_eq] at hnx
    rw [← ok_inj_ff hnx] at h ⊢
    exact h2.resolve_left h

/-- (hpzg gen 8) **`InvCdtJ` discharged** for every `P` implying `SlJAt K` (e.g. `inv_pathsKF`'s
`fun s => SlJAt K s ∧ InvQL …`). -/
theorem invCdtJ_of {K : KLayout} {P : S → Prop} (hP : ∀ s, P s → SlJAt (L := L) K s) : InvCdtJ st K P :=
  fun s _ hs hsl => slJAt_cdt (hP s hs) hsl

end

end Fl4Proofs.P2.PathObl
