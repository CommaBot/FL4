/-
P3 (DESIGN.md §9), CSpace: FL4's `ensure_no_children` decides the spec's
`∃ c, cdt c = some slot` (`noChildren_of_adj`, discharging `NoChildrenRel`).

The ghost tree lays every slot out followed immediately by its descendants
(`MdbOK`), so a slot has a child iff the next slot of its chain descends
from it. FL4 decides that last question with `is_mdb_parent_of slot next`,
from the caps and the revocable/first-badged bits. That the bit-level test
agrees with the ghost tree for adjacent slots is the remaining MDB
invariant (`ParentAdj`, the content of seL4's `mdb_chunked`/`valid_badges`
reasoning); it is not a consequence of `MdbLinks`, which constrains the
links but not the caps.
-/
import Fl4Proofs.P3.CnodeCaps
import Fl4Proofs.P3.Move
import Fl4Proofs.P3.EmptyRefine
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## The ghost tree: children and the next slot -/

theorem MdbLinks.has_child_iff {th : TypedHeap} (hP : Placed th) {mem : U64 → U64} {G : MdbGhost}
    (hM : MdbLinks th mem G) {x : U64} (hx : x ∈ G.chains.flatten) :
    (∃ c, G.par c = some x) ↔ (nextOf mem x ≠ 0#u64 ∧ Mdb.Desc G.par (nextOf mem x) x) := by
  obtain ⟨ch, hch, hxch⟩ := List.mem_flatten.1 hx
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hxch
  have hN := hM.next_eq_succ hch
  obtain ⟨d, rest, hB, hd⟩ := hM.tree.seg _ hch A x B rfl
  constructor
  · rintro ⟨c, hc⟩
    have hcd : c ∈ d := (hd c).1 (Relation.TransGen.single hc)
    cases d with
    | nil => simp at hcd
    | cons d0 d' =>
      subst hB
      have hd0 : d0 ∈ G.chains.flatten := List.mem_flatten.2 ⟨_, hch, by simp⟩
      have hns : nextOf mem x = d0 := by rw [hN]; simp
      rw [hns]
      exact ⟨(((hM.members d0).1 hd0).1).ne_zero hP, (hd d0).2 (by simp)⟩
  · rintro ⟨-, hdesc⟩
    obtain ⟨b, -, hb⟩ := Relation.TransGen.tail'_iff.1 hdesc
    exact ⟨b, hb⟩

/-! ## The spec's children through `CdtRel` -/

theorem CdtRel.has_child_iff {Z : Type} {th : TypedHeap} (hP : Placed th) {mem : U64 → U64}
    {σ : Fl4Spec.State Z} {G : MdbGhost} (hC : CdtRel th mem σ G) {sl : Fl4Spec.CslotPtr} (hs : AbsSlot th sl) :
    (∃ c, σ.cdt c = some sl) ↔ ∃ a, G.par a = some (cslotAddr sl) := by
  constructor
  · rintro ⟨c, hc⟩
    have hcs := (hC.cdt_slot c sl hc).1
    refine ⟨cslotAddr c, ?_⟩
    rw [← hC.cdt c hcs, hc]; rfl
  · rintro ⟨a, ha⟩
    obtain ⟨c, hcs, rfl⟩ := hC.par_slot a _ ha
    have h1 := hC.cdt c hcs
    rw [ha] at h1
    cases hq : σ.cdt c with
    | none => rw [hq] at h1; cases h1
    | some q =>
      rw [hq] at h1
      have hqe : cslotAddr q = cslotAddr sl := by simpa using h1
      have hqs := (hC.cdt_slot c q hq).2
      exact ⟨c, by rw [hq, cslotAddr_inj hP hqs hs hqe]⟩

/-! ## FL4's test -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- Hypothesis (an MDB invariant): for every slot of the tree with a next
slot, FL4's `is_mdb_parent_of slot next` terminates and says whether
`next` descends from `slot` in the ghost tree. -/
def ParentAdj (th : TypedHeap) (s : S) (G : MdbGhost) : Prop :=
  ∀ x ∈ G.chains.flatten, nextOf (L.mem s) x ≠ 0#u64 →
    ∃ b, cdt.is_mdb_parent_of st s x (nextOf (L.mem s) x) = ok b ∧
      (b = true ↔ Mdb.Desc G.par (nextOf (L.mem s) x) x)

/-- **`ensure_no_children` decides the spec's "has children"**, at a slot
of the tree (a non-null cap). -/
theorem noChildren_of_adj (th : TypedHeap) (hP : Placed th) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hA : ParentAdj (L := L) th s G)
    (sl : Fl4Spec.CslotPtr) (hs : AbsSlot th sl) (hx : cslotAddr sl ∈ G.chains.flatten) :
    NoChildrenRel (st := st) s σ (cslotAddr sl) sl := by
  have h1 := hC.has_child_iff hP hs
  have h2 := hM.has_child_iff hP hx
  unfold NoChildrenRel cdt.ensure_no_children
  rw [slot_next_eq]
  simp only [bind_ok, obj.Slot.is_null]
  by_cases hn : nextOf (L.mem s) (cslotAddr sl) = 0#u64
  · have : ¬ ∃ x, σ.cdt x = some sl := fun h => (h2.1 (h1.1 h)).1 hn
    simp [hn, this]
  · obtain ⟨b, hb, hbd⟩ := hA _ hx hn
    simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte, hb, bind_ok]
    cases b
    · have : ¬ ∃ x, σ.cdt x = some sl := fun h => by
        have := (h2.1 (h1.1 h)).2; simp [← hbd] at this
      simp [this]
    · have : ∃ x, σ.cdt x = some sl := h1.2 (h2.2 ⟨hn, hbd.1 rfl⟩)
      simp [this]

end

end

end Fl4Proofs.P3
