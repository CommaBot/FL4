/-
P3 (DESIGN.md §9), CSpace: **the invariant and the measures of `rec_del`**.

`DelInv`: every zombie cap is well formed (its object a CNode of its radix
or a TCB, its count within the object), no two zombies cover the same
object, and an empty slot has clear MDB links (`cdt::empty_slot` and
`cdt::move_cap` clear the slot; l4v: an empty slot has a null MDB node).

The measures bound the rounds of FL4's loops: `nnS` is the set of linked
(non-empty) slots, `mzS` those of them not holding a zombie in its own
first slot ("at home"). A round of the deferred loop that swaps a zombie
home takes a slot out of `mzS`.
-/
import Fl4Proofs.P3.DelFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- A well-formed zombie: over a TCB (type 65, at most 5 slots) or over a
CNode of radix `zt` (at most `2 ^ zt` slots). -/
def ZOK (th : TypedHeap) (p zt n : U64) : Prop :=
  (zt.val = 65 ∧ th p = some .tcb ∧ n.val ≤ tcbSlots) ∨
  (zt.val ≠ 65 ∧ th p = some (.cnode zt.val) ∧ n.val ≤ 2 ^ zt.val)

/-- The slot `y` holds a zombie at home (in the zombie's first slot). -/
def HomeZ (mem : U64 → U64) (y : U64) : Prop := ∃ zt n, capV mem y = .Zombie y zt n

structure DelInv (th : TypedHeap) (mem : U64 → U64) : Prop where
  zwf : ∀ y, IsSlot th y → ∀ p zt n, capV mem y = .Zombie p zt n → ZOK th p zt n
  zu : ∀ y y', IsSlot th y → IsSlot th y' → y ≠ y' → ∀ p zt n p' zt' n',
    capV mem y = .Zombie p zt n → capV mem y' = .Zombie p' zt' n' → p ≠ p'
  nc : ∀ y, IsSlot th y → capV mem y = .Null → prevOf mem y = 0#u64 ∧ nextOf mem y = 0#u64

/-! ## Measures -/

/-- The linked slots. -/
def nnS (G : MdbGhost) : Finset U64 := G.chains.flatten.toFinset

/-- The linked slots not holding a zombie at home. -/
def mzS (mem : U64 → U64) (G : MdbGhost) : Finset U64 := (nnS G).filter (fun y => ¬ HomeZ mem y)

/-- The measure of the deletion: linked slots, and those not holding a
zombie at home. -/
def psiD (mem : U64 → U64) (G : MdbGhost) : Nat := (nnS G).card + (mzS mem G).card

section
variable {th : TypedHeap}

theorem mem_nnS {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G) (y : U64) :
    y ∈ nnS G ↔ IsSlot th y ∧ capV mem y ≠ .Null := by
  unfold nnS; rw [List.mem_toFinset, hM.members y]
  constructor
  · rintro ⟨hy, c, hc, hcn⟩; exact ⟨hy, by rw [capV_of_capAt hc]; exact hcn⟩
  · rintro ⟨hy, hn⟩; exact ⟨hy, _, capAt_capV _ _, hn⟩

theorem nnS_card {G : MdbGhost} {mem : U64 → U64} (hM : MdbLinks th mem G) :
    (nnS G).card = G.chains.flatten.length := List.toFinset_card_of_nodup hM.tree.nodup

theorem mem_mzS {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G) (y : U64) :
    y ∈ mzS mem G ↔ IsSlot th y ∧ capV mem y ≠ .Null ∧ ¬ HomeZ mem y := by
  unfold mzS; rw [Finset.mem_filter, mem_nnS hM, and_assoc]

/-- The measure depends only on the caps. -/
theorem psiD_le {mem mem' : U64 → U64} {G G' : MdbGhost} (hM : MdbLinks th mem G) (hM' : MdbLinks th mem' G')
    (hnn : ∀ y, IsSlot th y → capV mem' y ≠ .Null → capV mem y ≠ .Null)
    (hmz : ∀ y, IsSlot th y → capV mem' y ≠ .Null → ¬ HomeZ mem' y → ¬ HomeZ mem y) :
    psiD mem' G' ≤ psiD mem G := by
  unfold psiD
  have h1 : nnS G' ⊆ nnS G := fun y hy => by
    rw [mem_nnS hM'] at hy; rw [mem_nnS hM]; exact ⟨hy.1, hnn y hy.1 hy.2⟩
  have h2 : mzS mem' G' ⊆ mzS mem G := fun y hy => by
    rw [mem_mzS hM'] at hy; rw [mem_mzS hM]; exact ⟨hy.1, hnn y hy.1 hy.2.1, hmz y hy.1 hy.2.1 hy.2.2⟩
  exact Nat.add_le_add (Finset.card_le_card h1) (Finset.card_le_card h2)

/-- Strictly smaller, when a slot leaves `mzS`. -/
theorem psiD_lt {mem mem' : U64 → U64} {G G' : MdbGhost} (hM : MdbLinks th mem G) (hM' : MdbLinks th mem' G')
    (hnn : ∀ y, IsSlot th y → capV mem' y ≠ .Null → capV mem y ≠ .Null)
    (hmz : ∀ y, IsSlot th y → capV mem' y ≠ .Null → ¬ HomeZ mem' y → ¬ HomeZ mem y)
    {z : U64} (hz : z ∈ mzS mem G) (hz' : z ∉ mzS mem' G') :
    psiD mem' G' < psiD mem G := by
  unfold psiD
  have h1 : nnS G' ⊆ nnS G := fun y hy => by
    rw [mem_nnS hM'] at hy; rw [mem_nnS hM]; exact ⟨hy.1, hnn y hy.1 hy.2⟩
  have h2 : mzS mem' G' ⊂ mzS mem G := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨fun y hy => ?_, fun e => hz' (e ▸ hz)⟩
    rw [mem_mzS hM'] at hy; rw [mem_mzS hM]; exact ⟨hy.1, hnn y hy.1 hy.2.1, hmz y hy.1 hy.2.1 hy.2.2⟩
  have := Finset.card_lt_card h2
  have := Finset.card_le_card h1
  omega

/-- Strictly smaller, when a slot becomes empty. -/
theorem psiD_lt_nn {mem mem' : U64 → U64} {G G' : MdbGhost} (hM : MdbLinks th mem G) (hM' : MdbLinks th mem' G')
    (hnn : ∀ y, IsSlot th y → capV mem' y ≠ .Null → capV mem y ≠ .Null)
    (hmz : ∀ y, IsSlot th y → capV mem' y ≠ .Null → ¬ HomeZ mem' y → ¬ HomeZ mem y)
    {z : U64} (hz : z ∈ nnS G) (hz' : z ∉ nnS G') :
    psiD mem' G' < psiD mem G := by
  unfold psiD
  have h1 : nnS G' ⊂ nnS G := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨fun y hy => ?_, fun e => hz' (e ▸ hz)⟩
    rw [mem_nnS hM'] at hy; rw [mem_nnS hM]; exact ⟨hy.1, hnn y hy.1 hy.2⟩
  have h2 : mzS mem' G' ⊆ mzS mem G := fun y hy => by
    rw [mem_mzS hM'] at hy; rw [mem_mzS hM]; exact ⟨hy.1, hnn y hy.1 hy.2.1, hmz y hy.1 hy.2.1 hy.2.2⟩
  have := Finset.card_lt_card h1
  have := Finset.card_le_card h2
  omega

theorem psiD_bound {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G) :
    psiD mem G ≤ 2 * G.chains.flatten.length := by
  unfold psiD
  have : mzS mem G ⊆ nnS G := Finset.filter_subset _ _
  have := Finset.card_le_card this
  rw [nnS_card hM] at *
  omega

/-- How a slot other than the one being finalised may change: not at all, or
to empty or to a zombie at home, when it did not hold a zombie at home. -/
def ChgOK (mem0 mem : U64 → U64) (y : U64) : Prop :=
  capV mem y = capV mem0 y ∨ ((capV mem y = .Null ∨ HomeZ mem y) ∧ ¬ HomeZ mem0 y)

theorem ChgOK.refl (mem : U64 → U64) (y : U64) : ChgOK mem mem y := Or.inl rfl

theorem ChgOK.trans {m0 m1 m2 : U64 → U64} {y : U64} (h1 : ChgOK m0 m1 y) (h2 : ChgOK m1 m2 y) :
    ChgOK m0 m2 y := by
  rcases h1 with e1 | ⟨h1, n1⟩
  · rcases h2 with e2 | ⟨h2, n2⟩
    · exact Or.inl (e2.trans e1)
    · refine Or.inr ⟨h2, fun ⟨zt, n, h⟩ => n2 ⟨zt, n, by rw [e1]; exact h⟩⟩
  · rcases h2 with e2 | ⟨h2, -⟩
    · refine Or.inr ⟨?_, n1⟩
      rcases h1 with h | ⟨zt, n, h⟩
      · exact Or.inl (e2.trans h)
      · exact Or.inr ⟨zt, n, e2.trans h⟩
    · exact Or.inr ⟨h2, n1⟩

theorem homeZ_iff (mem : U64 → U64) (y : U64) {c : capability.Cap} (h : capV mem y = c) :
    HomeZ mem y ↔ ∃ zt n, c = .Zombie y zt n := by
  unfold HomeZ; rw [h]

end

end

end Fl4Proofs.P3
