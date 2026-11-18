/-
P3 (issue #16): **the kernel-state block in P1's heap** — a regression
check that the kernel-state facts of `JAtZ` are jointly satisfiable.

`JAtZ` was unsatisfiable: the IRQ node's one-slot CNodes (`IntLayout.node`,
at `ksb + 1248 + 32 i`, inside the kernel-state block `[ksb, ksb + 13568)`)
are objects of the typed heap, so `JPlaced.cnode` puts them in `H`, while
`JPlaced.ks` kept every object of `H` off the block; and `blk`'s
`SgOK.ksΩ` puts every block word in `Ω = Heap.omega H`, i.e. inside an
object of `H`. Now `H` holds the block as `other` objects (`JPlaced.ks`
asks only the non-`other` objects off the block, `JPlaced.ksIn` the `other`
ones off it or inside it, `JCovD` exempts objects inside it, `KsObj`).

`ksH kb`: the IRQ node's CNodes (`other 5`) and 8-byte `other 3` tiles for
the block's other words. It is well formed (`ksH_ok`), holds the IRQ node's
CNodes as `JPlaced.cnode` asks (`ksH_node`), meets `JPlaced.ks` and
`JPlaced.ksIn` (`ksH_ks`, `ksH_in`), and puts every block word in its `Ω`
(`ksH_omega`, `SgOK.ksΩ`).
-/
import Fl4Proofs.P3.ScPlace
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1

noncomputable section

/-- **The kernel-state block as `H`'s objects** (module docstring). -/
def ksH (kb : U64) : Heap := fun p =>
  if kb.val + 1248 ≤ p.val ∧ p.val < kb.val + 5344 ∧ (p.val - kb.val) % 32 = 0 then some (.other 5)
  else if kb.val ≤ p.val ∧ p.val < kb.val + 13568 ∧ (p.val - kb.val) % 8 = 0 ∧
    ¬ (kb.val + 1248 ≤ p.val ∧ p.val < kb.val + 5344) then some (.other 3)
  else none

theorem ksU64_val {n : Nat} (h : n < 2 ^ 64) : (⟨BitVec.ofNat 64 n⟩ : U64).val = n := by
  show (BitVec.ofNat 64 n).toNat = n
  simp; omega

theorem ksH_some {kb p : U64} {k : HKind} (h : ksH kb p = some k) :
    (k = .other 5 ∧ kb.val + 1248 ≤ p.val ∧ p.val < kb.val + 5344 ∧ (p.val - kb.val) % 32 = 0) ∨
    (k = .other 3 ∧ kb.val ≤ p.val ∧ p.val < kb.val + 13568 ∧ (p.val - kb.val) % 8 = 0 ∧
      ¬ (kb.val + 1248 ≤ p.val ∧ p.val < kb.val + 5344)) := by
  unfold ksH at h
  split_ifs at h with h1 h2
  · cases h; exact Or.inl ⟨rfl, h1⟩
  · cases h; exact Or.inr ⟨rfl, h2⟩

/-- `ksH` is well formed. -/
theorem ksH_ok {kb : U64} (hf : kb.val + 13568 ≤ 2 ^ 64) (ha : kb.val % 32 = 0) : HeapOK (ksH kb) where
  align := by
    intro p k hp
    rcases ksH_some hp with ⟨rfl, h1, h2, h3⟩ | ⟨rfl, h1, h2, h3, -⟩ <;>
      simp only [HKind.bits, Nat.reducePow] <;> omega
  fits := by
    intro p k hp
    rcases ksH_some hp with ⟨rfl, h1, h2, h3⟩ | ⟨rfl, h1, h2, h3, -⟩ <;>
      simp only [HKind.bits, Nat.reducePow] <;> omega
  lt64 := by
    intro p k hp
    rcases ksH_some hp with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [HKind.bits]
  scmin := by
    intro p z hp
    rcases ksH_some hp with ⟨e, -⟩ | ⟨e, -⟩ <;> cases e
  disj := by
    intro p k q k' hp hq hne
    have hv : p.val ≠ q.val := fun e => hne (by rw [UScalar.eq_equiv]; exact e)
    rcases ksH_some hp with ⟨rfl, h1, h2, h3⟩ | ⟨rfl, h1, h2, h3, h4⟩ <;>
    rcases ksH_some hq with ⟨rfl, g1, g2, g3⟩ | ⟨rfl, g1, g2, g3, g4⟩ <;>
      simp only [HKind.bits, Nat.reducePow] <;> omega

/-- The IRQ node's CNodes are `ksH`'s (`JPlaced.cnode` at radix 0). -/
theorem ksH_node {kb i : U64} (hf : kb.val + 13568 ≤ 2 ^ 64) (ha : kb.val % 32 = 0) (hi : i.val < 128) :
    ksH kb (nodeA kb i) = some (.other (0 + 5)) := by
  have hv := nodeA_val hf hi
  unfold ksH
  rw [if_pos (by rw [hv]; omega)]

/-- `JPlaced.ks` holds of `ksH`: it has no object but `other` ones. -/
theorem ksH_ks {kb : U64} (s : U64) : ∀ p k, ksH kb p = some k → (∀ z, k ≠ .other z) →
    p.val + 2 ^ k.bits ≤ s.val ∨ s.val + 13568 ≤ p.val := by
  intro p k hp hk
  rcases ksH_some hp with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact absurd rfl (hk 5)
  · exact absurd rfl (hk 3)

/-- `JPlaced.ksIn` holds of `ksH`: its objects lie inside the block. -/
theorem ksH_in {kb : U64} : ∀ p z, ksH kb p = some (.other z) → p.val + 2 ^ z ≤ kb.val ∨
    kb.val + 13568 ≤ p.val ∨ (kb.val ≤ p.val ∧ p.val + 2 ^ z ≤ kb.val + 13568) := by
  intro p z hp
  right; right
  rcases ksH_some hp with ⟨e, h1, h2, h3⟩ | ⟨e, h1, h2, h3, -⟩ <;> cases e <;>
    simp only [Nat.reducePow] <;> omega

/-- **Every block word lies in an object of `ksH`** (P1's `SgOK.ksΩ` with
`Ω = Heap.omega (ksH kb)`). -/
theorem ksH_omega {kb : U64} (hf : kb.val + 13568 ≤ 2 ^ 64) (ha : kb.val % 32 = 0) :
    ∀ o : U64, o.val < 13568 → o.val % 8 = 0 → core.num.U64.wrapping_add kb o ∈ Heap.omega (ksH kb) := by
  intro o ho h8
  have hb : (core.num.U64.wrapping_add kb o).val = kb.val + o.val := by
    simp only [core.num.U64.wrapping_add_val_eq]; simp [U64.size, U64.numBits]; omega
  refine ⟨by unfold Aligned; rw [hb]; omega, ?_⟩
  by_cases hI : 1248 ≤ o.val ∧ o.val < 5344
  · have hpv := ksU64_val (n := kb.val + 1248 + 32 * ((o.val - 1248) / 32)) (by omega)
    refine ⟨⟨BitVec.ofNat 64 (kb.val + 1248 + 32 * ((o.val - 1248) / 32))⟩, .other 5, ?_,
      Or.inr (Or.inr (Or.inl ⟨5, rfl⟩)), ?_⟩
    · unfold ksH; rw [if_pos (by rw [hpv]; omega)]
    · unfold InObj; rw [hb, hpv]; simp only [HKind.bits, Nat.reducePow]; omega
  · refine ⟨core.num.U64.wrapping_add kb o, .other 3, ?_, Or.inr (Or.inr (Or.inl ⟨3, rfl⟩)), ?_⟩
    · unfold ksH; rw [if_neg (by rw [hb]; omega), if_pos (by rw [hb]; omega)]
    · unfold InObj; rw [hb]; simp only [HKind.bits, Nat.reducePow]; omega

end

end Fl4Proofs.P3.Sched
