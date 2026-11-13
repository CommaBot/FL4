/-
Range specs for small helpers whose callers' P0 proofs need more than
"does not fail", e.g. that a shift amount masked with `& 63` is below 64.
xtask/scripts/gen_p0.py derives each one's P0 theorem from its spec.
-/
import Fl4Core.Funs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P0
open fl4_core

@[step] theorem debug.type_shift.spec (bp : U64) :
    debug.type_shift bp ⦃ r => r.val < 64 ⦄ := by
  unfold debug.type_shift; step*

@[step] theorem debug.size_shift.spec (bp : U64) :
    debug.size_shift bp ⦃ r => r.val < 64 ⦄ := by
  unfold debug.size_shift; step*

/-- The library models in FunsExternal.lean never fail. -/
theorem bvTrailingZeros_le {w : Nat} (x : BitVec w) : bvTrailingZeros x ≤ w := by
  unfold bvTrailingZeros
  cases h : (List.range w).find? (fun i => x.getLsbD i) with
  | none => simp
  | some i =>
    have := List.mem_of_find?_eq_some h
    simp at this ⊢; omega

@[step] theorem core.num.U64.trailing_zeros.spec (x : U64) :
    core.num.U64.trailing_zeros x ⦃ r => r.val ≤ 64 ⦄ := by
  unfold core.num.U64.trailing_zeros
  have h := bvTrailingZeros_le x.bv
  simp only [WP.spec_ok]
  show (BitVec.ofNat 32 (bvTrailingZeros x.bv)).toNat ≤ 64
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact h

@[step] theorem core.result.Result.is_err.spec {T E : Type _} (r : core.result.Result T E) :
    core.result.Result.is_err r ⦃ _ => True ⦄ := by
  cases r <;> simp [core.result.Result.is_err]

/-- `saturating_sub` on u64 is truncated subtraction. -/
@[simp, scalar_tac_simps] theorem saturating_sub_u64_val (x y : U64) :
    (core.num.U64.saturating_sub x y).val = x.val - y.val := by
  have hx : x.val < 2 ^ 64 := by scalar_tac
  show (BitVec.ofNat 64 (max 0 (x.val - y.val))).toNat = x.val - y.val
  rw [BitVec.toNat_ofNat, Nat.zero_max, Nat.mod_eq_of_lt (by omega)]

end Fl4Proofs.P0
