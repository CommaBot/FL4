/-
Range specs for small helpers whose callers' P0 proofs need more than
"does not fail", e.g. that a shift amount masked with `& 63` is below 64.
xtask/scripts/gen_p0.py derives each one's P0 theorem from its spec.
AArch64 counterpart of Fl4Proofs/P0/Specs.lean: AArch64 has no
`debug.type_shift`/`size_shift` and no VMX MSR closures, and its EPT
(stage-2) error closures are `ept.root` and `ept.flush_frame`.
-/
import Fl4CoreA64.Funs
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P0
open fl4_core_a64

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

/-- Frame-size encodings always produce a valid shift amount. -/
@[step] theorem capability.FrameSize.bits.spec (sz : capability.FrameSize) :
    capability.FrameSize.bits sz ⦃ r => r.val = 12 ∨ r.val = 21 ∨ r.val = 30 ⦄ := by
  cases sz <;> simp [capability.FrameSize.bits]

@[step] theorem root_map_total {S : Type _} (st : machine.Store S) (r : core.result.Result U64 error.LookupFault) :
    core.result.Result.map_err (ept.root.closure.Insts.CoreOpsFunctionFnOnceTupleLookupFaultExc st) r () ⦃ _ => True ⦄ := by
  cases r <;> simp [core.result.Result.map_err,
    ept.root.closure.Insts.CoreOpsFunctionFnOnceTupleLookupFaultExc,
    ept.root.closure.Insts.CoreOpsFunctionFnOnceTupleLookupFaultExc.call_once]
@[step] theorem flush_frame_map_total {S : Type _} {A : Type _} (st : machine.Store S) (ar : machine.Arch A)
    (r : core.result.Result U64 error.LookupFault) :
    core.result.Result.map_err (ept.flush_frame.closure.Insts.CoreOpsFunctionFnOnceTupleLookupFaultExc st ar) r () ⦃ _ => True ⦄ := by
  cases r <;> simp [core.result.Result.map_err,
    ept.flush_frame.closure.Insts.CoreOpsFunctionFnOnceTupleLookupFaultExc,
    ept.flush_frame.closure.Insts.CoreOpsFunctionFnOnceTupleLookupFaultExc.call_once]

@[step] theorem one_shift_positive (n : U64) (hn : n.val < 64) :
    1#u64 <<< n ⦃ r => r.val = 2 ^ n.val ∧ r.bv = 1#64 <<< n.val ∧ 0 < r.val ⦄ := by
  have heq : (1#u64 <<< n : Result U64) = ok ⟨1#64 <<< n.val⟩ := by
    simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft]
    simp [hn]
  rw [heq, WP.spec_ok]
  have hp : 2 ^ n.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hn
  have hv : (1#64 <<< n.val).toNat = 2 ^ n.val := by
    rw [BitVec.toNat_shiftLeft]
    change (1 <<< n.val) % 2 ^ 64 = 2 ^ n.val
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt hp
  exact ⟨hv, rfl, by rw [show (⟨1#64 <<< n.val⟩ : U64).val = (1#64 <<< n.val).toNat from rfl, hv]; positivity⟩

end Fl4ProofsA64.P0
