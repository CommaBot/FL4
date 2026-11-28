/-
P3 (DESIGN.md §9), untyped (mmuAD gen 42b20): **`create_new_objects_loopB`**, `objects::create_new_objects`' inner
loop `create_new_objects_loop` from any index `i0`, for any `size` word, with no address bound (the `i`-th object at
`base + i·2^z` mod `2^64`, `z` the low six bits of `size`) and an invariant over the arch state, for any per-object
step (`create_object` into `Q`, then `insert_new_cap` into the slot `obj.Slot.index` returns, back to `I` at
`i + 1`). No `LawfulStore` asked.

It sits on `Fl4Core.Funs` alone (through P1/SyscallGen) so that both P3/UntypedLoop (whose
`create_new_objects_loopG`, the `slotAddr` form, is its corollary) and the arch-keeping walk P3/MachKeepG4j (whose
`step` must not see the `LawfulStore` lemmas of the P3 state-relation chain) can import it.

No named premises.
-/
import Fl4Proofs.P1.SyscallGen
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

section
variable {S : Type} {st : machine.Store S}

/-- **`create_new_objects`' inner loop from any index, any object size, over the arch state** (module docstring):
from `I s ar i0`, if `create_object` of the `i`-th object (at `base + i·2^z` mod `2^64`: no address bound asked)
goes from `I` to `Q` (state, arch state, the returned cap, `i`), and `insert_new_cap` of that cap into the slot
`obj.Slot.index dest (off + i)` returns from `Q` to `I … (i + 1)`, the loop ends in `I` at `max win i0`. -/
theorem create_new_objects_loopB {A' : Type} (arI : machine.Arch A') (ar : A') (s : S)
    (nt parent dest off win base us : U64) (dev : Bool) (size i0 : U64)
    (I : S → A' → Nat → Prop) (Q : S → A' → capability.Cap → Nat → Prop)
    (hco : ∀ (s1 : S) (a1 : A') (i : Nat), i < win.val → I s1 a1 i →
      objects.create_object st arI s1 a1 nt ⟨BitVec.ofNat 64 (base.val + i * 2 ^ (size &&& 63#u64).val)⟩ us dev
        ⦃ r => Q r.2.1 r.2.2 r.1 i ⦄)
    (hins : ∀ (s2 : S) (a2 : A') (c : capability.Cap) (iw : U64), iw.val < win.val → Q s2 a2 c iw.val →
      ∀ sl, obj.Slot.index dest (core.num.U64.wrapping_add off iw) = ok sl →
        cdt.insert_new_cap st s2 parent sl c ⦃ s3 => I s3 a2 (iw.val + 1) ⦄)
    (h0 : I s ar i0.val) :
    objects.create_new_objects_loop st arI s ar nt parent dest off win base us dev size i0 ⦃ res =>
      I res.1 res.2 (max win.val i0.val) ⦄ := by
  unfold objects.create_new_objects_loop
  obtain ⟨z, h63⟩ : ∃ z, (size &&& 63#u64).val = z := ⟨_, rfl⟩
  have hz : z < 64 := by
    have : (size &&& 63#u64).val = size.val % 64 := by
      simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
    omega
  refine loop.spec_decr_nat (measure := fun x => win.val - x.2.2.val)
    (inv := fun x => (x.2.2.val ≤ win.val ∧ i0.val ≤ win.val ∨ x.2.2 = i0) ∧ I x.1 x.2.1 x.2.2.val) _ _ _ ?_
    ⟨Or.inr rfl, h0⟩
  rintro ⟨s1, a1, i⟩ ⟨hiw, hI⟩
  simp only at hiw hI ⊢
  unfold objects.create_new_objects_loop.body
  by_cases hit : i < win
  · rw [if_pos hit]
    have hit' : i.val < win.val := hit
    have hi0w : i0.val ≤ win.val := by
      rcases hiw with ⟨-, h⟩ | h
      · exact h
      · rw [← h]; omega
    simp only [lift, bind_ok]
    refine WP.spec_bind (UScalar.ShiftLeft_spec i (size &&& 63#u64) _
      (by rw [h63]; simp [UScalarTy.U64_numBits_eq]; omega) rfl) fun i2 hsh => ?_
    obtain ⟨hv2, -⟩ := hsh
    have hi2v : i2.val = i.val * 2 ^ z % 2 ^ 64 := by
      rw [hv2, h63, Nat.shiftLeft_eq]
      simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits] <;> omega
    have hi3 : core.num.U64.wrapping_add base i2 = ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ z)⟩ := by
      apply UScalar.eq_of_val_eq
      show _ = (BitVec.ofNat 64 (base.val + i.val * 2 ^ z)).toNat
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hi2v] <;> omega
    rw [hi3]
    have hco' := hco s1 a1 i.val hit' hI
    rw [h63] at hco'
    refine WP.spec_bind hco' fun r hQ => ?_
    obtain ⟨c, s2, a2⟩ := r
    simp only at hQ ⊢
    have hsl : obj.Slot.index dest (core.num.U64.wrapping_add off i) = ok (core.num.U64.wrapping_add dest
        (core.num.U64.wrapping_mul (core.num.U64.wrapping_add off i) layout.cte.SIZE)) := by
      unfold obj.Slot.index; simp only [lift, bind_ok]
    rw [hsl]; simp only [bind_ok]
    refine WP.spec_bind (hins s2 a2 c i hit' hQ _ hsl) fun s3 h3 => ?_
    step as ⟨i5, hi5⟩
    have hi5' : i5.val = i.val + 1 := by omega
    try simp only [and_assoc]
    refine ⟨Or.inl ⟨by omega, hi0w⟩, ?_, by omega⟩
    rw [hi5']
    exact h3
  · rw [if_neg hit, WP.spec_ok]
    have hwi : win.val ≤ i.val := by have : ¬ i.val < win.val := hit; omega
    have hm : max win.val i0.val = i.val := by
      rcases hiw with ⟨h1, h2⟩ | h
      · omega
      · rw [← h]; omega
    show I s1 a1 (max win.val i0.val)
    rw [hm]; exact hI

end

end Fl4Proofs.P3
