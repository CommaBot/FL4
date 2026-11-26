import Fl4Proofs.P3.VirtSanSvm
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3.VirtSanSvm
open fl4_core Fl4Spec Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtSanEq

theorem and_eq_iff (x : U64) (m c : U64) (w v : Word) (hw : m.bv = w) (hv : c.bv = v) :
    (x.bv &&& w = v) ↔ (x &&& m = c) := by
  subst hw hv
  constructor
  · intro h; apply u64_ext; exact h
  · intro h; exact congrArg UScalar.bv h

set_option maxHeartbeats 1000000 in
theorem valid_xcr0_eq (x host : U64) : vcpu.valid_xcr0 x host = ok (validXcr0 x.bv host.bv) := by
  have e1 : (x.bv &&& ~~~host.bv = 0) ↔ (x &&& ~~~host = 0#u64) := by
    rw [← UScalar.bv_not]; exact and_eq_iff x _ _ _ _ rfl rfl
  have e2 : (x.bv &&& 1 = 0) ↔ (x &&& 1#u64 = 0#u64) := and_eq_iff x _ _ _ _ rfl rfl
  have e3 : (x.bv &&& 4 = 0) ↔ (x &&& 4#u64 = 0#u64) := and_eq_iff x _ _ _ _ rfl rfl
  have e4 : (x.bv &&& 2 = 0) ↔ (x &&& 2#u64 = 0#u64) := and_eq_iff x _ _ _ _ rfl rfl
  have e5 : (x.bv &&& 0xe0 = 0) ↔ (x &&& 224#u64 = 0#u64) := and_eq_iff x _ _ _ _ rfl rfl
  have e6 : (x.bv &&& 0xe0 = 0xe0) ↔ (x &&& 224#u64 = 224#u64) := and_eq_iff x _ _ _ _ rfl rfl
  have e7 : (x.bv &&& 6 = 6) ↔ (x &&& 6#u64 = 6#u64) := and_eq_iff x _ _ _ _ rfl rfl
  have e8 : (x.bv &&& 0x18 = 0) ↔ (x &&& 24#u64 = 0#u64) := and_eq_iff x _ _ _ _ rfl rfl
  have e9 : (x.bv &&& 0x18 = 0x18) ↔ (x &&& 24#u64 = 24#u64) := and_eq_iff x _ _ _ _ rfl rfl
  have e10 : (x.bv &&& 0x60000 = 0) ↔ (x &&& 393216#u64 = 0#u64) := and_eq_iff x _ _ _ _ rfl rfl
  have e11 : (x.bv &&& 0x60000 = 0x60000) ↔ (x &&& 393216#u64 = 393216#u64) := and_eq_iff x _ _ _ _ rfl rfl
  unfold vcpu.valid_xcr0 validXcr0
  simp only [lift, bind_ok, bne_iff_ne, ne_eq]
  simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
  split_ifs <;> simp (config := {decide := true}) only [*, decide_true, decide_false, Bool.true_and, Bool.and_true, Bool.false_and,
    Bool.and_false, Bool.not_true, Bool.not_false, Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or,
    not_true_eq_false, not_false_eq_true, decide_not]

end Fl4Proofs.P3.VirtSanSvm
