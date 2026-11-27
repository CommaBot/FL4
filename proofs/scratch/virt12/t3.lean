import Fl4Proofs.P3.VirtSanSvm
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3.VirtSanSvm
open fl4_core Fl4Spec Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtSanEq

example : Svm.writeRule 0x400 = some ⟨~~~0, 0, false⟩ := by rfl

example : Svm.writeRule 0x408 = some ⟨~~~0, 0, true⟩ := by
  unfold Svm.writeRule
  repeat rw [if_neg (by decide)]
  rw [if_neg (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; decide)]
  rw [if_pos (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; decide)]

example : Svm.writeRule 0x400 = some ⟨~~~0, 0, false⟩ := by
  unfold Svm.writeRule
  repeat rw [if_neg (by decide)]
  rw [if_pos (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; decide)]

example : Svm.writeRule 0x008 = some ⟨(4294967295#u64 ||| (⟨vcpu.SVM_I1_WRITABLE.bv <<< 32⟩ : U64)).bv,
      (393218#u64 ||| (⟨vcpu.SVM_I1_FORCED.bv <<< 32⟩ : U64)).bv, false⟩ := by
  unfold Svm.writeRule
  repeat rw [if_neg (by decide)]
  rw [if_pos (by decide)]
  simp only [UScalar.bv_or, vcpu.SVM_I1_WRITABLE, vcpu.SVM_I1_FORCED]
  decide

end Fl4Proofs.P3.VirtSanSvm
