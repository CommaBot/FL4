import Fl4Proofs.P3.VirtSanSvm
open Aeneas Aeneas.Std Result
namespace Fl4Proofs.P3.VirtSanSvm
open fl4_core Fl4Spec Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtSanEq
section
variable {A : Type} {ar : machine.Arch A} {a : A}
example : Svm.writeRule (1024#u64).bv = some ⟨core.num.U64.MAX.bv, (0#u64).bv, false⟩ := by svm_wr
example : Svm.writeRule (1032#u64).bv = some ⟨core.num.U64.MAX.bv, (0#u64).bv, true⟩ := by svm_wr
example : Svm.writeRule (168#u64).bv = some ⟨vcpu.SVM_EVENT.bv, (0#u64).bv, false⟩ := by svm_wr
example : Svm.writeRule (1352#u64).bv = some ⟨cr4AllowedHost, (0#u64).bv, false⟩ := by svm_wr
example : Svm.writeRule (8#u64).bv = some ⟨(4294967295#u64 ||| (⟨vcpu.SVM_I1_WRITABLE.bv <<< 32⟩ : U64)).bv,
      (393218#u64 ||| (⟨vcpu.SVM_I1_FORCED.bv <<< 32⟩ : U64)).bv, false⟩ := by svm_wr
set_option maxRecDepth 200000 in
/-- **VIRT-PLAN R1, SVM**: FL4's `sanitize_vmcb` is the spec's `sanitizeVmcb` for every word, old value and
value (under [P] `CapAgree`). -/
theorem sanitize_vmcb_rel (hc : CapAgree ar a) (f old value : U64) :
    ∃ r, vcpu.sanitize_vmcb ar a f old value = ok r ∧
      WordResRel r (sanitizeVmcb f.bv old.bv value.bv) := by
  unfold vcpu.sanitize_vmcb
  split
  all_goals try subst_vars
  case h_51 =>
    have hr : Svm.writeRule f.bv = none := by
      rcases hw : Svm.writeRule f.bv with _ | r
      · rfl
      · exfalso
        have hm := writeRule_mem (g := f.bv) (by rw [hw]; rfl)
        simp only [svmTab, List.mem_cons, List.not_mem_nil, or_false] at hm
        repeat (rcases hm with hm | hm; · exact absurd (u64_ext (y := ⟨_⟩) hm) (by assumption))
        exact absurd (u64_ext (y := ⟨_⟩) hm) (by assumption)
    refine ⟨_, rfl, ?_⟩
    simp [WordResRel, SysErrRel, sanitizeVmcb, hr]
  all_goals first
    | exact rel_plain (by svm_wr)
    | exact rel_addr hc (by svm_wr)
    | exact rel_cr4 hc (by svm_wr)
    | exact rel_arm8 (by svm_wr)
    | exact rel_shl24 (by svm_wr)
    | exact rel_shl12 (by svm_wr)
    | skip

end
end Fl4Proofs.P3.VirtSanSvm
