/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization, the SVM VCPU relation** `VcpuRelSvm`
(proofs/VIRT-PLAN.md §11.1, R0).

`VcpuRelSvm mem v vs`: the abstract VCPU `vs` is FL4's image at `v` on an SVM backend (`Ext/VirtRelBase` for the
shared part). On SVM the image starts with the VMCB (APM Vol. 2 App. B), so a VMCB word at byte offset `off` is
the memory word `v + off` (FL4 `vcpu::get(s, v, off)`). The relation covers every canonical `.vmcb` field FL4
keeps (`Svm.readable off`: 8-aligned below `svm::END`) except
* the hidden words and the host-cache words (`Svm.hiddenRead`: physical pointers, AVIC/GHCB/VMSA, the ASID word
  and the clean bits): the trusted layer owns them, the spec reads them as 0 (VIRT-PLAN decision Q4);
* RAX (`Svm.rax` = 0x5f8), whose canonical place is GPR 0 (`VField.canon`): GPR 0 is FL4's `REGS` word
  (`VcpuRelCommon.gpr`), and the VMCB copy agrees with it only at kernel exit (FL4 writes both; the trusted
  layer reads `REGS`): that agreement is the separate `SvmRaxSync` (VIRT-PLAN §11.1 "gpr 0 ↔ REGS **and** the
  agreement `mem (v + 0x5f8) = mem (v + REGS)` at kernel exit").
The syscall MSRs and CR2 are VMCB save-area words on SVM (`VField.canon`), so they are covered by the VMCB clause
(FL4 `vcpu::svm_msr` / `msr_addr` with `amd = true` gives the same addresses); XCR0 and `VM_IBPB_DEFER` are in the
shared part. The I/O bitmap is VMX-only in the spec (`VcpuState.ioDenied`, `Ext/VirtObj`), so SVM relates none.

Isabelle counterpart: l4v `proof/refine/ARM_HYP/StateRelation.thy` `vcpu_relation`. The ported modules are not
changed.
-/
import Fl4Spec.Ext.VirtRelVmx

namespace Fl4Spec

noncomputable section
open Classical

/-- **The SVM VCPU relation** (module docstring; VIRT-PLAN §11.1 `VcpuRelSvm`; l4v ARM_HYP `vcpu_relation`). -/
structure VcpuRelSvm (mem : Word → Word) (v : Word) (vs : VcpuState) : Prop extends VcpuRelCommon mem v vs where
  vmcb : ∀ off, Svm.readable off = true → Svm.hiddenRead off = false → off ≠ Svm.rax →
    vs.fields (.vmcb off) = mem (v + off)

/-- **The RAX agreement at kernel exit on SVM** (module docstring; VIRT-PLAN §11.1): the VMCB's RAX word equals
FL4's `REGS` word (GPR 0). -/
def SvmRaxSync (mem : Word → Word) (v : Word) : Prop := mem (v + Svm.rax) = mem (v + VcpuLay.REGS)

/-- The VCPU relation of the selected backend (VIRT-PLAN §11.1, "one per backend"); no VCPU relates on a
platform without x86 virtualization (`none`, and the unspecified `armEl2`). -/
def VcpuRel (k : VirtKind) (mem : Word → Word) (v : Word) (vs : VcpuState) : Prop :=
  match k with
  | .vmx => VcpuRelVmx mem v vs
  | .svm => VcpuRelSvm mem v vs
  | _ => False

end

end Fl4Spec
