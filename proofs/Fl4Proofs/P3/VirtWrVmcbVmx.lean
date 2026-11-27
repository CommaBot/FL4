/-
P3x for virtualization (line virt, gen 19, item 3): **WriteVMCB on a VMX (non-SVM) platform** — FL4's error
against the spec's `illegalOperation` (the half `wrvmcb_sys` of P3/VirtWrSys leaves out).

* `spec_decode_wrvmcb_vmx`: off SVM the spec's `decodeVcpuInvocation` at the WriteVMCB label throws
  `illegalOperation` for every argument list (Ext/VirtVcpu: `if ¬ amd then throwError .illegalOperation`, before any
  VCPU read).
* **`wrvmcb_vmx`**: FL4's WriteVMCB decode (`vcpu.decode … X86VCPUWriteVMCB`, `length ≥ 2`) on a platform with
  `virtKind ≠ .svm` returns after the stall `s1` (writes ⊆ IPI_PENDING) with `r.1 = .Err e`, `SysErrRel e
  .illegalOperation`, the store `s1` and the arch state the stall left, and the spec decode throws
  `illegalOperation`: the two answers relate. The backend word read after the stall is not 2 by `stall_code`
  (`VirtCodeAgree` / `VirtCodeKeepStall`).
* `wrvmcb_vmxJ`: the same with `ReplyPl` from `JKern` + `JVLay` + `JVm` (`JKern.replyPl`).

Named premises (unchanged, as `wrmsr_sys`): `VirtCodeAgree ar a` [P], `VirtCodeKeepStall ar` [P]. No VCPU relation
is needed (the spec never reads the VCPU here). No new premise. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtWrSys
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtWrVmcbVmx
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtSanSvm
open Fl4Proofs.P3.VirtVcpuRel Fl4Proofs.P3.VirtMsrEq Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit
open Fl4Proofs.P3.VirtMsrStore Fl4Proofs.P3.VirtVmcbStore Fl4Proofs.P3.VirtReplyKeep Fl4Proofs.P3.VirtVmcbDec
open Fl4Proofs.P3.VirtVmcbTail Fl4Proofs.P3.VirtMsrE2E Fl4Proofs.P3.VirtVmcbE2E Fl4Proofs.P3.VirtArgsSpec
open Fl4Proofs.P3.VirtWrSys

noncomputable section

section
variable {Z : Type} [StateExt Z]

/-- **Off SVM the spec's WriteVMCB decode throws `illegalOperation`.** -/
theorem spec_decode_wrvmcb_vmx (hk : virtKind ≠ .svm) {label : Data} (hl : vcpuLabelOf label = some .writeVmcb)
    (args : List Data) (v : ObjRef) (caps : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Z) label args v caps = NonDetE.throwError .illegalOperation := by
  unfold decodeVcpuInvocation
  simp only [hl]
  rw [if_pos (by simp [hk])]

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {Z : Type} [StateExt Z]

theorem illegal_eq : error.illegal Unit = ok (core.result.Result.Err (error.Exc.Sys error.SysError.IllegalOperation)) := by
  unfold error.illegal; rfl

set_option maxHeartbeats 1000000 in
/-- **WriteVMCB on VMX** (module docstring; premises `VirtCodeAgree`, `VirtCodeKeepStall`, both [P]; state fact
`ReplyPl`). -/
theorem wrvmcb_vmx (hnsvm : virtKind ≠ .svm) (hA : P0.ArchTotal ar) (hKv : VirtCodeKeepStall ar) {a : A}
    (hk : VirtCodeAgree ar a) {s : S} {v : U64} (P : ReplyPl st v s) (length : U64) (call : Bool) (buf : U64)
    (ex : Aeneas.Std.Array obj.Slot 3#usize) (hlen : ¬ length < 2#u64) {label : Data}
    (hl : vcpuLabelOf label = some .writeVmcb) (args : List Data) (caps : List (Cap × CslotPtr)) :
    vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteVMCB length v call buf ex ⦃ r =>
      ∃ (s1 : S) (a1 : A), vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        decodeVcpuInvocation (Z := Z) label args v.bv caps = NonDetE.throwError .illegalOperation ∧
        ∃ e, r.1 = .Err e ∧ SysErrRel e .illegalOperation ∧ r.2.1 = s1 ∧ r.2.2 = a1 ⦄ := by
  rw [decode_wrvmcb_eq s a length v call buf ex hlen]
  obtain ⟨⟨s1, a1⟩, hp, hW⟩ := spec_ex (vcpu_stall_w hA s a v P.ipiA_al)
  rw [hp, bind_tc_ok]
  dsimp only at hW ⊢
  obtain ⟨ct, hct, -⟩ := spec_ex (P1.sched.cur_thread.spec (L := L) s1)
  rw [hct]; simp only [bind_ok, bind_tc_ok]
  obtain ⟨i, hi, -⟩ := spec_ex (hA.virtualization a1)
  rw [hi]; simp only [bind_ok, bind_tc_ok]
  obtain ⟨f, hf⟩ := arg_ok (st := st) s1 ct buf (length > 0#u64) 0#u64
  rw [hf]; simp only [bind_ok, bind_tc_ok]
  obtain ⟨value, hval⟩ := arg_ok (st := st) s1 ct buf (length > 1#u64) 1#u64
  rw [hval]; simp only [bind_ok, bind_tc_ok]
  have hb : i ≠ 2#u64 := fun h => hnsvm ((stall_code hKv hk hp hi).1 h)
  rw [if_neg hb, illegal_eq, bind_ok]
  exact (WP.spec_ok _).2 ⟨s1, a1, rfl, hW, spec_decode_wrvmcb_vmx hnsvm hl args v.bv caps, _, rfl, trivial, rfl, rfl⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {AI : Type} {arI : machine.Arch AI}
variable {H : P1.Heap} {Cs D : Set U64} {th : TypedHeap} {σ : Fl4Spec.State Unit} {V U : Set U64}

/-- **WriteVMCB on VMX from `JKern` + `JVLay` + `JVm`** (premises as `wrvmcb_vmx`). -/
theorem wrvmcb_vmxJ (hnsvm : virtKind ≠ .svm) (hA : P0.ArchTotal ar) (hKv : VirtCodeKeepStall ar) {a : A}
    (hk : VirtCodeAgree ar a) {s : S}
    (K : JKern (L := L) arI H Cs D th s σ) (Ly : JVLay V th U) (Jv : JVm (L := L) V H s σ) {v : U64} (hvV : v ∈ V)
    (length : U64) (call : Bool) (buf : U64)
    (ex : Aeneas.Std.Array obj.Slot 3#usize) (hlen : ¬ length < 2#u64) {label : Data}
    (hl : vcpuLabelOf label = some .writeVmcb) (args : List Data) (caps : List (Cap × CslotPtr)) :
    vcpu.decode st ar s a fl4_abi.label.X86VCPUWriteVMCB length v call buf ex ⦃ r =>
      ∃ (s1 : S) (a1 : A), vcpu.stall st ar s a v = ok (s1, a1) ∧ P1.WritesIn st s s1 (· = ipiA st s) ∧
        decodeVcpuInvocation (Z := Unit) label args v.bv caps = NonDetE.throwError .illegalOperation ∧
        ∃ e, r.1 = .Err e ∧ SysErrRel e .illegalOperation ∧ r.2.1 = s1 ∧ r.2.2 = a1 ⦄ :=
  wrvmcb_vmx (Z := Unit) hnsvm hA hKv hk (JKern.replyPl K Ly Jv hvV) length call buf ex hlen hl args caps

end

end

end Fl4Proofs.P3.VirtWrVmcbVmx
