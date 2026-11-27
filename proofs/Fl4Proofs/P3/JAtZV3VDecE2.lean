/-
P3 (line mmuAD, gen 37): **the backend and length errors of the read and I/O-port VCPU labels at `JAtZV3`**, in
`VDecPost` form (`P3/JAtZV3VDec`), as `P3/JAtZV3VDecE` does for the write labels — so the dispatcher's open
labels (`VcpuNyp`, `P3/JAtZV3VDisp`) narrow to their main paths (`P3/JAtZV3VDisp2`).

* **`vdRvmcsA`** (ReadVMCS on SVM: illegal), **`vdRvmcsS`** (ReadVMCS off SVM, `len < 1`: illegal),
  **`vdRvmcbA`** (ReadVMCB off SVM: illegal), **`vdRvmcbS`** (ReadVMCB on SVM, `len < 2`: truncated),
  **`vdRmsrS`** (ReadMSR, `len < 1`: illegal), **`vdEioA`** / **`vdDioA`** (Enable/DisableIOPort on SVM:
  illegal), **`vdEioS`** / **`vdDioS`** (off SVM, `len < 2`: truncated). FL4's store unchanged, `JAtZV3` with the
  arch state after the stall; the spec decoder throws the related error at every argument list of that length.
* Spec side: `zv_decode_rvmcs_amd` / `_short`, `zv_decode_rvmcb_vmx` / `_short`, `zv_decode_rmsr_short`,
  `zv_decode_eio_amd` / `_short`, `zv_decode_dio_amd` / `_short`. The FL4-side proofs follow `JAtZV3VDecE`'s error
  lemmas line by line.

Premises: [P] `ZvVirtAgree arI`, `ARKeep arI AR`. No new premise; no existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3VDecE
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
open Fl4Spec

theorem zv_decode_rvmcs_amd (hvk : virtKind = .svm) (args : List Data) (v : ObjRef) (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 74 args v ec = NonDetE.throwError .illegalOperation := by
  unfold decodeVcpuInvocation; rw [zv_label_rvmcs]; simp only [hvk, decide_true, ↓reduceIte]

theorem zv_decode_rvmcs_short (hvk : virtKind ≠ .svm) {args : List Data} (hl : args.length < 1) (v : ObjRef)
    (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 74 args v ec = NonDetE.throwError .illegalOperation := by
  unfold decodeVcpuInvocation; rw [zv_label_rvmcs]
  simp only [hvk, hl, decide_false, Bool.false_eq_true, ↓reduceIte]

theorem zv_decode_rvmcb_vmx (hvk : virtKind ≠ .svm) (args : List Data) (v : ObjRef) (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 77 args v ec = NonDetE.throwError .illegalOperation := by
  unfold decodeVcpuInvocation; rw [zv_label_rvmcb]
  simp only [hvk, decide_false, Bool.false_eq_true, not_false_eq_true, ↓reduceIte]

theorem zv_decode_rvmcb_short (hvk : virtKind = .svm) {args : List Data} (hl : args.length < 2) (v : ObjRef)
    (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 77 args v ec = NonDetE.throwError .truncatedMessage := by
  unfold decodeVcpuInvocation; rw [zv_label_rvmcb]
  simp only [hvk, hl, decide_true, not_true_eq_false, ↓reduceIte]

theorem zv_decode_rmsr_short {args : List Data} (hl : args.length < 1) (v : ObjRef) (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 49 args v ec = NonDetE.throwError .illegalOperation := by
  unfold decodeVcpuInvocation; rw [zv_label_rmsr]; simp only [hl, ↓reduceIte]

theorem zv_decode_eio_amd (hvk : virtKind = .svm) (args : List Data) (v : ObjRef) (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 79 args v ec = NonDetE.throwError .illegalOperation := by
  unfold decodeVcpuInvocation; rw [zv_label_eio]; simp only [hvk, decide_true, ↓reduceIte]

theorem zv_decode_eio_short (hvk : virtKind ≠ .svm) {args : List Data} (hl : args.length < 2) (v : ObjRef)
    (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 79 args v ec = NonDetE.throwError .truncatedMessage := by
  unfold decodeVcpuInvocation; rw [zv_label_eio]
  simp only [hvk, hl, decide_false, Bool.false_eq_true, ↓reduceIte]

theorem zv_decode_dio_amd (hvk : virtKind = .svm) (args : List Data) (v : ObjRef) (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 80 args v ec = NonDetE.throwError .illegalOperation := by
  unfold decodeVcpuInvocation; rw [zv_label_dio]; simp only [hvk, decide_true, ↓reduceIte]

theorem zv_decode_dio_short (hvk : virtKind ≠ .svm) {args : List Data} (hl : args.length < 2) (v : ObjRef)
    (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 80 args v ec = NonDetE.throwError .truncatedMessage := by
  unfold decodeVcpuInvocation; rw [zv_label_dio]
  simp only [hvk, hl, decide_false, Bool.false_eq_true, ↓reduceIte]

end

section
open Classical Fl4Proofs.P3.Vs
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 16000000 in
/-- **X86VCPUReadVMCS on SVM** (module docstring). -/
theorem JAtZV3.vdRvmcsA (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) (hvk : Fl4Spec.virtKind = .svm) {p : U64} (hp : p ∈ V) (len : U64) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUReadVMCS len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUReadVMCS len p call buf b c r ⦄ := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hvt : L.mem s (vTcbA p) = 0#u64 ∨ L.mem s (vTcbA p) ∈ Z.T :=
    (J.z2.zv.extv.back p hp).imp id (fun h => B.thT _ h.1)
  unfold vcpu.decode
  refine WP.spec_bind (zv_vcpu_stall_id (arI := arI) hK hS a B.ar hvt) ?_
  rintro ⟨s1, a1⟩ ⟨e1, hAR1⟩
  try simp only [uncurry_apply_pair]
  try simp only at e1 hAR1
  subst s1
  have J1 := J.archV hAR1
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  rw [hct, bind_ok]
  obtain ⟨i, hi, hi2⟩ := hVA a1
  have h2 : i = 2#u64 := hi2.2 hvk
  rw [hi, bind_ok]
  obtain ⟨f, hf⟩ : ∃ f, (if len > 0#u64 then msg.syscall_arg st s ct buf 0#u64 else ok 0#u64) = ok f := by
    split
    · obtain ⟨f, hf, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 0#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨f, hf⟩
    · exact ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, (if len > 1#u64 then msg.syscall_arg st s ct buf 1#u64 else ok 0#u64) = ok x := by
    split
    · obtain ⟨x, hx, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 1#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨x, hx⟩
    · exact ⟨_, rfl⟩
  rw [hf, bind_ok, hx, bind_ok]
  have nSetTCB := zv_n fl4_abi.label.X86VCPUReadVMCS fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUReadVMCS, fl4_abi.label.X86VCPUSetTCB])
  have nWriteRegisters := zv_n fl4_abi.label.X86VCPUReadVMCS fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUReadVMCS, fl4_abi.label.X86VCPUWriteRegisters])
  have nFlushTLB := zv_n fl4_abi.label.X86VCPUReadVMCS fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUReadVMCS, fl4_abi.label.X86VCPUFlushTLB])
  simp only [if_neg nSetTCB, if_neg nWriteRegisters, if_neg nFlushTLB, eq_self_iff_true, ↓reduceIte, if_pos h2, error.illegal, bind_ok, WP.spec_ok]
  exact J1.vdErr (e := .Sys .IllegalOperation) (e' := .illegalOperation) hct trivial fun args ec hl => by
    rw [zv_rvmcs_bv]; exact zv_decode_rvmcs_amd hvk args _ ec

set_option maxHeartbeats 16000000 in
/-- **X86VCPUReadVMCS off SVM, `len < 1`** (module docstring). -/
theorem JAtZV3.vdRvmcsS (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) (hvk : Fl4Spec.virtKind ≠ .svm) {p : U64} (hp : p ∈ V) {len : U64} (hlen : len.val < 1) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUReadVMCS len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUReadVMCS len p call buf b c r ⦄ := by
  have g2 : len < 1#u64 := by scalar_tac
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hvt : L.mem s (vTcbA p) = 0#u64 ∨ L.mem s (vTcbA p) ∈ Z.T :=
    (J.z2.zv.extv.back p hp).imp id (fun h => B.thT _ h.1)
  unfold vcpu.decode
  refine WP.spec_bind (zv_vcpu_stall_id (arI := arI) hK hS a B.ar hvt) ?_
  rintro ⟨s1, a1⟩ ⟨e1, hAR1⟩
  try simp only [uncurry_apply_pair]
  try simp only at e1 hAR1
  subst s1
  have J1 := J.archV hAR1
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  rw [hct, bind_ok]
  obtain ⟨i, hi, hi2⟩ := hVA a1
  have h2 : ¬ i = 2#u64 := fun e => hvk (hi2.1 e)
  rw [hi, bind_ok]
  obtain ⟨f, hf⟩ : ∃ f, (if len > 0#u64 then msg.syscall_arg st s ct buf 0#u64 else ok 0#u64) = ok f := by
    split
    · obtain ⟨f, hf, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 0#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨f, hf⟩
    · exact ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, (if len > 1#u64 then msg.syscall_arg st s ct buf 1#u64 else ok 0#u64) = ok x := by
    split
    · obtain ⟨x, hx, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 1#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨x, hx⟩
    · exact ⟨_, rfl⟩
  rw [hf, bind_ok, hx, bind_ok]
  have nSetTCB := zv_n fl4_abi.label.X86VCPUReadVMCS fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUReadVMCS, fl4_abi.label.X86VCPUSetTCB])
  have nWriteRegisters := zv_n fl4_abi.label.X86VCPUReadVMCS fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUReadVMCS, fl4_abi.label.X86VCPUWriteRegisters])
  have nFlushTLB := zv_n fl4_abi.label.X86VCPUReadVMCS fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUReadVMCS, fl4_abi.label.X86VCPUFlushTLB])
  have nWriteVMCS := zv_n fl4_abi.label.X86VCPUReadVMCS fl4_abi.label.X86VCPUWriteVMCS
    (by simp [fl4_abi.label.X86VCPUReadVMCS, fl4_abi.label.X86VCPUWriteVMCS])
  simp only [if_neg nSetTCB, if_neg nWriteRegisters, if_neg nFlushTLB, if_neg nWriteVMCS, eq_self_iff_true, ↓reduceIte, if_neg h2, bind_ok, if_pos g2, error.illegal, bind_ok, WP.spec_ok]
  exact J1.vdErr (e := .Sys .IllegalOperation) (e' := .illegalOperation) hct trivial fun args ec hl => by
    rw [zv_rvmcs_bv]; exact zv_decode_rvmcs_short hvk (by omega) _ ec

set_option maxHeartbeats 16000000 in
/-- **X86VCPUReadVMCB off SVM** (module docstring). -/
theorem JAtZV3.vdRvmcbA (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) (hvk : Fl4Spec.virtKind ≠ .svm) {p : U64} (hp : p ∈ V) (len : U64) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUReadVMCB len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUReadVMCB len p call buf b c r ⦄ := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hvt : L.mem s (vTcbA p) = 0#u64 ∨ L.mem s (vTcbA p) ∈ Z.T :=
    (J.z2.zv.extv.back p hp).imp id (fun h => B.thT _ h.1)
  unfold vcpu.decode
  refine WP.spec_bind (zv_vcpu_stall_id (arI := arI) hK hS a B.ar hvt) ?_
  rintro ⟨s1, a1⟩ ⟨e1, hAR1⟩
  try simp only [uncurry_apply_pair]
  try simp only at e1 hAR1
  subst s1
  have J1 := J.archV hAR1
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  rw [hct, bind_ok]
  obtain ⟨i, hi, hi2⟩ := hVA a1
  have h2 : ¬ i = 2#u64 := fun e => hvk (hi2.1 e)
  rw [hi, bind_ok]
  obtain ⟨f, hf⟩ : ∃ f, (if len > 0#u64 then msg.syscall_arg st s ct buf 0#u64 else ok 0#u64) = ok f := by
    split
    · obtain ⟨f, hf, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 0#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨f, hf⟩
    · exact ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, (if len > 1#u64 then msg.syscall_arg st s ct buf 1#u64 else ok 0#u64) = ok x := by
    split
    · obtain ⟨x, hx, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 1#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨x, hx⟩
    · exact ⟨_, rfl⟩
  rw [hf, bind_ok, hx, bind_ok]
  have nSetTCB := zv_n fl4_abi.label.X86VCPUReadVMCB fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUSetTCB])
  have nWriteRegisters := zv_n fl4_abi.label.X86VCPUReadVMCB fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUWriteRegisters])
  have nFlushTLB := zv_n fl4_abi.label.X86VCPUReadVMCB fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUFlushTLB])
  have nReadVMCS := zv_n fl4_abi.label.X86VCPUReadVMCB fl4_abi.label.X86VCPUReadVMCS
    (by simp [fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUReadVMCS])
  have nWriteVMCS := zv_n fl4_abi.label.X86VCPUReadVMCB fl4_abi.label.X86VCPUWriteVMCS
    (by simp [fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUWriteVMCS])
  simp only [if_neg nSetTCB, if_neg nWriteRegisters, if_neg nFlushTLB, if_neg nReadVMCS, if_neg nWriteVMCS, eq_self_iff_true, ↓reduceIte, if_neg h2, error.illegal, bind_ok, WP.spec_ok]
  exact J1.vdErr (e := .Sys .IllegalOperation) (e' := .illegalOperation) hct trivial fun args ec hl => by
    rw [zv_rvmcb_bv]; exact zv_decode_rvmcb_vmx hvk args _ ec

set_option maxHeartbeats 16000000 in
/-- **X86VCPUReadVMCB on SVM, `len < 2`** (module docstring). -/
theorem JAtZV3.vdRvmcbS (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) (hvk : Fl4Spec.virtKind = .svm) {p : U64} (hp : p ∈ V) {len : U64} (hlen : len.val < 2) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUReadVMCB len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUReadVMCB len p call buf b c r ⦄ := by
  have g2 : len < 2#u64 := by scalar_tac
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hvt : L.mem s (vTcbA p) = 0#u64 ∨ L.mem s (vTcbA p) ∈ Z.T :=
    (J.z2.zv.extv.back p hp).imp id (fun h => B.thT _ h.1)
  unfold vcpu.decode
  refine WP.spec_bind (zv_vcpu_stall_id (arI := arI) hK hS a B.ar hvt) ?_
  rintro ⟨s1, a1⟩ ⟨e1, hAR1⟩
  try simp only [uncurry_apply_pair]
  try simp only at e1 hAR1
  subst s1
  have J1 := J.archV hAR1
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  rw [hct, bind_ok]
  obtain ⟨i, hi, hi2⟩ := hVA a1
  have h2 : i = 2#u64 := hi2.2 hvk
  rw [hi, bind_ok]
  obtain ⟨f, hf⟩ : ∃ f, (if len > 0#u64 then msg.syscall_arg st s ct buf 0#u64 else ok 0#u64) = ok f := by
    split
    · obtain ⟨f, hf, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 0#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨f, hf⟩
    · exact ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, (if len > 1#u64 then msg.syscall_arg st s ct buf 1#u64 else ok 0#u64) = ok x := by
    split
    · obtain ⟨x, hx, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 1#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨x, hx⟩
    · exact ⟨_, rfl⟩
  rw [hf, bind_ok, hx, bind_ok]
  have nSetTCB := zv_n fl4_abi.label.X86VCPUReadVMCB fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUSetTCB])
  have nWriteRegisters := zv_n fl4_abi.label.X86VCPUReadVMCB fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUWriteRegisters])
  have nFlushTLB := zv_n fl4_abi.label.X86VCPUReadVMCB fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUFlushTLB])
  have nReadVMCS := zv_n fl4_abi.label.X86VCPUReadVMCB fl4_abi.label.X86VCPUReadVMCS
    (by simp [fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUReadVMCS])
  have nWriteVMCS := zv_n fl4_abi.label.X86VCPUReadVMCB fl4_abi.label.X86VCPUWriteVMCS
    (by simp [fl4_abi.label.X86VCPUReadVMCB, fl4_abi.label.X86VCPUWriteVMCS])
  simp only [if_neg nSetTCB, if_neg nWriteRegisters, if_neg nFlushTLB, if_neg nReadVMCS, if_neg nWriteVMCS, eq_self_iff_true, ↓reduceIte, if_pos h2, if_pos g2, error.truncated, bind_ok, WP.spec_ok]
  exact J1.vdErr (e := .Sys .TruncatedMessage) (e' := .truncatedMessage) hct trivial fun args ec hl => by
    rw [zv_rvmcb_bv]; exact zv_decode_rvmcb_short hvk (by omega) _ ec

set_option maxHeartbeats 16000000 in
/-- **X86VCPUReadMSR, `len < 1`** (module docstring). -/
theorem JAtZV3.vdRmsrS (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) {p : U64} (hp : p ∈ V) {len : U64} (hlen : len.val < 1) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUReadMSR len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUReadMSR len p call buf b c r ⦄ := by
  have g2 : len < 1#u64 := by scalar_tac
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hvt : L.mem s (vTcbA p) = 0#u64 ∨ L.mem s (vTcbA p) ∈ Z.T :=
    (J.z2.zv.extv.back p hp).imp id (fun h => B.thT _ h.1)
  unfold vcpu.decode
  refine WP.spec_bind (zv_vcpu_stall_id (arI := arI) hK hS a B.ar hvt) ?_
  rintro ⟨s1, a1⟩ ⟨e1, hAR1⟩
  try simp only [uncurry_apply_pair]
  try simp only at e1 hAR1
  subst s1
  have J1 := J.archV hAR1
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  rw [hct, bind_ok]
  obtain ⟨i, hi, hi2⟩ := hVA a1
  rw [hi, bind_ok]
  obtain ⟨f, hf⟩ : ∃ f, (if len > 0#u64 then msg.syscall_arg st s ct buf 0#u64 else ok 0#u64) = ok f := by
    split
    · obtain ⟨f, hf, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 0#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨f, hf⟩
    · exact ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, (if len > 1#u64 then msg.syscall_arg st s ct buf 1#u64 else ok 0#u64) = ok x := by
    split
    · obtain ⟨x, hx, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 1#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨x, hx⟩
    · exact ⟨_, rfl⟩
  rw [hf, bind_ok, hx, bind_ok]
  have nSetTCB := zv_n fl4_abi.label.X86VCPUReadMSR fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUReadMSR, fl4_abi.label.X86VCPUSetTCB])
  have nWriteRegisters := zv_n fl4_abi.label.X86VCPUReadMSR fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUReadMSR, fl4_abi.label.X86VCPUWriteRegisters])
  have nFlushTLB := zv_n fl4_abi.label.X86VCPUReadMSR fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUReadMSR, fl4_abi.label.X86VCPUFlushTLB])
  have nReadVMCS := zv_n fl4_abi.label.X86VCPUReadMSR fl4_abi.label.X86VCPUReadVMCS
    (by simp [fl4_abi.label.X86VCPUReadMSR, fl4_abi.label.X86VCPUReadVMCS])
  have nWriteVMCS := zv_n fl4_abi.label.X86VCPUReadMSR fl4_abi.label.X86VCPUWriteVMCS
    (by simp [fl4_abi.label.X86VCPUReadMSR, fl4_abi.label.X86VCPUWriteVMCS])
  have nReadVMCB := zv_n fl4_abi.label.X86VCPUReadMSR fl4_abi.label.X86VCPUReadVMCB
    (by simp [fl4_abi.label.X86VCPUReadMSR, fl4_abi.label.X86VCPUReadVMCB])
  have nWriteVMCB := zv_n fl4_abi.label.X86VCPUReadMSR fl4_abi.label.X86VCPUWriteVMCB
    (by simp [fl4_abi.label.X86VCPUReadMSR, fl4_abi.label.X86VCPUWriteVMCB])
  have nWriteMSR := zv_n fl4_abi.label.X86VCPUReadMSR fl4_abi.label.X86VCPUWriteMSR
    (by simp [fl4_abi.label.X86VCPUReadMSR, fl4_abi.label.X86VCPUWriteMSR])
  simp only [if_neg nSetTCB, if_neg nWriteRegisters, if_neg nFlushTLB, if_neg nReadVMCS, if_neg nWriteVMCS, if_neg nReadVMCB, if_neg nWriteVMCB, if_neg nWriteMSR, eq_self_iff_true, ↓reduceIte, bind_ok, if_pos g2, error.illegal, bind_ok, WP.spec_ok]
  exact J1.vdErr (e := .Sys .IllegalOperation) (e' := .illegalOperation) hct trivial fun args ec hl => by
    rw [zv_rmsr_bv]; exact zv_decode_rmsr_short (by omega) _ ec

set_option maxHeartbeats 16000000 in
/-- **X86VCPUEnableIOPort on SVM** (module docstring). -/
theorem JAtZV3.vdEioA (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) (hvk : Fl4Spec.virtKind = .svm) {p : U64} (hp : p ∈ V) (len : U64) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUEnableIOPort len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUEnableIOPort len p call buf b c r ⦄ := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hvt : L.mem s (vTcbA p) = 0#u64 ∨ L.mem s (vTcbA p) ∈ Z.T :=
    (J.z2.zv.extv.back p hp).imp id (fun h => B.thT _ h.1)
  unfold vcpu.decode
  refine WP.spec_bind (zv_vcpu_stall_id (arI := arI) hK hS a B.ar hvt) ?_
  rintro ⟨s1, a1⟩ ⟨e1, hAR1⟩
  try simp only [uncurry_apply_pair]
  try simp only at e1 hAR1
  subst s1
  have J1 := J.archV hAR1
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  rw [hct, bind_ok]
  obtain ⟨i, hi, hi2⟩ := hVA a1
  have h2 : i = 2#u64 := hi2.2 hvk
  rw [hi, bind_ok]
  obtain ⟨f, hf⟩ : ∃ f, (if len > 0#u64 then msg.syscall_arg st s ct buf 0#u64 else ok 0#u64) = ok f := by
    split
    · obtain ⟨f, hf, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 0#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨f, hf⟩
    · exact ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, (if len > 1#u64 then msg.syscall_arg st s ct buf 1#u64 else ok 0#u64) = ok x := by
    split
    · obtain ⟨x, hx, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 1#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨x, hx⟩
    · exact ⟨_, rfl⟩
  rw [hf, bind_ok, hx, bind_ok]
  have nSetTCB := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUSetTCB])
  have nWriteRegisters := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUWriteRegisters])
  have nFlushTLB := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUFlushTLB])
  have nReadVMCS := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUReadVMCS
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUReadVMCS])
  have nWriteVMCS := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUWriteVMCS
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUWriteVMCS])
  have nReadVMCB := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUReadVMCB
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUReadVMCB])
  have nWriteVMCB := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUWriteVMCB
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUWriteVMCB])
  have nReadMSR := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUReadMSR
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUReadMSR])
  have nWriteMSR := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUWriteMSR
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUWriteMSR])
  simp only [if_neg nSetTCB, if_neg nWriteRegisters, if_neg nFlushTLB, if_neg nReadVMCS, if_neg nWriteVMCS, if_neg nReadVMCB, if_neg nWriteVMCB, if_neg nReadMSR, if_neg nWriteMSR, eq_self_iff_true, ↓reduceIte, if_pos h2, error.illegal, bind_ok, WP.spec_ok]
  exact J1.vdErr (e := .Sys .IllegalOperation) (e' := .illegalOperation) hct trivial fun args ec hl => by
    rw [zv_eio_bv]; exact zv_decode_eio_amd hvk args _ ec

set_option maxHeartbeats 16000000 in
/-- **X86VCPUEnableIOPort off SVM, `len < 2`** (module docstring). -/
theorem JAtZV3.vdEioS (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) (hvk : Fl4Spec.virtKind ≠ .svm) {p : U64} (hp : p ∈ V) {len : U64} (hlen : len.val < 2) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUEnableIOPort len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUEnableIOPort len p call buf b c r ⦄ := by
  have g2 : len < 2#u64 := by scalar_tac
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hvt : L.mem s (vTcbA p) = 0#u64 ∨ L.mem s (vTcbA p) ∈ Z.T :=
    (J.z2.zv.extv.back p hp).imp id (fun h => B.thT _ h.1)
  unfold vcpu.decode
  refine WP.spec_bind (zv_vcpu_stall_id (arI := arI) hK hS a B.ar hvt) ?_
  rintro ⟨s1, a1⟩ ⟨e1, hAR1⟩
  try simp only [uncurry_apply_pair]
  try simp only at e1 hAR1
  subst s1
  have J1 := J.archV hAR1
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  rw [hct, bind_ok]
  obtain ⟨i, hi, hi2⟩ := hVA a1
  have h2 : ¬ i = 2#u64 := fun e => hvk (hi2.1 e)
  rw [hi, bind_ok]
  obtain ⟨f, hf⟩ : ∃ f, (if len > 0#u64 then msg.syscall_arg st s ct buf 0#u64 else ok 0#u64) = ok f := by
    split
    · obtain ⟨f, hf, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 0#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨f, hf⟩
    · exact ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, (if len > 1#u64 then msg.syscall_arg st s ct buf 1#u64 else ok 0#u64) = ok x := by
    split
    · obtain ⟨x, hx, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 1#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨x, hx⟩
    · exact ⟨_, rfl⟩
  rw [hf, bind_ok, hx, bind_ok]
  have nSetTCB := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUSetTCB])
  have nWriteRegisters := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUWriteRegisters])
  have nFlushTLB := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUFlushTLB])
  have nReadVMCS := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUReadVMCS
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUReadVMCS])
  have nWriteVMCS := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUWriteVMCS
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUWriteVMCS])
  have nReadVMCB := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUReadVMCB
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUReadVMCB])
  have nWriteVMCB := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUWriteVMCB
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUWriteVMCB])
  have nReadMSR := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUReadMSR
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUReadMSR])
  have nWriteMSR := zv_n fl4_abi.label.X86VCPUEnableIOPort fl4_abi.label.X86VCPUWriteMSR
    (by simp [fl4_abi.label.X86VCPUEnableIOPort, fl4_abi.label.X86VCPUWriteMSR])
  simp only [if_neg nSetTCB, if_neg nWriteRegisters, if_neg nFlushTLB, if_neg nReadVMCS, if_neg nWriteVMCS, if_neg nReadVMCB, if_neg nWriteVMCB, if_neg nReadMSR, if_neg nWriteMSR, eq_self_iff_true, ↓reduceIte, if_neg h2, if_pos g2, error.truncated, bind_ok, WP.spec_ok]
  exact J1.vdErr (e := .Sys .TruncatedMessage) (e' := .truncatedMessage) hct trivial fun args ec hl => by
    rw [zv_eio_bv]; exact zv_decode_eio_short hvk (by omega) _ ec

set_option maxHeartbeats 16000000 in
/-- **X86VCPUDisableIOPort on SVM** (module docstring). -/
theorem JAtZV3.vdDioA (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) (hvk : Fl4Spec.virtKind = .svm) {p : U64} (hp : p ∈ V) (len : U64) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUDisableIOPort len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUDisableIOPort len p call buf b c r ⦄ := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hvt : L.mem s (vTcbA p) = 0#u64 ∨ L.mem s (vTcbA p) ∈ Z.T :=
    (J.z2.zv.extv.back p hp).imp id (fun h => B.thT _ h.1)
  unfold vcpu.decode
  refine WP.spec_bind (zv_vcpu_stall_id (arI := arI) hK hS a B.ar hvt) ?_
  rintro ⟨s1, a1⟩ ⟨e1, hAR1⟩
  try simp only [uncurry_apply_pair]
  try simp only at e1 hAR1
  subst s1
  have J1 := J.archV hAR1
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  rw [hct, bind_ok]
  obtain ⟨i, hi, hi2⟩ := hVA a1
  have h2 : i = 2#u64 := hi2.2 hvk
  rw [hi, bind_ok]
  obtain ⟨f, hf⟩ : ∃ f, (if len > 0#u64 then msg.syscall_arg st s ct buf 0#u64 else ok 0#u64) = ok f := by
    split
    · obtain ⟨f, hf, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 0#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨f, hf⟩
    · exact ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, (if len > 1#u64 then msg.syscall_arg st s ct buf 1#u64 else ok 0#u64) = ok x := by
    split
    · obtain ⟨x, hx, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 1#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨x, hx⟩
    · exact ⟨_, rfl⟩
  rw [hf, bind_ok, hx, bind_ok]
  have nSetTCB := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUSetTCB])
  have nWriteRegisters := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUWriteRegisters])
  have nFlushTLB := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUFlushTLB])
  have nReadVMCS := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUReadVMCS
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUReadVMCS])
  have nWriteVMCS := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUWriteVMCS
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUWriteVMCS])
  have nReadVMCB := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUReadVMCB
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUReadVMCB])
  have nWriteVMCB := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUWriteVMCB
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUWriteVMCB])
  have nReadMSR := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUReadMSR
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUReadMSR])
  have nWriteMSR := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUWriteMSR
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUWriteMSR])
  have nEnableIOPort := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUEnableIOPort
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUEnableIOPort])
  simp only [if_neg nSetTCB, if_neg nWriteRegisters, if_neg nFlushTLB, if_neg nReadVMCS, if_neg nWriteVMCS, if_neg nReadVMCB, if_neg nWriteVMCB, if_neg nReadMSR, if_neg nWriteMSR, if_neg nEnableIOPort, eq_self_iff_true, ↓reduceIte, if_pos h2, error.illegal, bind_ok, WP.spec_ok]
  exact J1.vdErr (e := .Sys .IllegalOperation) (e' := .illegalOperation) hct trivial fun args ec hl => by
    rw [zv_dio_bv]; exact zv_decode_dio_amd hvk args _ ec

set_option maxHeartbeats 16000000 in
/-- **X86VCPUDisableIOPort off SVM, `len < 2`** (module docstring). -/
theorem JAtZV3.vdDioS (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) (hvk : Fl4Spec.virtKind ≠ .svm) {p : U64} (hp : p ∈ V) {len : U64} (hlen : len.val < 2) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUDisableIOPort len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUDisableIOPort len p call buf b c r ⦄ := by
  have g2 : len < 2#u64 := by scalar_tac
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  have hvt : L.mem s (vTcbA p) = 0#u64 ∨ L.mem s (vTcbA p) ∈ Z.T :=
    (J.z2.zv.extv.back p hp).imp id (fun h => B.thT _ h.1)
  unfold vcpu.decode
  refine WP.spec_bind (zv_vcpu_stall_id (arI := arI) hK hS a B.ar hvt) ?_
  rintro ⟨s1, a1⟩ ⟨e1, hAR1⟩
  try simp only [uncurry_apply_pair]
  try simp only at e1 hAR1
  subst s1
  have J1 := J.archV hAR1
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  rw [hct, bind_ok]
  obtain ⟨i, hi, hi2⟩ := hVA a1
  have h2 : ¬ i = 2#u64 := fun e => hvk (hi2.1 e)
  rw [hi, bind_ok]
  obtain ⟨f, hf⟩ : ∃ f, (if len > 0#u64 then msg.syscall_arg st s ct buf 0#u64 else ok 0#u64) = ok f := by
    split
    · obtain ⟨f, hf, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 0#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨f, hf⟩
    · exact ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, (if len > 1#u64 then msg.syscall_arg st s ct buf 1#u64 else ok 0#u64) = ok x := by
    split
    · obtain ⟨x, hx, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 1#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨x, hx⟩
    · exact ⟨_, rfl⟩
  rw [hf, bind_ok, hx, bind_ok]
  have nSetTCB := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUSetTCB])
  have nWriteRegisters := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUWriteRegisters])
  have nFlushTLB := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUFlushTLB])
  have nReadVMCS := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUReadVMCS
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUReadVMCS])
  have nWriteVMCS := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUWriteVMCS
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUWriteVMCS])
  have nReadVMCB := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUReadVMCB
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUReadVMCB])
  have nWriteVMCB := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUWriteVMCB
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUWriteVMCB])
  have nReadMSR := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUReadMSR
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUReadMSR])
  have nWriteMSR := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUWriteMSR
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUWriteMSR])
  have nEnableIOPort := zv_n fl4_abi.label.X86VCPUDisableIOPort fl4_abi.label.X86VCPUEnableIOPort
    (by simp [fl4_abi.label.X86VCPUDisableIOPort, fl4_abi.label.X86VCPUEnableIOPort])
  simp only [if_neg nSetTCB, if_neg nWriteRegisters, if_neg nFlushTLB, if_neg nReadVMCS, if_neg nWriteVMCS, if_neg nReadVMCB, if_neg nWriteVMCB, if_neg nReadMSR, if_neg nWriteMSR, if_neg nEnableIOPort, eq_self_iff_true, ↓reduceIte, if_neg h2, if_pos g2, error.truncated, bind_ok, WP.spec_ok]
  exact J1.vdErr (e := .Sys .TruncatedMessage) (e' := .truncatedMessage) hct trivial fun args ec hl => by
    rw [zv_dio_bv]; exact zv_decode_dio_short hvk (by omega) _ ec

end

end

end Fl4Proofs.P3
