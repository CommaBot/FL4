/-
P3 (line mmuAD, gen 37): **the short VCPU arms at `JAtZV3`** in `VDecPost` form (`P3/JAtZV3VDec`): the extracted
`vcpu.decode` (vcpu.rs l. 822-1064) after its prefix (`stall`, `cur_thread`, `virtualization`, `syscall_arg` 0/1),
paired with the extended spec's `decodeVcpuInvocation` and FL4's perform.

* **`JAtZV3.vdFlush`**: X86VCPUFlushTLB (any length, either backend): FL4 stores `SVM_CPU := 0` (an unread word,
  `JAtZV3.svmWr`) and ends with `set_thread_state ct TS_RESTART`; the spec decoder returns `.flushTlb p`, whose
  perform is `return []` (tail (a)).
* **`JAtZV3.vdOther`**: a label that is no VCPU label (`vcpuLabelOf lbl = none`): FL4 falls through every label
  test to `IllegalOperation`, the spec decoder throws `illegalOperation`.
* Errors of the write labels outside the end-to-end theorems' scope: **`vdWregsS`** (WriteRegisters, `len < 15`:
  truncated), **`vdWvmcsA`** (WriteVMCS on SVM: illegal), **`vdWvmcsS`** (WriteVMCS on VMX, `len < 2`: illegal),
  **`vdWvmcbA`** (WriteVMCB off SVM: illegal), **`vdWvmcbS`** (WriteVMCB on SVM, `len < 2`: truncated),
  **`vdWmsrS`** (WriteMSR, `len < 2`: illegal). In each FL4's store is the entry store and `JAtZV3` holds with the
  arch state after the stall.
* Spec side: `zv_decode_flush`, `zv_perform_flush`, `zv_decode_other`, `zv_decode_wregs_short`,
  `zv_decode_wvmcs_amd` / `_short`, `zv_decode_wvmcb_vmx` / `_short`, `zv_decode_wmsr_short`; `zv_lbl_none`.

Premises: [P] `ZvVirtAgree arI` (gen 32), `ARKeep arI AR` (as every JAtZV3 step). No new premise; no existing
statement changed.
-/
import Fl4Proofs.P3.JAtZV3VDec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Spec side -/

section
open Fl4Spec

theorem zv_decode_flush (args : List Data) (v : ObjRef) (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 76 args v ec = NonDetE.returnOk (.flushTlb v) := by
  unfold decodeVcpuInvocation; rw [zv_label_flush]

theorem zv_perform_flush (σ : State Unit) (v : ObjRef) :
    performVcpuInvocationF (Z := Unit) (.flushTlb v) σ = ({([], σ)}, False) := rfl

theorem zv_decode_other {l : Data} (hn : vcpuLabelOf l = none) (args : List Data) (v : ObjRef)
    (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) l args v ec = NonDetE.throwError .illegalOperation := by
  unfold decodeVcpuInvocation; rw [hn]

theorem zv_decode_wregs_short {args : List Data} (hl : args.length < 15) (v : ObjRef) (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 81 args v ec = NonDetE.throwError .truncatedMessage := by
  unfold decodeVcpuInvocation; rw [zv_label_wregs]; simp only [hl, ↓reduceIte]

theorem zv_decode_wvmcs_amd (hvk : virtKind = .svm) (args : List Data) (v : ObjRef) (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 75 args v ec = NonDetE.throwError .illegalOperation := by
  unfold decodeVcpuInvocation; rw [zv_label_wvmcs]; simp only [hvk, decide_true, ↓reduceIte]

theorem zv_decode_wvmcs_short (hvk : virtKind = .vmx) {args : List Data} (hl : args.length < 2) (v : ObjRef)
    (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 75 args v ec = NonDetE.throwError .illegalOperation := by
  unfold decodeVcpuInvocation; rw [zv_label_wvmcs]
  simp only [hvk, hl, decide_false, reduceCtorEq, Bool.false_eq_true, ↓reduceIte]

theorem zv_decode_wvmcb_vmx (hvk : virtKind ≠ .svm) (args : List Data) (v : ObjRef) (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 78 args v ec = NonDetE.throwError .illegalOperation := by
  unfold decodeVcpuInvocation; rw [zv_label_wvmcb]
  simp only [hvk, decide_false, Bool.false_eq_true, not_false_eq_true, ↓reduceIte]

theorem zv_decode_wvmcb_short (hvk : virtKind = .svm) {args : List Data} (hl : args.length < 2) (v : ObjRef)
    (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 78 args v ec = NonDetE.throwError .truncatedMessage := by
  unfold decodeVcpuInvocation; rw [zv_label_wvmcb]
  simp only [hvk, hl, decide_true, not_true_eq_false, ↓reduceIte]

theorem zv_decode_wmsr_short {args : List Data} (hl : args.length < 2) (v : ObjRef) (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 50 args v ec = NonDetE.throwError .illegalOperation := by
  unfold decodeVcpuInvocation; rw [zv_label_wmsr]; simp only [hl, ↓reduceIte]

end

/-- A label outside `vcpuLabelOf` is none of FL4's VCPU labels. -/
theorem zv_lbl_none {lbl c : U64} {n : Fl4Spec.Data} {l : Fl4Spec.VcpuLabel} (hc : c.bv = n)
    (hl : Fl4Spec.vcpuLabelOf n = some l) (hn : Fl4Spec.vcpuLabelOf lbl.bv = none) : ¬ lbl = c := fun e => by
  subst e; rw [hc, hl] at hn; cases hn

/-! ## FL4 side -/

section
open Classical Fl4Proofs.P3.Vs
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

theorem zv_n (x y : U64) (h : x.val ≠ y.val) : ¬ x = y := zv_lbl_ne h

set_option maxHeartbeats 16000000 in
/-- **X86VCPUFlushTLB at `JAtZV3`** (module docstring). -/
theorem JAtZV3.vdFlush (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) {p : U64} (hp : p ∈ V) (len : U64) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUFlushTLB len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUFlushTLB len p call buf b c r ⦄ := by
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
  obtain ⟨i, hi, -⟩ := hVA a1
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
  have n73 := zv_n fl4_abi.label.X86VCPUFlushTLB fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUFlushTLB, fl4_abi.label.X86VCPUSetTCB])
  have n81 := zv_n fl4_abi.label.X86VCPUFlushTLB fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUFlushTLB, fl4_abi.label.X86VCPUWriteRegisters])
  simp only [if_neg n73, if_neg n81, eq_self_iff_true, ↓reduceIte]
  simp only [vcpu.set, lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s2 e2 => ?_
  have J2 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s2 a1 σ := by rw [e2]; exact J1.svmWr hp 0#u64
  obtain ⟨s3, h3, -⟩ := P1.spec_ex_fd
    (P0.sched.set_thread_state.p0 st s2 ct sched.TS_RESTART (P1.LawfulStore.total (st := st)))
  rw [h3, bind_ok, WP.spec_ok]
  exact ⟨ct, hct, fun args ec _ _ => Or.inr ⟨.flushTlb p.bv, [], s2, σ, Ac, Lst, rfl,
    by rw [zv_flush_bv, zv_decode_flush], zv_perform_flush σ _, J2, Or.inl ⟨rfl, h3⟩⟩⟩

set_option maxHeartbeats 16000000 in
/-- **A label that is no VCPU label** (module docstring). -/
theorem JAtZV3.vdOther (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) {p : U64} (hp : p ∈ V) {lbl : U64} (hn : Fl4Spec.vcpuLabelOf lbl.bv = none)
    (len : U64) (call : Bool) (buf : U64) (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a lbl len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ lbl len p call buf b c r ⦄ := by
  have n73 := zv_lbl_none zv_stcb_bv zv_label_stcb hn
  have n81 := zv_lbl_none zv_wregs_bv zv_label_wregs hn
  have n76 := zv_lbl_none zv_flush_bv zv_label_flush hn
  have n74 := zv_lbl_none zv_rvmcs_bv zv_label_rvmcs hn
  have n75 := zv_lbl_none zv_wvmcs_bv zv_label_wvmcs hn
  have n77 := zv_lbl_none zv_rvmcb_bv zv_label_rvmcb hn
  have n78 := zv_lbl_none zv_wvmcb_bv zv_label_wvmcb hn
  have n49 := zv_lbl_none zv_rmsr_bv zv_label_rmsr hn
  have n50 := zv_lbl_none zv_wmsr_bv zv_label_wmsr hn
  have n79 := zv_lbl_none zv_eio_bv zv_label_eio hn
  have n80 := zv_lbl_none zv_dio_bv zv_label_dio hn
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
  obtain ⟨i, hi, -⟩ := hVA a1
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
  simp only [if_neg n73, if_neg n81, if_neg n76, if_neg n74, if_neg n75, if_neg n77, if_neg n78, if_neg n49,
    if_neg n50, if_neg n79, if_neg n80, error.illegal, bind_ok, WP.spec_ok]
  exact J1.vdErr (e := .Sys .IllegalOperation) (e' := .illegalOperation) hct trivial fun args ec _ => zv_decode_other hn args _ ec

set_option maxHeartbeats 16000000 in
/-- **X86VCPUWriteRegisters, `len < 15`** (module docstring). -/
theorem JAtZV3.vdWregsS (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) {p : U64} (hp : p ∈ V) {len : U64} (hlen : len.val < 15) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUWriteRegisters len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUWriteRegisters len p call buf b c r ⦄ := by
  have g2 : len < 15#u64 := by scalar_tac
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
  obtain ⟨i, hi, -⟩ := hVA a1
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
  have n73 := zv_n fl4_abi.label.X86VCPUWriteRegisters fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUWriteRegisters, fl4_abi.label.X86VCPUSetTCB])
  simp only [if_neg n73, eq_self_iff_true, ↓reduceIte, if_pos g2, error.truncated, bind_ok, WP.spec_ok]
  exact J1.vdErr (e := .Sys .TruncatedMessage) (e' := .truncatedMessage) hct trivial fun args ec hl => by
    rw [zv_wregs_bv]; exact zv_decode_wregs_short (by omega) _ ec

set_option maxHeartbeats 16000000 in
/-- **X86VCPUWriteVMCS on SVM** (module docstring). -/
theorem JAtZV3.vdWvmcsA (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) (hvk : Fl4Spec.virtKind = .svm) {p : U64} (hp : p ∈ V) (len : U64) (call : Bool)
    (buf : U64) (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUWriteVMCS len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUWriteVMCS len p call buf b c r ⦄ := by
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
  have n73 := zv_n fl4_abi.label.X86VCPUWriteVMCS fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUWriteVMCS, fl4_abi.label.X86VCPUSetTCB])
  have n81 := zv_n fl4_abi.label.X86VCPUWriteVMCS fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUWriteVMCS, fl4_abi.label.X86VCPUWriteRegisters])
  have n76 := zv_n fl4_abi.label.X86VCPUWriteVMCS fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUWriteVMCS, fl4_abi.label.X86VCPUFlushTLB])
  have n74 := zv_n fl4_abi.label.X86VCPUWriteVMCS fl4_abi.label.X86VCPUReadVMCS
    (by simp [fl4_abi.label.X86VCPUWriteVMCS, fl4_abi.label.X86VCPUReadVMCS])
  simp only [if_neg n73, if_neg n81, if_neg n76, if_neg n74, eq_self_iff_true, ↓reduceIte, if_pos h2,
    error.illegal, bind_ok, WP.spec_ok]
  exact J1.vdErr (e := .Sys .IllegalOperation) (e' := .illegalOperation) hct trivial fun args ec _ => by
    rw [zv_wvmcs_bv]; exact zv_decode_wvmcs_amd hvk args _ ec

set_option maxHeartbeats 16000000 in
/-- **X86VCPUWriteVMCS on VMX, `len < 2`** (module docstring). -/
theorem JAtZV3.vdWvmcsS (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) (hvk : Fl4Spec.virtKind = .vmx) {p : U64} (hp : p ∈ V) {len : U64}
    (hlen : len.val < 2) (call : Bool) (buf : U64) (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUWriteVMCS len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUWriteVMCS len p call buf b c r ⦄ := by
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
  have h2 : ¬ i = 2#u64 := fun e => by have := hi2.1 e; rw [hvk] at this; exact absurd this (by decide)
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
  have n73 := zv_n fl4_abi.label.X86VCPUWriteVMCS fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUWriteVMCS, fl4_abi.label.X86VCPUSetTCB])
  have n81 := zv_n fl4_abi.label.X86VCPUWriteVMCS fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUWriteVMCS, fl4_abi.label.X86VCPUWriteRegisters])
  have n76 := zv_n fl4_abi.label.X86VCPUWriteVMCS fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUWriteVMCS, fl4_abi.label.X86VCPUFlushTLB])
  have n74 := zv_n fl4_abi.label.X86VCPUWriteVMCS fl4_abi.label.X86VCPUReadVMCS
    (by simp [fl4_abi.label.X86VCPUWriteVMCS, fl4_abi.label.X86VCPUReadVMCS])
  simp only [if_neg n73, if_neg n81, if_neg n76, if_neg n74, eq_self_iff_true, ↓reduceIte, if_neg h2,
    bind_ok, if_pos g2, error.illegal, WP.spec_ok]
  exact J1.vdErr (e := .Sys .IllegalOperation) (e' := .illegalOperation) hct trivial fun args ec hl => by
    rw [zv_wvmcs_bv]; exact zv_decode_wvmcs_short hvk (by omega) _ ec

set_option maxHeartbeats 16000000 in
/-- **X86VCPUWriteVMCB off SVM** (module docstring). -/
theorem JAtZV3.vdWvmcbA (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) (hvk : Fl4Spec.virtKind ≠ .svm) {p : U64} (hp : p ∈ V) (len : U64) (call : Bool)
    (buf : U64) (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUWriteVMCB len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUWriteVMCB len p call buf b c r ⦄ := by
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
  have n73 := zv_n fl4_abi.label.X86VCPUWriteVMCB fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUWriteVMCB, fl4_abi.label.X86VCPUSetTCB])
  have n81 := zv_n fl4_abi.label.X86VCPUWriteVMCB fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUWriteVMCB, fl4_abi.label.X86VCPUWriteRegisters])
  have n76 := zv_n fl4_abi.label.X86VCPUWriteVMCB fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUWriteVMCB, fl4_abi.label.X86VCPUFlushTLB])
  have n74 := zv_n fl4_abi.label.X86VCPUWriteVMCB fl4_abi.label.X86VCPUReadVMCS
    (by simp [fl4_abi.label.X86VCPUWriteVMCB, fl4_abi.label.X86VCPUReadVMCS])
  have n75 := zv_n fl4_abi.label.X86VCPUWriteVMCB fl4_abi.label.X86VCPUWriteVMCS
    (by simp [fl4_abi.label.X86VCPUWriteVMCB, fl4_abi.label.X86VCPUWriteVMCS])
  have n77 := zv_n fl4_abi.label.X86VCPUWriteVMCB fl4_abi.label.X86VCPUReadVMCB
    (by simp [fl4_abi.label.X86VCPUWriteVMCB, fl4_abi.label.X86VCPUReadVMCB])
  simp only [if_neg n73, if_neg n81, if_neg n76, if_neg n74, if_neg n75, if_neg n77, eq_self_iff_true,
    ↓reduceIte, if_neg h2, error.illegal, bind_ok, WP.spec_ok]
  exact J1.vdErr (e := .Sys .IllegalOperation) (e' := .illegalOperation) hct trivial fun args ec _ => by
    rw [zv_wvmcb_bv]; exact zv_decode_wvmcb_vmx hvk args _ ec

set_option maxHeartbeats 16000000 in
/-- **X86VCPUWriteVMCB on SVM, `len < 2`** (module docstring). -/
theorem JAtZV3.vdWvmcbS (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) (hvk : Fl4Spec.virtKind = .svm) {p : U64} (hp : p ∈ V) {len : U64}
    (hlen : len.val < 2) (call : Bool) (buf : U64) (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUWriteVMCB len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUWriteVMCB len p call buf b c r ⦄ := by
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
  have n73 := zv_n fl4_abi.label.X86VCPUWriteVMCB fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUWriteVMCB, fl4_abi.label.X86VCPUSetTCB])
  have n81 := zv_n fl4_abi.label.X86VCPUWriteVMCB fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUWriteVMCB, fl4_abi.label.X86VCPUWriteRegisters])
  have n76 := zv_n fl4_abi.label.X86VCPUWriteVMCB fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUWriteVMCB, fl4_abi.label.X86VCPUFlushTLB])
  have n74 := zv_n fl4_abi.label.X86VCPUWriteVMCB fl4_abi.label.X86VCPUReadVMCS
    (by simp [fl4_abi.label.X86VCPUWriteVMCB, fl4_abi.label.X86VCPUReadVMCS])
  have n75 := zv_n fl4_abi.label.X86VCPUWriteVMCB fl4_abi.label.X86VCPUWriteVMCS
    (by simp [fl4_abi.label.X86VCPUWriteVMCB, fl4_abi.label.X86VCPUWriteVMCS])
  have n77 := zv_n fl4_abi.label.X86VCPUWriteVMCB fl4_abi.label.X86VCPUReadVMCB
    (by simp [fl4_abi.label.X86VCPUWriteVMCB, fl4_abi.label.X86VCPUReadVMCB])
  simp only [if_neg n73, if_neg n81, if_neg n76, if_neg n74, if_neg n75, if_neg n77, eq_self_iff_true,
    ↓reduceIte, if_pos h2, if_pos g2, error.truncated, bind_ok, WP.spec_ok]
  exact J1.vdErr (e := .Sys .TruncatedMessage) (e' := .truncatedMessage) hct trivial fun args ec hl => by
    rw [zv_wvmcb_bv]; exact zv_decode_wvmcb_short hvk (by omega) _ ec

set_option maxHeartbeats 16000000 in
/-- **X86VCPUWriteMSR, `len < 2`** (module docstring). -/
theorem JAtZV3.vdWmsrS (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hVA : ZvVirtAgree arI) {p : U64} (hp : p ∈ V) {len : U64} (hlen : len.val < 2) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUWriteMSR len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUWriteMSR len p call buf b c r ⦄ := by
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
  obtain ⟨i, hi, -⟩ := hVA a1
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
  have n73 := zv_n fl4_abi.label.X86VCPUWriteMSR fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUWriteMSR, fl4_abi.label.X86VCPUSetTCB])
  have n81 := zv_n fl4_abi.label.X86VCPUWriteMSR fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUWriteMSR, fl4_abi.label.X86VCPUWriteRegisters])
  have n76 := zv_n fl4_abi.label.X86VCPUWriteMSR fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUWriteMSR, fl4_abi.label.X86VCPUFlushTLB])
  have n74 := zv_n fl4_abi.label.X86VCPUWriteMSR fl4_abi.label.X86VCPUReadVMCS
    (by simp [fl4_abi.label.X86VCPUWriteMSR, fl4_abi.label.X86VCPUReadVMCS])
  have n75 := zv_n fl4_abi.label.X86VCPUWriteMSR fl4_abi.label.X86VCPUWriteVMCS
    (by simp [fl4_abi.label.X86VCPUWriteMSR, fl4_abi.label.X86VCPUWriteVMCS])
  have n77 := zv_n fl4_abi.label.X86VCPUWriteMSR fl4_abi.label.X86VCPUReadVMCB
    (by simp [fl4_abi.label.X86VCPUWriteMSR, fl4_abi.label.X86VCPUReadVMCB])
  have n78 := zv_n fl4_abi.label.X86VCPUWriteMSR fl4_abi.label.X86VCPUWriteVMCB
    (by simp [fl4_abi.label.X86VCPUWriteMSR, fl4_abi.label.X86VCPUWriteVMCB])
  have n49 := zv_n fl4_abi.label.X86VCPUWriteMSR fl4_abi.label.X86VCPUReadMSR
    (by simp [fl4_abi.label.X86VCPUWriteMSR, fl4_abi.label.X86VCPUReadMSR])
  simp only [if_neg n73, if_neg n81, if_neg n76, if_neg n74, if_neg n75, if_neg n77, if_neg n78, if_neg n49,
    eq_self_iff_true, ↓reduceIte, bind_ok, if_pos g2, error.illegal, WP.spec_ok]
  exact J1.vdErr (e := .Sys .IllegalOperation) (e' := .illegalOperation) hct trivial fun args ec hl => by
    rw [zv_wmsr_bv]; exact zv_decode_wmsr_short (by omega) _ ec

end

end

end Fl4Proofs.P3
