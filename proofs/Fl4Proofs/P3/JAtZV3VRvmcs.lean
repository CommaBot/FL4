/-
P3 (line mmuAD, gen 38): **X86VCPUReadVMCS end to end at `JAtZV3`** — the extracted `vcpu.decode` at label
`X86VCPUReadVMCS` (vcpu.rs l. 876-934, the read side on VMX, `len ≥ 1`: `contains(&READ_FIELDS, f)` else
`IllegalOperation`; `vcpu_sync`; `supported` — false for `GUEST_PERF_GLOBAL_CTRL` without bit 13 of
`vcpu_capability(0x484) >> 32` and for `GUEST_PREEMPTION_TIMER_VALUE` without bit 6 of `vcpu_capability(0x481) >> 32`;
the word `read_vmcs(v, f)` or 0; `reply`) paired with the extended spec's `decodeVcpuInvocation` (`.readVmcs v f` /
`illegalOperation` for `¬ Vmx.readable f`) and `performVcpuInvocationF (.readVmcs v f)` (`[if Vmx.readSupported f
then vs.get virtKind (.vmcs f) else 0]`), in `VDecPost` form (`P3/JAtZV3VDec`), tail (b).

* **`zv_read_map`**: FL4's `READ_FIELDS` is the spec's `vmxReadFields` element for element (as virt's
  `VirtSanEq.write_map` for `WRITE_FIELDS`); **`zv_contains_read`**: `contains(&READ_FIELDS, f) = Vmx.readable f`.
* **`zv_rsupp`**: FL4's `supported` block is `Vmx.readSupported f` under `CapAgree`.
* Spec side: `zv_decode_rvmcs_bad`, `zv_decode_rvmcs_ok`, `zv_perform_rvmcs`.
* **`JAtZV3.readVmcsJ`**: the label at `JAtZV3`, off SVM, `len ≥ 1`; FL4's store is unchanged, `JAtZV3` holds with
  the arch state after `vcpu_sync` (`ZvSyncKeep`), the reply word is the spec's (`VcpuRelVmx.vmcs`, `v3_vmcs_addr`).
  **`vcpuNyp_rvmcs`**: `VcpuNyp3`'s `readVmcs` field, proved.

Premises: [P] `ZvVirtAgree arI`, [P] `ZvSyncKeep arI AR`, [P] `∀ a, CapAgree arI a`, `ARKeep arI AR` (existing).
No new premise; no existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3VDio
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
open Fl4Spec

theorem zv_read_map : vcpu.READ_FIELDS.val.map (·.bv) = Vmx.vmxReadFields := by
  simp only [vcpu.READ_FIELDS, vcpu.vmx.CONTROL_CR0_MASK, vcpu.vmx.CONTROL_CR0_READ_SHADOW, vcpu.vmx.CONTROL_CR4_MASK, vcpu.vmx.CONTROL_CR4_READ_SHADOW, vcpu.vmx.CONTROL_ENTRY_CONTROLS, vcpu.vmx.CONTROL_ENTRY_INTERRUPTION_INFO, vcpu.vmx.CONTROL_EXCEPTION_BITMAP, vcpu.vmx.CONTROL_EXIT_CONTROLS, vcpu.vmx.CONTROL_PIN_EXECUTION_CONTROLS, vcpu.vmx.CONTROL_PRIMARY_PROCESSOR_CONTROLS, vcpu.vmx.CONTROL_SECONDARY_PROCESSOR_CONTROLS, vcpu.vmx.CONTROL_TSC_OFFSET, vcpu.vmx.DATA_EXIT_INSTRUCTION_INFO, vcpu.vmx.DATA_EXIT_INSTRUCTION_LENGTH, vcpu.vmx.DATA_EXIT_INTERRUPT_ERROR, vcpu.vmx.DATA_EXIT_INTERRUPT_INFO, vcpu.vmx.DATA_GUEST_LINEAR_ADDRESS, vcpu.vmx.DATA_GUEST_PHYSICAL, vcpu.vmx.DATA_IDT_VECTOR_ERROR, vcpu.vmx.DATA_IDT_VECTOR_INFO, vcpu.vmx.DATA_INSTRUCTION_ERROR, vcpu.vmx.DATA_IO_RCX, vcpu.vmx.DATA_IO_RDI, vcpu.vmx.DATA_IO_RIP, vcpu.vmx.DATA_IO_RSI, vcpu.vmx.GUEST_ACTIVITY, vcpu.vmx.GUEST_CR0, vcpu.vmx.GUEST_CR3, vcpu.vmx.GUEST_CR4, vcpu.vmx.GUEST_CS_ACCESS_RIGHTS, vcpu.vmx.GUEST_CS_BASE, vcpu.vmx.GUEST_CS_LIMIT, vcpu.vmx.GUEST_CS_SELECTOR, vcpu.vmx.GUEST_DEBUGCTRL, vcpu.vmx.GUEST_DR7, vcpu.vmx.GUEST_DS_ACCESS_RIGHTS, vcpu.vmx.GUEST_DS_BASE, vcpu.vmx.GUEST_DS_LIMIT, vcpu.vmx.GUEST_DS_SELECTOR, vcpu.vmx.GUEST_EFER, vcpu.vmx.GUEST_ES_ACCESS_RIGHTS, vcpu.vmx.GUEST_ES_BASE, vcpu.vmx.GUEST_ES_LIMIT, vcpu.vmx.GUEST_ES_SELECTOR, vcpu.vmx.GUEST_FS_ACCESS_RIGHTS, vcpu.vmx.GUEST_FS_BASE, vcpu.vmx.GUEST_FS_LIMIT, vcpu.vmx.GUEST_FS_SELECTOR, vcpu.vmx.GUEST_GDTR_BASE, vcpu.vmx.GUEST_GDTR_LIMIT, vcpu.vmx.GUEST_GS_ACCESS_RIGHTS, vcpu.vmx.GUEST_GS_BASE, vcpu.vmx.GUEST_GS_LIMIT, vcpu.vmx.GUEST_GS_SELECTOR, vcpu.vmx.GUEST_IDTR_BASE, vcpu.vmx.GUEST_IDTR_LIMIT, vcpu.vmx.GUEST_INTERRUPTABILITY, vcpu.vmx.GUEST_LDTR_ACCESS_RIGHTS, vcpu.vmx.GUEST_LDTR_BASE, vcpu.vmx.GUEST_LDTR_LIMIT, vcpu.vmx.GUEST_LDTR_SELECTOR, vcpu.vmx.GUEST_PAT, vcpu.vmx.GUEST_PDPTE0, vcpu.vmx.GUEST_PDPTE1, vcpu.vmx.GUEST_PDPTE2, vcpu.vmx.GUEST_PDPTE3, vcpu.vmx.GUEST_PENDING_DEBUG_EXCEPTIONS, vcpu.vmx.GUEST_PERF_GLOBAL_CTRL, vcpu.vmx.GUEST_PREEMPTION_TIMER_VALUE, vcpu.vmx.GUEST_RFLAGS, vcpu.vmx.GUEST_RIP, vcpu.vmx.GUEST_RSP, vcpu.vmx.GUEST_SMBASE, vcpu.vmx.GUEST_SS_ACCESS_RIGHTS, vcpu.vmx.GUEST_SS_BASE, vcpu.vmx.GUEST_SS_LIMIT, vcpu.vmx.GUEST_SS_SELECTOR, vcpu.vmx.GUEST_SYSENTER_CS, vcpu.vmx.GUEST_SYSENTER_EIP, vcpu.vmx.GUEST_SYSENTER_ESP, vcpu.vmx.GUEST_TR_ACCESS_RIGHTS, vcpu.vmx.GUEST_TR_BASE, vcpu.vmx.GUEST_TR_LIMIT, vcpu.vmx.GUEST_TR_SELECTOR]
  simp
  simp only [Vmx.vmxReadFields, Vmx.controlCr0Mask, Vmx.controlCr0ReadShadow, Vmx.controlCr4Mask, Vmx.controlCr4ReadShadow, Vmx.controlEntryControls, Vmx.controlEntryInterruptionInfo, Vmx.controlExceptionBitmap, Vmx.controlExitControls, Vmx.controlPinExecutionControls, Vmx.controlPrimaryProcessorControls, Vmx.controlSecondaryProcessorControls, Vmx.controlTscOffset, Vmx.dataExitInstructionInfo, Vmx.dataExitInstructionLength, Vmx.dataExitInterruptError, Vmx.dataExitInterruptInfo, Vmx.dataGuestLinearAddress, Vmx.dataGuestPhysical, Vmx.dataIdtVectorError, Vmx.dataIdtVectorInfo, Vmx.dataInstructionError, Vmx.dataIoRcx, Vmx.dataIoRdi, Vmx.dataIoRip, Vmx.dataIoRsi, Vmx.guestActivity, Vmx.guestCr0, Vmx.guestCr3, Vmx.guestCr4, Vmx.guestCsAccessRights, Vmx.guestCsBase, Vmx.guestCsLimit, Vmx.guestCsSelector, Vmx.guestDebugctrl, Vmx.guestDr7, Vmx.guestDsAccessRights, Vmx.guestDsBase, Vmx.guestDsLimit, Vmx.guestDsSelector, Vmx.guestEfer, Vmx.guestEsAccessRights, Vmx.guestEsBase, Vmx.guestEsLimit, Vmx.guestEsSelector, Vmx.guestFsAccessRights, Vmx.guestFsBase, Vmx.guestFsLimit, Vmx.guestFsSelector, Vmx.guestGdtrBase, Vmx.guestGdtrLimit, Vmx.guestGsAccessRights, Vmx.guestGsBase, Vmx.guestGsLimit, Vmx.guestGsSelector, Vmx.guestIdtrBase, Vmx.guestIdtrLimit, Vmx.guestInterruptability, Vmx.guestLdtrAccessRights, Vmx.guestLdtrBase, Vmx.guestLdtrLimit, Vmx.guestLdtrSelector, Vmx.guestPat, Vmx.guestPdpte0, Vmx.guestPdpte1, Vmx.guestPdpte2, Vmx.guestPdpte3, Vmx.guestPendingDebugExceptions, Vmx.guestPerfGlobalCtrl, Vmx.guestPreemptionTimerValue, Vmx.guestRflags, Vmx.guestRip, Vmx.guestRsp, Vmx.guestSmbase, Vmx.guestSsAccessRights, Vmx.guestSsBase, Vmx.guestSsLimit, Vmx.guestSsSelector, Vmx.guestSysenterCs, Vmx.guestSysenterEip, Vmx.guestSysenterEsp, Vmx.guestTrAccessRights, Vmx.guestTrBase, Vmx.guestTrLimit, Vmx.guestTrSelector]
  simp

theorem zv_contains_read (f : U64) :
    vcpu.contains (Array.to_slice vcpu.READ_FIELDS) f = ok (Vmx.readable f.bv) := by
  unfold vcpu.contains
  rw [VirtSanEq.contains_loop_eq _ _ _ _ (by simp)]
  simp only [Bool.false_or, List.drop_zero, Vmx.readable, ← zv_read_map]
  congr 1
  rw [decide_eq_decide]
  have h0 : (Array.to_slice vcpu.READ_FIELDS).val = vcpu.READ_FIELDS.val := by
    first | rfl | simp [Array.to_slice]
  rw [h0]
  show f ∈ List.drop 0 vcpu.READ_FIELDS.val ↔ _
  rw [List.drop_zero]
  constructor
  · intro h; exact List.mem_map_of_mem h
  · intro h; obtain ⟨y, hy, e⟩ := List.mem_map.1 h; rwa [← VirtSanEq.u64_ext e]

theorem zv_decode_rvmcs_bad (hvk : virtKind ≠ .svm) {args : List Data} (hl : 1 ≤ args.length) {f : Word}
    (h0 : args.getD 0 0 = f) (hb : Vmx.readable f = false) (v : ObjRef) (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 74 args v ec = NonDetE.throwError .illegalOperation := by
  have hn : ¬ args.length < 1 := by omega
  unfold decodeVcpuInvocation; rw [zv_label_rvmcs]
  simp only [hvk, hn, h0, hb, decide_false, Bool.false_eq_true, not_false_eq_true, ↓reduceIte]

theorem zv_decode_rvmcs_ok (hvk : virtKind ≠ .svm) {args : List Data} (hl : 1 ≤ args.length) {f : Word}
    (h0 : args.getD 0 0 = f) (hb : Vmx.readable f = true) (v : ObjRef) (ec : List (Cap × CslotPtr)) :
    decodeVcpuInvocation (Z := Unit) 74 args v ec = NonDetE.returnOk (.readVmcs v f) := by
  have hn : ¬ args.length < 1 := by omega
  unfold decodeVcpuInvocation; rw [zv_label_rvmcs]
  simp only [hvk, hn, h0, hb, decide_false, Bool.false_eq_true, not_true_eq_false, ↓reduceIte]

theorem zv_perform_rvmcs {σ : State Unit} {v : ObjRef} {vs : VcpuState}
    (hk : σ.kheap v = some (.archObj (.vcpu vs))) (f : Word) :
    performVcpuInvocationF (Z := Unit) (.readVmcs v f) σ =
      ({([if Vmx.readSupported f then vs.get virtKind (.vmcs f) else 0], σ)}, False) := by
  show ((getVcpu (Z := Unit) v) >>= fun st =>
    (pure [if Vmx.readSupported f then st.get virtKind (.vmcs f) else 0] : SMonad Unit (List Data))) σ = _
  rw [Notif.nd_bind_one (zv_getVcpu_eq hk)]
  rfl

end

section
open Classical Fl4Proofs.P3.Vs
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- A masked test of FL4's word is the spec's on its `.bv`. -/
theorem zv_and_zero_iff (X : U64) (w : Fl4Spec.Word) (h : X.bv = w) : X = 0#u64 ↔ w = 0 :=
  ⟨fun e => by rw [← h, e]; rfl, fun e => VirtSanEq.u64_ext (by rw [h, e]; rfl)⟩

theorem zv_perf_bv : vcpu.vmx.GUEST_PERF_GLOBAL_CTRL.bv = Fl4Spec.Vmx.guestPerfGlobalCtrl := by
  unfold vcpu.vmx.GUEST_PERF_GLOBAL_CTRL Fl4Spec.Vmx.guestPerfGlobalCtrl; rfl
theorem zv_pretim_bv : vcpu.vmx.GUEST_PREEMPTION_TIMER_VALUE.bv = Fl4Spec.Vmx.guestPreemptionTimerValue := by
  unfold vcpu.vmx.GUEST_PREEMPTION_TIMER_VALUE Fl4Spec.Vmx.guestPreemptionTimerValue; rfl

theorem zv_u64_eq_bv {f g : U64} {w : Fl4Spec.Word} (hg : g.bv = w) : f = g ↔ f.bv = w :=
  ⟨fun e => by rw [e, hg], fun e => VirtSanEq.u64_ext (by rw [e, hg])⟩

set_option maxHeartbeats 4000000 in
/-- **FL4's `supported` is `Vmx.readSupported`** (module docstring). -/
theorem zv_rsupp {a2 : A} (hc : VirtSanEq.CapAgree arI a2) (f : U64) :
    (if f = vcpu.vmx.GUEST_PERF_GLOBAL_CTRL then do
      let i2 ← arI.vcpu_capability a2 1156#u64
      let i3 ← i2 >>> 32#i32
      let i4 ← 1#u64 <<< 13#i32
      let i5 ← lift (i3 &&& i4)
      if i5 = 0#u64 then ok false
      else
        if f = vcpu.vmx.GUEST_PREEMPTION_TIMER_VALUE then do
          let i6 ← arI.vcpu_capability a2 1153#u64
          let i7 ← i6 >>> 32#i32
          let i8 ← 1#u64 <<< 6#i32
          let i9 ← lift (i7 &&& i8)
          if i9 = 0#u64 then ok false else ok true
        else ok true
    else
      if f = vcpu.vmx.GUEST_PREEMPTION_TIMER_VALUE then do
        let i2 ← arI.vcpu_capability a2 1153#u64
        let i3 ← i2 >>> 32#i32
        let i4 ← 1#u64 <<< 6#i32
        let i5 ← lift (i3 &&& i4)
        if i5 = 0#u64 then ok false else ok true
      else ok true) = ok (Fl4Spec.Vmx.readSupported f.bv) := by
  have hpp : ¬ vcpu.vmx.GUEST_PERF_GLOBAL_CTRL = vcpu.vmx.GUEST_PREEMPTION_TIMER_VALUE :=
    zv_n _ _ (by simp [vcpu.vmx.GUEST_PERF_GLOBAL_CTRL, vcpu.vmx.GUEST_PREEMPTION_TIMER_VALUE])
  unfold Fl4Spec.Vmx.readSupported
  by_cases h1 : f = vcpu.vmx.GUEST_PERF_GLOBAL_CTRL
  · have hb1 : f.bv = Fl4Spec.Vmx.guestPerfGlobalCtrl := by rw [h1, zv_perf_bv]
    have h2 : ¬ f = vcpu.vmx.GUEST_PREEMPTION_TIMER_VALUE := by rw [h1]; exact hpp
    rw [if_pos h1, if_pos hb1, hc, bind_ok, VirtSanEq.shr_32, bind_ok, VirtSanEq.shl_13, bind_ok]
    simp only [lift, bind_ok, if_neg h2]
    split
    · rename_i hz
      congr 1; symm; apply decide_eq_false; rw [not_not]
      exact (zv_and_zero_iff _ _ (by rfl)).1 hz
    · rename_i hz
      congr 1; symm; apply decide_eq_true
      intro h
      exact hz ((zv_and_zero_iff _ _ (by rfl)).2 h)
  · have hb1 : ¬ f.bv = Fl4Spec.Vmx.guestPerfGlobalCtrl := fun e => h1 ((zv_u64_eq_bv zv_perf_bv).2 e)
    rw [if_neg h1, if_neg hb1]
    by_cases h2 : f = vcpu.vmx.GUEST_PREEMPTION_TIMER_VALUE
    · have hb2 : f.bv = Fl4Spec.Vmx.guestPreemptionTimerValue := by rw [h2, zv_pretim_bv]
      rw [if_pos h2, if_pos hb2, hc, bind_ok, VirtSanEq.shr_32, bind_ok, VirtSanEq.shl_6, bind_ok]
      simp only [lift, bind_ok]
      split
      · rename_i hz
        congr 1; symm; apply decide_eq_false; rw [not_not]
        exact (zv_and_zero_iff _ _ (by rfl)).1 hz
      · rename_i hz
        congr 1; symm; apply decide_eq_true
        intro h
        exact hz ((zv_and_zero_iff _ _ (by rfl)).2 h)
    · have hb2 : ¬ f.bv = Fl4Spec.Vmx.guestPreemptionTimerValue :=
        fun e => h2 ((zv_u64_eq_bv zv_pretim_bv).2 e)
      rw [if_neg h2, if_neg hb2]

set_option maxHeartbeats 16000000 in
/-- **X86VCPUReadVMCS at `JAtZV3`, off SVM, `len ≥ 1`** (module docstring). -/
theorem JAtZV3.readVmcsJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hSy : ZvSyncKeep arI AR) (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a')
    (hvk : Fl4Spec.virtKind ≠ .svm) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) {len : U64} (hlen : 1 ≤ len.val) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) :
    vcpu.decode st arI s a fl4_abi.label.X86VCPUReadVMCS len p call buf ex ⦃ r =>
      VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ fl4_abi.label.X86VCPUReadVMCS len p call buf b c r ⦄ := by
  have g0 : len > 0#u64 := by scalar_tac
  have g1 : ¬ len < 1#u64 := by scalar_tac
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
  obtain ⟨f, hf, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 0#u64 (P1.LawfulStore.total (st := st)))
  obtain ⟨x, hx⟩ : ∃ x, (if len > 1#u64 then msg.syscall_arg st s ct buf 1#u64 else ok 0#u64) = ok x := by
    split
    · obtain ⟨x, hx, -⟩ := P1.spec_ex_fd (P0.msg.syscall_arg.p0 st s ct buf 1#u64 (P1.LawfulStore.total (st := st)))
      exact ⟨x, hx⟩
    · exact ⟨_, rfl⟩
  rw [if_pos g0, hf, bind_ok, hx, bind_ok]
  have n73 := zv_n fl4_abi.label.X86VCPUReadVMCS fl4_abi.label.X86VCPUSetTCB
    (by simp [fl4_abi.label.X86VCPUReadVMCS, fl4_abi.label.X86VCPUSetTCB])
  have n81 := zv_n fl4_abi.label.X86VCPUReadVMCS fl4_abi.label.X86VCPUWriteRegisters
    (by simp [fl4_abi.label.X86VCPUReadVMCS, fl4_abi.label.X86VCPUWriteRegisters])
  have n76 := zv_n fl4_abi.label.X86VCPUReadVMCS fl4_abi.label.X86VCPUFlushTLB
    (by simp [fl4_abi.label.X86VCPUReadVMCS, fl4_abi.label.X86VCPUFlushTLB])
  have n75 := zv_n fl4_abi.label.X86VCPUReadVMCS fl4_abi.label.X86VCPUWriteVMCS
    (by simp [fl4_abi.label.X86VCPUReadVMCS, fl4_abi.label.X86VCPUWriteVMCS])
  simp only [if_neg n73, if_neg n81, if_neg n76, eq_self_iff_true, ↓reduceIte, if_neg h2, if_neg n75, bind_ok,
    if_neg g1]
  rw [show (lift (Array.to_slice vcpu.READ_FIELDS) : Result (Slice U64)) = ok (Array.to_slice vcpu.READ_FIELDS)
    from rfl, bind_ok, zv_contains_read, bind_ok]
  have hf0 : ∀ args : List Fl4Spec.Data, VArgs st s ct buf len args → args.getD 0 0 = f.bv :=
    fun args hA => hA.a0 (by omega) hf
  by_cases hrd : Fl4Spec.Vmx.readable f.bv = true
  · rw [if_pos hrd]
    refine WP.spec_bind (hSy a1 p f _ hAR1) fun a2 hAR2 => ?_
    have J2 := J.archV hAR2
    rw [zv_rsupp (hCap a2) f, bind_ok]
    -- the word FL4 reads
    have hfv := (J.z2.zv.base.jvLay J.z2.zv.vm).vfit p hp
    have hv : VFits p := ⟨hfv.1, hfv.2⟩
    have ho := VirtMsrStore.vmcsOff_nat f.bv
    have hval : (L.mem s ⟨p.bv + Fl4Spec.vmcsOff f.bv⟩).bv = vs.get Fl4Spec.virtKind (.vmcs f.bv) := by
      have R0 := J.vr p hp vs hk
      rw [← v3_vmemW_al hv (by omega) ho.2 (L.mem s)]
      revert R0
      rcases hvk' : Fl4Spec.virtKind with _ | _ | _ | _
      · intro R0; exact (show False from R0).elim
      · intro R0
        exact (R0.vmcs f.bv (Or.inr hrd)).symm
      · exact absurd hvk' hvk
      · intro R0; exact (show False from R0).elim
    by_cases hsup : Fl4Spec.Vmx.readSupported f.bv = true
    · rw [if_pos hsup]
      unfold vcpu.read_vmcs
      rw [v3_vmcs_addr, bind_ok, L.read_eq, bind_ok]
      obtain ⟨s4, h4, -⟩ := P1.spec_ex_fd
        (P0.vcpu.reply.p0 st s call (L.mem s ⟨p.bv + Fl4Spec.vmcsOff f.bv⟩) (P1.LawfulStore.total (st := st)))
      rw [h4, bind_ok, WP.spec_ok]
      have hP : Fl4Spec.performVcpuInvocationF (Z := Unit) (.readVmcs p.bv f.bv) σ =
          ({([(L.mem s ⟨p.bv + Fl4Spec.vmcsOff f.bv⟩).bv], σ)}, False) := by
        rw [zv_perform_rvmcs hk, if_pos hsup, hval]
      refine ⟨ct, hct, fun args ec hA _ => Or.inr ⟨.readVmcs p.bv f.bv, _, s, σ, Ac, Lst, rfl, ?_, hP, J2,
        Or.inr (Or.inl ⟨_, rfl, h4⟩)⟩⟩
      rw [zv_rvmcs_bv, zv_decode_rvmcs_ok hvk (by rw [hA.1]; exact hlen) (hf0 args hA) hrd]
    · rw [if_neg hsup]
      obtain ⟨s4, h4, -⟩ := P1.spec_ex_fd (P0.vcpu.reply.p0 st s call 0#u64 (P1.LawfulStore.total (st := st)))
      rw [bind_ok, h4, bind_ok, WP.spec_ok]
      have hP : Fl4Spec.performVcpuInvocationF (Z := Unit) (.readVmcs p.bv f.bv) σ =
          ({([(0#u64 : U64).bv], σ)}, False) := by
        rw [zv_perform_rvmcs hk, if_neg hsup]; rfl
      refine ⟨ct, hct, fun args ec hA _ => Or.inr ⟨.readVmcs p.bv f.bv, _, s, σ, Ac, Lst, rfl, ?_, hP, J2,
        Or.inr (Or.inl ⟨_, rfl, h4⟩)⟩⟩
      rw [zv_rvmcs_bv, zv_decode_rvmcs_ok hvk (by rw [hA.1]; exact hlen) (hf0 args hA) hrd]
  · have hrd' : Fl4Spec.Vmx.readable f.bv = false := by simpa using hrd
    rw [if_neg hrd]
    simp only [error.illegal, bind_ok, WP.spec_ok]
    exact ⟨ct, hct, fun args ec hA _ => Or.inl ⟨_, .illegalOperation, rfl, trivial, by
      rw [zv_rvmcs_bv, zv_decode_rvmcs_bad hvk (by rw [hA.1]; exact hlen) (hf0 args hA) hrd' _ ec],
      rfl, J1⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **`VcpuNyp3`'s `readVmcs` field, proved** (module docstring). -/
theorem vcpuNyp_rvmcs {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} :
    VLabelOKN (L := L) arI AR fl4_abi.label.X86VCPUReadVMCS (fun _ _ => True)
      (Fl4Spec.virtKind ≠ .svm) 1 := by
  intro hK hSy hVA hCap _ V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c hv hl J hp hk _ _
  exact WP.spec_mono (J.readVmcsJ hK hSy hVA hCap hv hp hk hl call buf ex b c) fun r h => h.toC

end

end

end Fl4Proofs.P3
