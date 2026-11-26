/-
P3x for virtualization (line virt, gen 11): **VIRT-PLAN R1 — FL4's extracted sanitizer is the extended spec's**,
bit for bit (FL4 `crates/fl4-core/src/vcpu.rs` `sanitize_vmcs` l. 516-586, `controls` l. 511-515, `cr4_allowed`
l. 56-58, `contains` l. 500-510, `canonical` l. 476-480; spec `Fl4Spec/Ext/VirtSanitize` `sanitizeVmcs`,
`vmxControls`, `cr4AllowedHost`, `canonical`, field tables `Fl4Spec/Ext/VirtFields`).

* `WordResRel`: FL4's `KResult<u64>` against the spec's `Except SyscallError Word` (`Ok x` ↔ `.ok x.bv`, errors by
  P3's `SysErrRel`).
* `contains_write`: FL4's `contains(&WRITE_FIELDS, f)` is `Vmx.writable f` (loop lemma `contains_loop_eq`; FL4's
  `WRITE_FIELDS` is the spec's `vmxWriteFields` element for element, `write_map`).
* `controls_eq` (`vcpu::controls` = `vmxControls`), `cr4_allowed_eq` (`vcpu::cr4_allowed` = `cr4AllowedHost`),
  `canonical_eq` (`vcpu::canonical` = `canonical`).
* **`sanitize_vmcs_rel`**: for every field and value, `vcpu::sanitize_vmcs` returns, and its result is
  `WordResRel`-related to `sanitizeVmcs f.bv value.bv` (IllegalOperation off `WRITE_FIELDS`, InvalidArgument 1 for an
  activity state > 1, otherwise the same stored value). No field differs.
* **`write_vmcs_rel`** (with `Fl4Proofs.P3.VirtSanRel.VcpuRelVmx.write_vmcs`): FL4's WriteVMCS store of the sanitized
  value at `vmcs_addr` keeps `VcpuRelVmx`, against the spec's `vs.set .vmx (.vmcs f) x` with `x` the spec's
  sanitized value — the R1 statement over the gen-10 relation.

Named premise: **`CapAgree ar a` [P]** — `Arch::vcpu_capability` returns the spec's `vcpuCapability` (VIRT-PLAN §11.1
"the capability agreement … a [P] premise of the platform"); the spec's capability words are underspecified
(`Ext/VirtBackend.virtPlatform`), FL4's come from the trusted `Arch`.

Not here (open): `sanitize_vmcb` (SVM) — FL4's 50-arm match proof hits `maxRecDepth` in the per-arm closers
(the split itself and the default arm go through); `valid_pat`; `valid_xcr0`.
-/
import Fl4Proofs.P3.VirtSanRel
import Fl4Proofs.P1.FastDecline
import Fl4Proofs.P1.FastFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtSanEq
open fl4_core Fl4Spec Fl4Proofs.P3.VirtSanRel

theorem u64_ext {x y : U64} (h : x.bv = y.bv) : x = y := by
  cases x; cases y; cases h; rfl

theorem shr_i32 (x : U64) (k : I32) (h0 : 0 ≤ k.val) (h : k.toNat < 64) :
    x >>> k = ok ⟨x.bv >>> k.toNat⟩ := by
  show UScalar.shiftRight_IScalar x k = _
  unfold UScalar.shiftRight_IScalar UScalar.shiftRight
  rw [if_pos h0, if_pos (by simpa using h)]; rfl

theorem shl_i32 (x : U64) (k : I32) (h0 : 0 ≤ k.val) (h : k.toNat < 64) :
    x <<< k = ok ⟨x.bv <<< k.toNat⟩ := by
  show UScalar.shiftLeft_IScalar x k = _
  unfold UScalar.shiftLeft_IScalar UScalar.shiftLeft
  rw [if_pos h0, if_pos (by simpa using h)]; rfl

example : (1#u64 <<< 12#i32) = ok 4096#u64 := by
  rw [shl_i32 _ _ (by decide) (by decide)]; rfl

theorem write_map : vcpu.WRITE_FIELDS.val.map (·.bv) = Vmx.vmxWriteFields := by
  simp only [vcpu.WRITE_FIELDS, vcpu.vmx.CONTROL_CR0_MASK, vcpu.vmx.CONTROL_CR0_READ_SHADOW, vcpu.vmx.CONTROL_CR4_MASK, vcpu.vmx.CONTROL_CR4_READ_SHADOW, vcpu.vmx.CONTROL_ENTRY_CONTROLS, vcpu.vmx.CONTROL_ENTRY_EXCEPTION_ERROR_CODE, vcpu.vmx.CONTROL_ENTRY_INSTRUCTION_LENGTH, vcpu.vmx.CONTROL_ENTRY_INTERRUPTION_INFO, vcpu.vmx.CONTROL_EXCEPTION_BITMAP, vcpu.vmx.CONTROL_EXIT_CONTROLS, vcpu.vmx.CONTROL_PIN_EXECUTION_CONTROLS, vcpu.vmx.CONTROL_PRIMARY_PROCESSOR_CONTROLS, vcpu.vmx.CONTROL_SECONDARY_PROCESSOR_CONTROLS, vcpu.vmx.CONTROL_TSC_OFFSET, vcpu.vmx.GUEST_ACTIVITY, vcpu.vmx.GUEST_CR3, vcpu.vmx.GUEST_CS_ACCESS_RIGHTS, vcpu.vmx.GUEST_CS_BASE, vcpu.vmx.GUEST_CS_LIMIT, vcpu.vmx.GUEST_CS_SELECTOR, vcpu.vmx.GUEST_DEBUGCTRL, vcpu.vmx.GUEST_DR7, vcpu.vmx.GUEST_DS_ACCESS_RIGHTS, vcpu.vmx.GUEST_DS_BASE, vcpu.vmx.GUEST_DS_LIMIT, vcpu.vmx.GUEST_DS_SELECTOR, vcpu.vmx.GUEST_EFER, vcpu.vmx.GUEST_ES_ACCESS_RIGHTS, vcpu.vmx.GUEST_ES_BASE, vcpu.vmx.GUEST_ES_LIMIT, vcpu.vmx.GUEST_ES_SELECTOR, vcpu.vmx.GUEST_FS_ACCESS_RIGHTS, vcpu.vmx.GUEST_FS_BASE, vcpu.vmx.GUEST_FS_LIMIT, vcpu.vmx.GUEST_FS_SELECTOR, vcpu.vmx.GUEST_GDTR_BASE, vcpu.vmx.GUEST_GDTR_LIMIT, vcpu.vmx.GUEST_GS_ACCESS_RIGHTS, vcpu.vmx.GUEST_GS_BASE, vcpu.vmx.GUEST_GS_LIMIT, vcpu.vmx.GUEST_GS_SELECTOR, vcpu.vmx.GUEST_IDTR_BASE, vcpu.vmx.GUEST_IDTR_LIMIT, vcpu.vmx.GUEST_INTERRUPTABILITY, vcpu.vmx.GUEST_LDTR_ACCESS_RIGHTS, vcpu.vmx.GUEST_LDTR_BASE, vcpu.vmx.GUEST_LDTR_LIMIT, vcpu.vmx.GUEST_LDTR_SELECTOR, vcpu.vmx.GUEST_PAT, vcpu.vmx.GUEST_PDPTE0, vcpu.vmx.GUEST_PDPTE1, vcpu.vmx.GUEST_PDPTE2, vcpu.vmx.GUEST_PDPTE3, vcpu.vmx.GUEST_PENDING_DEBUG_EXCEPTIONS, vcpu.vmx.GUEST_PERF_GLOBAL_CTRL, vcpu.vmx.GUEST_PREEMPTION_TIMER_VALUE, vcpu.vmx.GUEST_RFLAGS, vcpu.vmx.GUEST_RIP, vcpu.vmx.GUEST_RSP, vcpu.vmx.GUEST_SMBASE, vcpu.vmx.GUEST_SS_ACCESS_RIGHTS, vcpu.vmx.GUEST_SS_BASE, vcpu.vmx.GUEST_SS_LIMIT, vcpu.vmx.GUEST_SS_SELECTOR, vcpu.vmx.GUEST_SYSENTER_CS, vcpu.vmx.GUEST_SYSENTER_EIP, vcpu.vmx.GUEST_SYSENTER_ESP, vcpu.vmx.GUEST_TR_ACCESS_RIGHTS, vcpu.vmx.GUEST_TR_BASE, vcpu.vmx.GUEST_TR_LIMIT, vcpu.vmx.GUEST_TR_SELECTOR, vcpu.vmx.GUEST_CR0, vcpu.vmx.GUEST_CR4]
  simp
  simp only [Vmx.vmxWriteFields, Vmx.guestRip, Vmx.guestRsp, Vmx.guestEsSelector, Vmx.guestCsSelector, Vmx.guestSsSelector, Vmx.guestDsSelector, Vmx.guestFsSelector, Vmx.guestGsSelector, Vmx.guestLdtrSelector, Vmx.guestTrSelector, Vmx.guestDebugctrl, Vmx.guestPat, Vmx.guestEfer, Vmx.guestPerfGlobalCtrl, Vmx.guestPdpte0, Vmx.guestPdpte1, Vmx.guestPdpte2, Vmx.guestPdpte3, Vmx.guestEsLimit, Vmx.guestCsLimit, Vmx.guestSsLimit, Vmx.guestDsLimit, Vmx.guestFsLimit, Vmx.guestGsLimit, Vmx.guestLdtrLimit, Vmx.guestTrLimit, Vmx.guestGdtrLimit, Vmx.guestIdtrLimit, Vmx.guestEsAccessRights, Vmx.guestCsAccessRights, Vmx.guestSsAccessRights, Vmx.guestDsAccessRights, Vmx.guestFsAccessRights, Vmx.guestGsAccessRights, Vmx.guestLdtrAccessRights, Vmx.guestTrAccessRights, Vmx.guestInterruptability, Vmx.guestSmbase, Vmx.guestSysenterCs, Vmx.guestPreemptionTimerValue, Vmx.guestEsBase, Vmx.guestCsBase, Vmx.guestSsBase, Vmx.guestDsBase, Vmx.guestFsBase, Vmx.guestGsBase, Vmx.guestLdtrBase, Vmx.guestTrBase, Vmx.guestGdtrBase, Vmx.guestIdtrBase, Vmx.guestDr7, Vmx.guestRflags, Vmx.guestPendingDebugExceptions, Vmx.guestSysenterEsp, Vmx.guestSysenterEip, Vmx.controlCr0ReadShadow, Vmx.controlCr4ReadShadow, Vmx.guestCr3, Vmx.controlEntryInterruptionInfo, Vmx.controlEntryExceptionErrorCode, Vmx.controlEntryInstructionLength, Vmx.controlTscOffset, Vmx.guestActivity, Vmx.controlExceptionBitmap, Vmx.controlCr0Mask, Vmx.controlCr4Mask, Vmx.controlPinExecutionControls, Vmx.controlPrimaryProcessorControls, Vmx.controlSecondaryProcessorControls, Vmx.controlEntryControls, Vmx.controlExitControls, Vmx.guestCr0, Vmx.guestCr4]
  simp

theorem contains_loop_eq (s : Slice U64) (f : U64) (i : Usize) (found : Bool) (hi : i.val ≤ s.val.length) :
    vcpu.contains_loop s f i found = ok (found || decide (f ∈ s.val.drop i.val)) := by
  have hL : s.length = s.val.length := rfl
  apply P1.eq_of_spec_fd
  unfold vcpu.contains_loop
  apply loop.spec_decr_nat (measure := fun y : Usize × Bool => s.val.length - y.1.val)
    (inv := fun y => y.1.val ≤ s.val.length ∧
      (y.2 || decide (f ∈ s.val.drop y.1.val)) = (found || decide (f ∈ s.val.drop i.val)))
  · rintro ⟨j, fd⟩ ⟨hj, he⟩
    simp only at hj he
    unfold vcpu.contains_loop.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : j.val < s.val.length := by rw [← hL]; simpa using hlt
      step with Aeneas.Std.Slice.index_usize_spec as ⟨x, hx⟩
      have hd : s.val.drop j.val = x :: s.val.drop (j.val + 1) := by
        rw [hx]; exact List.drop_eq_getElem_cons _
      by_cases hxf : x = f
      · simp only [hxf, if_true, bind_ok]
        step as ⟨j1, hj1⟩
        refine ⟨by omega, ?_, by omega⟩
        rw [← he, hd, hxf]; simp
      · simp only [hxf, if_false, bind_ok]
        step as ⟨j1, hj1⟩
        refine ⟨by omega, ?_, by omega⟩
        have hfx : f ≠ x := fun h => hxf h.symm
        rw [← he, hd, hj1]; simp [hfx]
    · rename_i hge
      have h2 : ¬ j.val < s.val.length := by rw [← hL]; simpa using hge
      have : j.val = s.val.length := by omega
      refine (WP.spec_ok _).2 ?_
      rw [← he, this]; simp
  · exact ⟨hi, rfl⟩

theorem shl_1 (x : U64) : x <<< (1#i32) = ok ⟨x.bv <<< 1⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_2 (x : U64) : x <<< (2#i32) = ok ⟨x.bv <<< 2⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_3 (x : U64) : x <<< (3#i32) = ok ⟨x.bv <<< 3⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_5 (x : U64) : x <<< (5#i32) = ok ⟨x.bv <<< 5⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_6 (x : U64) : x <<< (6#i32) = ok ⟨x.bv <<< 6⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_9 (x : U64) : x <<< (9#i32) = ok ⟨x.bv <<< 9⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_12 (x : U64) : x <<< (12#i32) = ok ⟨x.bv <<< 12⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_13 (x : U64) : x <<< (13#i32) = ok ⟨x.bv <<< 13⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_14 (x : U64) : x <<< (14#i32) = ok ⟨x.bv <<< 14⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_15 (x : U64) : x <<< (15#i32) = ok ⟨x.bv <<< 15⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_16 (x : U64) : x <<< (16#i32) = ok ⟨x.bv <<< 16⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_17 (x : U64) : x <<< (17#i32) = ok ⟨x.bv <<< 17⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_18 (x : U64) : x <<< (18#i32) = ok ⟨x.bv <<< 18⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_19 (x : U64) : x <<< (19#i32) = ok ⟨x.bv <<< 19⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_20 (x : U64) : x <<< (20#i32) = ok ⟨x.bv <<< 20⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_21 (x : U64) : x <<< (21#i32) = ok ⟨x.bv <<< 21⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_22 (x : U64) : x <<< (22#i32) = ok ⟨x.bv <<< 22⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_24 (x : U64) : x <<< (24#i32) = ok ⟨x.bv <<< 24⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_29 (x : U64) : x <<< (29#i32) = ok ⟨x.bv <<< 29⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_31 (x : U64) : x <<< (31#i32) = ok ⟨x.bv <<< 31⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shl_32 (x : U64) : x <<< (32#i32) = ok ⟨x.bv <<< 32⟩ := by
  rw [shl_i32 x _ (by decide) (by decide)]; rfl
theorem shr_13 (x : U64) : x >>> (13#i32) = ok ⟨x.bv >>> 13⟩ := by
  rw [shr_i32 x _ (by decide) (by decide)]; rfl
theorem shr_32 (x : U64) : x >>> (32#i32) = ok ⟨x.bv >>> 32⟩ := by
  rw [shr_i32 x _ (by decide) (by decide)]; rfl
theorem shr_47 (x : U64) : x >>> (47#i32) = ok ⟨x.bv >>> 47⟩ := by
  rw [shr_i32 x _ (by decide) (by decide)]; rfl
theorem shr_56 (x : U64) : x >>> (56#i32) = ok ⟨x.bv >>> 56⟩ := by
  rw [shr_i32 x _ (by decide) (by decide)]; rfl

section
variable {A : Type} (ar : machine.Arch A) (a : A)

/-- **[P]** The platform agreement on the VMX capability words (VIRT-PLAN §11.1): FL4's
`Arch::vcpu_capability` is the spec's `vcpuCapability` for every index. -/
def CapAgree : Prop := ∀ g : U64, ar.vcpu_capability a g = ok ⟨vcpuCapability g.bv⟩

/-- FL4's `KResult<u64>` against the spec's `Except SyscallError Word`. -/
def WordResRel : core.result.Result U64 error.Exc → Except SyscallError Word → Prop
  | .Ok x, .ok y => x.bv = y
  | .Err e, .error e' => SysErrRel e e'
  | _, _ => False

theorem EXC_eq : vcpu.EXCEPTIONS = ok 393218#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.EXCEPTIONS.spec
theorem CR0O_eq : vcpu.CR0_OWNED = ok 2147155904#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.CR0_OWNED.spec
theorem PIN_eq : vcpu.PIN_ALLOWED = ok 41#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.PIN_ALLOWED.spec
theorem PRIMF_eq : vcpu.PRIMARY_FORCED = ok 2996308992#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.PRIMARY_FORCED.spec
theorem SECA_eq : vcpu.SECONDARY_ALLOWED = ok 71918#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.SECONDARY_ALLOWED.spec
theorem EXITF_eq : vcpu.EXIT_FORCED = ok 3932676#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.EXIT_FORCED.spec
theorem DBG_eq : vcpu.DEBUGCTL_ALLOWED = ok 2#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.DEBUGCTL_ALLOWED.spec
theorem CR4A_eq : vcpu.CR4_ALLOWED = ok 7802879#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.CR4_ALLOWED.spec

variable {ar a}

theorem controls_eq (hc : CapAgree ar a) (msr value forced allowed : U64) :
    vcpu.controls ar a msr value forced allowed = ok ⟨vmxControls msr.bv value.bv forced.bv allowed.bv⟩ := by
  have hc' : ∀ g, ar.vcpu_capability a g = ok ⟨vcpuCapability g.bv⟩ := hc
  unfold vcpu.controls vmxControls
  simp only [hc', lift, bind_ok, shl_1, shl_2, shl_3, shl_5, shl_6, shl_9, shl_12, shl_13, shl_14, shl_15, shl_16, shl_17, shl_18, shl_19, shl_20, shl_21, shl_22, shl_24, shl_29, shl_31, shl_32, shr_13, shr_32, shr_47, shr_56]
  congr 1

theorem cr4Allowed_bv : (7802879#u64).bv = cr4Allowed := by decide
theorem bne_u64 (x y : U64) : (x != y) = !decide (x.bv = y.bv) := by
  by_cases h : x = y
  · subst h; simp
  · have : x.bv ≠ y.bv := fun e => h (u64_ext e)
    simp [h, this]

theorem ite_bne {α : Type _} (x y : U64) (A B : α) :
    (if (x != y) = true then A else B) = (if x.bv = y.bv then B else A) := by
  by_cases h : x = y
  · subst h; simp
  · have : x.bv ≠ y.bv := fun e => h (u64_ext e)
    simp [h, this]

theorem bind_ite_ok {α β : Type} (c : Prop) [Decidable c] (x y : α) (f : α → Result β) :
    (do let z ← (if c then ok x else ok y); f z) = f (if c then x else y) := by
  by_cases h : c <;> simp [h]

theorem cr4_allowed_eq (hc : CapAgree ar a) : vcpu.cr4_allowed ar a = ok ⟨cr4AllowedHost⟩ := by
  have hc' : ∀ g, ar.vcpu_capability a g = ok ⟨vcpuCapability g.bv⟩ := hc
  unfold vcpu.cr4_allowed cr4AllowedHost hostXcr0
  simp only [hc', lift, bind_ok, CR4A_eq, shl_9, shl_22, bne_u64, UScalar.bv_and, U64.ofNat_bv, U64.bv]
  split <;> split <;> rename_i h1 h2
  all_goals first
    | (exact congrArg ok (u64_ext (by decide)))
    | (exfalso; revert h1 h2; simp [UScalarTy.numBits]; done)
    | (congr 1; apply u64_ext; simp only [U64.ofNat_bv, UScalar.bv_and, UScalar.bv_not, U64.bv, UScalarTy.numBits, cr4Allowed]; decide)
    | skip

theorem contains_write (f : U64) :
    vcpu.contains (Array.to_slice vcpu.WRITE_FIELDS) f = ok (Vmx.writable f.bv) := by
  unfold vcpu.contains
  rw [contains_loop_eq _ _ _ _ (by simp)]
  simp only [Bool.false_or, List.drop_zero, Vmx.writable, ← write_map]
  congr 1
  rw [decide_eq_decide]
  have h0 : (Array.to_slice vcpu.WRITE_FIELDS).val = vcpu.WRITE_FIELDS.val := by
    first | rfl | simp [Array.to_slice]
  rw [h0]
  show f ∈ List.drop 0 vcpu.WRITE_FIELDS.val ↔ _
  rw [List.drop_zero]
  constructor
  · intro h; exact List.mem_map_of_mem h
  · intro h; obtain ⟨y, hy, e⟩ := List.mem_map.1 h; rwa [← u64_ext e]

set_option maxHeartbeats 4000000 in
theorem sanitize_vmcs_rel (hc : CapAgree ar a) (f value : U64) :
    ∃ r, vcpu.sanitize_vmcs ar a f value = ok r ∧ WordResRel r (sanitizeVmcs f.bv value.bv) := by
  have hc' : ∀ g, ar.vcpu_capability a g = ok ⟨vcpuCapability g.bv⟩ := hc
  unfold vcpu.sanitize_vmcs
  simp only [lift, bind_ok, contains_write]
  by_cases hw : Vmx.writable f.bv = true
  · rw [if_pos hw]
    revert hw
    split
    case h_13 =>
      rename_i n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12
      intro hw
      have e1 : f.bv ≠ Vmx.guestActivity := fun h => n1 (u64_ext h)
      have e2 : f.bv ≠ Vmx.controlExceptionBitmap := fun h => n2 (u64_ext h)
      have e3 : f.bv ≠ Vmx.controlCr0Mask := fun h => n3 (u64_ext h)
      have e4 : f.bv ≠ Vmx.controlCr4Mask := fun h => n4 (u64_ext h)
      have e5 : f.bv ≠ Vmx.controlPinExecutionControls := fun h => n5 (u64_ext h)
      have e6 : f.bv ≠ Vmx.controlPrimaryProcessorControls := fun h => n6 (u64_ext h)
      have e7 : f.bv ≠ Vmx.controlSecondaryProcessorControls := fun h => n7 (u64_ext h)
      have e8 : f.bv ≠ Vmx.controlExitControls := fun h => n8 (u64_ext h)
      have e9 : f.bv ≠ Vmx.controlEntryControls := fun h => n9 (u64_ext h)
      have e10 : f.bv ≠ Vmx.guestCr0 := fun h => n10 (u64_ext h)
      have e11 : f.bv ≠ Vmx.guestCr4 := fun h => n11 (u64_ext h)
      have e12 : f.bv ≠ Vmx.guestDebugctrl := fun h => n12 (u64_ext h)
      have hs : sanitizeVmcs f.bv value.bv = .ok (vmxWidthMask f.bv value.bv) := by
        simp only [sanitizeVmcs, hw, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, if_false, false_and,
          not_true_eq_false]
      rw [hs]
      try simp only [bind_ok, lift, shr_13]
      split
      · rename_i hm
        have h0 : f.bv >>> (13 : Nat) = 0 := congrArg UScalar.bv hm
        refine ⟨_, rfl, ?_⟩
        show U64.bv _ = vmxWidthMask f.bv value.bv
        unfold vmxWidthMask Vmx.fieldWidth
        rw [if_pos h0]
        try rfl
      · rename_i hm
        have h2 : f.bv >>> (13 : Nat) = 2 := congrArg UScalar.bv hm
        refine ⟨_, rfl, ?_⟩
        show U64.bv _ = vmxWidthMask f.bv value.bv
        unfold vmxWidthMask Vmx.fieldWidth
        rw [if_neg (by rw [h2]; decide), if_pos h2]
        try rfl
      · rename_i hm1 hm2
        have h0 : f.bv >>> (13 : Nat) ≠ 0 := fun h => hm1 (u64_ext h)
        have h2 : f.bv >>> (13 : Nat) ≠ 2 := fun h => hm2 (u64_ext h)
        refine ⟨_, rfl, ?_⟩
        show U64.bv _ = vmxWidthMask f.bv value.bv
        unfold vmxWidthMask Vmx.fieldWidth
        rw [if_neg h0, if_neg h2]
        try rfl
    case h_1 =>
      intro hw
      simp only [bind_ok, lift, U64.ofNat_bv, U64.bv, UScalarTy.numBits] at hw ⊢
      by_cases hv : value > 1#u64
      · have hv1 : (1 : Word) < value.bv := by rw [BitVec.lt_def]; exact hv
        have hs : sanitizeVmcs (18470#64) value.bv = .error (.invalidArgument 1) := by
          simp [sanitizeVmcs, hw, Vmx.guestActivity]; exact hv1
        rw [if_pos hv, hs]; exact ⟨_, rfl, rfl⟩
      · rw [if_neg hv]
        have hv1 : ¬ (1 : Word) < value.bv := by rw [BitVec.lt_def]; exact hv
        have hs : sanitizeVmcs (18470#64) value.bv = .ok (value.bv &&& 0xffff_ffff) := by
          simp [sanitizeVmcs, hw, Vmx.guestActivity, vmxWidthMask, Vmx.fieldWidth]
          exact BitVec.not_lt.mp hv1
        rw [hs]
        simp only [shr_13, bind_ok]
        exact ⟨_, rfl, rfl⟩
    all_goals
      intro hw
      simp only [EXC_eq, CR0O_eq, PIN_eq, PRIMF_eq, SECA_eq, EXITF_eq, DBG_eq, cr4_allowed_eq hc, controls_eq hc,
        hc', bind_ok, bind_tc_ok, lift, UScalarTy.numBits, vcpu.PRIMARY_ALLOWED, ite_bne, bind_ite_ok, shl_1, shl_2, shl_3, shl_5, shl_6, shl_9, shl_12, shl_13, shl_14, shl_15, shl_16, shl_17, shl_18, shl_19, shl_20, shl_21, shl_22, shl_24, shl_29, shl_31, shl_32, shr_13, shr_32, shr_47, shr_56, U64.ofNat_bv, U64.bv] at hw ⊢
      repeat' split
      all_goals try simp only [bind_ok, bind_tc_ok]
      all_goals first
        | (exfalso; rename_i h1 h2 h3
           first
             | exact absurd (congrArg UScalar.bv h3) (by decide)
             | exact absurd (congrArg UScalar.bv h2) (by decide)
             | exact absurd (congrArg UScalar.bv h1) (by decide))
        | (exfalso; rename_i hm1 hm2
           first | exact hm1 (u64_ext (by decide)) | exact hm2 (u64_ext (by decide)))
        | (rename_i hv
           have hv1 : (1 : Word) < value.bv := by rw [BitVec.lt_def]; exact hv
           refine ⟨_, rfl, ?_⟩
           simp [WordResRel, SysErrRel, sanitizeVmcs, hw, hv1, Vmx.guestActivity]; done)
        | (rename_i hm; exact absurd (congrArg UScalar.bv hm) (by decide))
        | (refine ⟨_, rfl, ?_⟩
           simp [WordResRel, SysErrRel, sanitizeVmcs, hw, vmxWidthMask, Vmx.fieldWidth, Vmx.guestActivity, Vmx.controlExceptionBitmap, Vmx.controlCr0Mask, Vmx.controlCr4Mask, Vmx.controlPinExecutionControls, Vmx.controlPrimaryProcessorControls, Vmx.controlSecondaryProcessorControls, Vmx.controlExitControls, Vmx.controlEntryControls, Vmx.guestCr0, Vmx.guestCr4, Vmx.guestDebugctrl,
             vcpuExceptions, cr0Owned, pinAllowed, primaryForced, primaryAllowed, secondaryAllowed, exitForced,
             debugctlAllowed]; done)
        | (refine ⟨_, rfl, ?_⟩
           simp_all [WordResRel, SysErrRel, sanitizeVmcs, vmxWidthMask, Vmx.fieldWidth, bne_u64, Vmx.controlEntryControls,
             U64.ofNat_bv, UScalarTy.numBits]; done)
        | (refine ⟨_, rfl, ?_⟩
           rename_i hc0
           simp at hc0
           simp [WordResRel, sanitizeVmcs, hw, vmxWidthMask, Vmx.fieldWidth, Vmx.controlEntryControls,
             Vmx.guestActivity, Vmx.controlExceptionBitmap, Vmx.controlCr0Mask, Vmx.controlCr4Mask,
             Vmx.controlPinExecutionControls, Vmx.controlPrimaryProcessorControls,
             Vmx.controlSecondaryProcessorControls, Vmx.controlExitControls, Vmx.guestCr0, Vmx.guestCr4,
             Vmx.guestDebugctrl, cr0Owned, hc0]; done)
  · rw [if_neg hw]
    refine ⟨_, rfl, ?_⟩
    simp [sanitizeVmcs, hw, WordResRel, SysErrRel]


/-- **WriteVMCS over the relation** (VIRT-PLAN R1 stated over `VcpuRelVmx`): when FL4's `sanitize_vmcs` stores `r`,
the spec's `sanitizeVmcs` stores the same word, and FL4's store of it at the field's place (`vmcs_addr`) relates to
the spec's VCPU with that field set. -/
theorem write_vmcs_rel (hc : CapAgree ar a) {mem : Word → Word} {v : Word} {vs : VcpuState} {f value r : U64}
    (hr : vcpu.sanitize_vmcs ar a f value = ok (.Ok r)) (h : VcpuRelVmx mem v vs) :
    sanitizeVmcs f.bv value.bv = .ok r.bv ∧
      VcpuRelVmx (Function.update mem (v + vmcsOff f.bv) r.bv) v (vs.set .vmx (.vmcs f.bv) r.bv) := by
  obtain ⟨r', e, hrel⟩ := sanitize_vmcs_rel hc f value
  rw [hr] at e
  have e' : r' = .Ok r := (P1.ok_inj_ff e).symm
  subst e'
  have hs : sanitizeVmcs f.bv value.bv = .ok r.bv := by
    rcases hsv : sanitizeVmcs f.bv value.bv with er | y
    · rw [hsv] at hrel; exact absurd hrel (by simp [WordResRel])
    · rw [hsv] at hrel; simp only [WordResRel] at hrel; rw [hrel]
  refine ⟨hs, VcpuRelVmx.write_vmcs h ?_⟩
  by_contra hw
  simp only [Bool.not_eq_true] at hw
  simp [sanitizeVmcs, hw] at hs

/-! ## SVM -/

theorem mk_inj (x y : BitVec 64) : (@UScalar.mk .U64 x = @UScalar.mk .U64 y) = (x = y) :=
  propext ⟨congrArg UScalar.bv, fun h => h ▸ rfl⟩

theorem MAX_bv : core.num.U64.MAX.bv = ~~~(0 : Word) := by
  first | rfl | decide | (simp [core.num.U64.MAX, U64.rMax]; done) | (apply BitVec.eq_of_toNat_eq; simp [core.num.U64.MAX, U64.rMax])
theorem canonical_eq (value width : U64) :
    vcpu.canonical value width = ok (canonical value.bv width.bv) := by
  have r56 : ∀ x : Word, x >>> (56 : Word) = x >>> (56 : Nat) := fun _ => rfl
  have r47 : ∀ x : Word, x >>> (47 : Word) = x >>> (47 : Nat) := fun _ => rfl
  have hm : core.num.U64.MAX.bv = ~~~(0 : Word) := MAX_bv
  unfold vcpu.canonical canonical
  by_cases hw : width = 57#u64
  · have hw' : width.bv = 57 := by rw [hw]; rfl
    simp only [if_pos hw, hw', if_true, bind_ok, bind_tc_ok, shr_56, r56]
    by_cases ht : value.bv >>> (56 : Nat) = 0#64 <;>
      simp [UScalar.eq_equiv_bv_eq, ht, U64.ofNat_bv, UScalarTy.numBits, shr_56, core.num.U64.MAX, U64.rMax]
  · have hw' : width.bv ≠ 57 := fun h => hw (u64_ext h)
    simp only [if_neg hw, hw', if_false, bind_ok, bind_tc_ok, shr_47, r47]
    by_cases ht : value.bv >>> (47 : Nat) = 0#64 <;>
      simp [UScalar.eq_equiv_bv_eq, ht, U64.ofNat_bv, UScalarTy.numBits, shr_47, core.num.U64.MAX, U64.rMax]


end

end Fl4Proofs.P3.VirtSanEq
