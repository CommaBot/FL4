/-
P3x for virtualization (line virt, gen 13, item 2; proofs/VIRT-PLAN.md R1, last piece): **FL4's MSR decode is the
extended spec's** — `vcpu::msr_addr` (FL4 `crates/fl4-core/src/vcpu.rs` l. 805-819, with `msr_slot` l. 784-793 and
`svm_msr` l. 794-804) and the WriteMSR value checks of `vcpu::decode` (l. 981-1006) against the spec's MSR fields
(`Fl4Spec/Ext/VirtFields` `vcpuMsrs`, `VField.canon`) and `checkMsrWrite` (`Ext/VirtSanitize`).

* `svmMsrOff`, `msrOff amd m`: FL4's offset of MSR field `m` from the VCPU base, by backend (`amd`), read on the
  spec's words (proof-side transcription of `svm_msr` / `msr_slot` / `msr_addr`'s constants).
* **`msr_addr_eq`**: for every base `v`, field `f` and backend, `vcpu.msr_addr v f amd` returns, and its result is
  `msrOff amd f.bv` added to `v`; `svm_msr_eq`, `msr_slot_eq` its pieces.
* **`msrOff_isSome`**: FL4 has an address exactly for the spec's MSR fields `vcpuMsrs` (both backends): ReadMSR /
  WriteMSR's `IllegalOperation` off the table agrees.
* **`msrOff_rel_vmx`**, **`msrOff_rel_svm`**: the address is the relation's place of the spec's value —
  `VcpuRelVmx mem v vs` (resp. `VcpuRelSvm`) and `msrOff false m = some o` (resp. `true`) give
  `vs.get .vmx (.msr m) = mem (v + o)` (VMX: `MSRS + 8·slot`, `CR2`, `XCR0`, `VM_IBPB_DEFER`; SVM: the VMCB save-area
  words `VField.canon` names, and the two shared pseudo-MSRs). So FL4's ReadMSR reads the spec's value.
* `fl4WriteMsr`: FL4's WriteMSR arm after its length check, **transcribed** from `vcpu::decode` (l. 987-1006; the
  extracted `vcpu.decode` inlines it four times with the disjunctions unfolded into nested `if`s): `msr_addr`, then
  LSTAR / CSTAR / KERNEL_GS_BASE `canonical(value, vcpu_capability(1))`, XCR0 `valid_xcr0(value,
  vcpu_capability(0))`, `MSR_VM_IBPB_DEFER` `value ≤ 1`, each failure `invalid_arg(1)`; `Ok x` = FL4 then writes
  `value` at `x`. This is a statement about the arm's decision, not a walk of `vcpu.decode` itself.
* **`fl4WriteMsr_rel`** (under `CapAgree ar a` [P]): it returns, its result agrees with `checkMsrWrite f.bv
  value.bv` (same error, or success), and on success the address is `v + msrOff amd f.bv`.

Named premise: `CapAgree ar a` [P] (gen 11's, VIRT-PLAN §11.1 capability agreement; only in `fl4WriteMsr_rel`).
No other premise. New file only.
-/
import Fl4Proofs.P3.VirtSanSvm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtMsrEq
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanSvm

/-! ## FL4's offsets on the spec's words -/

/-- FL4 `vcpu::svm_msr` on the spec's words: the VMCB save-area word of a syscall MSR or CR2. -/
def svmMsrOff (m : Word) : Option Word :=
  if m = msrStar then some Svm.star
  else if m = msrLstar then some Svm.lstar
  else if m = msrCstar then some Svm.cstar
  else if m = msrFmask then some Svm.sfmask
  else if m = msrKernelGsBase then some Svm.kernelGsBase
  else if m = msrCr2 then some Svm.cr2
  else none

/-- FL4 `vcpu::msr_addr`'s offset of MSR field `m` from the VCPU base (`amd`: the SVM backend). -/
def msrOff (amd : Bool) (m : Word) : Option Word :=
  if m = msrXcr0 then some VcpuLay.XCR0
  else if m = msrVmIbpbDefer then some VcpuLay.VM_IBPB_DEFER
  else if amd then svmMsrOff m
  else if m = msrCr2 then some VcpuLay.CR2
  else (msrSlot m).map fun i => VcpuLay.MSRS + i * 8

theorem STAR_eq : vcpu.svm.STAR = ok 1536#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.svm.STAR.spec
theorem LSTAR_eq : vcpu.svm.LSTAR = ok 1544#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.svm.LSTAR.spec
theorem CSTAR_eq : vcpu.svm.CSTAR = ok 1552#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.svm.CSTAR.spec
theorem SFMASK_eq : vcpu.svm.SFMASK = ok 1560#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.svm.SFMASK.spec
theorem KGS_eq : vcpu.svm.KERNEL_GS_BASE = ok 1568#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.svm.KERNEL_GS_BASE.spec
theorem SCR2_eq : vcpu.svm.CR2 = ok 1600#u64 := P1.eq_of_spec_fd P0.Consts.vcpu.svm.CR2.spec

theorem svm_msr_eq (f : U64) : ∃ o, vcpu.svm_msr f = ok o ∧ o.map (·.bv) = svmMsrOff f.bv := by
  unfold vcpu.svm_msr
  split
  all_goals try subst_vars
  all_goals first
    | (rw [STAR_eq, bind_ok]; exact ⟨_, rfl, by rfl⟩)
    | (rw [LSTAR_eq, bind_ok]; exact ⟨_, rfl, by rfl⟩)
    | (rw [CSTAR_eq, bind_ok]; exact ⟨_, rfl, by rfl⟩)
    | (rw [SFMASK_eq, bind_ok]; exact ⟨_, rfl, by rfl⟩)
    | (rw [KGS_eq, bind_ok]; exact ⟨_, rfl, by rfl⟩)
    | (rw [SCR2_eq, bind_ok]; exact ⟨_, rfl, by rfl⟩)
    | skip
  refine ⟨none, rfl, ?_⟩
  unfold svmMsrOff
  repeat rw [if_neg (fun hm => absurd (u64_ext (y := ⟨_⟩) hm) (by assumption))]
  rfl

theorem msr_slot_eq (f : U64) : ∃ o, vcpu.msr_slot f = ok o ∧ o.map (·.bv) = msrSlot f.bv := by
  unfold vcpu.msr_slot
  split
  all_goals try subst_vars
  all_goals first
    | exact ⟨_, rfl, by rfl⟩
    | exact ⟨_, rfl, by decide⟩
    | skip
  refine ⟨none, rfl, ?_⟩
  unfold msrSlot
  repeat rw [if_neg (fun hm => absurd (u64_ext (y := ⟨_⟩) hm) (by assumption))]
  rfl

theorem wadd_bv (x y : U64) : (core.num.U64.wrapping_add x y).bv = x.bv + y.bv := by
  first
    | rfl
    | simp [core.num.U64.wrapping_add, UScalar.wrapping_add]
    | simp [core.num.U64.wrapping_add_bv_eq]

theorem wmul_bv (x y : U64) : (core.num.U64.wrapping_mul x y).bv = x.bv * y.bv := by
  first
    | rfl
    | simp [core.num.U64.wrapping_mul, UScalar.wrapping_mul]
    | simp [core.num.U64.wrapping_mul_bv_eq]

theorem lift_ok {α : Type} (x : α) : (lift x : Result α) = ok x := rfl

theorem omap0 (v i : U64) :
    core.option.Option.map vcpu.msr_addr.closure.Insts.CoreOpsFunctionFnOnceTupleU64U64 (some i) v =
      ok (some (core.num.U64.wrapping_add v i)) := by
  unfold core.option.Option.map
  simp [vcpu.msr_addr.closure.Insts.CoreOpsFunctionFnOnceTupleU64U64.call_once]

theorem omap1 (v i : U64) :
    core.option.Option.map vcpu.msr_addr.closure_1.Insts.CoreOpsFunctionFnOnceTupleU64U64 (some i) v =
      ok (some (core.num.U64.wrapping_add (core.num.U64.wrapping_add v vcpu.MSRS)
        (core.num.U64.wrapping_mul i 8#u64))) := by
  unfold core.option.Option.map
  simp [vcpu.msr_addr.closure_1.Insts.CoreOpsFunctionFnOnceTupleU64U64.call_once, lift_ok]

theorem XCR0_bv : vcpu.XCR0.bv = VcpuLay.XCR0 := by unfold vcpu.XCR0; rfl
theorem IBPB_bv : vcpu.VM_IBPB_DEFER.bv = VcpuLay.VM_IBPB_DEFER := by unfold vcpu.VM_IBPB_DEFER; rfl
theorem MSRIB_eq : vcpu.MSR_VM_IBPB_DEFER = 4294967293#u64 := by unfold vcpu.MSR_VM_IBPB_DEFER; rfl
theorem CR2_bv : vcpu.CR2.bv = VcpuLay.CR2 := by unfold vcpu.CR2; rfl
theorem MSRS_bv : vcpu.MSRS.bv = VcpuLay.MSRS := by unfold vcpu.MSRS; rfl

/-- **FL4 `vcpu::msr_addr` is `v + msrOff amd f`** for every base, field and backend. -/
theorem msr_addr_eq (v f : U64) (amd : Bool) :
    ∃ o, vcpu.msr_addr v f amd = ok o ∧ o.map (·.bv) = (msrOff amd f.bv).map (v.bv + ·) := by
  unfold vcpu.msr_addr
  by_cases h1 : f = 4294967294#u64
  · rw [if_pos h1]; subst h1
    refine ⟨some (core.num.U64.wrapping_add v vcpu.XCR0), by simp only [lift_ok, bind_ok], ?_⟩
    simp only [Option.map_some, wadd_bv, XCR0_bv]
    rfl
  rw [if_neg h1]
  have n1 : f.bv ≠ msrXcr0 := fun h => h1 (u64_ext h)
  rw [MSRIB_eq]
  by_cases h2 : f = 4294967293#u64
  · rw [if_pos h2]; subst h2
    refine ⟨some (core.num.U64.wrapping_add v vcpu.VM_IBPB_DEFER), by simp only [lift_ok, bind_ok], ?_⟩
    simp only [Option.map_some, wadd_bv, IBPB_bv]
    rfl
  rw [if_neg h2]
  have n2 : f.bv ≠ msrVmIbpbDefer := fun h => h2 (u64_ext h)
  have hoff : msrOff amd f.bv = if amd then svmMsrOff f.bv else if f.bv = msrCr2 then some VcpuLay.CR2
      else (msrSlot f.bv).map fun i => VcpuLay.MSRS + i * 8 := by
    unfold msrOff; rw [if_neg n1, if_neg n2]
  rw [hoff]
  cases amd with
  | true =>
    obtain ⟨o, ho, hm⟩ := svm_msr_eq f
    rw [if_pos rfl, if_pos rfl, ho, bind_ok]
    cases o with
    | none =>
      refine ⟨none, rfl, ?_⟩
      rw [← hm]; rfl
    | some i =>
      refine ⟨_, omap0 v i, ?_⟩
      rw [← hm]
      simp only [Option.map_some]
      show some (core.num.U64.wrapping_add v i).bv = _
      rw [wadd_bv]
  | false =>
    rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    by_cases h3 : f = 4294967295#u64
    · rw [if_pos h3]; subst h3
      refine ⟨some (core.num.U64.wrapping_add v vcpu.CR2), by simp only [lift_ok, bind_ok], ?_⟩
      simp only [Option.map_some, wadd_bv, CR2_bv]
      rfl
    rw [if_neg h3]
    have n3 : f.bv ≠ msrCr2 := fun h => h3 (u64_ext h)
    rw [if_neg n3]
    obtain ⟨o, ho, hm⟩ := msr_slot_eq f
    rw [ho, bind_ok]
    cases o with
    | none =>
      refine ⟨none, rfl, ?_⟩
      rw [← hm]; rfl
    | some i =>
      refine ⟨_, omap1 v i, ?_⟩
      rw [← hm]
      simp only [Option.map_some, Option.map_map]
      show some (core.num.U64.wrapping_add (core.num.U64.wrapping_add v vcpu.MSRS) (core.num.U64.wrapping_mul i 8#u64)).bv = _
      rw [wadd_bv, wadd_bv, wmul_bv, MSRS_bv]
      simp [BitVec.add_assoc]

/-- **FL4 has an MSR address exactly for the spec's MSR fields** (both backends). -/
theorem msrOff_isSome (amd : Bool) (m : Word) : (msrOff amd m).isSome = true ↔ m ∈ vcpuMsrs := by
  constructor
  · intro h
    by_contra hn
    simp only [vcpuMsrs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := hn
    cases amd <;> simp [msrOff, svmMsrOff, msrSlot, n1, n2, n3, n4, n5, n6, n7, n8] at h
  · intro h
    simp only [vcpuMsrs, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases amd <;> rfl

/-! ## The relation's places -/

/-- **On VMX, FL4's MSR address holds the spec's MSR value.** -/
theorem msrOff_rel_vmx {mem : Word → Word} {v : Word} {vs : VcpuState} {m o : Word} (h : VcpuRelVmx mem v vs)
    (ho : msrOff false m = some o) : vs.get .vmx (.msr m) = mem (v + o) := by
  have hc : VField.canon .vmx (.msr m) = .msr m := by simp [VField.canon]
  unfold VcpuState.get; rw [hc]
  unfold msrOff at ho
  by_cases h1 : m = msrXcr0
  · rw [if_pos h1] at ho; cases ho; subst h1; exact h.xcr0
  rw [if_neg h1] at ho
  by_cases h2 : m = msrVmIbpbDefer
  · rw [if_pos h2] at ho; cases ho; subst h2; exact h.ibpb
  rw [if_neg h2, if_neg Bool.false_ne_true] at ho
  by_cases h3 : m = msrCr2
  · rw [if_pos h3] at ho; cases ho; subst h3; exact h.cr2
  rw [if_neg h3] at ho
  rcases hs : msrSlot m with _ | i
  · rw [hs] at ho; cases ho
  · rw [hs] at ho; cases ho; exact h.msr m i hs

/-- **On SVM, FL4's MSR address holds the spec's MSR value** (a VMCB save-area word, or a shared pseudo-MSR). -/
theorem msrOff_rel_svm {mem : Word → Word} {v : Word} {vs : VcpuState} {m o : Word} (h : VcpuRelSvm mem v vs)
    (ho : msrOff true m = some o) : vs.get .svm (.msr m) = mem (v + o) := by
  unfold VcpuState.get
  unfold msrOff at ho
  by_cases h1 : m = msrXcr0
  · rw [if_pos h1] at ho; cases ho; subst h1
    have hc : VField.canon .svm (.msr msrXcr0) = .msr msrXcr0 := by
      simp only [VField.canon]; decide
    rw [hc]; exact h.xcr0
  rw [if_neg h1] at ho
  by_cases h2 : m = msrVmIbpbDefer
  · rw [if_pos h2] at ho; cases ho; subst h2
    have hc : VField.canon .svm (.msr msrVmIbpbDefer) = .msr msrVmIbpbDefer := by
      simp only [VField.canon]; decide
    rw [hc]; exact h.ibpb
  rw [if_neg h2, if_pos rfl] at ho
  have hv : ∀ off, off ∈ [Svm.star, Svm.lstar, Svm.cstar, Svm.sfmask, Svm.kernelGsBase, Svm.cr2] →
      vs.fields (.vmcb off) = mem (v + off) := by
    intro off hoff
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    refine h.vmcb off ?_ ?_ ?_ <;>
      rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  unfold svmMsrOff at ho
  simp only [VField.canon, if_pos rfl]
  by_cases a1 : m = msrStar
  · rw [if_pos a1] at ho ⊢; cases ho; exact hv _ (by simp)
  rw [if_neg a1] at ho ⊢
  by_cases a2 : m = msrLstar
  · rw [if_pos a2] at ho ⊢; cases ho; exact hv _ (by simp)
  rw [if_neg a2] at ho ⊢
  by_cases a3 : m = msrCstar
  · rw [if_pos a3] at ho ⊢; cases ho; exact hv _ (by simp)
  rw [if_neg a3] at ho ⊢
  by_cases a4 : m = msrFmask
  · rw [if_pos a4] at ho ⊢; cases ho; exact hv _ (by simp)
  rw [if_neg a4] at ho ⊢
  by_cases a5 : m = msrKernelGsBase
  · rw [if_pos a5] at ho ⊢; cases ho; exact hv _ (by simp)
  rw [if_neg a5] at ho ⊢
  by_cases a6 : m = msrCr2
  · rw [if_pos a6] at ho ⊢; cases ho; exact hv _ (by simp)
  rw [if_neg a6] at ho
  cases ho

/-! ## WriteMSR's checks -/

section
variable {A : Type} (ar : machine.Arch A) (a : A)

/-- **FL4 `vcpu::decode`'s WriteMSR arm after its length check** (vcpu.rs l. 987-1006, transcribed; module
docstring): `Ok x` means FL4 writes `value` at `x` and replies `read(x)`. -/
def fl4WriteMsr (v f value : U64) (amd : Bool) : Result (core.result.Result U64 error.Exc) := do
  let o ← vcpu.msr_addr v f amd
  match o with
  | none => error.illegal U64
  | some x =>
    let c ← if f = 3221225602#u64 ∨ f = 3221225603#u64 ∨ f = 3221225730#u64 then do
        let w ← ar.vcpu_capability a 1#u64
        vcpu.canonical value w
      else ok true
    if c = false then error.invalid_arg U64 1#u64
    else
      let c0 ← if f = 4294967294#u64 then do
          let hx ← ar.vcpu_capability a 0#u64
          vcpu.valid_xcr0 value hx
        else ok true
      if c0 = false then error.invalid_arg U64 1#u64
      else if f = vcpu.MSR_VM_IBPB_DEFER ∧ value > 1#u64 then error.invalid_arg U64 1#u64
      else ok (.Ok x)

/-- FL4's WriteMSR verdict against the spec's `checkMsrWrite`. -/
def MsrResRel : core.result.Result U64 error.Exc → Except SyscallError Unit → Prop
  | .Ok _, .ok () => True
  | .Err e, .error e' => SysErrRel e e'
  | _, _ => False

variable {ar a}

theorem gt1_iff (x : U64) : (x > 1#u64) ↔ x.bv > 1 := by
  show (1#u64).val < x.val ↔ (1 : Word) < x.bv
  rw [BitVec.lt_def]
  rfl

/-- **FL4's WriteMSR decision is the spec's `checkMsrWrite`** (premise `CapAgree` [P]): FL4 returns, with the same
error or success, and on success its address is `v + msrOff amd f`. -/
theorem fl4WriteMsr_rel (hc : CapAgree ar a) (v f value : U64) (amd : Bool) :
    ∃ r, fl4WriteMsr ar a v f value amd = ok r ∧ MsrResRel r (checkMsrWrite f.bv value.bv) ∧
      ∀ x, r = .Ok x → (msrOff amd f.bv).map (v.bv + ·) = some x.bv := by
  have hc' : ∀ g, ar.vcpu_capability a g = ok ⟨vcpuCapability g.bv⟩ := hc
  obtain ⟨o, ho, hm⟩ := msr_addr_eq v f amd
  unfold fl4WriteMsr
  rw [ho, bind_ok]
  cases o with
  | none =>
    have hn : msrOff amd f.bv = none := by
      rcases h : msrOff amd f.bv with _ | y
      · rfl
      · rw [h] at hm; cases hm
    have hnm : f.bv ∉ vcpuMsrs := fun hmem => by
      have := (msrOff_isSome amd f.bv).2 hmem
      rw [hn] at this; cases this
    refine ⟨_, rfl, ?_, fun x hx => by cases hx⟩
    simp [checkMsrWrite, hnm, MsrResRel, SysErrRel]
  | some x =>
    have hs : msrOff amd f.bv = some (x.bv - v.bv) := by
      rcases h : msrOff amd f.bv with _ | y
      · rw [h] at hm; cases hm
      · rw [h] at hm
        simp only [Option.map_some, Option.some.injEq] at hm
        rw [hm]; simp
    have hmem : f.bv ∈ vcpuMsrs := (msrOff_isSome amd f.bv).1 (by rw [hs]; rfl)
    have hx : ∀ y, (.Ok x : core.result.Result U64 error.Exc) = .Ok y →
        (msrOff amd f.bv).map (v.bv + ·) = some y.bv := by
      intro y hy; cases hy; rw [← hm]; rfl
    have e1 : (f = 3221225602#u64 ∨ f = 3221225603#u64 ∨ f = 3221225730#u64) ↔
        (f.bv = msrLstar ∨ f.bv = msrCstar ∨ f.bv = msrKernelGsBase) := by
      constructor
      · rintro (rfl | rfl | rfl) <;> decide
      · rintro (h | h | h)
        · exact Or.inl (u64_ext h)
        · exact Or.inr (Or.inl (u64_ext h))
        · exact Or.inr (Or.inr (u64_ext h))
    have e2 : (f = 4294967294#u64) ↔ f.bv = msrXcr0 := ⟨fun h => by subst h; decide, fun h => u64_ext h⟩
    have e3 : (f = vcpu.MSR_VM_IBPB_DEFER) ↔ f.bv = msrVmIbpbDefer := by
      rw [MSRIB_eq]; exact ⟨fun h => by subst h; decide, fun h => u64_ext h⟩
    have k1 : (do let w ← ar.vcpu_capability a 1#u64; vcpu.canonical value w) =
        ok (canonical value.bv canonWidth) := by
      rw [hc', bind_ok, canonical_eq]; rfl
    have k0 : (do let hx ← ar.vcpu_capability a 0#u64; vcpu.valid_xcr0 value hx) =
        ok (validXcr0 value.bv hostXcr0) := by
      rw [hc', bind_ok, valid_xcr0_eq]; rfl
    have cap1 : ar.vcpu_capability a 1#u64 = ok ⟨canonWidth⟩ := hc' 1#u64
    have cap0 : ar.vcpu_capability a 0#u64 = ok ⟨hostXcr0⟩ := hc' 0#u64
    simp only [e1, e2, e3, gt1_iff, cap1, cap0, bind_ok, canonical_eq, valid_xcr0_eq]
    unfold checkMsrWrite
    rw [if_neg (not_not.2 hmem)]
    have ne12 : msrLstar ≠ msrXcr0 ∧ msrCstar ≠ msrXcr0 ∧ msrKernelGsBase ≠ msrXcr0 := by decide
    have ne13 : msrLstar ≠ msrVmIbpbDefer ∧ msrCstar ≠ msrVmIbpbDefer ∧ msrKernelGsBase ≠ msrVmIbpbDefer := by
      decide
    have ne23 : msrXcr0 ≠ msrVmIbpbDefer := by decide
    by_cases c1 : (f.bv = msrLstar ∨ f.bv = msrCstar ∨ f.bv = msrKernelGsBase)
    · have c2 : ¬ f.bv = msrXcr0 := by
        rcases c1 with h | h | h <;> rw [h] <;> simp [ne12]
      have c3 : ¬ f.bv = msrVmIbpbDefer := by
        rcases c1 with h | h | h <;> rw [h] <;> simp [ne13]
      by_cases d1 : canonical value.bv canonWidth = true
      · simp only [c1, c2, c3, d1, if_true, if_false, true_and, false_and, not_true_eq_false, and_false,
          Bool.true_eq_false, ↓reduceIte, bind_ok]
        exact ⟨_, rfl, trivial, hx⟩
      · have d1' : canonical value.bv canonWidth = false := by simpa using d1
        simp only [c1, d1', if_true, true_and, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, bind_ok]
        exact ⟨_, rfl, by simp [MsrResRel, SysErrRel], fun y hy => by cases hy⟩
    · simp only [c1, if_false, false_and, ↓reduceIte, bind_ok, Bool.true_eq_false]
      by_cases c2 : f.bv = msrXcr0
      · have c3 : ¬ f.bv = msrVmIbpbDefer := by rw [c2]; exact ne23
        by_cases d2 : validXcr0 value.bv hostXcr0 = true
        · simp only [c2, c3, d2, if_true, if_false, true_and, false_and, not_true_eq_false, and_false,
            Bool.true_eq_false, ↓reduceIte, bind_ok]
          exact ⟨_, rfl, trivial, by rw [← c2]; exact hx⟩
        · have d2' : validXcr0 value.bv hostXcr0 = false := by simpa using d2
          simp only [c2, d2', if_true, true_and, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, bind_ok]
          exact ⟨_, rfl, by simp [MsrResRel, SysErrRel], fun y hy => by cases hy⟩
      · simp only [c2, if_false, false_and, ↓reduceIte, bind_ok, Bool.true_eq_false]
        by_cases c3 : f.bv = msrVmIbpbDefer ∧ value.bv > 1
        · simp only [c3, and_self, ↓reduceIte]
          exact ⟨_, rfl, by simp [MsrResRel, SysErrRel], fun y hy => by cases hy⟩
        · simp only [c3, ↓reduceIte]
          exact ⟨_, rfl, trivial, hx⟩

end

end Fl4Proofs.P3.VirtMsrEq
