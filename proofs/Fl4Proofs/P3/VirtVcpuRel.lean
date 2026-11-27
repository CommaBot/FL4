/-
P3x for virtualization (line virt, gen 10, item 2): **VIRT-PLAN R0, virt's half — facts about the VCPU field
relations `VcpuRelVmx` / `VcpuRelSvm` that need no FL4-side invariant** (the relations themselves are spec
extensions: `Fl4Spec/Ext/VirtRelBase`, `VirtRelVmx`, `VirtRelSvm`).

* Footprint: every place either relation reads is `v + o` with `o < VcpuLay.SIZE` (32 KiB, the VCPU object):
  `vmcsIdx_lt` / `vmcsOff_lt'` (every VMCS encoding: FL4's index has 11 bits), `gprOff_lt`,
  `exitOff_lt`, `msrOff_lt`, `ioOff_lt` (every port), `svmOff_lt` (every readable VMCB word), the fixed words.
* **Frame** (`VcpuRelCommon.congr`, **`VcpuRelVmx.congr`**, **`VcpuRelSvm.congr`**, `SvmRaxSync.congr`): memories that
  agree on `[v, v + SIZE)` relate the same abstract VCPU — so a kernel write outside the VCPU's object never
  breaks the relation.
* **Retype** (**`vcpuRelVmx_blank`**, **`vcpuRelSvm_blank`**, `svmRaxSync_zero`): a zeroed image relates to
  `VcpuState.blank`, the object a VT-x retype creates before `vcpu::init` (FL4's retype zeroes the memory).
* **Abstraction is functional** (**`VcpuRelVmx.unique`**, **`VcpuRelSvm.unique`**): two abstract VCPUs related to
  the same image have the same binding, exit record and (VMX) I/O bitmap, and the same value at every field of
  the backend's table (VMX: `VField.valid .vmx`; SVM: every valid canonical field but the hidden / host-cache
  VMCB words, which the spec deliberately leaves to the trusted layer — not determined by memory, as stated).
* The link to this line's `NR` epoch: **`vcpuAt_none_of_nr`** / `tcbVcpuOf_none_of_nr`: on `NR` states there is no
  VCPU object, so the VCPU half of VIRT-PLAN's `VirtRel` is vacuous on the spec side there (FL4's VCPU list must be
  empty — mmuAD's `JAtZV2` side, not on this branch).

No named premise; no [J]/[P]/[W]/[S]. New file only.
-/
import Fl4Spec.Ext.VirtRelSvm
import Fl4Proofs.P3.VirtR7e
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtVcpuRel
open Fl4Spec

noncomputable section

/-! ## Footprint -/

theorem toNat_ff : (0xff : Word).toNat = 255 := rfl
theorem toNat_three : (3 : Word).toNat = 3 := rfl
theorem toNat_eight : (8 : Word).toNat = 8 := rfl

/-- FL4's VMCS index has 11 bits (for every encoding). -/
theorem vmcsIdx_lt (f : Word) : (vmcsIdx f).toNat < 2 ^ 11 := by
  unfold vmcsIdx
  rw [BitVec.toNat_or, BitVec.toNat_or]
  refine Nat.or_lt_two_pow (Nat.or_lt_two_pow ?_ ?_) ?_
  · rw [BitVec.toNat_ushiftRight, BitVec.toNat_and, toNat_ff, Nat.shiftRight_eq_div_pow]
    have := @Nat.and_le_right (f.toNat) 255
    simp only [Nat.reducePow]
    omega
  · rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ushiftRight, toNat_three, Nat.shiftLeft_eq]
    have := @Nat.and_le_right (f.toNat >>> 10) 3
    simp only [Nat.reducePow]
    have := Nat.mod_le ((f.toNat >>> 10 &&& 3) * 128) 18446744073709551616
    omega
  · rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ushiftRight, toNat_three, Nat.shiftLeft_eq]
    have := @Nat.and_le_right (f.toNat >>> 13) 3
    simp only [Nat.reducePow]
    have := Nat.mod_le ((f.toNat >>> 13 &&& 3) * 512) 18446744073709551616
    omega

/-- **Every VMCS encoding's place lies in the image** (`SHADOW + 8 · idx f ≤ 0x4ff8`, below `TCB`). -/
theorem vmcsOff_lt' (f : Word) : vmcsOff f < VcpuLay.SIZE := by
  have h := vmcsIdx_lt f
  have a : VcpuLay.SHADOW.toNat = 4096 := rfl
  have c : VcpuLay.SIZE.toNat = 32768 := rfl
  rw [BitVec.lt_def]
  unfold vmcsOff
  rw [BitVec.toNat_add, BitVec.toNat_mul, a, c, toNat_eight]
  simp only [Nat.reducePow] at h ⊢
  omega

/-- Every VMCS field of FL4's tables lies in the image. -/
theorem vmcsOff_lt {f : Word} (_h : Vmx.writable f = true ∨ Vmx.readable f = true) : vmcsOff f < VcpuLay.SIZE :=
  vmcsOff_lt' f

theorem gprOff_lt : ∀ i, gprOff i < VcpuLay.SIZE := by decide

theorem exitOff_lt : ∀ i, exitOff i < VcpuLay.SIZE := by decide

theorem msrOff_lt {m i : Word} (h : msrSlot m = some i) : VcpuLay.MSRS + i * 8 < VcpuLay.SIZE := by
  unfold msrSlot at h
  split_ifs at h <;> first | (obtain rfl := Option.some.inj h; decide) | cases h

theorem ioOff_lt (p : BitVec 16) : vcpuIoOff p < VcpuLay.SIZE := by
  have hp : p.toNat < 65536 := p.isLt
  rw [BitVec.lt_def]
  simp [vcpuIoOff, VcpuLay.IO, VcpuLay.SIZE, BitVec.toNat_add, BitVec.toNat_mul]
  omega

theorem svmOff_lt {off : Word} (h : Svm.readable off = true) : off < VcpuLay.SIZE := by
  have h2 : off < Svm.svmEnd := by
    simp only [Svm.readable, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2
  rw [BitVec.lt_def] at h2 ⊢
  exact Nat.lt_of_lt_of_le h2 (by decide)

theorem tcb_lt : VcpuLay.TCB < VcpuLay.SIZE := by decide
theorem valid_lt : VcpuLay.VALID < VcpuLay.SIZE := by decide
theorem pending_lt : VcpuLay.PENDING < VcpuLay.SIZE := by decide
theorem xcr0_lt : VcpuLay.XCR0 < VcpuLay.SIZE := by decide
theorem ibpb_lt : VcpuLay.VM_IBPB_DEFER < VcpuLay.SIZE := by decide
theorem cr2_lt : VcpuLay.CR2 < VcpuLay.SIZE := by decide
theorem regs_lt : VcpuLay.REGS < VcpuLay.SIZE := by decide
theorem rax_lt : Svm.rax < VcpuLay.SIZE := by decide

/-- Two memories agree on the VCPU object at `v`. -/
def AgreeAt (mem mem' : Word → Word) (v : Word) : Prop := ∀ o, o < VcpuLay.SIZE → mem' (v + o) = mem (v + o)

/-! ## Frame -/

theorem VcpuRelCommon.congr {mem mem' : Word → Word} {v : Word} {vs : VcpuState} (hm : AgreeAt mem mem' v)
    (h : VcpuRelCommon mem v vs) : VcpuRelCommon mem' v vs where
  tcb := by rw [hm _ tcb_lt]; exact h.tcb
  valid := by rw [hm _ valid_lt]; exact h.valid
  pending := by rw [hm _ pending_lt]; exact h.pending
  mrs i := by rw [hm _ (exitOff_lt i)]; exact h.mrs i
  gpr i := by rw [hm _ (gprOff_lt i)]; exact h.gpr i
  xcr0 := by rw [hm _ xcr0_lt]; exact h.xcr0
  ibpb := by rw [hm _ ibpb_lt]; exact h.ibpb

/-- **Frame for VMX**: the relation reads only the VCPU's object. -/
theorem VcpuRelVmx.congr {mem mem' : Word → Word} {v : Word} {vs : VcpuState} (hm : AgreeAt mem mem' v)
    (h : VcpuRelVmx mem v vs) : VcpuRelVmx mem' v vs :=
  { VcpuRelCommon.congr hm h.toVcpuRelCommon with
    vmcs := fun f hf => by rw [hm _ (vmcsOff_lt hf)]; exact h.vmcs f hf
    msr := fun m i hi => by rw [hm _ (msrOff_lt hi)]; exact h.msr m i hi
    cr2 := by rw [hm _ cr2_lt]; exact h.cr2
    io := fun p => by rw [hm _ (ioOff_lt p)]; exact h.io p }

/-- **Frame for SVM**. -/
theorem VcpuRelSvm.congr {mem mem' : Word → Word} {v : Word} {vs : VcpuState} (hm : AgreeAt mem mem' v)
    (h : VcpuRelSvm mem v vs) : VcpuRelSvm mem' v vs :=
  { VcpuRelCommon.congr hm h.toVcpuRelCommon with
    vmcb := fun off hr hh hx => by rw [hm _ (svmOff_lt hr)]; exact h.vmcb off hr hh hx }

theorem SvmRaxSync.congr {mem mem' : Word → Word} {v : Word} (hm : AgreeAt mem mem' v) (h : SvmRaxSync mem v) :
    SvmRaxSync mem' v := by
  unfold SvmRaxSync at *
  rw [hm _ rax_lt, hm _ regs_lt]; exact h

/-- Frame for the selected backend's relation. -/
theorem VcpuRel.congr {k : VirtKind} {mem mem' : Word → Word} {v : Word} {vs : VcpuState}
    (hm : AgreeAt mem mem' v) (h : VcpuRel k mem v vs) : VcpuRel k mem' v vs := by
  cases k with
  | vmx => exact VcpuRelVmx.congr hm h
  | svm => exact VcpuRelSvm.congr hm h
  | none => exact h.elim
  | armEl2 => exact h.elim

/-! ## Retype: a zeroed image is the blank VCPU -/

/-- The VCPU object at `v` is zero. -/
def ZeroAt (mem : Word → Word) (v : Word) : Prop := ∀ o, o < VcpuLay.SIZE → mem (v + o) = 0

theorem vcpuRelCommon_blank {mem : Word → Word} {v : Word} (hz : ZeroAt mem v) :
    VcpuRelCommon mem v VcpuState.blank where
  tcb := by rw [hz _ tcb_lt]; simp [VcpuState.blank, vcpuTcbRef]
  valid := by rw [hz _ valid_lt]; simp [VcpuState.blank]
  pending := by rw [hz _ pending_lt]; simp [VcpuState.blank]
  mrs i := by rw [hz _ (exitOff_lt i)]; rfl
  gpr i := by rw [hz _ (gprOff_lt i)]; rfl
  xcr0 := by rw [hz _ xcr0_lt]; rfl
  ibpb := by rw [hz _ ibpb_lt]; rfl

/-- **A zeroed image relates to the blank VCPU on VMX** (FL4's retype zeroes the object before `vcpu::init`). -/
theorem vcpuRelVmx_blank {mem : Word → Word} {v : Word} (hz : ZeroAt mem v) : VcpuRelVmx mem v VcpuState.blank :=
  { vcpuRelCommon_blank hz with
    vmcs := fun f hf => by rw [hz _ (vmcsOff_lt hf)]; rfl
    msr := fun m i hi => by rw [hz _ (msrOff_lt hi)]; rfl
    cr2 := by rw [hz _ cr2_lt]; rfl
    io := fun p => by rw [hz _ (ioOff_lt p)]; simp [VcpuState.blank] }

/-- **A zeroed image relates to the blank VCPU on SVM.** -/
theorem vcpuRelSvm_blank {mem : Word → Word} {v : Word} (hz : ZeroAt mem v) : VcpuRelSvm mem v VcpuState.blank :=
  { vcpuRelCommon_blank hz with
    vmcb := fun off hr _ _ => by rw [hz _ (svmOff_lt hr)]; rfl }

theorem svmRaxSync_zero {mem : Word → Word} {v : Word} (hz : ZeroAt mem v) : SvmRaxSync mem v := by
  unfold SvmRaxSync; rw [hz _ rax_lt, hz _ regs_lt]

/-! ## Abstraction is functional -/

theorem exitRecord_ext {e e' : ExitRecord} (h1 : e.valid = e'.valid) (h2 : e.pending = e'.pending)
    (h3 : e.mrs = e'.mrs) : e = e' := by
  cases e; cases e'
  simp_all

theorem VcpuRelCommon.unique {mem : Word → Word} {v : Word} {vs vs' : VcpuState} (h : VcpuRelCommon mem v vs)
    (h' : VcpuRelCommon mem v vs') :
    vs.tcb = vs'.tcb ∧ vs.exit = vs'.exit ∧ (∀ i, vs.fields (.gpr i) = vs'.fields (.gpr i)) ∧
      vs.fields (.msr msrXcr0) = vs'.fields (.msr msrXcr0) ∧
      vs.fields (.msr msrVmIbpbDefer) = vs'.fields (.msr msrVmIbpbDefer) :=
  ⟨h.tcb.trans h'.tcb.symm,
   exitRecord_ext (h.valid.trans h'.valid.symm) (h.pending.trans h'.pending.symm)
     (funext fun i => (h.mrs i).trans (h'.mrs i).symm),
   fun i => (h.gpr i).trans (h'.gpr i).symm, h.xcr0.trans h'.xcr0.symm, h.ibpb.trans h'.ibpb.symm⟩

theorem msrSlot_star : msrSlot msrStar = some 0 := by decide
theorem msrSlot_lstar : msrSlot msrLstar = some 1 := by decide
theorem msrSlot_cstar : msrSlot msrCstar = some 2 := by decide
theorem msrSlot_fmask : msrSlot msrFmask = some 3 := by decide
theorem msrSlot_kgs : msrSlot msrKernelGsBase = some 4 := by decide

/-- **The VMX abstraction is functional on the backend's table**: binding, exit record, I/O bitmap and every
field of the VMX table (`VField.valid .vmx`) are determined by the image. -/
theorem VcpuRelVmx.unique {mem : Word → Word} {v : Word} {vs vs' : VcpuState} (h : VcpuRelVmx mem v vs)
    (h' : VcpuRelVmx mem v vs') :
    vs.tcb = vs'.tcb ∧ vs.exit = vs'.exit ∧ vs.ioDenied = vs'.ioDenied ∧
      ∀ f, f.valid .vmx = true → vs.fields f = vs'.fields f := by
  obtain ⟨ht, he, hg, hx, hb⟩ := VcpuRelCommon.unique h.toVcpuRelCommon h'.toVcpuRelCommon
  refine ⟨ht, he, funext fun p => (h.io p).trans (h'.io p).symm, ?_⟩
  intro f hf
  cases f with
  | vmcs g =>
    have hg' : Vmx.writable g = true ∨ Vmx.readable g = true := by
      simpa [VField.valid] using hf
    exact (h.vmcs g hg').trans (h'.vmcs g hg').symm
  | vmcb off => simp [VField.valid] at hf
  | gpr i => exact hg i
  | msr m =>
    have hm : m ∈ vcpuMsrs := by
      simpa [VField.valid] using hf
    simp only [vcpuMsrs, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (h.msr _ _ msrSlot_star).trans (h'.msr _ _ msrSlot_star).symm
    · exact (h.msr _ _ msrSlot_lstar).trans (h'.msr _ _ msrSlot_lstar).symm
    · exact (h.msr _ _ msrSlot_cstar).trans (h'.msr _ _ msrSlot_cstar).symm
    · exact (h.msr _ _ msrSlot_fmask).trans (h'.msr _ _ msrSlot_fmask).symm
    · exact (h.msr _ _ msrSlot_kgs).trans (h'.msr _ _ msrSlot_kgs).symm
    · exact h.cr2.trans h'.cr2.symm
    · exact hx
    · exact hb

theorem canon_svm_star : VField.canon .svm (.msr msrStar) = .vmcb Svm.star := by decide
theorem canon_svm_lstar : VField.canon .svm (.msr msrLstar) = .vmcb Svm.lstar := by decide
theorem canon_svm_cstar : VField.canon .svm (.msr msrCstar) = .vmcb Svm.cstar := by decide
theorem canon_svm_fmask : VField.canon .svm (.msr msrFmask) = .vmcb Svm.sfmask := by decide
theorem canon_svm_kgs : VField.canon .svm (.msr msrKernelGsBase) = .vmcb Svm.kernelGsBase := by decide
theorem canon_svm_cr2 : VField.canon .svm (.msr msrCr2) = .vmcb Svm.cr2 := by decide

/-- **The SVM abstraction is functional on the backend's table, but the trusted layer's words**: binding, exit
record and every valid canonical field except the hidden / host-cache VMCB words (`Svm.hiddenRead`, which the
spec leaves to the trusted layer) are determined by the image. -/
theorem VcpuRelSvm.unique {mem : Word → Word} {v : Word} {vs vs' : VcpuState} (h : VcpuRelSvm mem v vs)
    (h' : VcpuRelSvm mem v vs') :
    vs.tcb = vs'.tcb ∧ vs.exit = vs'.exit ∧
      ∀ f, f.valid .svm = true → f.canon .svm = f → (∀ off, f = .vmcb off → Svm.hiddenRead off = false) →
        vs.fields f = vs'.fields f := by
  obtain ⟨ht, he, hg, hx, hb⟩ := VcpuRelCommon.unique h.toVcpuRelCommon h'.toVcpuRelCommon
  refine ⟨ht, he, ?_⟩
  intro f hf hc hh
  cases f with
  | vmcs g => simp [VField.valid] at hf
  | vmcb off =>
    have hr : Svm.readable off = true := by
      simpa [VField.valid] using hf
    have hx' : off ≠ Svm.rax := by
      intro e; subst e
      simp [VField.canon] at hc
    exact (h.vmcb off hr (hh off rfl) hx').trans (h'.vmcb off hr (hh off rfl) hx').symm
  | gpr i => exact hg i
  | msr m =>
    have hm : m ∈ vcpuMsrs := by
      simpa [VField.valid] using hf
    simp only [vcpuMsrs, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [canon_svm_star] at hc; cases hc
    · rw [canon_svm_lstar] at hc; cases hc
    · rw [canon_svm_cstar] at hc; cases hc
    · rw [canon_svm_fmask] at hc; cases hc
    · rw [canon_svm_kgs] at hc; cases hc
    · rw [canon_svm_cr2] at hc; cases hc
    · exact hx
    · exact hb

/-! ## The `NR` epoch has no VCPU -/

/-- **No VCPU object at an `NR` state.** -/
theorem vcpuAt_none_of_nr {σ : State Unit} (h : VirtR7e.NR σ) (v : ObjRef) : vcpuAt σ v = none := by
  unfold vcpuAt
  split
  · rename_i st hk
    have hv : VirtR7b.NVV σ := h.1.2
    exact (hv v _ hk rfl).elim
  · rfl

theorem tcbVcpuOf_none_of_nr {σ : State Unit} (h : VirtR7e.NR σ) (t : ObjRef) : tcbVcpuOf σ t = none :=
  tcbVcpuOf_none.2 fun v st hv => by rw [vcpuAt_none_of_nr h v] at hv; cases hv

end

end Fl4Proofs.P3.VirtVcpuRel
