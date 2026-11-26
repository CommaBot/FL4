/-
P3 (line mmuAD, gen 34): **the VCPU words FL4's `vcpu::report` reads, through `VRel`** (step 2 of gen 33's plan
toward `ReportJ3`).

At a `JAtZV3` state, for a VCPU `p ∈ V` whose spec object is `vs` (gen 30's `VRel`, virt's `VcpuRel`):

* `v3_get_eq`: `vcpu.get s p o` reads `p + o`; `v3_rdw`: that word is the relation's word view at `p.bv + o.bv`
  (aligned offsets inside the VCPU).
* **`JAtZV3.rdPend`**, **`rdValid`** (`PENDING` / `VALID` nonzero = the spec flags), **`rdExit`** (exit MR `j` =
  `vs.exit.mrs j`), **`rdGpr`** (GPR `j` = `vs.get k (.gpr j)`), both backends (`VcpuRelCommon`).
* VMX (`virtKind = .vmx`): **`rdVmcs`** (a readable VMCS field at gen 32's `vmcsOff` = `vs.get k (.vmcs f)`),
  **`rdCr2Vmx`** (`CR2` word = `vs.get k (.msr msrCr2)`).
* SVM (`virtKind = .svm`): **`rdVmcb`** (a readable, not hidden, non-RAX VMCB word = `vs.get k (.vmcb off)`),
  **`rdCr2Svm`** (VMCB CR2 = `vs.get k (.msr msrCr2)`, its canonical place).

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3Gpr
import Fl4Proofs.P3.JAtZV3Vmcs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
open Fl4Spec

theorem v3_exit_val : ∀ j : Fin 30, (exitOff j).toNat = 20992 + 8 * j.val := by decide

theorem v3_relC {k : VirtKind} {mem : Word → Word} {v : Word} {vs : VcpuState} (h : VcpuRel k mem v vs) :
    VcpuRelCommon mem v vs := by
  cases k with
  | vmx => exact (h : VcpuRelVmx mem v vs).toVcpuRelCommon
  | svm => exact (h : VcpuRelSvm mem v vs).toVcpuRelCommon
  | none => exact h.elim
  | armEl2 => exact h.elim

theorem v3_bne0 (x : U64) : (x != 0#u64) = decide (x.bv ≠ 0) := by
  by_cases h : x.bv = 0
  · have hx : x = 0#u64 := UScalar.eq_of_val_eq (by show x.bv.toNat = (0#u64 : U64).val; rw [h]; rfl)
    subst hx; simp
  · have hx : x ≠ 0#u64 := fun e => h (by rw [e]; rfl)
    rw [bne_iff_ne.2 hx]
    exact (decide_eq_true h).symm

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem v3_get_eq (s : S) (p o : U64) : vcpu.get st s p o = ok (L.mem s (core.num.U64.wrapping_add p o)) := by
  unfold vcpu.get
  simp only [lift, bind_ok, L.read_eq]

/-- An aligned word of a VCPU, as the relation's word view. -/
theorem v3_rdw (m : U64 → U64) {p : U64} (hf : p.val % 32768 = 0 ∧ p.val + 32768 ≤ 2 ^ 64) {o : U64}
    (ho : o.val < 32768) (ha : o.val % 8 = 0) :
    (m (core.num.U64.wrapping_add p o)).bv = vmemW m (p.bv + o.bv) := by
  have hlt : o.bv < Fl4Spec.VcpuLay.SIZE := by
    rw [BitVec.lt_def]; exact ho
  have e := v3_toNat_add hf.2 hlt
  have hov : o.bv.toNat = o.val := rfl
  have hal : (p.bv + o.bv).toNat % 8 = 0 := by rw [e, hov]; omega
  unfold vmemW
  rw [if_pos hal]
  have hw : core.num.U64.wrapping_add p o = (⟨p.bv + o.bv⟩ : U64) := by
    apply UScalar.eq_of_val_eq
    show (core.num.U64.wrapping_add p o).val = (p.bv + o.bv).toNat
    have hs : UScalar.size UScalarTy.U64 = 2 ^ 64 := by simp [U64.size_def, U64.numBits]
    rw [e, hov, core.num.U64.wrapping_add_val_eq]
    first | omega | (rw [hs]; exact Nat.mod_eq_of_lt (by omega)) | (simp only [hs]; omega)
  rw [hw]

variable {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

theorem JAtZV3.vfitV (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V) :
    p.val % 32768 = 0 ∧ p.val + 32768 ≤ 2 ^ 64 :=
  (J.z2.zv.base.jvLay J.z2.zv.vm).vfit p hp

/-- The word at offset `o` of a VCPU of `V`, as the relation's view (`v3_rdw` at a `JAtZV3` state). -/
theorem JAtZV3.rdw (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V) {o : U64}
    (ho : o.val < 32768) (ha : o.val % 8 = 0) :
    (L.mem s (core.num.U64.wrapping_add p o)).bv = vmemW (L.mem s) (p.bv + o.bv) :=
  v3_rdw _ (J.vfitV hp) ho ha

theorem JAtZV3.rdPend (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) :
    (L.mem s (core.num.U64.wrapping_add p vcpu.PENDING) != 0#u64) = vs.exit.pending := by
  have hC := v3_relC (J.vr p hp vs hk)
  have e : vcpu.PENDING.bv = Fl4Spec.VcpuLay.PENDING := by unfold vcpu.PENDING; rfl
  have hv : vcpu.PENDING.val = 20520 := by unfold vcpu.PENDING; rfl
  rw [v3_bne0, J.rdw hp (by rw [hv]; omega) (by rw [hv]), e, hC.pending]

theorem JAtZV3.rdValid (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) :
    (L.mem s (core.num.U64.wrapping_add p vcpu.VALID) != 0#u64) = vs.exit.valid := by
  have hC := v3_relC (J.vr p hp vs hk)
  have e : vcpu.VALID.bv = Fl4Spec.VcpuLay.VALID := by unfold vcpu.VALID; rfl
  have hv : vcpu.VALID.val = 20528 := by unfold vcpu.VALID; rfl
  rw [v3_bne0, J.rdw hp (by rw [hv]; omega) (by rw [hv]), e, hC.valid]

/-- `VALID` read as zero exactly when the spec has no saved exit. -/
theorem JAtZV3.rdValid0 (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) :
    L.mem s (core.num.U64.wrapping_add p vcpu.VALID) = 0#u64 ↔ vs.exit.valid = false := by
  rw [← J.rdValid hp hk]
  simp

theorem JAtZV3.rdExit (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (o : U64) (j : Fin 30)
    (ho : o.val = 20992 + 8 * j.val) :
    (L.mem s (core.num.U64.wrapping_add p o)).bv = vs.exit.mrs j := by
  have hC := v3_relC (J.vr p hp vs hk)
  have e : o.bv = Fl4Spec.exitOff j := BitVec.eq_of_toNat_eq (by rw [v3_exit_val]; exact ho)
  rw [J.rdw hp (by have := j.isLt; omega) (by omega), e, hC.mrs]

theorem JAtZV3.rdGpr (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (o : U64) (j : Fin 15)
    (ho : o.val = 20736 + 8 * j.val) :
    (L.mem s (core.num.U64.wrapping_add p o)).bv = vs.get Fl4Spec.virtKind (.gpr j) := by
  have hC := v3_relC (J.vr p hp vs hk)
  have e : o.bv = Fl4Spec.gprOff j := BitVec.eq_of_toNat_eq (by rw [v3_gpr_val]; exact ho)
  rw [J.rdw hp (by have := j.isLt; omega) (by omega), e, ← hC.gpr]
  rfl

theorem JAtZV3.rdVmcs (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (hvk : Fl4Spec.virtKind = .vmx)
    (f : U64) (hf : Fl4Spec.Vmx.readable f.bv = true) :
    (L.mem s ⟨p.bv + Fl4Spec.vmcsOff f.bv⟩).bv = vs.get Fl4Spec.virtKind (.vmcs f.bv) := by
  have R0 := J.vr p hp vs hk
  rw [hvk] at R0
  have R : Fl4Spec.VcpuRelVmx (vmemW (L.mem s)) p.bv vs := R0
  have hfv := J.vfitV hp
  have e1 := v3_toNat_add hfv.2 (VirtVcpuRel.vmcsOff_lt' f.bv)
  have hov := v3_vmcsOff_val f.bv
  have hal : (p.bv + Fl4Spec.vmcsOff f.bv).toNat % 8 = 0 := by
    have : p.val % 32768 = 0 := hfv.1
    rw [e1, hov]; omega
  have hw : vmemW (L.mem s) (p.bv + Fl4Spec.vmcsOff f.bv) = (L.mem s ⟨p.bv + Fl4Spec.vmcsOff f.bv⟩).bv := by
    unfold vmemW; rw [if_pos hal]
  rw [← hw, ← R.vmcs f.bv (Or.inr hf), hvk]
  rfl

theorem JAtZV3.rdCr2Vmx (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (hvk : Fl4Spec.virtKind = .vmx) :
    (L.mem s (core.num.U64.wrapping_add p vcpu.CR2)).bv = vs.get Fl4Spec.virtKind (.msr Fl4Spec.msrCr2) := by
  have R0 := J.vr p hp vs hk
  rw [hvk] at R0
  have R : Fl4Spec.VcpuRelVmx (vmemW (L.mem s)) p.bv vs := R0
  have e : vcpu.CR2.bv = Fl4Spec.VcpuLay.CR2 := by unfold vcpu.CR2; rfl
  have hv : vcpu.CR2.val = 20512 := by unfold vcpu.CR2; rfl
  rw [J.rdw hp (by rw [hv]; omega) (by rw [hv]), e, ← R.cr2, hvk]
  rfl

theorem JAtZV3.rdVmcb (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (hvk : Fl4Spec.virtKind = .svm)
    (o : U64) (hr : Fl4Spec.Svm.readable o.bv = true) (hh : Fl4Spec.Svm.hiddenRead o.bv = false)
    (hx : o.bv ≠ Fl4Spec.Svm.rax) (ho : o.val < 20480) :
    (L.mem s (core.num.U64.wrapping_add p o)).bv = vs.get Fl4Spec.virtKind (.vmcb o.bv) := by
  have R0 := J.vr p hp vs hk
  rw [hvk] at R0
  have R : Fl4Spec.VcpuRelSvm (vmemW (L.mem s)) p.bv vs := R0
  have ha : o.val % 8 = 0 := by
    have h7 : o.bv &&& 7 = 0 := by
      unfold Fl4Spec.Svm.readable at hr; simp only [Bool.and_eq_true, decide_eq_true_eq] at hr; exact hr.1
    have := congrArg BitVec.toNat h7
    rw [BitVec.toNat_and] at this
    have e7 : (7 : BitVec 64).toNat = 2 ^ 3 - 1 := rfl
    rw [e7, Nat.and_two_pow_sub_one_eq_mod] at this
    exact this
  rw [J.rdw hp (by omega) ha, ← R.vmcb o.bv hr hh hx, hvk]
  show _ = vs.fields (Fl4Spec.VField.canon .svm (.vmcb o.bv))
  simp [Fl4Spec.VField.canon, hx]

theorem v3_cr2_val : (Fl4Spec.Svm.cr2).toNat = 1600 := by decide
theorem v3_cr2_rd : Fl4Spec.Svm.readable Fl4Spec.Svm.cr2 = true := by decide
theorem v3_cr2_hid : Fl4Spec.Svm.hiddenRead Fl4Spec.Svm.cr2 = false := by decide
theorem v3_cr2_rax : Fl4Spec.Svm.cr2 ≠ Fl4Spec.Svm.rax := by decide
theorem v3_cr2_canon : Fl4Spec.VField.canon .svm (.msr Fl4Spec.msrCr2) = .vmcb Fl4Spec.Svm.cr2 := by
  have h1 : Fl4Spec.msrCr2 ≠ Fl4Spec.msrStar := by decide
  have h2 : Fl4Spec.msrCr2 ≠ Fl4Spec.msrLstar := by decide
  have h3 : Fl4Spec.msrCr2 ≠ Fl4Spec.msrCstar := by decide
  have h4 : Fl4Spec.msrCr2 ≠ Fl4Spec.msrFmask := by decide
  have h5 : Fl4Spec.msrCr2 ≠ Fl4Spec.msrKernelGsBase := by decide
  simp only [Fl4Spec.VField.canon, ↓reduceIte, h1, h2, h3, h4, h5]
theorem v3_cr2_canon' : Fl4Spec.VField.canon .svm (.vmcb Fl4Spec.Svm.cr2) = .vmcb Fl4Spec.Svm.cr2 := by
  simp only [Fl4Spec.VField.canon, v3_cr2_rax, and_false, ↓reduceIte]

theorem JAtZV3.rdCr2Svm (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (hvk : Fl4Spec.virtKind = .svm) :
    (L.mem s (core.num.U64.wrapping_add p 1600#u64)).bv = vs.get Fl4Spec.virtKind (.msr Fl4Spec.msrCr2) := by
  have e : (1600#u64 : U64) = ⟨Fl4Spec.Svm.cr2⟩ :=
    UScalar.eq_of_val_eq (by show (1600#u64 : U64).val = (Fl4Spec.Svm.cr2).toNat; rw [v3_cr2_val]; rfl)
  have ho : (⟨Fl4Spec.Svm.cr2⟩ : U64).val < 20480 := by show (Fl4Spec.Svm.cr2).toNat < 20480; rw [v3_cr2_val]; omega
  rw [e, J.rdVmcb hp hk hvk ⟨Fl4Spec.Svm.cr2⟩ v3_cr2_rd v3_cr2_hid v3_cr2_rax ho, hvk]
  show vs.fields (Fl4Spec.VField.canon .svm (.vmcb Fl4Spec.Svm.cr2)) =
    vs.fields (Fl4Spec.VField.canon .svm (.msr Fl4Spec.msrCr2))
  rw [v3_cr2_canon, v3_cr2_canon']

end

end

end Fl4Proofs.P3
