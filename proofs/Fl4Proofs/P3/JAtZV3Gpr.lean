/-
P3 (line mmuAD, gen 31): **VCPU GPR words with the paired spec update at `JAtZV3`** — the per-word core of
`vcpu::decode` X86VCPUWriteRegisters (vcpu.rs: `set(s, v, REGS + i * 8, val)` for `i < 15`, then on SVM
`set(s, v, svm::RAX, get(s, v, REGS))`), against the extended spec's `performVcpuInvocation (.writeRegisters v
vals)` = `vcpuUpdate v (VcpuState.setGprs vals)` (Ext/VirtVcpu). WriteRegisters has no sanitize step (neither in
FL4 nor in the spec's decoder), so it needs nothing from the virt line's sanitize work.

* **`vsSetGpr i x vs`**: the spec VCPU with GPR `i` set to `x`; **`vsSetGpr_fold`**: the 15 single updates in
  FL4's loop order (`i = 0..14`) give `VcpuState.setGprs vals`.
* Offsets: **`v3_gpr_val`** (`gprOff i = 20736 + 8 i`), **`v3_rax_val`** (the VMCB RAX word, offset `0x5f8`),
  **`v3_vmcs_ge`** (VMCS shadow words start at `SHADOW = 0x1000`).
* **`v3_gprR`**: the VCPU relation (either backend) across a change of GPR word `i` only, with the spec GPR `i`
  set to the new word. **`v3_raxR`**: the relation is unaffected by a change of the VMCB RAX word only, on both
  backends (VMX reads no word below `SHADOW` but the fixed words; SVM's `vmcb` clause excludes RAX, which only the
  kernel-exit `SvmRaxSync` relates).
* **`JAtZV3.gprWr`**: FL4's write of GPR word `i` of a VCPU of `V` with `x`, paired with the spec's
  `vsSetGpr i x.bv`, keeps `JAtZV3` (via gen 30's `JAtZV3.vcpuStep`). **`JAtZV3.raxWr`**: FL4's write of the
  VMCB RAX word keeps `JAtZV3` with the spec unchanged.

Not covered here: the extracted `vcpu.decode` front end and loop (`stall`, `cur_thread`, `syscall_arg`, the
Aeneas loop over `i`), whose WP composes 15 `gprWr` + `raxWr` + `vsSetGpr_fold`; and the platform agreement
`a.virtualization() = 2 ↔ virtKind = .svm` is not needed for these two lemmas (RAX is unread on both backends).

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
open Fl4Spec

/-- The spec VCPU with GPR `i` set to `x` (module docstring). -/
def vsSetGpr (i : Fin 15) (x : Word) (vs : VcpuState) : VcpuState :=
  { vs with fields := fun f => if f = .gpr i then x else vs.fields f }

/-- **FL4's loop order gives `setGprs`** (module docstring). -/
theorem vsSetGpr_fold (vals : Fin 15 → Word) (vs : VcpuState) :
    (List.finRange 15).foldl (fun st i => vsSetGpr i (vals i) st) vs = vs.setGprs vals := by
  have hl : List.finRange 15 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] := by decide
  rw [hl]
  cases vs with
  | mk tcb fields exit io =>
    simp only [List.foldl, VcpuState.setGprs, vsSetGpr]
    congr 1
    funext f
    cases f with
    | gpr j => fin_cases j <;> simp
    | vmcs e => simp
    | vmcb e => simp
    | msr e => simp

theorem vsSetGpr_ne {i : Fin 15} {x : Word} {vs : VcpuState} {f : VField} (h : f ≠ VField.gpr i) :
    (vsSetGpr i x vs).fields f = vs.fields f := if_neg h

theorem v3_gpr_val : ∀ i : Fin 15, (gprOff i).toNat = 20736 + 8 * i.val := by decide

theorem v3_rax_val : Svm.rax.toNat = 1528 := by decide

theorem v3_vmcs_ge (f : Word) : 4096 ≤ (vmcsOff f).toNat := by
  have h := VirtVcpuRel.vmcsIdx_lt f
  have a : VcpuLay.SHADOW.toNat = 4096 := rfl
  unfold vmcsOff
  rw [BitVec.toNat_add, BitVec.toNat_mul, a, VirtVcpuRel.toNat_eight]
  simp only [Nat.reducePow] at h ⊢
  omega

theorem v3_ne_gpr_lt {o : Word} (h : o.toNat < 20736) (i : Fin 15) : o ≠ gprOff i := fun e => by
  have := v3_gpr_val i; rw [← e] at this; omega

theorem v3_ne_gpr_ge {o : Word} (h : 20864 ≤ o.toNat) (i : Fin 15) : o ≠ gprOff i := fun e => by
  have := v3_gpr_val i; rw [← e] at this; have := i.isLt; omega

theorem v3_gpr_ne {i j : Fin 15} (h : j ≠ i) : gprOff j ≠ gprOff i := fun e => by
  have a := v3_gpr_val i; have b := v3_gpr_val j; rw [e] at b
  exact h (Fin.ext (by omega))

theorem v3_ne_rax {o : Word} (h : 4096 ≤ o.toNat) : o ≠ Svm.rax := fun e => by
  have := v3_rax_val; rw [← e] at this; omega

theorem v3_fix_vals : VcpuLay.TCB.toNat = 20480 ∧ VcpuLay.VALID.toNat = 20528 ∧ VcpuLay.PENDING.toNat = 20520 ∧
    VcpuLay.XCR0.toNat = 20504 ∧ VcpuLay.VM_IBPB_DEFER.toNat = 20544 ∧ VcpuLay.CR2.toNat = 20512 := by decide

theorem v3_gprC {mem mem' : Word → Word} {v : Word} {vs : VcpuState} {i : Fin 15}
    (hm : ∀ o, o < VcpuLay.SIZE → o ≠ gprOff i → mem' (v + o) = mem (v + o)) (h : VcpuRelCommon mem v vs) :
    VcpuRelCommon mem' v (vsSetGpr i (mem' (v + gprOff i)) vs) := by
  obtain ⟨f1, f2, f3, f4, f5, -⟩ := v3_fix_vals
  exact {
    tcb := by rw [hm _ VirtVcpuRel.tcb_lt (v3_ne_gpr_lt (by omega) i)]; exact h.tcb
    valid := by rw [hm _ VirtVcpuRel.valid_lt (v3_ne_gpr_lt (by omega) i)]; exact h.valid
    pending := by rw [hm _ VirtVcpuRel.pending_lt (v3_ne_gpr_lt (by omega) i)]; exact h.pending
    mrs := fun j => by
      rw [hm _ (VirtVcpuRel.exitOff_lt j) (v3_ne_gpr_ge (by have := v3_exit_ge j; omega) i)]; exact h.mrs j
    gpr := fun j => by
      by_cases e : j = i
      · rw [e]; simp [vsSetGpr]
      · rw [vsSetGpr_ne (fun h' => e (VField.gpr.inj h')), hm _ (VirtVcpuRel.gprOff_lt j) (v3_gpr_ne e)]
        exact h.gpr j
    xcr0 := by
      rw [vsSetGpr_ne (fun h' => VField.noConfusion h'), hm _ VirtVcpuRel.xcr0_lt (v3_ne_gpr_lt (by omega) i)]
      exact h.xcr0
    ibpb := by
      rw [vsSetGpr_ne (fun h' => VField.noConfusion h'), hm _ VirtVcpuRel.ibpb_lt (v3_ne_gpr_lt (by omega) i)]
      exact h.ibpb }


theorem v3_gprVmx {mem mem' : Word → Word} {v : Word} {vs : VcpuState} {i : Fin 15}
    (hm : ∀ o, o < VcpuLay.SIZE → o ≠ gprOff i → mem' (v + o) = mem (v + o)) (h : VcpuRelVmx mem v vs) :
    VcpuRelVmx mem' v (vsSetGpr i (mem' (v + gprOff i)) vs) := by
  obtain ⟨-, -, -, -, -, f6⟩ := v3_fix_vals
  exact { v3_gprC hm h.toVcpuRelCommon with
    vmcs := fun f hf => by
      rw [vsSetGpr_ne (fun h' => VField.noConfusion h'),
        hm _ (VirtVcpuRel.vmcsOff_lt hf) (v3_ne_gpr_lt (by have := v3_vmcs_lt f; omega) i)]
      exact h.vmcs f hf
    msr := fun m j hj => by
      rw [vsSetGpr_ne (fun h' => VField.noConfusion h'),
        hm _ (VirtVcpuRel.msrOff_lt hj) (v3_ne_gpr_ge (v3_msr_ge hj) i)]
      exact h.msr m j hj
    cr2 := by
      rw [vsSetGpr_ne (fun h' => VField.noConfusion h'), hm _ VirtVcpuRel.cr2_lt (v3_ne_gpr_lt (by omega) i)]
      exact h.cr2
    io := fun p => by
      rw [hm _ (VirtVcpuRel.ioOff_lt p) (v3_ne_gpr_ge (by have := v3_io_ge p; omega) i)]; exact h.io p }

theorem v3_gprSvm {mem mem' : Word → Word} {v : Word} {vs : VcpuState} {i : Fin 15}
    (hm : ∀ o, o < VcpuLay.SIZE → o ≠ gprOff i → mem' (v + o) = mem (v + o)) (h : VcpuRelSvm mem v vs) :
    VcpuRelSvm mem' v (vsSetGpr i (mem' (v + gprOff i)) vs) :=
  { v3_gprC hm h.toVcpuRelCommon with
    vmcb := fun off hr hh hx => by
      rw [vsSetGpr_ne (fun h' => VField.noConfusion h'),
        hm _ (VirtVcpuRel.svmOff_lt hr) (v3_ne_gpr_lt (by have := v3_vmcb_lt hr; omega) i)]
      exact h.vmcb off hr hh hx }

/-- **The relation across a change of GPR word `i` only** (module docstring). -/
theorem v3_gprR {k : VirtKind} {mem mem' : Word → Word} {v : Word} {vs : VcpuState} {i : Fin 15}
    (hm : ∀ o, o < VcpuLay.SIZE → o ≠ gprOff i → mem' (v + o) = mem (v + o)) (h : VcpuRel k mem v vs) :
    VcpuRel k mem' v (vsSetGpr i (mem' (v + gprOff i)) vs) := by
  cases k with
  | vmx => exact v3_gprVmx hm h
  | svm => exact v3_gprSvm hm h
  | none => exact h.elim
  | armEl2 => exact h.elim

/-- **The relation does not read the VMCB RAX word** (module docstring). -/
theorem v3_raxR {k : VirtKind} {mem mem' : Word → Word} {v : Word} {vs : VcpuState}
    (hm : ∀ o, o < VcpuLay.SIZE → o ≠ Svm.rax → mem' (v + o) = mem (v + o)) (h : VcpuRel k mem v vs) :
    VcpuRel k mem' v vs := by
  obtain ⟨f0, f1, f2, f3, f4, f6⟩ := v3_fix_vals
  have hc : VcpuRelCommon mem v vs → VcpuRelCommon mem' v vs := fun h => {
    tcb := by rw [hm _ VirtVcpuRel.tcb_lt (v3_ne_rax (by omega))]; exact h.tcb
    valid := by rw [hm _ VirtVcpuRel.valid_lt (v3_ne_rax (by omega))]; exact h.valid
    pending := by rw [hm _ VirtVcpuRel.pending_lt (v3_ne_rax (by omega))]; exact h.pending
    mrs := fun j => by
      rw [hm _ (VirtVcpuRel.exitOff_lt j) (v3_ne_rax (by have := v3_exit_ge j; omega))]; exact h.mrs j
    gpr := fun j => by
      rw [hm _ (VirtVcpuRel.gprOff_lt j) (v3_ne_rax (by have := v3_gpr_ge j; omega))]; exact h.gpr j
    xcr0 := by rw [hm _ VirtVcpuRel.xcr0_lt (v3_ne_rax (by omega))]; exact h.xcr0
    ibpb := by rw [hm _ VirtVcpuRel.ibpb_lt (v3_ne_rax (by omega))]; exact h.ibpb }
  cases k with
  | vmx =>
    have h : VcpuRelVmx mem v vs := h
    exact show VcpuRelVmx mem' v vs from { hc h.toVcpuRelCommon with
      vmcs := fun f hf => by
        rw [hm _ (VirtVcpuRel.vmcsOff_lt hf) (v3_ne_rax (v3_vmcs_ge f))]; exact h.vmcs f hf
      msr := fun m j hj => by
        rw [hm _ (VirtVcpuRel.msrOff_lt hj) (v3_ne_rax (by have := v3_msr_ge hj; omega))]; exact h.msr m j hj
      cr2 := by rw [hm _ VirtVcpuRel.cr2_lt (v3_ne_rax (by omega))]; exact h.cr2
      io := fun p => by
        rw [hm _ (VirtVcpuRel.ioOff_lt p) (v3_ne_rax (by have := v3_io_ge p; omega))]; exact h.io p }
  | svm =>
    have h : VcpuRelSvm mem v vs := h
    exact show VcpuRelSvm mem' v vs from { hc h.toVcpuRelCommon with
      vmcb := fun off hr hh hx => by
        rw [hm _ (VirtVcpuRel.svmOff_lt hr) hx]; exact h.vmcb off hr hh hx }
  | none => exact h.elim
  | armEl2 => exact h.elim

end

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **FL4's write of GPR word `i` paired with the spec's GPR update** (module docstring). -/
theorem JAtZV3.gprWr (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p w : U64} (hp : p ∈ V)
    (i : Fin 15) (hwi : w.val = p.val + 20736 + 8 * i.val) (x : U64)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s w x) a
      (Notif.updK σ p.bv (.archObj (.vcpu (vsSetGpr i x.bv vs)))) := by
  have Ly := J.z2.zv.base.jvLay J.z2.zv.vm
  have hf := Ly.vfit p hp
  have hfu := hf.2
  have hil := i.isLt
  have hal : P1.Aligned w := by
    show w.val % 8 = 0
    have : p.val % 32768 = 0 := hf.1
    omega
  have hW : P1.WritesIn st s (L.wr s w x) (· = w) := P1.writesIn_wr hal
  have R0 := J.vr p hp vs hk
  have hg := v3_gpr_val i
  have e1 := v3_toNat_add hfu (VirtVcpuRel.gprOff_lt i)
  have hR := v3_gprR (k := Fl4Spec.virtKind) (mem := vmemW (L.mem s)) (mem' := vmemW (L.mem (L.wr s w x)))
    (i := i) (v3_agree hfu fun b hb _ _ hne => hW.mem_eq hb fun e' => hne (by rw [e', hg]; omega)) R0
  have hx : vmemW (L.mem (L.wr s w x)) (p.bv + Fl4Spec.gprOff i) = x.bv := by
    have ha : (p.bv + Fl4Spec.gprOff i).toNat % 8 = 0 := by rw [e1, hg]; omega
    unfold vmemW
    rw [if_pos ha]
    rw [show (⟨p.bv + Fl4Spec.gprOff i⟩ : U64) = w from
      UScalar.eq_of_val_eq (by show (p.bv + Fl4Spec.gprOff i).toNat = w.val; rw [e1, hg, hwi]; omega)]
    rw [L.mem_wr s w x w hal hal, if_pos rfl]
  rw [hx] at hR
  exact J.vcpuStep hp hal (by omega) (by omega) ⟨by omega, by omega, by omega⟩ x hk _ rfl hR

/-- **FL4's write of the VMCB RAX word** keeps `JAtZV3` with the spec unchanged (module docstring). -/
theorem JAtZV3.raxWr (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p w : U64} (hp : p ∈ V)
    (hwi : w.val = p.val + 1528) (x : U64) :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s w x) a σ := by
  have Ly := J.z2.zv.base.jvLay J.z2.zv.vm
  have hf := Ly.vfit p hp
  have hal : P1.Aligned w := by
    show w.val % 8 = 0
    have : p.val % 32768 = 0 := hf.1
    omega
  have hW : P1.WritesIn st s (L.wr s w x) (· = w) := P1.writesIn_wr hal
  refine ⟨J.z2.vcpuWr hp hal (by omega) (by have := hf.2; omega) ⟨by omega, by omega, by omega⟩ x, J.vo, ?_⟩
  intro u hu vs hk
  have R0 := J.vr u hu vs hk
  have hfu := (Ly.vfit u hu).2
  by_cases e : u = p
  · rw [e] at R0 hfu ⊢
    exact v3_raxR (v3_agree hfu fun b hb _ _ hne => hW.mem_eq hb fun e' => hne (by rw [e', v3_rax_val]; omega)) R0
  · refine VirtVcpuRel.VcpuRel.congr (v3_agreeAll hfu fun b hb b1 b2 => hW.mem_eq hb fun e' => ?_) R0
    rw [e'] at b1 b2
    rcases Ly.vv u hu p hp e with h | h <;> omega

end

end

end Fl4Proofs.P3
