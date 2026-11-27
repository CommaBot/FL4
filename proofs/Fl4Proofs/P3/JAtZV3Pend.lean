/-
P3 (line mmuAD, gen 33): **`PENDING := 0` with the paired spec update `VcpuState.reported`** at `JAtZV3` — the VCPU
write of FL4's `vcpu::report` on a pending exit (`set(s, v, PENDING, 0)`), against `vmReportF`'s `vcpuUpdate v
VcpuState.reported` (Ext/VirtReport; `reported` clears `exit.pending`, Ext/VirtState).

* **`v3_pendR`**: the VCPU relation (either backend) across a change of the `PENDING` word only, the new word 0,
  with the spec VCPU `reported` (gen 31's `v3_gprR` pattern: every other related word is at another offset).
* **`JAtZV3.pendClr`**: FL4's write of 0 at `p + PENDING` (`p ∈ V`) paired with the spec's `updK p (vcpu
  vs.reported)` keeps `JAtZV3` (via gen 30's `JAtZV3.vcpuStep`).

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3Gpr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
open Fl4Spec

theorem v3_ne_pend {o : Word} (h : o.toNat ≠ 20520) : o ≠ VcpuLay.PENDING := fun e => h (by rw [e]; rfl)

/-- **The relation across a change of the `PENDING` word only, to 0** (module docstring). -/
theorem v3_pendR {k : VirtKind} {mem mem' : Word → Word} {v : Word} {vs : VcpuState}
    (hm : ∀ o, o < VcpuLay.SIZE → o ≠ VcpuLay.PENDING → mem' (v + o) = mem (v + o))
    (h0 : mem' (v + VcpuLay.PENDING) = 0) (h : VcpuRel k mem v vs) :
    VcpuRel k mem' v vs.reported := by
  obtain ⟨f0, f1, f2, f3, f4, f6⟩ := v3_fix_vals
  have hc : VcpuRelCommon mem v vs → VcpuRelCommon mem' v vs.reported := fun h => {
    tcb := by rw [hm _ VirtVcpuRel.tcb_lt (v3_ne_pend (by omega))]; exact h.tcb
    valid := by rw [hm _ VirtVcpuRel.valid_lt (v3_ne_pend (by omega))]; exact h.valid
    pending := by rw [h0]; simp [VcpuState.reported]
    mrs := fun j => by
      rw [hm _ (VirtVcpuRel.exitOff_lt j) (v3_ne_pend (by have := v3_exit_ge j; omega))]; exact h.mrs j
    gpr := fun j => by
      rw [hm _ (VirtVcpuRel.gprOff_lt j) (v3_ne_pend (by have := v3_gpr_ge j; omega))]; exact h.gpr j
    xcr0 := by rw [hm _ VirtVcpuRel.xcr0_lt (v3_ne_pend (by omega))]; exact h.xcr0
    ibpb := by rw [hm _ VirtVcpuRel.ibpb_lt (v3_ne_pend (by omega))]; exact h.ibpb }
  cases k with
  | vmx =>
    have h : VcpuRelVmx mem v vs := h
    exact show VcpuRelVmx mem' v vs.reported from { hc h.toVcpuRelCommon with
      vmcs := fun f hf => by
        rw [hm _ (VirtVcpuRel.vmcsOff_lt hf) (v3_ne_pend (by have := v3_vmcs_lt f; omega))]; exact h.vmcs f hf
      msr := fun m j hj => by
        rw [hm _ (VirtVcpuRel.msrOff_lt hj) (v3_ne_pend (by have := v3_msr_ge hj; omega))]; exact h.msr m j hj
      cr2 := by rw [hm _ VirtVcpuRel.cr2_lt (v3_ne_pend (by omega))]; exact h.cr2
      io := fun p => by
        rw [hm _ (VirtVcpuRel.ioOff_lt p) (v3_ne_pend (by have := v3_io_ge p; omega))]; exact h.io p }
  | svm =>
    have h : VcpuRelSvm mem v vs := h
    exact show VcpuRelSvm mem' v vs.reported from { hc h.toVcpuRelCommon with
      vmcb := fun off hr hh hx => by
        rw [hm _ (VirtVcpuRel.svmOff_lt hr) (v3_ne_pend (by have := v3_vmcb_lt hr; omega))]
        exact h.vmcb off hr hh hx }
  | none => exact h.elim
  | armEl2 => exact h.elim

end

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **FL4's `PENDING := 0` paired with the spec's `VcpuState.reported`** (module docstring). -/
theorem JAtZV3.pendClr (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p w : U64} (hp : p ∈ V)
    (hwp : w.val = p.val + 20520)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) :
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr s w 0#u64) a
      (Notif.updK σ p.bv (.archObj (.vcpu vs.reported))) := by
  have Ly := J.z2.zv.base.jvLay J.z2.zv.vm
  have hf := Ly.vfit p hp
  have hfu := hf.2
  have hal : P1.Aligned w := by
    show w.val % 8 = 0
    have : p.val % 32768 = 0 := hf.1
    omega
  have hW : P1.WritesIn st s (L.wr s w 0#u64) (· = w) := P1.writesIn_wr hal
  have R0 := J.vr p hp vs hk
  have hpv : Fl4Spec.VcpuLay.PENDING.toNat = 20520 := v3_fix_vals.2.2.1
  have e1 := v3_toNat_add hfu VirtVcpuRel.pending_lt
  have h0 : vmemW (L.mem (L.wr s w 0#u64)) (p.bv + Fl4Spec.VcpuLay.PENDING) = 0 := by
    have ha : (p.bv + Fl4Spec.VcpuLay.PENDING).toNat % 8 = 0 := by rw [e1, hpv]; omega
    unfold vmemW
    rw [if_pos ha]
    rw [show (⟨p.bv + Fl4Spec.VcpuLay.PENDING⟩ : U64) = w from
      UScalar.eq_of_val_eq (by show (p.bv + Fl4Spec.VcpuLay.PENDING).toNat = w.val; rw [e1, hpv, hwp])]
    rw [L.mem_wr s w 0#u64 w hal hal, if_pos rfl]
    rfl
  have hR := v3_pendR (k := Fl4Spec.virtKind) (mem := vmemW (L.mem s)) (mem' := vmemW (L.mem (L.wr s w 0#u64)))
    (v3_agree hfu fun b hb _ _ hne => hW.mem_eq hb fun e' => hne (by rw [e', hpv]; omega)) h0 R0
  exact J.vcpuStep hp hal (by omega) (by omega) ⟨by omega, by omega, by omega⟩ 0#u64 hk _ rfl hR

end

end

end Fl4Proofs.P3
