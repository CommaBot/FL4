/-
P3 (line mmuAD, gen 34): helpers of `ReportJ3`'s branches (P3/JAtZV3ReportJ3): `rvTriple` (the 3-MR branch's entry-state reads), `v3_full_reply` (`full_reply` = `repFull`), `v3_list3`, `v3_gpr0`, `v3_ite_spec`.

No named premise beyond [P] `ZvVirtAgree arI` (gen 32). No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3RepMrs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

theorem JAtZV3.rvTriple (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) {i : U64}
    (hi : i = 2#u64 ↔ Fl4Spec.virtKind = .svm) :
    (if i = 2#u64
      then
        do
        let i1 ← vcpu.svm.RIP
        let i2 ← vcpu.get st s p i1
        let i3 ← vcpu.get st s p vcpu.svm.INTERCEPT_EXC
        let i4 ← i3 >>> 32#i32
        let i5 ← vcpu.get st s p vcpu.svm.EVENT_INJ
        ok (i2, i4, i5)
      else
        do
        let i1 ← vcpu.read_vmcs st s p vcpu.vmx.GUEST_RIP
        let i2 ←
          vcpu.read_vmcs st s p
            vcpu.vmx.CONTROL_PRIMARY_PROCESSOR_CONTROLS
        let i3 ←
          vcpu.read_vmcs st s p
            vcpu.vmx.CONTROL_ENTRY_INTERRUPTION_INFO
        ok (i1, i2, i3)) ⦃ r => r.1.bv = vs.entryIp Fl4Spec.virtKind ∧ r.2.1.bv = vs.entryCtl Fl4Spec.virtKind ∧
          r.2.2.bv = vs.entryIntr Fl4Spec.virtKind ⦄ := by
  have hR : vcpu.svm.RIP = ok 1400#u64 := by unfold vcpu.svm.RIP vcpu.svm.SAVE; rfl
  by_cases hs : Fl4Spec.virtKind = .svm
  · have h2 := hi.2 hs
    have e1 := J.rvIp hp hk hi
    rw [if_pos h2, hR, bind_ok, v3_get_eq, WP.spec_ok] at e1
    have e2 := J.rvCtl hp hk hi
    rw [if_pos h2, v3_get_eq, bind_ok, v3_shr32, WP.spec_ok] at e2
    have e3 := J.rvIntr hp hk hi
    rw [if_pos h2, v3_get_eq, WP.spec_ok] at e3
    rw [if_pos h2, hR, bind_ok, v3_get_eq, bind_ok, v3_get_eq, bind_ok, v3_shr32, bind_ok, v3_get_eq, bind_ok,
      WP.spec_ok]
    exact ⟨e1, e2, e3⟩
  · have h2 : ¬ i = 2#u64 := fun h => hs (hi.1 h)
    have e1 := J.rvIp hp hk hi
    rw [if_neg h2, v3_read_vmcs_eq, WP.spec_ok] at e1
    have e2 := J.rvCtl hp hk hi
    rw [if_neg h2, v3_read_vmcs_eq, WP.spec_ok] at e2
    have e3 := J.rvIntr hp hk hi
    rw [if_neg h2, v3_read_vmcs_eq, WP.spec_ok] at e3
    rw [if_neg h2, v3_read_vmcs_eq, bind_ok, v3_read_vmcs_eq, bind_ok, v3_read_vmcs_eq, bind_ok, WP.spec_ok]
    exact ⟨e1, e2, e3⟩

theorem v3_full_reply (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) :
    vcpu.full_reply st s t ⦃ r => r = repFull x ⦄ := by
  have B := J.z2.zv.base
  unfold vcpu.full_reply
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s t _) ?_
  rintro m rfl
  rw [WP.spec_ok]
  have h := ((B.xtop.irelK B.ks B.buf).1.toE.at_tcb ht hk).regs Fl4Spec.msg_info_register
  rw [Endp.regIdx_msgInfo] at h
  unfold repFull vcpu.NUM_MRS
  rw [← h]
  apply decide_eq_decide.2
  constructor
  · intro e; rw [e]; rfl
  · intro e
    apply UScalar.eq_of_val_eq
    show (L.mem s (Endp.regA t layout.reg.MSG_INFO)).bv.toNat = (30#u64 : U64).bv.toNat
    rw [e]; rfl

theorem v3_list3 (a b c : U64) :
    mrUpd (mrUpd (mrUpd [] (0#u64 : U64).val a.bv) (1#u64 : U64).val b.bv) (2#u64 : U64).val c.bv = [a.bv, b.bv, c.bv] := by
  simp [mrUpd]

theorem v3_gpr0 (vs : Fl4Spec.VcpuState) (F : Nat → Fl4Spec.Word) :
    (List.range 30).map (gprOv vs F (0#u64 : U64).val) = (List.range 30).map F :=
  v3_map_congr 30 fun k _ => by
    unfold gprOv
    rw [dif_neg (fun h => by have : (0#u64 : U64).val = 0 := rfl; omega)]


theorem v3_ite_spec {α : Type} {c : Prop} [Decidable c] {P R : Result α} {Q : α → Prop}
    (h1 : c → P ⦃ Q ⦄) (h2 : ¬ c → R ⦃ Q ⦄) : (if c then P else R) ⦃ Q ⦄ := by
  by_cases h : c
  · rw [if_pos h]; exact h1 h
  · rw [if_neg h]; exact h2 h


end

end

end Fl4Proofs.P3
