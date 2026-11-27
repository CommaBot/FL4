/-
P3x for virtualization (line virt, gen 15, item 2b): **WriteVMCB's stores keep the SVM relation**, RAX included —
FL4 `vcpu::decode`'s WriteVMCB arm after `sanitize_vmcb` (vcpu.rs l. 934-950: `set(v, f, val)`; for CR0 / CR3 / CR4
/ EFER / G_PAT `set(v, SVM_CPU, 0)`; for RAX also `set(v, REGS, val)`) against the spec's
`performVcpuInvocation (.writeVmcb v f val)` (Ext/VirtVcpu: `vs.set virtKind (.vmcb f) val`, whose canonical place for
RAX is GPR 0, `VField.canon`).

* `VcpuRelCommon.keep`, **`VcpuRelSvm.keep_word`**: a write of the VMCB's RAX word or of `SVM_CPU` (0x5038) keeps
  the relation (neither is a related place: RAX's is `REGS`, `SVM_CPU` is FL4's host-side TLB tag).
* `svm_writable_nat` (every writable VMCB word is 8-aligned below 1768).
* **`VcpuRelSvm.store_vmcb`**: storing `x` at a writable word other than RAX relates to `vs.set .svm (.vmcb f) x`
  (gen 10's `write_vmcb` over `WrAt`, P3/VirtMsrStore).
* **`VcpuRelSvm.store_rax`**: storing `x` at `REGS` relates to `vs.set .svm (.vmcb Svm.rax) x` (= GPR 0 := x).
* **`vmcbStore_svm`**: FL4's whole store sequence (word, optional `SVM_CPU := 0`, RAX's `REGS` copy) relates to
  `vs.set .svm (.vmcb f) x` — the RAX case gen 10's `write_vmcb` excluded is closed here.
* Spec side: **`writeVmcb_out`**, **`writeVmcb_rel_svm`** (both halves joined, `VRelAt`).

Not here: the extracted `vcpu.decode` on `X86VCPUWriteVMCB` (the decode-equality `decode_wrmsr_eq` gave for
WriteMSR), so this is the store half at the relation level; the `old` word FL4 reads (`get(v, f)`) agrees with the
spec's `st.get virtKind (.vmcb f)` by the relation's `vmcb` clause off RAX, and RAX's rule has the full mask
(`Svm.writeRule`: `⟨~~~0, 0, false⟩`), so `old` does not matter there.
No named premise; no [J]/[P]/[W]/[S]. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtMsrStore
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtVmcbStore
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtVcpuRel Fl4Proofs.P3.VirtInitWalk
open Fl4Proofs.P3.VirtRetypeInit Fl4Proofs.P3.VirtMsrStore

noncomputable section

theorem VcpuRelCommon.keep {mem mem' : Word → Word} {v o y : Word} {vs : VcpuState}
    (h : VcpuRelCommon mem v vs) (hw : WrAt mem mem' v o y) (hO : HO o) (hx : o.toNat ≠ 20504)
    (hi : o.toNat ≠ 20544) : VcpuRelCommon mem' v vs where
  tcb := by rw [hw.keep (by decide) (by decide) (fun e => hO.1 (by rw [← e]; rfl))]; exact h.tcb
  valid := by rw [hw.keep (by decide) (by decide) (fun e => hO.2.1 (by rw [← e]; rfl))]; exact h.valid
  pending := by rw [hw.keep (by decide) (by decide) (fun e => hO.2.2.1 (by rw [← e]; rfl))]; exact h.pending
  mrs i := by
    have e := exitOff_nat i
    rw [hw.keep (by omega) (by omega) (fun e' => hO.2.2.2.2 i.val i.isLt (by omega))]; exact h.mrs i
  gpr i := by
    have e := gprOff_nat i
    rw [hw.keep (by omega) (by omega) (fun e' => hO.2.2.2.1 i.val i.isLt (by omega))]; exact h.gpr i
  xcr0 := by rw [hw.keep (by decide) (by decide) (fun e => hx (by rw [← e]; rfl))]; exact h.xcr0
  ibpb := by rw [hw.keep (by decide) (by decide) (fun e => hi (by rw [← e]; rfl))]; exact h.ibpb

theorem rax_nat : Svm.rax.toNat = 1528 := by decide

/-- **A write of RAX's VMCB copy or of `SVM_CPU` keeps the SVM relation.** -/
theorem VcpuRelSvm.keep_word {mem mem' : Word → Word} {v o y : Word} {vs : VcpuState} (h : VcpuRelSvm mem v vs)
    (hw : WrAt mem mem' v o y) (ho : o = Svm.rax ∨ o.toNat = 20536) : VcpuRelSvm mem' v vs := by
  have hn : o.toNat = 1528 ∨ o.toNat = 20536 := by
    rcases ho with rfl | h'
    · exact Or.inl rax_nat
    · exact Or.inr h'
  refine { VcpuRelCommon.keep h.toVcpuRelCommon hw
      ⟨by omega, by omega, by omega, fun i _ => by omega, fun i _ => by omega⟩ (by omega) (by omega) with
    vmcb := fun off hr hh hx => ?_ }
  have := readable_nat hr
  rw [hw.keep (by omega) this.1 ?_]
  · exact h.vmcb off hr hh hx
  · rcases ho with rfl | h'
    · exact toNat_ne_of_ne hx
    · omega

theorem svm_writable_nat {f : Word} (hf : Svm.writable f = true) : f.toNat % 8 = 0 ∧ f.toNat < 1768 := by
  have hm := writeRule_mem hf
  simp only [svmTab, List.mem_cons, List.not_mem_nil, or_false] at hm
  repeat (rcases hm with rfl | hm; · decide)

/-- **Storing a writable VMCB word other than RAX.** -/
theorem VcpuRelSvm.store_vmcb {mem mem' : Word → Word} {v f x : Word} {vs : VcpuState} (h : VcpuRelSvm mem v vs)
    (hf : Svm.writable f = true) (hr : f ≠ Svm.rax) (hw : WrAt mem mem' v f x) :
    VcpuRelSvm mem' v (vs.set .svm (.vmcb f) x) := by
  have hn := svm_writable_nat hf
  have hc : VField.canon .svm (.vmcb f) = .vmcb f := by simp [VField.canon, hr]
  unfold VcpuState.set
  rw [hc]
  refine { VcpuRelCommon.upd h.toVcpuRelCommon hw (fun i => by simp)
      ⟨by omega, by omega, by omega, fun i _ => by omega, fun i _ => by omega⟩
      (Or.inr ⟨by simp, by omega⟩) (Or.inr ⟨by simp, by omega⟩) with
    vmcb := fun off hr' hh hx => ?_ }
  show Function.update vs.fields (.vmcb f) x (.vmcb off) = _
  by_cases e : off = f
  · subst e; rw [Function.update_self, hw.1]
  · have := readable_nat hr'
    rw [Function.update_of_ne (by simpa using e), hw.keep (by omega) this.1 (toNat_ne_of_ne e)]
    exact h.vmcb off hr' hh hx

theorem regs_gpr0 : gprOff 0 = VcpuLay.REGS := by decide

/-- **Storing RAX's canonical place `REGS`** (= GPR 0). -/
theorem VcpuRelSvm.store_rax {mem mem' : Word → Word} {v x : Word} {vs : VcpuState} (h : VcpuRelSvm mem v vs)
    (hw : WrAt mem mem' v VcpuLay.REGS x) : VcpuRelSvm mem' v (vs.set .svm (.vmcb Svm.rax) x) := by
  have hc : VField.canon .svm (.vmcb Svm.rax) = .gpr 0 := by simp [VField.canon]
  have hR : VcpuLay.REGS.toNat = 20736 := by decide
  unfold VcpuState.set
  rw [hc]
  refine
    { tcb := by rw [hw.keep (by decide) (by decide) (by rw [hR]; decide)]; exact h.tcb
      valid := by rw [hw.keep (by decide) (by decide) (by rw [hR]; decide)]; exact h.valid
      pending := by rw [hw.keep (by decide) (by decide) (by rw [hR]; decide)]; exact h.pending
      mrs := fun i => by
        have e := exitOff_nat i
        rw [hw.keep (by omega) (by omega) (by omega)]; exact h.mrs i
      gpr := fun i => ?_
      xcr0 := by
        show Function.update vs.fields (.gpr 0) x (.msr msrXcr0) = _
        rw [Function.update_of_ne (by simp), hw.keep (by decide) (by decide) (by rw [hR]; decide)]; exact h.xcr0
      ibpb := by
        show Function.update vs.fields (.gpr 0) x (.msr msrVmIbpbDefer) = _
        rw [Function.update_of_ne (by simp), hw.keep (by decide) (by decide) (by rw [hR]; decide)]; exact h.ibpb
      vmcb := fun off hr hh hx => ?_ }
  · show Function.update vs.fields (.gpr 0) x (.gpr i) = _
    by_cases e : i = 0
    · subst e; rw [Function.update_self, regs_gpr0, hw.1]
    · have e2 := gprOff_nat i
      have hi : i.val ≠ 0 := fun h' => e (Fin.ext h')
      rw [Function.update_of_ne (by simpa using e), hw.keep (by omega) (by omega) (by omega)]; exact h.gpr i
  · show Function.update vs.fields (.gpr 0) x (.vmcb off) = _
    have := readable_nat hr
    rw [Function.update_of_ne (by simp), hw.keep (by omega) this.1 (by omega)]; exact h.vmcb off hr hh hx

/-- **FL4's WriteVMCB stores, whole** (module docstring): the word, the optional `SVM_CPU := 0`, and for RAX the
`REGS` copy, relate to `vs.set .svm (.vmcb f) x`. -/
theorem vmcbStore_svm {m0 m1 m2 m3 : Word → Word} {v f x : Word} {vs : VcpuState} (h : VcpuRelSvm m0 v vs)
    (hf : Svm.writable f = true) (h1 : WrAt m0 m1 v f x)
    (h2 : m2 = m1 ∨ ∃ o, o.toNat = 20536 ∧ WrAt m1 m2 v o 0)
    (h3 : (f = Svm.rax → WrAt m2 m3 v VcpuLay.REGS x) ∧ (f ≠ Svm.rax → m3 = m2)) :
    VcpuRelSvm m3 v (vs.set .svm (.vmcb f) x) := by
  have step2 : ∀ {vs'}, VcpuRelSvm m1 v vs' → VcpuRelSvm m2 v vs' := fun {vs'} r => by
    rcases h2 with rfl | ⟨o, ho, hw⟩
    · exact r
    · exact VcpuRelSvm.keep_word r hw (Or.inr ho)
  by_cases hr : f = Svm.rax
  · subst hr
    exact VcpuRelSvm.store_rax (step2 (VcpuRelSvm.keep_word h h1 (Or.inl rfl))) (h3.1 rfl)
  · rw [h3.2 hr]
    exact step2 (VcpuRelSvm.store_vmcb h hf hr h1)

/-! ## Spec side -/

section
variable {Z : Type}

/-- **The spec's WriteVMCB**: the VCPU becomes `vs.set virtKind (.vmcb f) val`, the reply is `[val]`. -/
theorem writeVmcb_out {σ : State Z} {v : ObjRef} {f val : Word} {vs : VcpuState} (hv : vcpuAt σ v = some vs)
    {x : List Data × State Z} (hx : x ∈ (performVcpuInvocation (Z := Z) (.writeVmcb v f val) σ).1) :
    vcpuAt x.2 v = some (vs.set virtKind (.vmcb f) val) ∧ x.1 = [val] := by
  simp only [performVcpuInvocation] at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hx
  exact ⟨vcpuUpdate_out hv hy, rfl⟩

/-- **WriteVMCB, both halves** (SVM backend). -/
theorem writeVmcb_rel_svm (hk : virtKind = .svm) {mem : Word → Word} {σ : State Z} {v : ObjRef} {f val : Word}
    {vs : VcpuState} (hv : vcpuAt σ v = some vs) (hf : VcpuRelSvm mem v (vs.set .svm (.vmcb f) val))
    {x : List Data × State Z} (hx : x ∈ (performVcpuInvocation (Z := Z) (.writeVmcb v f val) σ).1) :
    VRelAt mem x.2 v := by
  obtain ⟨e, -⟩ := writeVmcb_out hv hx
  exact ⟨_, e, fun _ => by rw [hk]; exact hf, fun h => absurd hk h⟩

end

end
end Fl4Proofs.P3.VirtVmcbStore
