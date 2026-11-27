/-
P3 (line mmuAD, gen 39): **the VCPU dispatcher at `JAtZV3` with every label proved** — `vcpuDecodeJ5` /
`vcpuInvJ5`: P3/JAtZV3VDisp's `vcpuDecodeJ` / P3/JAtZV3VInv's `vcpuInvJ` with no VCPU [J] premise. gen 38's
[J] `VcpuNyp4` (EnableIOPort) is not used: its field is false as stated (P3/JAtZV3VDisp4: an `ex[0]` that is no
CNode slot); here EnableIOPort is proved under a **new field form** whose scope sees the slot.

* **`EioScope th ex p`**: the invoked VCPU's pointer `p` is canonical, and a non-null `ex[0]` is a CNode slot of
  `th` (`cslotAddr (pc, idx)`, `th pc = some (.cnode r)`, `idx.length = r`). Both come from the front end:
  `ex` is `lookup_extra_caps`' array (ipc.rs l. 28-44: every entry a `cspace::lookup_slot` result, a CNode slot),
  `p` the pointer of the invoked cap `Cap::Vcpu { ptr }` decoded from its slot (syscall.rs l. 153, `Cap::decode`
  unpacks a canonical pointer). P3/JAtZV3EioFront derives it from `ExtraOK` (the front end's relation) and the
  invoked slot's cap. Not false on reachable states: FL4's front end calls `vcpu::decode` with exactly such `ex`
  and `p` (syscall.rs l. 184-197).
* **`VLabelOKS … lbl Sc`**: `VLabelOK` (P3/JAtZV3VDisp) with a scope `Sc th ex p b c` that sees the typed heap,
  the extra-slot array and the VCPU (gen 37's `VLabelOK` scope sees only `b c`, too little for EnableIOPort).
* **`vcpuOK_eio`**: the EnableIOPort field in that form, scope `IoFresh b c ∧ EioScope th ex p`, **proved**
  (VMX `len ≥ 2`: P3/JAtZV3VEio's `enableIoPortJ`; SVM / `len < 2`: `vdEioA` / `vdEioS`).
* `vOK_rvmcs`, `vOK_rvmcb`, `vOK_rmsr`, `vOK_dio`: the other four gen 37 fields, proved (gen 38's `vcpuNyp_rvmcs`,
  `vcpuNyp_rvmcb`, `vcpuNyp_dio`, gen 37's `readMsrJ`, with the backend / length errors of P3/JAtZV3VDecE2).
* **`JAtZV3.vcpuDecodeJ5`**, **`JAtZV3.vcpuInvJ5`**: the dispatcher and its syscall-level VCPU-cap arm, every
  label, scope `BufOut V buf`, the slot facts, `hct`, `lbl = EnableIOPort → IoFresh b c` and
  `lbl = EnableIOPort → EioScope Z.th ex p`.

Premises: [P] `ZvVirtAgree`, [P] `ZvSyncKeep`, [P] `∀ a, CapAgree arI a`, `P0.ArchTotal`, `ARKeep` (existing; the
same as `vcpuDecodeJ4`'s). **No VCPU [J]**: `VcpuNyp4` dropped. Scope added: `EioScope` (EnableIOPort only).
`IoFresh` kept (decision Q2). No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3VEio
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- **The EnableIOPort scope from the front end** (module docstring). -/
def EioScope (th : TypedHeap) (ex : Array obj.Slot 3#usize) (p : U64) : Prop :=
  Canonical p ∧ ∀ sl, Array.index_usize ex 0#usize = ok sl → obj.Slot.is_null sl = ok false →
    ∃ pc r idx, th pc = some (.cnode r) ∧ idx.length = r ∧ sl = cslotAddr (pc.bv, idx)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- `VLabelOK` with a scope that sees the typed heap, the extra-slot array and the VCPU (module docstring). -/
def VLabelOKS (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) (lbl : U64)
    (Sc : TypedHeap → Array obj.Slot 3#usize → U64 → Bool → capability.Cap → Prop) : Prop :=
  ARKeep arI AR → ZvSyncKeep arI AR → ZvVirtAgree arI → (∀ a', VirtSanEq.CapAgree arI a') → P0.ArchTotal arI →
  ∀ (V X : Set U64) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S)
    (a : A) (σ : Fl4Spec.State Unit) (p : U64) (vs : Fl4Spec.VcpuState) (len : U64) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap),
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ → p ∈ V → σ.kheap p.bv = some (.archObj (.vcpu vs)) →
    ExtraSlot st s ex b c → Sc Z.th ex p b c →
    vcpu.decode st arI s a lbl len p call buf ex ⦃ r =>
      VDecPostC (L := L) arI V X AR Z H Cs Ac Lst D s σ lbl len p call buf b c r ⦄

/-- **The EnableIOPort field, proved** (module docstring). -/
theorem vcpuOK_eio {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} :
    VLabelOKS (L := L) arI AR fl4_abi.label.X86VCPUEnableIOPort
      (fun th ex p b c => IoFresh b c ∧ EioScope th ex p) := by
  intro hK _ hVA _ _ V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX hS
  obtain ⟨hio, hcan, hsc⟩ := hS
  obtain ⟨sl, hsl, hbn, hc⟩ := hX
  by_cases hv : Fl4Spec.virtKind = .svm
  · exact WP.spec_mono (J.vdEioA hK hVA hv hp len call buf ex b c) fun r h => h.toC
  · by_cases hl : 2 ≤ len.val
    · exact J.enableIoPortJ hK hVA hv hp hcan hk hl call buf ex hsl hbn hc hio
        (fun hb => hsc sl hsl (by rw [← hb]; exact hbn))
    · exact WP.spec_mono (J.vdEioS hK hVA hv hp (by omega) call buf ex b c) fun r h => h.toC

theorem vOK_rvmcs {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} :
    VLabelOK (L := L) arI AR fl4_abi.label.X86VCPUReadVMCS fun _ _ => True := by
  intro hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX hS
  by_cases hv : Fl4Spec.virtKind = .svm
  · exact WP.spec_mono (J.vdRvmcsA hK hVA hv hp len call buf ex b c) fun r h => h.toC
  · by_cases hl : 1 ≤ len.val
    · exact vcpuNyp_rvmcs hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c hv hl J hp hk hX hS
    · exact WP.spec_mono (J.vdRvmcsS hK hVA hv hp (by omega) call buf ex b c) fun r h => h.toC

theorem vOK_rvmcb {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} :
    VLabelOK (L := L) arI AR fl4_abi.label.X86VCPUReadVMCB fun _ _ => True := by
  intro hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX hS
  by_cases hv : Fl4Spec.virtKind = .svm
  · by_cases hl : 2 ≤ len.val
    · exact vcpuNyp_rvmcb hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c hv hl J hp hk hX hS
    · exact WP.spec_mono (J.vdRvmcbS hK hVA hv hp (by omega) call buf ex b c) fun r h => h.toC
  · exact WP.spec_mono (J.vdRvmcbA hK hVA hv hp len call buf ex b c) fun r h => h.toC

theorem vOK_rmsr {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} :
    VLabelOK (L := L) arI AR fl4_abi.label.X86VCPUReadMSR fun _ _ => True := by
  intro hK _ hVA hCap _ V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk _ _
  by_cases hl : 1 ≤ len.val
  · exact WP.spec_mono (J.readMsrJ hK hVA hCap hp hk hl call buf ex b c) fun r h => h.toC
  · exact WP.spec_mono (J.vdRmsrS hK hVA hp (by omega) call buf ex b c) fun r h => h.toC

theorem vOK_dio {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} :
    VLabelOK (L := L) arI AR fl4_abi.label.X86VCPUDisableIOPort fun _ _ => True := by
  intro hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX hS
  by_cases hv : Fl4Spec.virtKind = .svm
  · exact WP.spec_mono (J.vdDioA hK hVA hv hp len call buf ex b c) fun r h => h.toC
  · by_cases hl : 2 ≤ len.val
    · exact vcpuNyp_dio hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c hv hl J hp hk hX hS
    · exact WP.spec_mono (J.vdDioS hK hVA hv hp (by omega) call buf ex b c) fun r h => h.toC

end

section
open Classical
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **The VCPU invocation dispatcher at `JAtZV3`, every label proved** (module docstring). -/
theorem JAtZV3.vcpuDecodeJ5 (hK : ARKeep arI AR) (hSy : ZvSyncKeep arI AR)
    (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a') (hAT : P0.ArchTotal arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (lbl len : U64) (call : Bool) {buf : U64}
    (hb : BufOut V buf) (ex : Array obj.Slot 3#usize) {sl : obj.Slot} {b : Bool}
    (hsl : Array.index_usize ex 0#usize = ok sl) (hbn : obj.Slot.is_null sl = ok b) {c : capability.Cap}
    (hc : b = false → obj.Slot.cap st sl s = ok c) (hct : ∀ t, c = .Thread t → Z.th t = some .tcb)
    (hIo : lbl = fl4_abi.label.X86VCPUEnableIOPort → IoFresh b c)
    (hEs : lbl = fl4_abi.label.X86VCPUEnableIOPort → EioScope Z.th ex p) :
    vcpu.decode st arI s a lbl len p call buf ex ⦃ r =>
      VDecPostC (L := L) arI V X AR Z H Cs Ac Lst D s σ lbl len p call buf b c r ⦄ := by
  have hX : ExtraSlot st s ex b c := ⟨sl, hsl, hbn, hc⟩
  have hvk : Fl4Spec.virtKind = .vmx ∨ Fl4Spec.virtKind = .svm := by
    have R := J.vr p hp vs hk
    revert R
    cases Fl4Spec.virtKind
    all_goals first
      | (intro _; exact Or.inl rfl)
      | (intro _; exact Or.inr rfl)
      | (intro R; exact R.elim)
  rcases hl : Fl4Spec.vcpuLabelOf lbl.bv with _ | l
  · exact WP.spec_mono (J.vdOther hK hVA hp hl len call buf ex b c) fun r h => h.toC
  · cases l
    case setTcb =>
      have e := zv_lbl_eqc hl rfl (n := 73) (c := fl4_abi.label.X86VCPUSetTCB) (by first | simp [fl4_abi.label.X86VCPUSetTCB] | (unfold fl4_abi.label.X86VCPUSetTCB; rfl))
      subst e
      exact WP.spec_mono (JAtZV3.vdStcb hAT hVA J hK hp len call buf ex hsl hbn hc hct) fun r h => h.toC
    case writeRegisters =>
      have e := zv_lbl_eqc hl rfl (n := 81) (c := fl4_abi.label.X86VCPUWriteRegisters)
        (by first | simp [fl4_abi.label.X86VCPUWriteRegisters] | (unfold fl4_abi.label.X86VCPUWriteRegisters; rfl))
      subst e
      by_cases h15 : 15 ≤ len.val
      · exact WP.spec_mono (J.vdWregs hK hAT hp hk h15 call hb ex b c) fun r h => h.toC
      · exact WP.spec_mono (J.vdWregsS hK hVA hp (by omega) call buf ex b c) fun r h => h.toC
    case flushTlb =>
      have e := zv_lbl_eqc hl rfl (n := 76) (c := fl4_abi.label.X86VCPUFlushTLB) (by first | simp [fl4_abi.label.X86VCPUFlushTLB] | (unfold fl4_abi.label.X86VCPUFlushTLB; rfl))
      subst e
      exact WP.spec_mono (J.vdFlush hK hVA hp len call buf ex b c) fun r h => h.toC
    case readVmcs =>
      have e := zv_lbl_eqc hl rfl (n := 74) (c := fl4_abi.label.X86VCPUReadVMCS) (by first | simp [fl4_abi.label.X86VCPUReadVMCS] | (unfold fl4_abi.label.X86VCPUReadVMCS; rfl))
      subst e
      exact vOK_rvmcs hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX trivial
    case writeVmcs =>
      have e := zv_lbl_eqc hl rfl (n := 75) (c := fl4_abi.label.X86VCPUWriteVMCS) (by first | simp [fl4_abi.label.X86VCPUWriteVMCS] | (unfold fl4_abi.label.X86VCPUWriteVMCS; rfl))
      subst e
      rcases hvk with hv | hv
      · by_cases h2 : 2 ≤ len.val
        · exact WP.spec_mono (J.vdWvmcs hK hSy hVA hCap hv hp hk h2 call buf ex b c) fun r h => h.toC
        · exact WP.spec_mono (J.vdWvmcsS hK hVA hv hp (by omega) call buf ex b c) fun r h => h.toC
      · exact WP.spec_mono (J.vdWvmcsA hK hVA hv hp len call buf ex b c) fun r h => h.toC
    case readVmcb =>
      have e := zv_lbl_eqc hl rfl (n := 77) (c := fl4_abi.label.X86VCPUReadVMCB) (by first | simp [fl4_abi.label.X86VCPUReadVMCB] | (unfold fl4_abi.label.X86VCPUReadVMCB; rfl))
      subst e
      exact vOK_rvmcb hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX trivial
    case writeVmcb =>
      have e := zv_lbl_eqc hl rfl (n := 78) (c := fl4_abi.label.X86VCPUWriteVMCB) (by first | simp [fl4_abi.label.X86VCPUWriteVMCB] | (unfold fl4_abi.label.X86VCPUWriteVMCB; rfl))
      subst e
      rcases hvk with hv | hv
      · exact WP.spec_mono (J.vdWvmcbA hK hVA (by rw [hv]; decide) hp len call buf ex b c) fun r h => h.toC
      · by_cases h2 : 2 ≤ len.val
        · exact WP.spec_mono (J.vdWvmcb hK hVA hCap hv hp hk h2 call buf ex b c) fun r h => h.toC
        · exact WP.spec_mono (J.vdWvmcbS hK hVA hv hp (by omega) call buf ex b c) fun r h => h.toC
    case enableIoPort =>
      have e := zv_lbl_eqc hl rfl (n := 79) (c := fl4_abi.label.X86VCPUEnableIOPort)
        (by first | simp [fl4_abi.label.X86VCPUEnableIOPort] | (unfold fl4_abi.label.X86VCPUEnableIOPort; rfl))
      subst e
      exact vcpuOK_eio hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX
        ⟨hIo rfl, hEs rfl⟩
    case disableIoPort =>
      have e := zv_lbl_eqc hl rfl (n := 80) (c := fl4_abi.label.X86VCPUDisableIOPort)
        (by first | simp [fl4_abi.label.X86VCPUDisableIOPort] | (unfold fl4_abi.label.X86VCPUDisableIOPort; rfl))
      subst e
      exact vOK_dio hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX
        trivial
    case readMsr =>
      have e := zv_lbl_eqc hl rfl (n := 49) (c := fl4_abi.label.X86VCPUReadMSR) (by first | simp [fl4_abi.label.X86VCPUReadMSR] | (unfold fl4_abi.label.X86VCPUReadMSR; rfl))
      subst e
      exact vOK_rmsr hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX trivial
    case writeMsr =>
      have e := zv_lbl_eqc hl rfl (n := 50) (c := fl4_abi.label.X86VCPUWriteMSR) (by first | simp [fl4_abi.label.X86VCPUWriteMSR] | (unfold fl4_abi.label.X86VCPUWriteMSR; rfl))
      subst e
      by_cases h2 : 2 ≤ len.val
      · exact WP.spec_mono (J.vdWmsr hAT hK hVA hCap hp hk h2 call buf ex b c) fun r h => h.toC
      · exact WP.spec_mono (J.vdWmsrS hK hVA hp (by omega) call buf ex b c) fun r h => h.toC


/-- **The VCPU-cap arm of the invocation step at `JAtZV3`, every label proved** (module docstring). -/
theorem JAtZV3.vcpuInvJ5 (hK : ARKeep arI AR) (hSy : ZvSyncKeep arI AR)
    (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a') (hAT : P0.ArchTotal arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (lbl len : U64) (slot : obj.Slot) (block call cd fp : Bool)
    {buf : U64} (hb : BufOut V buf) (ex : Array obj.Slot 3#usize) {sl : obj.Slot} {b : Bool}
    (hsl : Array.index_usize ex 0#usize = ok sl) (hbn : obj.Slot.is_null sl = ok b) {c : capability.Cap}
    (hc : b = false → obj.Slot.cap st sl s = ok c) (hct : ∀ t, c = .Thread t → Z.th t = some .tcb)
    (hIo : lbl = fl4_abi.label.X86VCPUEnableIOPort → IoFresh b c)
    (hEs : lbl = fl4_abi.label.X86VCPUEnableIOPort → EioScope Z.th ex p) :
    syscall.decode_invocation st arI s a lbl len slot (.Vcpu p) block call cd fp buf ex ⦃ r =>
      VInvPost (L := L) arI V X AR Z H Cs Ac Lst D s σ lbl len p call buf b c r ⦄ := by
  rw [zv_sysdec_vcpu]
  refine WP.spec_mono (J.vcpuDecodeJ5 hK hSy hVA hCap hAT hp hk lbl len call hb ex hsl hbn hc hct hIo hEs) ?_
  rintro r ⟨ct, hct', HH⟩
  refine ⟨ct, hct', fun args ec hA hC fp cref slot' buffer onCore remoteCur bl ca cd => ?_⟩
  rcases HH args ec hA hC with ⟨e, e', h1, h2, h3, h4, h5⟩ | ⟨inv, rep, s', σ', Ac', Lst', h1, h2, h3, h4, h5⟩
  · refine Or.inl ⟨e, e', h1, h2, ?_, h4, h5⟩
    rw [zv_decV_vcpu]
    exact run_liftME_err (h3.trans rfl)
  · refine Or.inr ⟨inv, rep, s', σ', Ac', Lst', h1, ?_, ?_, h4, h5⟩
    · rw [zv_decV_vcpu]
      exact run_liftME_ok (h2.trans rfl)
    · rw [zv_perfV_vcpu]
      exact run_liftE' h3

end

end

end Fl4Proofs.P3
