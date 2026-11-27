/-
P3 (line mmuAD, gen 37): **the VCPU dispatcher at `JAtZV3` with ReadMSR proved** — `P3/JAtZV3VDisp2`'s
`vcpuDecodeJ2` / `vcpuInvJ2` restated over **`VcpuNyp3`** = `VcpuNyp2` without its `readMsr` field, which is now
`P3/JAtZV3VRmsr`'s `JAtZV3.readMsrJ`.

* **`VcpuNyp3 arI AR`** — **[J] the X86VCPU paths not yet proved at `JAtZV3`**: `readVmcs` (VMX, `len ≥ 1`),
  `readVmcb` (SVM, `len ≥ 2`), `enableIoPort` (VMX, `len ≥ 2`, `IoFresh`), `disableIoPort` (VMX, `len ≥ 2`);
  claims, narrowing and the not-false argument as in `P3/JAtZV3VDisp` / `P3/JAtZV3VDisp2`.
* **`VcpuNyp3.toNyp2`**; **`JAtZV3.vcpuDecodeJ3`**, **`JAtZV3.vcpuInvJ3`**: the dispatcher and its syscall-level
  VCPU-cap arm over `VcpuNyp3`.

Premises: **[J] `VcpuNyp3 arI AR`** (new, replaces `VcpuNyp2` as the open premise); the platform premises and scope
of `vcpuDecodeJ` unchanged. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3VRmsr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **[J] The X86VCPU paths not yet proved at `JAtZV3`** (module docstring). -/
structure VcpuNyp3 (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) : Prop where
  readVmcs : VLabelOKN (L := L) arI AR fl4_abi.label.X86VCPUReadVMCS (fun _ _ => True)
    (Fl4Spec.virtKind ≠ .svm) 1
  readVmcb : VLabelOKN (L := L) arI AR fl4_abi.label.X86VCPUReadVMCB (fun _ _ => True)
    (Fl4Spec.virtKind = .svm) 2
  enableIoPort : VLabelOKN (L := L) arI AR fl4_abi.label.X86VCPUEnableIOPort IoFresh (Fl4Spec.virtKind ≠ .svm) 2
  disableIoPort : VLabelOKN (L := L) arI AR fl4_abi.label.X86VCPUDisableIOPort (fun _ _ => True)
    (Fl4Spec.virtKind ≠ .svm) 2

theorem VcpuNyp3.toNyp2 {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (N : VcpuNyp3 (L := L) arI AR) :
    VcpuNyp2 (L := L) arI AR where
  readVmcs := N.readVmcs
  readVmcb := N.readVmcb
  readMsr := by
    intro hK _ hVA hCap _ V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c _ hl J hp hk _ _
    exact WP.spec_mono (J.readMsrJ hK hVA hCap hp hk hl call buf ex b c) fun r h => h.toC
  enableIoPort := N.enableIoPort
  disableIoPort := N.disableIoPort

end

section
open Classical
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **The VCPU invocation dispatcher at `JAtZV3`, over `VcpuNyp3`** (module docstring). -/
theorem JAtZV3.vcpuDecodeJ3 (N : VcpuNyp3 (L := L) arI AR) (hK : ARKeep arI AR) (hSy : ZvSyncKeep arI AR)
    (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a') (hAT : P0.ArchTotal arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (lbl len : U64) (call : Bool) {buf : U64}
    (hb : BufOut V buf) (ex : Array obj.Slot 3#usize) {sl : obj.Slot} {b : Bool}
    (hsl : Array.index_usize ex 0#usize = ok sl) (hbn : obj.Slot.is_null sl = ok b) {c : capability.Cap}
    (hc : b = false → obj.Slot.cap st sl s = ok c) (hct : ∀ t, c = .Thread t → Z.th t = some .tcb)
    (hIo : lbl = fl4_abi.label.X86VCPUEnableIOPort → IoFresh b c) :
    vcpu.decode st arI s a lbl len p call buf ex ⦃ r =>
      VDecPostC (L := L) arI V X AR Z H Cs Ac Lst D s σ lbl len p call buf b c r ⦄ :=
  J.vcpuDecodeJ2 N.toNyp2 hK hSy hVA hCap hAT hp hk lbl len call hb ex hsl hbn hc hct hIo

/-- **The VCPU-cap arm of the invocation step at `JAtZV3`, over `VcpuNyp3`** (module docstring). -/
theorem JAtZV3.vcpuInvJ3 (N : VcpuNyp3 (L := L) arI AR) (hK : ARKeep arI AR) (hSy : ZvSyncKeep arI AR)
    (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a') (hAT : P0.ArchTotal arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (lbl len : U64) (slot : obj.Slot) (block call cd fp : Bool)
    {buf : U64} (hb : BufOut V buf) (ex : Array obj.Slot 3#usize) {sl : obj.Slot} {b : Bool}
    (hsl : Array.index_usize ex 0#usize = ok sl) (hbn : obj.Slot.is_null sl = ok b) {c : capability.Cap}
    (hc : b = false → obj.Slot.cap st sl s = ok c) (hct : ∀ t, c = .Thread t → Z.th t = some .tcb)
    (hIo : lbl = fl4_abi.label.X86VCPUEnableIOPort → IoFresh b c) :
    syscall.decode_invocation st arI s a lbl len slot (.Vcpu p) block call cd fp buf ex ⦃ r =>
      VInvPost (L := L) arI V X AR Z H Cs Ac Lst D s σ lbl len p call buf b c r ⦄ :=
  J.vcpuInvJ2 N.toNyp2 hK hSy hVA hCap hAT hp hk lbl len slot block call cd fp hb ex hsl hbn hc hct hIo

end

end

end Fl4Proofs.P3
