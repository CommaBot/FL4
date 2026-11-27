/-
P3 (line mmuAD, gen 37): **the VCPU dispatcher at `JAtZV3` with the open labels narrowed to their main paths** —
`P3/JAtZV3VDisp`'s `vcpuDecodeJ` and `P3/JAtZV3VInv`'s `vcpuInvJ` restated over **`VcpuNyp2`**, whose fields
leave out the backend and length errors proved in `P3/JAtZV3VDecE2`.

* **`VLabelOKN … lbl Sc Bk n`**: `VLabelOK` (`P3/JAtZV3VDisp`) only on the backend `Bk` and for `n ≤ len`.
* **`VcpuNyp2 arI AR`** — **[J] the X86VCPU paths not yet proved at `JAtZV3`** (replaces gen 37's `VcpuNyp` as
  the dispatcher's open premise; same claims, narrower):
  - `readVmcs`: ReadVMCS off SVM (i.e. VMX at a `JAtZV3` state with a VCPU), `len ≥ 1`;
  - `readVmcb`: ReadVMCB on SVM, `len ≥ 2`;
  - `readMsr`: ReadMSR, `len ≥ 1`;
  - `enableIoPort`: EnableIOPort off SVM, `len ≥ 2`, `IoFresh` (the extra I/O-port cap was never granted:
    without it the label is false as stated, `P3/JAtZV3VDisp`: FL4 revokes the range from the earlier owner VCPU,
    the spec's `ioPortRevoke` does nothing, decision Q2);
  - `disableIoPort`: DisableIOPort off SVM, `len ≥ 2`.
  What each claims and why it is not false on reachable states: `P3/JAtZV3VDisp`'s module docstring (FL4's arm
  and the spec's arm on the same words; `vmcb_hidden` = `Svm.hiddenRead`, the same eleven offsets).
* **`VcpuNyp2.toNyp`**: `VcpuNyp2` and the `JAtZV3VDecE2` errors give `VcpuNyp`.
* **`JAtZV3.vcpuDecodeJ2`**, **`JAtZV3.vcpuInvJ2`**: the dispatcher and its syscall-level VCPU-cap arm over
  `VcpuNyp2`.

Premises: **[J] `VcpuNyp2 arI AR`** (new, above); the platform premises and scope of `vcpuDecodeJ` unchanged.
No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3VDecE2
import Fl4Proofs.P3.JAtZV3VInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- `VLabelOK` on the backend `Bk` and for `n ≤ len` (module docstring). -/
def VLabelOKN (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) (lbl : U64)
    (Sc : Bool → capability.Cap → Prop) (Bk : Prop) (n : ℕ) : Prop :=
  ARKeep arI AR → ZvSyncKeep arI AR → ZvVirtAgree arI → (∀ a', VirtSanEq.CapAgree arI a') → P0.ArchTotal arI →
  ∀ (V X : Set U64) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S)
    (a : A) (σ : Fl4Spec.State Unit) (p : U64) (vs : Fl4Spec.VcpuState) (len : U64) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap),
    Bk → n ≤ len.val →
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ → p ∈ V → σ.kheap p.bv = some (.archObj (.vcpu vs)) →
    ExtraSlot st s ex b c → Sc b c →
    vcpu.decode st arI s a lbl len p call buf ex ⦃ r =>
      VDecPostC (L := L) arI V X AR Z H Cs Ac Lst D s σ lbl len p call buf b c r ⦄

/-- **[J] The X86VCPU paths not yet proved at `JAtZV3`** (module docstring). -/
structure VcpuNyp2 (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) : Prop where
  readVmcs : VLabelOKN (L := L) arI AR fl4_abi.label.X86VCPUReadVMCS (fun _ _ => True)
    (Fl4Spec.virtKind ≠ .svm) 1
  readVmcb : VLabelOKN (L := L) arI AR fl4_abi.label.X86VCPUReadVMCB (fun _ _ => True)
    (Fl4Spec.virtKind = .svm) 2
  readMsr : VLabelOKN (L := L) arI AR fl4_abi.label.X86VCPUReadMSR (fun _ _ => True) True 1
  enableIoPort : VLabelOKN (L := L) arI AR fl4_abi.label.X86VCPUEnableIOPort IoFresh (Fl4Spec.virtKind ≠ .svm) 2
  disableIoPort : VLabelOKN (L := L) arI AR fl4_abi.label.X86VCPUDisableIOPort (fun _ _ => True)
    (Fl4Spec.virtKind ≠ .svm) 2

/-- **`VcpuNyp2` gives `VcpuNyp`** (module docstring). -/
theorem VcpuNyp2.toNyp {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (N : VcpuNyp2 (L := L) arI AR) :
    VcpuNyp (L := L) arI AR where
  readVmcs := by
    intro hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX hS
    by_cases hv : Fl4Spec.virtKind = .svm
    · exact WP.spec_mono (J.vdRvmcsA hK hVA hv hp len call buf ex b c) fun r h => h.toC
    · by_cases hl : 1 ≤ len.val
      · exact N.readVmcs hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c hv hl J hp hk hX hS
      · exact WP.spec_mono (J.vdRvmcsS hK hVA hv hp (by omega) call buf ex b c) fun r h => h.toC
  readVmcb := by
    intro hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX hS
    by_cases hv : Fl4Spec.virtKind = .svm
    · by_cases hl : 2 ≤ len.val
      · exact N.readVmcb hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c hv hl J hp hk hX hS
      · exact WP.spec_mono (J.vdRvmcbS hK hVA hv hp (by omega) call buf ex b c) fun r h => h.toC
    · exact WP.spec_mono (J.vdRvmcbA hK hVA hv hp len call buf ex b c) fun r h => h.toC
  readMsr := by
    intro hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX hS
    by_cases hl : 1 ≤ len.val
    · exact N.readMsr hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c trivial hl J hp hk hX hS
    · exact WP.spec_mono (J.vdRmsrS hK hVA hp (by omega) call buf ex b c) fun r h => h.toC
  enableIoPort := by
    intro hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX hS
    by_cases hv : Fl4Spec.virtKind = .svm
    · exact WP.spec_mono (J.vdEioA hK hVA hv hp len call buf ex b c) fun r h => h.toC
    · by_cases hl : 2 ≤ len.val
      · exact N.enableIoPort hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c hv hl J hp hk hX
          hS
      · exact WP.spec_mono (J.vdEioS hK hVA hv hp (by omega) call buf ex b c) fun r h => h.toC
  disableIoPort := by
    intro hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX hS
    by_cases hv : Fl4Spec.virtKind = .svm
    · exact WP.spec_mono (J.vdDioA hK hVA hv hp len call buf ex b c) fun r h => h.toC
    · by_cases hl : 2 ≤ len.val
      · exact N.disableIoPort hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c hv hl J hp hk
          hX hS
      · exact WP.spec_mono (J.vdDioS hK hVA hv hp (by omega) call buf ex b c) fun r h => h.toC

end

section
open Classical
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **The VCPU invocation dispatcher at `JAtZV3`, over `VcpuNyp2`** (module docstring). -/
theorem JAtZV3.vcpuDecodeJ2 (N : VcpuNyp2 (L := L) arI AR) (hK : ARKeep arI AR) (hSy : ZvSyncKeep arI AR)
    (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a') (hAT : P0.ArchTotal arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (lbl len : U64) (call : Bool) {buf : U64}
    (hb : BufOut V buf) (ex : Array obj.Slot 3#usize) {sl : obj.Slot} {b : Bool}
    (hsl : Array.index_usize ex 0#usize = ok sl) (hbn : obj.Slot.is_null sl = ok b) {c : capability.Cap}
    (hc : b = false → obj.Slot.cap st sl s = ok c) (hct : ∀ t, c = .Thread t → Z.th t = some .tcb)
    (hIo : lbl = fl4_abi.label.X86VCPUEnableIOPort → IoFresh b c) :
    vcpu.decode st arI s a lbl len p call buf ex ⦃ r =>
      VDecPostC (L := L) arI V X AR Z H Cs Ac Lst D s σ lbl len p call buf b c r ⦄ :=
  J.vcpuDecodeJ N.toNyp hK hSy hVA hCap hAT hp hk lbl len call hb ex hsl hbn hc hct hIo

/-- **The VCPU-cap arm of the invocation step at `JAtZV3`, over `VcpuNyp2`** (module docstring). -/
theorem JAtZV3.vcpuInvJ2 (N : VcpuNyp2 (L := L) arI AR) (hK : ARKeep arI AR) (hSy : ZvSyncKeep arI AR)
    (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a') (hAT : P0.ArchTotal arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (lbl len : U64) (slot : obj.Slot) (block call cd fp : Bool)
    {buf : U64} (hb : BufOut V buf) (ex : Array obj.Slot 3#usize) {sl : obj.Slot} {b : Bool}
    (hsl : Array.index_usize ex 0#usize = ok sl) (hbn : obj.Slot.is_null sl = ok b) {c : capability.Cap}
    (hc : b = false → obj.Slot.cap st sl s = ok c) (hct : ∀ t, c = .Thread t → Z.th t = some .tcb)
    (hIo : lbl = fl4_abi.label.X86VCPUEnableIOPort → IoFresh b c) :
    syscall.decode_invocation st arI s a lbl len slot (.Vcpu p) block call cd fp buf ex ⦃ r =>
      VInvPost (L := L) arI V X AR Z H Cs Ac Lst D s σ lbl len p call buf b c r ⦄ :=
  J.vcpuInvJ N.toNyp hK hSy hVA hCap hAT hp hk lbl len slot block call cd fp hb ex hsl hbn hc hct hIo

end

end

end Fl4Proofs.P3
