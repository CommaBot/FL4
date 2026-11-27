/-
P3 (line mmuAD, gen 37): **the VCPU invocation dispatcher at `JAtZV3`** — one theorem for FL4's whole extracted
`vcpu.decode` (vcpu.rs l. 822-1064, every label), paired with the extended spec's `decodeVcpuInvocation` and FL4's
perform `performVcpuInvocationF` (Ext/VirtKernelF), in the post `VDecPostC` (= gen 37's `VDecPost`,
`P3/JAtZV3VDec`, with the front end's full extra-cap agreement `VCaps`).

* **`VCaps b c ec`**: FL4's first extra-cap slot (null flag `b`, cap `c`) against the spec's extra caps: none ↔
  `[]`, otherwise the spec's first extra cap is `absCap c` (the cap abstraction of `P3/CapRel`). **`VCaps.stcb`**:
  it implies gen 35's `StcbCaps` (`absCap` of a non-thread cap is no `threadCap`), so **`VDecPost.toC`**.
* **`VLabelOK … lbl Sc`**: the statement the dispatcher proves for one label, for every `JAtZV3` state, VCPU
  `p ∈ V` of the spec heap, FL4 extra-cap slot `ex[0]` with null flag `b` / cap `c` (`ExtraSlot`) inside the scope
  `Sc b c`, under the platform premises.
* **`VcpuNyp arI AR`** — **[J] the X86VCPU labels not yet proved at `JAtZV3`**, one field per label, each a
  `VLabelOK`:
  - `readVmcs` (X86VCPUReadVMCS; VMX: `READ_FIELDS` ↔ `Vmx.readable`, `vcpu_sync`, the `supported` capability
    test ↔ `Vmx.readSupported` under `CapAgree`, `read_vmcs` ↔ the `vmcs` relation, tail (b); SVM / `len < 1`:
    illegal);
  - `readVmcb` (X86VCPUReadVMCB; SVM: the four `invalid_arg` checks ↔ the spec's, the words `vmcb_hidden` ↔
    `Svm.hiddenRead` (the same eleven offsets 0x040 0x048 0x058 0x098 0x0a0 0x0b0 0x0c0 0x0e0 0x0f0 0x0f8 0x108),
    RAX from `REGS`, tail (c); VMX: illegal; `len < 2`: truncated);
  - `readMsr` (X86VCPUReadMSR; `len < 1` illegal, VMX_MISC 0x485 ↔ `.readVmxMisc`, `msr_addr` none ↔ `∉ vcpuMsrs`,
    the read ↔ the `msr` relation, tail (b));
  - `enableIoPort` (X86VCPUEnableIOPort) **narrowed by `IoFresh b c`**: the extra cap, when an I/O-port cap, has
    owner word 0 (no earlier grant). Without it the label is **false as stated**: FL4's `decode_loop4` revokes the
    cap's range from the earlier owner VCPU `prior` (`vcpu.ports prior first last true`), while the spec's
    `ioPortRevoke` does nothing (`ioPortOwner = none`, decision Q2, VIRT-PLAN.md §3.3.1) — a VMX state with
    `prior ∈ V` in the VCPU list and a port of the range allowed there breaks `VcpuRelVmx.io` at `prior`;
  - `disableIoPort` (X86VCPUDisableIOPort; VMX: `vcpu.ports v lo hi true` ↔ `setPorts lo hi true`, tail (a); SVM:
    illegal; `len < 2`: truncated).
  Not false on reachable states (checked against FL4's text and the spec, as above): every field is FL4's arm and
  the spec's arm doing the same thing on the same words; the EnableIOPort difference is excluded by `IoFresh`.
* **`JAtZV3.vcpuDecodeJ`**: for every label `lbl`, `vcpu.decode … lbl len p call buf ex` from `JAtZV3` satisfies
  `VDecPostC`. Proved labels: SetTCB (`vdStcb`), WriteRegisters (`vdWregs` / `vdWregsS`), FlushTLB (`vdFlush`),
  WriteVMCS (`vdWvmcs` / `vdWvmcsS` / `vdWvmcsA`), WriteVMCB (`vdWvmcb` / `vdWvmcbS` / `vdWvmcbA`), WriteMSR
  (`vdWmsr` / `vdWmsrS`), every non-VCPU label (`vdOther`); the five others from `VcpuNyp`.

Premises: **[J] `VcpuNyp arI AR`** (new, above); [P] `ZvVirtAgree`, [P] `ZvSyncKeep`, [P] `∀ a, CapAgree arI a`,
`P0.ArchTotal`, `ARKeep` (existing). Scope: `BufOut V buf` (WriteRegisters, as `writeRegsJ`), the slot facts and
`hct` (SetTCB, as `setTcbJ`), `lbl = EnableIOPort → IoFresh b c`. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3VDecE
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- FL4's first extra-cap slot against the spec's extra caps (module docstring). -/
def VCaps (b : Bool) (c : capability.Cap) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) : Prop :=
  (b = true → ec = []) ∧ (b = false → ∃ cp rest, ec = (absCap c, cp) :: rest)

theorem VCaps.stcb {b : Bool} {c : capability.Cap} {ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    (h : VCaps b c ec) : StcbCaps b c ec := by
  refine ⟨h.1, fun hb => ?_⟩
  obtain ⟨cp, rest, e⟩ := h.2 hb
  refine ⟨absCap c, cp, rest, e, ?_⟩
  cases c
  case Thread t => exact Or.inl ⟨t, rfl, rfl⟩
  all_goals exact Or.inr ⟨(fun t e => by first | cases e | exact capability.Cap.noConfusion e | simp at e), (fun t e => by simp [absCap] at e)⟩

/-- An I/O-port extra cap without an earlier grant (module docstring). -/
def IoFresh (b : Bool) (c : capability.Cap) : Prop :=
  b = false → ∀ f l q, c = .IoPort f l q → q = 0#u64

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- FL4's first extra-cap slot: its null flag `b` and, when not null, its cap `c`. -/
def ExtraSlot (st : machine.Store S) (s : S) (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap) : Prop :=
  ∃ sl, Array.index_usize ex 0#usize = ok sl ∧ obj.Slot.is_null sl = ok b ∧ (b = false → obj.Slot.cap st sl s = ok c)

/-- `VDecPost` with the full extra-cap agreement `VCaps` (module docstring). -/
def VDecPostC (arI : machine.Arch A) (V X : Set U64) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap)
    (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (σ : Fl4Spec.State Unit)
    (lbl len p : U64) (call : Bool) (buf : U64) (b : Bool) (c : capability.Cap)
    (r : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ ct : U64, sched.cur_thread st s = ok ct ∧
    ∀ (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), VArgs st s ct buf len args →
      VCaps b c ec →
      (∃ e e', r.1 = .Err e ∧ SysErrRel e e' ∧
        ExceptT.run (Fl4Spec.decodeVcpuInvocation (Z := Unit) lbl.bv args p.bv ec) σ =
          ExceptT.run (Fl4Spec.NonDetE.throwError (σ := Fl4Spec.State Unit) (α := Fl4Spec.VcpuInvocation) e') σ ∧
        r.2.1 = s ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s r.2.2 σ) ∨
      (∃ (inv : Fl4Spec.VcpuInvocation) (rep : List Fl4Spec.Data) (s' : S) (σ' : Fl4Spec.State Unit)
          (Ac' : Set U64) (Lst' : U64 → List U64), r.1 = .Ok () ∧
        ExceptT.run (Fl4Spec.decodeVcpuInvocation (Z := Unit) lbl.bv args p.bv ec) σ =
          ExceptT.run (Fl4Spec.NonDetE.returnOk (σ := Fl4Spec.State Unit) (ε := Fl4Spec.SyscallError) inv) σ ∧
        Fl4Spec.performVcpuInvocationF (Z := Unit) inv σ = ({(rep, σ')}, False) ∧
        JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D s' r.2.2 σ' ∧ VDecTail st ct call rep s' r.2.1)

theorem VDecPost.toC {arI : machine.Arch A} {V X : Set U64} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets}
    {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {σ : Fl4Spec.State Unit}
    {lbl len p : U64} {call : Bool} {buf : U64} {b : Bool} {c : capability.Cap}
    {r : core.result.Result Unit error.Exc × S × A}
    (h : VDecPost (L := L) arI V X AR Z H Cs Ac Lst D s σ lbl len p call buf b c r) :
    VDecPostC (L := L) arI V X AR Z H Cs Ac Lst D s σ lbl len p call buf b c r := by
  obtain ⟨ct, hct, HH⟩ := h
  exact ⟨ct, hct, fun args ec hA hC => HH args ec hA hC.stcb⟩

/-- The statement the dispatcher proves for one label (module docstring). -/
def VLabelOK (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) (lbl : U64)
    (Sc : Bool → capability.Cap → Prop) : Prop :=
  ARKeep arI AR → ZvSyncKeep arI AR → ZvVirtAgree arI → (∀ a', VirtSanEq.CapAgree arI a') → P0.ArchTotal arI →
  ∀ (V X : Set U64) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S)
    (a : A) (σ : Fl4Spec.State Unit) (p : U64) (vs : Fl4Spec.VcpuState) (len : U64) (call : Bool) (buf : U64)
    (ex : Array obj.Slot 3#usize) (b : Bool) (c : capability.Cap),
    JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ → p ∈ V → σ.kheap p.bv = some (.archObj (.vcpu vs)) →
    ExtraSlot st s ex b c → Sc b c →
    vcpu.decode st arI s a lbl len p call buf ex ⦃ r =>
      VDecPostC (L := L) arI V X AR Z H Cs Ac Lst D s σ lbl len p call buf b c r ⦄

/-- **[J] The X86VCPU labels not yet proved at `JAtZV3`** (module docstring: what each field claims, why it is
not false on reachable states, and why `enableIoPort` is narrowed by `IoFresh`). -/
structure VcpuNyp (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) : Prop where
  readVmcs : VLabelOK (L := L) arI AR fl4_abi.label.X86VCPUReadVMCS fun _ _ => True
  readVmcb : VLabelOK (L := L) arI AR fl4_abi.label.X86VCPUReadVMCB fun _ _ => True
  readMsr : VLabelOK (L := L) arI AR fl4_abi.label.X86VCPUReadMSR fun _ _ => True
  enableIoPort : VLabelOK (L := L) arI AR fl4_abi.label.X86VCPUEnableIOPort IoFresh
  disableIoPort : VLabelOK (L := L) arI AR fl4_abi.label.X86VCPUDisableIOPort fun _ _ => True

end

/-- A VCPU label of `lbl` names FL4's label constant. -/
theorem zv_lbl_eqc {lbl c : U64} {n : ℕ} {l : Fl4Spec.VcpuLabel} (h : Fl4Spec.vcpuLabelOf lbl.bv = some l)
    (hn : l.num = n) (hc : c.val = n) : lbl = c := by
  unfold Fl4Spec.vcpuLabelOf at h
  have h0 := List.find?_some h
  have h1 : Fl4Spec.dataToNat lbl.bv = l.num := of_decide_eq_true h0
  apply UScalar.eq_of_val_eq
  rw [hc, ← hn, ← h1]
  rfl

section
open Classical
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **The VCPU invocation dispatcher at `JAtZV3`** (module docstring). -/
theorem JAtZV3.vcpuDecodeJ (N : VcpuNyp (L := L) arI AR) (hK : ARKeep arI AR) (hSy : ZvSyncKeep arI AR)
    (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a') (hAT : P0.ArchTotal arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (lbl len : U64) (call : Bool) {buf : U64}
    (hb : BufOut V buf) (ex : Array obj.Slot 3#usize) {sl : obj.Slot} {b : Bool}
    (hsl : Array.index_usize ex 0#usize = ok sl) (hbn : obj.Slot.is_null sl = ok b) {c : capability.Cap}
    (hc : b = false → obj.Slot.cap st sl s = ok c) (hct : ∀ t, c = .Thread t → Z.th t = some .tcb)
    (hIo : lbl = fl4_abi.label.X86VCPUEnableIOPort → IoFresh b c) :
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
      exact N.readVmcs hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX trivial
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
      exact N.readVmcb hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX trivial
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
      exact N.enableIoPort hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX
        (hIo rfl)
    case disableIoPort =>
      have e := zv_lbl_eqc hl rfl (n := 80) (c := fl4_abi.label.X86VCPUDisableIOPort)
        (by first | simp [fl4_abi.label.X86VCPUDisableIOPort] | (unfold fl4_abi.label.X86VCPUDisableIOPort; rfl))
      subst e
      exact N.disableIoPort hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX
        trivial
    case readMsr =>
      have e := zv_lbl_eqc hl rfl (n := 49) (c := fl4_abi.label.X86VCPUReadMSR) (by first | simp [fl4_abi.label.X86VCPUReadMSR] | (unfold fl4_abi.label.X86VCPUReadMSR; rfl))
      subst e
      exact N.readMsr hK hSy hVA hCap hAT V X Z H Cs Ac Lst D s a σ p vs len call buf ex b c J hp hk hX trivial
    case writeMsr =>
      have e := zv_lbl_eqc hl rfl (n := 50) (c := fl4_abi.label.X86VCPUWriteMSR) (by first | simp [fl4_abi.label.X86VCPUWriteMSR] | (unfold fl4_abi.label.X86VCPUWriteMSR; rfl))
      subst e
      by_cases h2 : 2 ≤ len.val
      · exact WP.spec_mono (J.vdWmsr hAT hK hVA hCap hp hk h2 call buf ex b c) fun r h => h.toC
      · exact WP.spec_mono (J.vdWmsrS hK hVA hp (by omega) call buf ex b c) fun r h => h.toC

end

end

end Fl4Proofs.P3
