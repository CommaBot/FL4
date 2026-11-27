/-
P3 (line mmuAD, gen 38): **the VCPU dispatcher at `JAtZV3` with DisableIOPort, ReadVMCS and ReadVMCB proved** —
`P3/JAtZV3VDisp3`'s `vcpuDecodeJ3` / `vcpuInvJ3` restated over **`VcpuNyp4`** = `VcpuNyp3` without its
`disableIoPort` (`P3/JAtZV3VDio`'s `vcpuNyp_dio`), `readVmcs` (`P3/JAtZV3VRvmcs`'s `vcpuNyp_rvmcs`) and
`readVmcb` (`P3/JAtZV3VRvmcb`'s `vcpuNyp_rvmcb`) fields.

* **`VcpuNyp4 arI AR`** — **[J] the one X86VCPU path not proved at `JAtZV3`**: `enableIoPort` (VMX, `len ≥ 2`,
  `IoFresh`), `VcpuNyp3.enableIoPort` verbatim (same claim, same narrowing).
  **Found false as stated (gen 38), for every generation's form of this field (`VcpuNyp`, `VcpuNyp2`, `VcpuNyp3`,
  `VcpuNyp4`):** `VLabelOKN` quantifies over every `ex`, and `obj.Slot` is a bare address (`Types.lean`:
  `def obj.Slot := Std.U64`), so `ExtraSlot` does not make `ex[0]` a CNode slot. Counterexample shape: a VMX `JAtZV3`
  state, `p ∈ V`, `ex[0]` = an address inside `p`'s own I/O bitmap (`p + IO + 8 k`, aligned) whose two words decode
  as `IoPort first last 0` (word 0 = the tag 21 in bits 63:59, word 1 = `first | last << 16`; the VMM can put that
  pattern there with Enable/DisableIOPort ranges), and arguments `lo..hi ⊆ first..last` lying in another bitmap word.
  FL4 (vcpu.rs l. 1007-1058; `set_cap` l. 1046, `Slot::is_null` is `addr == 0`, obj.rs l. 297) walks the VCPU list (no effect, `prior = 0`), then `ex[0].set_cap(IoPort first last
  v)` rewrites word 0 to `tag | pack(v)`, flipping bits of bitmap word `k` of `p`, then `ports(v, lo, hi, false)`;
  the spec's `performVcpuInvocationF (.enableIoPort …)` changes `ioDenied` only on `lo..hi`. So `VcpuRelVmx.io`
  fails at `p` for a port of word `k`, and no `σ'` satisfies `JAtZV3`. Unreachable from FL4's front end (its
  `ex[0]` comes from the extra-cap lookup, a CNode slot), so the field needs the front end's slot fact as scope
  (e.g. `IsSlot Z.th ex[0]`), not a change of the code. Not narrowed here (owner/next-generation decision); with
  that scope the remaining work is the slot rewrite `set_cap` (abstract cap unchanged: `absCap` ignores the owner,
  `JExtV.cap`'s `VtxCap (.IoPort _ _ o)` needs `o ∈ V`, true for `v = p`).
* **`VcpuNyp4.toNyp3`**: `VcpuNyp4` and the three gen 38 theorems give `VcpuNyp3`.
* **`JAtZV3.vcpuDecodeJ4`**, **`JAtZV3.vcpuInvJ4`**: the dispatcher and its syscall-level VCPU-cap arm over
  `VcpuNyp4`.

Premises: **[J] `VcpuNyp4 arI AR`** (new, replaces `VcpuNyp3` as the open premise; found false as stated, above);
the platform premises and scope of `vcpuDecodeJ` unchanged. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3VRvmcb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **[J] The one X86VCPU path not proved at `JAtZV3`** (module docstring; found false as stated for an `ex[0]`
that is no CNode slot). -/
structure VcpuNyp4 (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop) : Prop where
  enableIoPort : VLabelOKN (L := L) arI AR fl4_abi.label.X86VCPUEnableIOPort IoFresh (Fl4Spec.virtKind ≠ .svm) 2

theorem VcpuNyp4.toNyp3 {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} (N : VcpuNyp4 (L := L) arI AR) :
    VcpuNyp3 (L := L) arI AR where
  readVmcs := vcpuNyp_rvmcs
  readVmcb := vcpuNyp_rvmcb
  enableIoPort := N.enableIoPort
  disableIoPort := vcpuNyp_dio

end

section
open Classical
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **The VCPU invocation dispatcher at `JAtZV3`, over `VcpuNyp4`** (module docstring). -/
theorem JAtZV3.vcpuDecodeJ4 (N : VcpuNyp4 (L := L) arI AR) (hK : ARKeep arI AR) (hSy : ZvSyncKeep arI AR)
    (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a') (hAT : P0.ArchTotal arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (lbl len : U64) (call : Bool) {buf : U64}
    (hb : BufOut V buf) (ex : Array obj.Slot 3#usize) {sl : obj.Slot} {b : Bool}
    (hsl : Array.index_usize ex 0#usize = ok sl) (hbn : obj.Slot.is_null sl = ok b) {c : capability.Cap}
    (hc : b = false → obj.Slot.cap st sl s = ok c) (hct : ∀ t, c = .Thread t → Z.th t = some .tcb)
    (hIo : lbl = fl4_abi.label.X86VCPUEnableIOPort → IoFresh b c) :
    vcpu.decode st arI s a lbl len p call buf ex ⦃ r =>
      VDecPostC (L := L) arI V X AR Z H Cs Ac Lst D s σ lbl len p call buf b c r ⦄ :=
  J.vcpuDecodeJ3 N.toNyp3 hK hSy hVA hCap hAT hp hk lbl len call hb ex hsl hbn hc hct hIo

/-- **The VCPU-cap arm of the invocation step at `JAtZV3`, over `VcpuNyp4`** (module docstring). -/
theorem JAtZV3.vcpuInvJ4 (N : VcpuNyp4 (L := L) arI AR) (hK : ARKeep arI AR) (hSy : ZvSyncKeep arI AR)
    (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a') (hAT : P0.ArchTotal arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (lbl len : U64) (slot : obj.Slot) (block call cd fp : Bool)
    {buf : U64} (hb : BufOut V buf) (ex : Array obj.Slot 3#usize) {sl : obj.Slot} {b : Bool}
    (hsl : Array.index_usize ex 0#usize = ok sl) (hbn : obj.Slot.is_null sl = ok b) {c : capability.Cap}
    (hc : b = false → obj.Slot.cap st sl s = ok c) (hct : ∀ t, c = .Thread t → Z.th t = some .tcb)
    (hIo : lbl = fl4_abi.label.X86VCPUEnableIOPort → IoFresh b c) :
    syscall.decode_invocation st arI s a lbl len slot (.Vcpu p) block call cd fp buf ex ⦃ r =>
      VInvPost (L := L) arI V X AR Z H Cs Ac Lst D s σ lbl len p call buf b c r ⦄ :=
  J.vcpuInvJ3 N.toNyp3 hK hSy hVA hCap hAT hp hk lbl len slot block call cd fp hb ex hsl hbn hc hct hIo

end

end

end Fl4Proofs.P3
