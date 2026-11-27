/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization, the VMX VCPU relation** `VcpuRelVmx`
(proofs/VIRT-PLAN.md §11.1, R0).

`VcpuRelVmx mem v vs`: the abstract VCPU `vs` is FL4's image at `v` on a VMX backend (`Ext/VirtRelBase` for the
shared part). VMX-specific places (FL4 `crates/fl4-core/src/vcpu.rs`):
* a VMCS field `f` of FL4's tables (`Vmx.writable f ∨ Vmx.readable f`, the 86 fields) at `vmcs_addr v f =
  v + SHADOW + 8 · idx f` with `idx f = ((f & 0xff) >> 1) | (((f >> 10) & 3) << 7) | (((f >> 13) & 3) << 9)`
  (`vmcsIdx`, verbatim);
* the syscall MSRs STAR, LSTAR, CSTAR, FMASK, KERNEL_GS_BASE at `MSRS + 8 · msr_slot m` (`msrSlot`, verbatim),
  CR2 (pseudo-MSR `0xffff_ffff`) at `CR2` (FL4 `vcpu::msr_addr` with `amd = false`);
* the I/O bitmap: port `p` is denied iff bit `p & 63` of the word `IO + 8 · (p >> 6)` is set (FL4 `vcpu::ports`).

Isabelle counterpart: l4v `proof/refine/ARM_HYP/StateRelation.thy` `vcpu_relation` (field-wise agreement of the
abstract and concrete VCPU). The ported modules are not changed.
-/
import Fl4Spec.Ext.VirtRelBase

namespace Fl4Spec

noncomputable section
open Classical

/-- FL4 `vcpu::vmcs_addr`'s index of a VMCS encoding (VIRT-PLAN §11.1 `idx f`): bits 7:1, type 11:10, width
14:13 of the encoding packed into 11 bits. -/
def vmcsIdx (f : Word) : Word :=
  ((f &&& 0xff) >>> 1) ||| (((f >>> 10) &&& 3) <<< 7) ||| (((f >>> 13) &&& 3) <<< 9)

/-- The offset of VMCS field `f` in the image: `SHADOW + 8 · idx f` (FL4 `vcpu::vmcs_addr v f =
v.wrapping_add(SHADOW).wrapping_add(i * 8)`, i.e. `v + vmcsOff f`). -/
def vmcsOff (f : Word) : Word := VcpuLay.SHADOW + vmcsIdx f * 8

/-- FL4 `vcpu::msr_slot`: the MSR-area slot of a syscall MSR on VMX. -/
def msrSlot (m : Word) : Option Word :=
  if m = msrStar then some 0
  else if m = msrLstar then some 1
  else if m = msrCstar then some 2
  else if m = msrFmask then some 3
  else if m = msrKernelGsBase then some 4
  else none

/-- FL4 `vcpu::ports`' bit of port `p` in its bitmap word (`1 << (port & 63)`). -/
def vcpuIoBit (p : BitVec 16) : Word := 1 <<< (p.toNat % 64)

/-- FL4 `vcpu::ports`' word of port `p`: `IO + 8 · (p >> 6)`. -/
def vcpuIoOff (p : BitVec 16) : Word := VcpuLay.IO + BitVec.ofNat 64 (p.toNat / 64) * 8

/-- **The VMX VCPU relation** (module docstring; VIRT-PLAN §11.1 `VcpuRelVmx mem v vs`; l4v ARM_HYP
`vcpu_relation`). On VMX every field is its own canonical place (`VField.canon .vmx f = f`). -/
structure VcpuRelVmx (mem : Word → Word) (v : Word) (vs : VcpuState) : Prop extends VcpuRelCommon mem v vs where
  vmcs : ∀ f, (Vmx.writable f = true ∨ Vmx.readable f = true) → vs.fields (.vmcs f) = mem (v + vmcsOff f)
  msr : ∀ m i, msrSlot m = some i → vs.fields (.msr m) = mem (v + (VcpuLay.MSRS + i * 8))
  cr2 : vs.fields (.msr msrCr2) = mem (v + VcpuLay.CR2)
  io : ∀ p, vs.ioDenied p = decide (mem (v + vcpuIoOff p) &&& vcpuIoBit p ≠ 0)

end

end Fl4Spec
