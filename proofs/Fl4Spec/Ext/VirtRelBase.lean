/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization, the VCPU's word layout for the refinement
relation** (proofs/VIRT-PLAN.md §11.1 "Relations", R0; §3.4 "refinement relation only").

The abstract VCPU (`VcpuState`, `Ext/VirtObj`) is a table of fields; FL4 keeps a VCPU as a 32 KiB image in kernel
memory (`crates/fl4-core/src/vcpu.rs`). This module names the places of that image the refinement reads
(`VcpuLay.*`, FL4's `vcpu::` constants, verbatim) and the part of the relation both backends share
(`VcpuRelCommon`): the binding word `TCB`, the exit record (`EXIT`, `VALID`, `PENDING`), the 15 GPRs (`REGS`), and
the two pseudo-MSRs that are VCPU words on both backends (`XCR0`, `VM_IBPB_DEFER`). The backend-specific relations
are `VcpuRelVmx` (`Ext/VirtRelVmx`) and `VcpuRelSvm` (`Ext/VirtRelSvm`).

Memory is abstract here: `mem : Word → Word`, the 64-bit words of kernel memory (FL4's `Store::read`). The
relation is stated over it so that it does not depend on FL4's store model (the J layer instantiates `mem` with
`L.mem s`).

Isabelle counterpart: l4v `proof/refine/ARM_HYP/StateRelation.thy` `vcpu_relation` (the abstract `vcpu` against
the executable `vcpu`); here the concrete side is FL4's word image rather than a Haskell record.

The ported modules are not changed.
-/
import Fl4Spec.Ext.VirtState

namespace Fl4Spec

noncomputable section
open Classical

/-! FL4's VCPU image layout (`crates/fl4-core/src/vcpu.rs`, constants of the same names). -/
namespace VcpuLay
/-- `vcpu::SHADOW`: the VMCS software image (VMX). -/
def SHADOW : Word := 0x1000
/-- `vcpu::TCB`: the bound thread, 0 if none (l4v ARM_HYP `vcpu_tcb`). -/
def TCB : Word := 0x5000
/-- `vcpu::XCR0`: the guest XCR0 (pseudo-MSR `0xffff_fffe`). -/
def XCR0 : Word := 0x5018
/-- `vcpu::CR2`: the guest CR2 on VMX (pseudo-MSR `0xffff_ffff`). -/
def CR2 : Word := 0x5020
/-- `vcpu::PENDING`: an exit for the VMM not yet reported (`ExitRecord.pending`). -/
def PENDING : Word := 0x5028
/-- `vcpu::VALID`: the last entry reached the guest and exited (`ExitRecord.valid`). -/
def VALID : Word := 0x5030
/-- `vcpu::VM_IBPB_DEFER` (pseudo-MSR `0xffff_fffd`). -/
def VM_IBPB_DEFER : Word := 0x5040
/-- `vcpu::REGS`: the 15 GPRs of the VMEnter layout. -/
def REGS : Word := 0x5100
/-- `vcpu::MSRS`: STAR, LSTAR, CSTAR, FMASK, KERNEL_GS_BASE on VMX. -/
def MSRS : Word := 0x5180
/-- `vcpu::EXIT`: the 30 exit-record message registers. -/
def EXIT : Word := 0x5200
/-- `vcpu::IO`: the VT-x I/O bitmap, 1024 words. -/
def IO : Word := 0x6000
/-- The image size (32 KiB, `seL4_X86_VCPUBits` 15). -/
def SIZE : Word := 0x8000
end VcpuLay

/-- The bound-thread word as an optional reference (0 = unbound; FL4 `vcpu::TCB`, `tl::VCPU`). -/
def vcpuTcbRef (w : Word) : Option ObjRef := if w = 0 then none else some w

/-- GPR `i`'s offset: `REGS + 8 i` (FL4 `vcpu::decode` WriteRegisters, `vcpu::report`). -/
def gprOff (i : Fin 15) : Word := VcpuLay.REGS + BitVec.ofNat 64 i.val * 8

/-- Exit MR `i`'s offset: `EXIT + 8 i` (FL4 `vcpu::report`). -/
def exitOff (i : Fin 30) : Word := VcpuLay.EXIT + BitVec.ofNat 64 i.val * 8

/-- **The relation part both backends share** (module docstring; VIRT-PLAN §11.1: `gpr i ↔ REGS + 8i`, XCR0 ↔
`XCR0`, `exit.mrs i ↔ EXIT + 8i`, `valid ↔ VALID ≠ 0`, `pending ↔ PENDING ≠ 0`, `tcb ↔ TCB`; plus FL4's
`VM_IBPB_DEFER` pseudo-MSR). `v` is the VCPU's base address. -/
structure VcpuRelCommon (mem : Word → Word) (v : Word) (vs : VcpuState) : Prop where
  tcb : vs.tcb = vcpuTcbRef (mem (v + VcpuLay.TCB))
  valid : vs.exit.valid = decide (mem (v + VcpuLay.VALID) ≠ 0)
  pending : vs.exit.pending = decide (mem (v + VcpuLay.PENDING) ≠ 0)
  mrs : ∀ i, vs.exit.mrs i = mem (v + exitOff i)
  gpr : ∀ i, vs.fields (.gpr i) = mem (v + gprOff i)
  xcr0 : vs.fields (.msr msrXcr0) = mem (v + VcpuLay.XCR0)
  ibpb : vs.fields (.msr msrVmIbpbDefer) = mem (v + VcpuLay.VM_IBPB_DEFER)

end

end Fl4Spec
