/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization,
the VCPU object** (proofs/VIRT-PLAN.md §3.1, decision Q1 of 2026-11-21).

The abstract VCPU is the content of the heap object
`ArchKernelObj.vcpu (st : VcpuState)` (`Fl4Spec/X64/Structs`), as l4v
ARM_HYP's `arch_kernel_obj.VCPU vcpu` (`Arch_Structs_A.vcpu`). This module
holds only the types the object needs, so that `X64/Structs` can import
it; the operations on them are in `Ext/VirtFields` and later modules.

* `VField`: a field of the backend's table (`Ext/VirtFields` gives the
  tables and the classes).
* `ExitRecord`: the pending-exit record, the 30 VMEnter message registers
  of libsel4 `sel4/arch/vmenter.h`, with the flags `valid` (the last entry
  reached the guest and exited; FL4 word `VALID`) and `pending` (an exit
  for the VMM not yet reported; `PENDING`).
* `VcpuState`: `tcb` the bound thread (FL4 word `vcpu::TCB`, l4v ARM_HYP
  `vcpu_tcb`); `fields` the field table, indexed by canonical fields only
  (`VField.canon`); `exit`; `ioDenied` the VT-x I/O bitmap (FL4 `vcpu::IO`,
  a set bit traps the port; SDM Vol. 3C §25.6.4; SVM uses one shared
  all-intercepting map, so the bitmap is VMX-only).

The TCB → VCPU direction of the binding (FL4 `tl::VCPU`, l4v ARM_HYP
`tcb_vcpu`) is not stored: it is the inverse of `VcpuState.tcb`
(`tcbVcpuOf`, `Ext/VirtState`), unique by the binding invariant
(`VcpuBindingInv`).

`VcpuState.blank` is the object a retype creates (`default_arch_object`,
all words zero, as FL4's retype zeroes the memory); FL4's `vcpu::init`
then writes the initial fields (`initVcpu`, the retype hook of
`Ext/VirtFinalise`).

The ported modules are not changed, except that `X64/Structs` imports this
module for the argument of the FL4 constructor `ArchKernelObj.vcpu`.
-/
import Fl4Spec.Machine

namespace Fl4Spec

noncomputable section
open Classical

/-- A VCPU field (module docstring; `Ext/VirtFields`). -/
inductive VField where
  | vmcs (enc : Word)
  | vmcb (off : Word)
  | gpr (i : Fin 15)
  | msr (m : Word)
deriving DecidableEq, Inhabited

/-- The pending-exit record (module docstring). -/
structure ExitRecord where
  valid : Bool
  pending : Bool
  mrs : Fin 30 → Word

/-- The abstract VCPU (module docstring). -/
structure VcpuState where
  tcb : Option ObjRef
  fields : VField → Word
  exit : ExitRecord
  ioDenied : BitVec 16 → Bool

/-- The VCPU a retype creates before FL4's `vcpu::init` (zeroed memory:
unbound, every field 0, no exit, every I/O port allowed by the zero
bitmap; `vcpu::init` then sets it to `initVcpu`). -/
def VcpuState.blank : VcpuState where
  tcb := none
  fields := fun _ => 0
  exit := ⟨false, false, fun _ => 0⟩
  ioDenied := fun _ => false

instance : Inhabited VcpuState := ⟨VcpuState.blank⟩

end

end Fl4Spec
