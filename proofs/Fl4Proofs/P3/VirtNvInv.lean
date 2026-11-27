/-
P3x for virtualization, spec side (line virt, gen 6; proofs/VIRT-PLAN.md §10, table row "NoVirt reachability"):
**what a decoded invocation must satisfy for its perform to keep `NV`** (the carried decode fact of the NV
reachability proof, as vih3's `InvCAd` for `ValidIrqHandlers`).

* `VtxTy`: the five VT-x object types (seL4 object numbers 14..18: VCPU and the four EPT levels); their default
  caps are virtualization caps (`isVirt_defaultCap`), the VCPU default object is the only `aVcpu` object.
* `CnNV` (the caps a CNode invocation writes), `ArchNV` (the cap a page map writes), **`InvNV`**: retype type not
  `VtxTy`, `TcbCapsOK` of a TCB invocation, `CnNV`, the set-handler cap and `ArchNV` not virtualization caps.

Definitions and small facts only; no premises; no [J]/[P]/[W]/[S]. New file only.
-/
import Fl4Proofs.P3.VirtTcbOK
open Classical

namespace Fl4Proofs.P3.VirtNvInv
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtNvTcb Fl4Proofs.P3.VirtInvOK

noncomputable section

/-- The VT-x object types (`isVtxObjectTypeNum`: seL4 numbers 14..18). -/
def VtxTy : ApiObjectType → Prop
  | .archObject .vcpuObj => True
  | .archObject .eptPml4Obj => True
  | .archObject .eptPdptObj => True
  | .archObject .eptPdObj => True
  | .archObject .eptPtObj => True
  | _ => False

/-- The default cap of a non-VT-x type is not a virtualization cap. -/
theorem defaultCap_nv {t : ApiObjectType} (ht : ¬ VtxTy t) (o : ObjRef) (b : Nat) (d : Bool) :
    ¬ IsVirtCap (defaultCap t o b d) := by
  cases t with
  | archObject a => cases a <;> simp_all [VtxTy, defaultCap, archDefaultCap, IsVirtCap]
  | _ => simp [defaultCap, IsVirtCap]

theorem vtxTy_vcpu : VtxTy (.archObject .vcpuObj) := trivial

/-- The caps a CNode invocation writes are not virtualization caps. -/
def CnNV : CnodeInvocation → Prop
  | .insertCall c _ _ => ¬ IsVirtCap c
  | .moveCall c _ _ => ¬ IsVirtCap c
  | .rotateCall c1 c2 _ _ _ => ¬ IsVirtCap c1 ∧ ¬ IsVirtCap c2
  | _ => True

/-- The cap a page map writes is not a virtualization cap (the ported decoder builds a `vmVSpaceMap` cap). -/
def ArchNV : Fl4ArchInvocation → Prop
  | .spec (.invokePage (.pageMap c _ _ _)) => ¬ IsVirtCap c
  | _ => True

/-- **The carried decode fact of the NV reachability proof** (module docstring). -/
def InvNV : Fl4Invocation → Prop
  | .invokeUntyped ui => ¬ VtxTy (utType ui)
  | .invokeTCB i => TcbCapsOK i
  | .invokeCNode i => CnNV i
  | .invokeIRQHandler (.setIRQHandler _ c _) => ¬ IsVirtCap c
  | .invokeArchObject a => ArchNV a
  | _ => True

end

end Fl4Proofs.P3.VirtNvInv
