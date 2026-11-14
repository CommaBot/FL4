/-
P3 (DESIGN.md §9), VSpace: top module.

* VsRel: the ASID table and pools (`VsRel`), `find_vspace_for_asid`;
* VsDel: `delete_asid` (with `VsHyps`: TLB invalidation and `set_vm_root`
  as arch effects matched to l4v `hw_asid_invalidate` / `set_vm_root`);
* VsDelPool: `delete_asid_pool`;
* VsAssign, VsAssignRel: ASIDPool `Assign` (decode, `Restart`, perform);
* VsMakePool: the ASID-table side of ASIDControl `MakePool`.
-/
import Fl4Proofs.P3.VsMakePool
