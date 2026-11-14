/-
P3 (DESIGN.md §9), VSpace: top module.

* VsRel: the ASID table and pools (`VsRel`), `find_vspace_for_asid`;
* VsDel: `delete_asid` (`delete_asid_relR`, with `VsHypsR`: TLB
  invalidation and `set_vm_root` as arch effects matched to l4v
  `hw_asid_invalidate` / `set_vm_root`);
* VsDelPool: `delete_asid_pool` (`delete_asid_pool_relR`);
* VsAssign, VsAssignRel: ASIDPool `Assign` (decode, `Restart`, perform);
* VsMakePool: the ASID-table side of ASIDControl `MakePool`;
* VsRoot: `set_vm_root` against l4v `set_vm_root` (CR3 as an arch effect);
* VsDelRoot: `delete_asid` / `delete_asid_pool` with `VsHyps`, without
  `set_vm_root` as a hypothesis;
* VsPt: the page-table relation `PtRel` and the walks `lookup_pdpt_slot`,
  `lookup_pd_slot`, `lookup_pt_slot`;
* VsPte: 4K PTE construction (`make_user_page`) against l4v's `SmallPagePTE`;
* VsPtWrite: `write_mapping` against `store_pte` and the paging-structure
  cache flush.
-/
import Fl4Proofs.P3.VsMakePool
import Fl4Proofs.P3.VsDelRoot
import Fl4Proofs.P3.VsPtWrite
