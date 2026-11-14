/-
FL4 differences (PORTING.md, "FL4 differences"): **VSpace extensions**
(l4h patches).

1. l4h 0017: `seL4_X64_PML4_Flush`, on a PML4 cap: flush the TLB entries
   of the cap's ASID. An unmapped PML4 cap (no ASID) is rejected with
   `InvalidCapability 0`. The flush is l4v's `flush_all` of the PML4 and its
   ASID (`invalidateASID`).
2. l4h 0023/0029: `Page_TestAndClearAccessed`, on a mapped 4K or 2M frame
   cap: if the cap's mapping is still in place, report whether the page was
   accessed and clear the accessed bit. The accessed bit is hardware state
   that the abstract model does not keep (l4v's `attr_mask` drops it from
   every entry), so the reply is either value and the abstract state does
   not change. Huge frames and unmapped caps are rejected with
   `IllegalOperation`; a cap whose mapping is gone (the ASID or the entry)
   with `InvalidCapability 0`.

The ported modules are not changed.
-/
import Fl4Spec

namespace Fl4Spec

noncomputable section
open Classical

/-- l4h 0017: a PML4 invocation. -/
inductive Fl4Pml4Invocation where
  | flush (pml4 : ObjRef) (asid : Asid)

section
variable {Z : Type} [StateExt Z]

/-- l4h 0017: the decode of `X64PML4Flush`. -/
def decodePml4Flush (cap : ArchCap) : SEMonad Z Fl4Pml4Invocation :=
  match cap with
  | .pml4Cap p (some asid) => NonDetE.returnOk (.flush p asid)
  | .pml4Cap _ none => NonDetE.throwError (.invalidCapability 0)
  | _ => NonDetE.liftE NonDet.fail

/-- l4h 0017: the flush. -/
def performPml4Flush : Fl4Pml4Invocation → SMonad Z Unit
  | .flush p asid => flushAll p asid

/-- l4h 0023/0029: the entry slot of a frame cap's mapping, if it is still
in place; else `InvalidCapability 0`. -/
def frameMappingSlot (p : ObjRef) (sz : VMPageSize) (asid : Asid) (vaddr : VSpaceRef) : SEMonad Z ObjRef := do
  let vs ← NonDetE.handleE (findVspaceForAsid asid) fun _ => NonDetE.throwError (.invalidCapability 0)
  match sz with
  | .x64SmallPage => do
      let slot ← NonDetE.handleE (lookupPtSlot vs vaddr) fun _ => NonDetE.throwError (.invalidCapability 0)
      let pte ← NonDetE.liftE (getPte slot)
      NonDetE.unlessE (checkMappingPptr p (.vmPTE pte)) (NonDetE.throwError (.invalidCapability 0))
      NonDetE.returnOk slot
  | _ => do
      let slot ← NonDetE.handleE (lookupPdSlot vs vaddr) fun _ => NonDetE.throwError (.invalidCapability 0)
      let pde ← NonDetE.liftE (getPde slot)
      NonDetE.unlessE (checkMappingPptr p (.vmPDE pde)) (NonDetE.throwError (.invalidCapability 0))
      NonDetE.returnOk slot

/-- l4h 0023/0029: the decode of `Page_TestAndClearAccessed`. -/
def decodeTestAndClearAccessed (cap : ArchCap) : SEMonad Z ObjRef :=
  match cap with
  | .pageCap _ p _ _ sz mapped =>
    if sz = .x64HugePage then NonDetE.throwError .illegalOperation
    else match mapped with
      | none => NonDetE.throwError .illegalOperation
      | some (asid, vaddr) => do
          NonDetE.whenE (asid = 0) (NonDetE.throwError .illegalOperation)
          frameMappingSlot p sz asid vaddr
  | _ => NonDetE.liftE NonDet.fail

/-- l4h 0023/0029: the invocation: whether the page was accessed (either
answer: the model does not keep the accessed bit). -/
def performTestAndClearAccessed (_slot : ObjRef) : SMonad Z (List Data) :=
  NonDet.select {[0], [1]}

end

end

end Fl4Spec
