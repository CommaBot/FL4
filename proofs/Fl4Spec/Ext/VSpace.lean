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

3. l4h 0029: `Page_DeriveSubframe`, on a RAM-backed 2 MiB frame cap: 4 KiB
   frame caps for `count` consecutive pages from `offset`, inserted with
   `cap_insert` from the large frame cap's slot into `count` empty slots of
   a CNode from `node_offset`. The checks, in FL4's order: the extra cap
   and six arguments (`TruncatedMessage`); a non-device large frame cap
   (`IllegalOperation`); `offset` 4K-aligned below 2 MiB
   (`InvalidArgument 3`); `1 ≤ count ≤ (2 MiB - offset) / 4K`
   (`RangeError 1 max`); the CNode (the extra cap, or the slot it reaches
   with `lookup_target_slot` for a non-zero depth; not a CNode:
   `FailedLookup (MissingCapability depth)`); `node_offset` in it
   (`RangeError 0 (size - 1)`) and the run fitting (`RangeError 1 (size -
   node_offset)`); the slots empty (`DeleteFirst`). The rights are the
   frame's masked with the sixth argument (`mask_vm_rights`,
   `data_to_rights`).

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


/-- l4h 0029: a `DeriveSubframe` invocation: the large frame cap's slot, the
first page, the rights, and the destination slots. -/
structure Fl4SubframeInvocation where
  src : CslotPtr
  base : ObjRef
  rights : VMRights
  dests : List CslotPtr

section
variable {Z : Type} [StateExt Z]

/-- l4h 0029: the CNode cap the subframe caps go in. -/
def subframeNode (nodeCap : Cap) (index depth : Data) : SEMonad Z Cap :=
  if depth = 0 then NonDetE.returnOk nodeCap
  else do
    let slot ← lookupTargetSlot nodeCap (toBl index) (unat depth)
    NonDetE.liftE (getCap slot)

/-- l4h 0029: the decode of `Page_DeriveSubframe`. -/
def decodeDeriveSubframe (args : List Data) (cte : CslotPtr) (cap : ArchCap)
    (excaps : List (Cap × CslotPtr)) : SEMonad Z Fl4SubframeInvocation :=
  if excaps.length = 0 ∨ args.length < 6 then NonDetE.throwError .truncatedMessage
  else match cap with
    | .pageCap false p r _ .x64LargePage _ => do
        let index := the args[0]?
        let depth := the args[1]?
        let nOff := the args[2]?
        let off := the args[3]?
        let count := the args[4]?
        NonDetE.whenE (2 ^ 21 ≤ unat off ∨ unat off % 4096 ≠ 0) <| NonDetE.throwError (.invalidArgument 3)
        let mx := (2 ^ 21 - unat off) / 4096
        NonDetE.whenE (unat count < 1 ∨ mx < unat count) <|
          NonDetE.throwError (.rangeError 1 (BitVec.ofNat 64 mx))
        let nc ← subframeNode (the excaps[0]?).1 index depth
        match nc with
        | .cnodeCap ptr bits _ => do
            let size := 2 ^ bits
            NonDetE.whenE (size - 1 < unat nOff) <|
              NonDetE.throwError (.rangeError 0 (BitVec.ofNat 64 (size - 1)))
            NonDetE.whenE (size - unat nOff < unat count) <|
              NonDetE.throwError (.rangeError 1 (BitVec.ofNat 64 (size - unat nOff)))
            let dests := (List.range' (unat nOff) (unat count)).map fun i => (ptr, natToCref bits i)
            NonDetE.mapMEx ensureEmpty dests
            NonDetE.returnOk ⟨cte, p + off, maskVmRights r (dataToRights (the args[5]?)), dests⟩
        | _ => NonDetE.throwError (.failedLookup false (.missingCapability (unat depth)))
    | _ => NonDetE.throwError .illegalOperation

/-- l4h 0029: the invocation: `cap_insert` of the `i`-th 4 KiB frame cap into
the `i`-th destination slot. -/
def performDeriveSubframe (iv : Fl4SubframeInvocation) : SMonad Z Unit :=
  NonDet.mapMx (fun d : Nat × CslotPtr =>
      capInsert (.archObjectCap (.pageCap false (iv.base + BitVec.ofNat 64 (d.1 * 4096)) iv.rights .vmNoMap
        .x64SmallPage none)) iv.src d.2)
    ((List.range iv.dests.length).zip iv.dests)

end

end

end Fl4Spec
