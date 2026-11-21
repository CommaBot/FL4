/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization,
the guest page-table invocations** (proofs/VIRT-PLAN.md §5.2, §6).

FL4's `crates/fl4-core/src/ept.rs` (`find`, `root`, `lookup`, `unmap`,
`map_frame`, `decode`), the EPT branches of `arch/x86_64/vspace.rs`
(`decode_frame`'s `X86PageMapEPT` / EPT-mapped `X86PageMap` and
`X86PageUnmap`, `X86ASIDPoolAssign` of an EPT root), in the decode /
perform structure of l4v's `ArchDecode_A` / `Arch_A` (every FL4 check
precedes its first write). One spec for Intel EPT and AMD nested paging:
the entry encoding is `GuestPte.encode virtKind` (`Ext/VirtEpt`).

* `findGuestRoot asid` (FL4 `ept::find`): the guest-tagged root of an ASID
  (`r ||| 1` in its pool), `InvalidRoot` otherwise.
* `guestLookupSlot root gpa level` (FL4 `ept::lookup`): the table holding
  the entry for `gpa` at `level` (39, 30, 21 or 12), walking only through
  present non-large entries; `MissingCapability shift` at a missing or
  large entry.
* `guestUnmap asid gpa ptr level table` (FL4 `ept::unmap`): clears the
  entry iff it is present, of the right kind and names `ptr`. The
  invalidation on every recorded core (`ept::invalidate`) has no abstract
  effect: the guest oracle reads the current tables (`Ext/VirtGuest`).
* `decodeEptInvocation` / `decodeEptFrameInvocation` /
  `decodeEptAsidPoolAssign` and `performEptInvocation`.

The labels are FL4's ABI numbers (`fl4_abi::label`).

The ported modules are not changed.
-/
import Fl4Spec.Ext.VirtVcpu

namespace Fl4Spec

noncomputable section
open Classical

/-- FL4 label numbers (`fl4_abi::label`). -/
def fl4PageMapEptLabel : Nat := 60
def fl4EptPdptMapLabel : Nat := 82
def fl4EptPdptUnmapLabel : Nat := 83
def fl4EptPdMapLabel : Nat := 84
def fl4EptPdUnmapLabel : Nat := 85
def fl4EptPtMapLabel : Nat := 86
def fl4EptPtUnmapLabel : Nat := 87

/-- FL4 `ept::LIMIT`: guest-physical addresses below 2^47. -/
def guestGpaLimit : Word := 1 <<< 47

/-- The map and unmap labels of an EPT table level (FL4 `ept::decode`;
any level but 39 and 30 is a PT). -/
def eptTableLabels (level : Nat) : Nat × Nat :=
  if level = 39 then (fl4EptPdptMapLabel, fl4EptPdptUnmapLabel)
  else if level = 30 then (fl4EptPdMapLabel, fl4EptPdUnmapLabel)
  else (fl4EptPtMapLabel, fl4EptPtUnmapLabel)

/-- A decoded guest page-table invocation. -/
inductive EptInvocation where
  /-- map table `ptr` (level `level`, cap in `slot`) into entry `idx` of
  table `table` under the root of `asid`, at `gpa` -/
  | tableMap (ptr : ObjRef) (level : Nat) (slot : CslotPtr) (table : ObjRef) (idx : BitVec 9)
      (asid : Asid) (gpa : VSpaceRef)
  /-- unmap table `ptr` (if `mapped`) and clear it -/
  | tableUnmap (ptr : ObjRef) (level : Nat) (mapped : Option (Asid × VSpaceRef)) (slot : CslotPtr)
  /-- X86PageMapEPT: write `entry` (0 for a kernel-only frame) into entry
  `idx` of `table`; the frame cap in `slot` becomes `newCap` -/
  | frameMap (newCap : ArchCap) (slot : CslotPtr) (table : ObjRef) (idx : BitVec 9) (entry : Word)
  /-- X86PageUnmap of an EPT-mapped frame -/
  | frameUnmap (cap : ArchCap) (slot : CslotPtr)
  /-- X86ASIDPoolAssign of an unmapped EPT root (cap in `slot`) -/
  | poolAssign (asid : Asid) (pool : ObjRef) (slot : CslotPtr)
deriving Inhabited

section
variable {Z : Type} [StateExt Z]

/-- A guest table (fails unless the object is one; l4v `get_pd` style). -/
def getEpt (p : ObjRef) : SMonad Z (Nat × (BitVec 9 → Word)) := do
  let kobj ← getObject p
  match kobj with
  | .archObj (.ept l es) => return (l, es)
  | _ => NonDet.fail

/-- Store one guest-table entry. -/
def storeGuestEntry (p : ObjRef) (i : BitVec 9) (e : Word) : SMonad Z Unit := do
  let (l, es) ← getEpt p
  setObject p (.archObj (.ept l (Function.update es i e)))

/-- FL4 `ept::find` (module docstring). -/
def findGuestRoot (asid : Asid) : LFMonad Z ObjRef := do
  let asidTable ← NonDetE.liftE (NonDet.gets fun s : State Z => s.archState.x64AsidTable)
  let pool ← match asidTable (asidHighBitsOf asid) with
    | some ptr => NonDetE.liftE (getAsidPool ptr)
    | none => NonDetE.throwError .invalidRoot
  match pool (asidLowBitsOf asid) with
  | none => NonDetE.throwError .invalidRoot
  | some e => if e &&& 1 = 0 then NonDetE.throwError .invalidRoot else NonDetE.returnOk (asidEntryRoot e)

/-- FL4 `ept::root`: the root and ASID of a mapped level-0 EPT cap whose
ASID still names it. -/
def eptCapRoot (c : Cap) : SEMonad Z (ObjRef × Asid) :=
  match c with
  | .archObjectCap (.eptCap ptr 0 (some (asid, _))) => do
    let r ← NonDetE.handleE (findGuestRoot asid) fun lf => NonDetE.throwError (.failedLookup false lf)
    NonDetE.whenE (r ≠ ptr) <| NonDetE.throwError (.invalidCapability 1)
    NonDetE.returnOk (r, asid)
  | _ => NonDetE.throwError (.invalidCapability 1)

/-- FL4 `ept::lookup` (module docstring): the table that holds the entry
of `gpa` at `level`. -/
def guestLookupSlot (root : ObjRef) (gpa : Word) (level : Nat) : LFMonad Z ObjRef :=
  go root [39, 30, 21]
where
  go : ObjRef → List Nat → LFMonad Z ObjRef
  | t, [] => NonDetE.returnOk t
  | t, s :: rest =>
    if s > level then do
      let (_, es) ← NonDetE.liftE (getEpt t)
      let e := es (guestIndex gpa s)
      if e &&& 1 = 0 ∨ e &&& 128 ≠ 0 then NonDetE.throwError (.missingCapability s)
      else go (ptrFromPAddr (e &&& guestPteAddress)) rest
    else NonDetE.returnOk t

/-- FL4 `ept::slot`: `guestLookupSlot` with its fault as a syscall error. -/
def guestSlot (root : ObjRef) (gpa : Word) (level : Nat) : SEMonad Z ObjRef :=
  NonDetE.handleE (guestLookupSlot root gpa level) fun lf => NonDetE.throwError (.failedLookup false lf)

/-- **FL4 `ept::unmap`** (module docstring): `table` for a table's entry,
otherwise a frame of `2^level` bytes. -/
def guestUnmap (asid : Asid) (gpa : Word) (ptr : ObjRef) (level : Nat) (table : Bool) : SMonad Z Unit := do
  let r ← ExceptT.run (findGuestRoot asid)
  match r with
  | .error _ => return ()
  | .ok root => do
    let t ← ExceptT.run (guestLookupSlot root gpa level)
    match t with
    | .error _ => return ()
    | .ok tbl => do
      let (_, es) ← getEpt tbl
      let i := guestIndex gpa level
      let e := es i
      let large := !table && decide (level > 12)
      let msk : Word := if large then guestPteAddress &&& ~~~(((1 : Word) <<< level) - 1) else guestPteAddress
      NonDet.unless (e &&& 1 = 0 ∨ (level ≠ 12 ∧ decide (e &&& 128 ≠ 0) ≠ large) ∨
          e &&& msk ≠ addrFromPPtr ptr) <|
        storeGuestEntry tbl i 0

/-- **The EPT table decoder** (FL4 `ept::decode`; a level-0 cap and any
other label: `IllegalOperation`). -/
def decodeEptInvocation (label : Data) (args : List Data) (slot : CslotPtr) (cap : ArchCap)
    (extraCaps : List (Cap × CslotPtr)) : SEMonad Z EptInvocation :=
  match cap with
  | .eptCap ptr level mapped =>
    if level = 0 then NonDetE.throwError .illegalOperation
    else
      let (mapL, unmapL) := eptTableLabels level
      if dataToNat label = unmapL then do
        let final ← NonDetE.liftE <| isFinalCap (.archObjectCap cap)
        NonDetE.unlessE final <| NonDetE.throwError .revokeFirst
        NonDetE.returnOk (.tableUnmap ptr level mapped slot)
      else if dataToNat label = mapL then
        match extraCaps with
        | [] => NonDetE.throwError .truncatedMessage
        | (rootCap, _) :: _ =>
          if args.length < 2 then NonDetE.throwError .truncatedMessage
          else if mapped.isSome then NonDetE.throwError (.invalidCapability 0)
          else do
            let gpa := args.getD 0 0 &&& ~~~(((1 : Word) <<< level) - 1)
            NonDetE.whenE (gpa ≥ guestGpaLimit) <| NonDetE.throwError (.invalidArgument 0)
            let (r, asid) ← eptCapRoot rootCap
            let tbl ← guestSlot r gpa level
            let (_, es) ← NonDetE.liftE (getEpt tbl)
            NonDetE.whenE (es (guestIndex gpa level) &&& 1 ≠ 0) <| NonDetE.throwError .deleteFirst
            NonDetE.returnOk (.tableMap ptr level slot tbl (guestIndex gpa level) asid gpa)
      else NonDetE.throwError .illegalOperation
  | _ => NonDetE.throwError .illegalOperation

/-- **X86PageMapEPT** (FL4 `ept::map_frame`), in FL4's order. -/
def decodePageMapEpt (args : List Data) (slot : CslotPtr) (cap : ArchCap)
    (extraCaps : List (Cap × CslotPtr)) : SEMonad Z EptInvocation :=
  if args.length < 3 ∨ extraCaps = [] then NonDetE.throwError .truncatedMessage
  else do
    let gpa := args.getD 0 0 &&& ~~~(4095 : Word)
    NonDetE.whenE (gpa ≥ guestGpaLimit) <| NonDetE.throwError (.invalidArgument 0)
    let mask := args.getD 1 0
    let attr := args.getD 2 0
    match cap with
    | .pageCap dev p R _ sz none => do
      let (r, asid) ← eptCapRoot (the extraCaps.head?).1
      let bits := pageBitsForSize sz
      NonDetE.whenE (gpa &&& (((1 : Word) <<< bits) - 1) ≠ 0) <| NonDetE.throwError .alignmentError
      NonDetE.whenE (sz = .x64HugePage) <| NonDetE.throwError (.invalidCapability 0)
      let tbl ← guestSlot r gpa bits
      let (_, es) ← NonDetE.liftE (getEpt tbl)
      NonDetE.whenE (es (guestIndex gpa bits) &&& 1 ≠ 0) <| NonDetE.throwError .deleteFirst
      let rights := maskVmRights R (dataToRights mask)
      let entry : Word := if rights = vmKernelOnly then 0
        else GuestPte.encode virtKind
          (.frame (addrFromPPtr p) (sz = .x64LargePage) (rights ≠ vmReadOnly) (guestMemoryType attr))
      -- A kernel-only frame leaves the entry and the cap unmapped
      -- (FL4 `map_frame`'s comment).
      let newCap := if entry = 0 then ArchCap.pageCap dev p R .vmNoMap sz none
        else .pageCap dev p R .vmEptMap sz (some (asid, gpa))
      NonDetE.returnOk (.frameMap newCap slot tbl (guestIndex gpa bits) entry)
    | _ => NonDetE.throwError (.invalidCapability 0)

/-- X86ASIDPoolAssign of an unmapped EPT root (the EPT case of FL4's
`X86ASIDPoolAssign`; the checks are the ported decoder's). -/
def decodeEptAsidPoolAssign (p : ObjRef) (base : Asid) (rootSlot : CslotPtr) : SEMonad Z EptInvocation := do
  let asidTable ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.archState.x64AsidTable
  let poolPtr ← NonDetE.returnOk (asidTable (asidHighBitsOf base))
  NonDetE.whenE (poolPtr = none) <| NonDetE.throwError (.failedLookup false .invalidRoot)
  NonDetE.whenE (p ≠ the poolPtr) <| NonDetE.throwError (.invalidCapability 0)
  let pool ← NonDetE.liftE <| getAsidPool p
  let freeSet ← NonDetE.returnOk ((dom pool)ᶜ ∩ {x | ucast asidRepLen x + base ≠ 0})
  NonDetE.whenE (freeSet = ∅) <| NonDetE.throwError .deleteFirst
  let offset ← NonDetE.liftE <| selectExt (fun _ => freeAsidPoolSelect pool base) freeSet
  NonDetE.returnOk <| .poolAssign (ucast asidRepLen offset + base) p rootSlot

/-- **The guest page-table invocations** (FL4's effects). -/
def performEptInvocation : EptInvocation → SMonad Z Unit
  | .tableMap ptr level slot tbl i asid gpa => do
    storeGuestEntry tbl i (GuestPte.encode virtKind (.table (addrFromPPtr ptr)))
    setCap (.archObjectCap (.eptCap ptr level (some (asid, gpa)))) slot
  | .tableUnmap ptr level mapped slot => do
    match mapped with
    | some (asid, gpa) => do
      guestUnmap asid gpa ptr level true
      -- seL4 clears an unmapped table (FL4 `s.zero(ptr, 4096)`).
      let (l, _) ← getEpt ptr
      setObject ptr (.archObj (.ept l fun _ => 0))
    | none => return ()
    setCap (.archObjectCap (.eptCap ptr level none)) slot
  | .frameMap newCap slot tbl i entry => do
    setCap (.archObjectCap newCap) slot
    storeGuestEntry tbl i entry
  | .frameUnmap cap slot =>
    match cap with
    | .pageCap dev p R _ sz m => do
      match m with
      | some (asid, gpa) => NonDet.when (asid ≠ 0) <| guestUnmap asid gpa p (pageBitsForSize sz) false
      | none => return ()
      setCap (.archObjectCap (.pageCap dev p R .vmNoMap sz none)) slot
    | _ => NonDet.fail
  | .poolAssign asid pool slot => do
    let c ← getCap slot
    match c with
    | .archObjectCap (.eptCap r 0 _) => do
      setCap (.archObjectCap (.eptCap r 0 (some (asid, 0)))) slot
      storeAsidPoolEntry pool asid (some (r ||| 1))
    | _ => NonDet.fail

end

end

end Fl4Spec
