/-
FL4 differences (PORTING.md, "FL4 differences"): **`X86PML4FrameBatch`**, an
FL4 extension with no seL4 / l4v counterpart (FL4 #71,
`interfaces/object-api-extensions.xml`; fl4-core `vspace::decode_frame_batch`,
`frame_batch_entry`, `batch_map`, `unmap_page_unflushed`). KENTRY-PLAN
"fb-spec" gives the semantics in full; this module states them as a
composition of the ported operations.

On a PML4 cap, at FL4's label number 90 (`fl4FrameBatchLabel`), one op for
`n` entries, run in order, stopping at the first that fails:

* **copy-and-map** (source CPtr, destination CPtr, vaddr): CNode_Copy's
  steps (`lookupTargetSlot`, `ensureEmpty`, `lookupSourceSlot`, `maskCap`,
  `deriveCap`, `capInsert`) for a frame cap, then the map of the copy
  (`fbMap`); a failing map deletes the copy (`capDelete`), so an entry is
  all or nothing;
* **remap** (CPtr, vaddr): the map of the frame cap in the slot;
* **delete** (CPtr): an empty slot is no error; a frame cap is deleted with
  `capDelete`; with the defer flag, a non-device frame mapped in this
  address space is first unmapped without its TLB invalidation
  (`unmapPageUnflushed`) and its cap made unmapped, and the batch ends with
  one `flushAll` of the address space if any entry was cleared.

The map (`fbMap`) is l4v's `X64PageMap`: `decodePageInvocation` at the
`X64PageMap` label with the batch's rights, attributes and PML4 cap, then
`performPageInvocation`, after FL4's rejection of an EPT-mapped cap
(`InvalidCapability 0`).

A failing entry is no syscall error: the invocation returns the reply
`[entries done, the failing entry's seL4_Error code or 0]` (sent only to a
Call, by the shell's `replyFromKernel`); a deletion's preemption, which a
frame cap's finalisation never reaches, counts as `IllegalOperation` (FL4's
`Err(_)` branch). The header's errors are decode errors.

The ported modules are not changed; the dispatch is `Ext/Invocation`'s
`fl4ArchDecodeInvocation` / `fl4ArchPerformInvocation`.
-/
import Fl4Spec

namespace Fl4Spec

noncomputable section
open Classical

/-- FL4 extension: the label number of `X86PML4FrameBatch` (`fl4_abi::label`,
after `UntypedRetypeShared` = 89, in the x86-64 configuration with the
hardware debug API, as `fl4Pml4FlushLabel`). -/
def fl4FrameBatchLabel : Nat := 90

/-- The batch's op (header bits 0-1). -/
inductive FbOp where
  | copyMap
  | remap
  | delete
deriving DecidableEq, Inhabited

/-- The op of a header's bits 0-1 (0 is none). -/
def fbOpOf (n : Nat) : Option FbOp :=
  if n = 1 then some .copyMap else if n = 2 then some .remap else if n = 3 then some .delete else none

/-- Words per entry (`frame_batch::entry_words`). -/
def FbOp.words : FbOp → Nat
  | .copyMap => 3
  | .remap => 2
  | .delete => 1

/-- The header bits FL4 defines (`frame_batch::DEFINED`): op, count, depth,
map rights, copy rights, attributes, `DEFER_DELETE_FLUSH`. -/
def fbDefined : Data :=
  0x3#64 ||| (0xff#64 <<< 8) ||| (0x7f#64 <<< 16) ||| (0xf#64 <<< 24) ||| (0xf#64 <<< 28) |||
    (0x1f#64 <<< 32) ||| (1#64 <<< 40)

/-- A decoded batch: the address space (its PML4 and ASID), the header's
fields, the lookup CNode caps and the entries' words (unused words 0). -/
structure Fl4FrameBatchInvocation where
  vspace : ObjRef
  asid : Asid
  op : FbOp
  depth : Nat
  mapRights : Data
  capRights : Data
  attr : Data
  deferDelete : Bool
  cnode : Cap
  destCnode : Cap
  entries : List (Data × Data × Data)
deriving Inhabited

/-- The entries' words from the message (entry `i` from word `1 + words * i`). -/
def fbEntries (args : List Data) (words n : Nat) : List (Data × Data × Data) :=
  (List.range n).map fun i =>
    let k := 1 + words * i
    (the args[k]?, if words > 1 then the args[k + 1]? else 0, if words > 2 then the args[k + 2]? else 0)

/-- The label `decodePageInvocation` maps a frame at (`X64PageMap`). -/
def fbPageMapLabel : Data := BitVec.ofNat 64 (InvocationLabel.fromEnum (.archInvocationLabel .x64PageMap))

/-- A frame cap. -/
def isPageCap : Cap → Bool
  | .archObjectCap (.pageCap ..) => true
  | _ => false

section
variable {Z : Type} [StateExt Z]

/-- The decode (`decode_frame_batch` up to its loop), in FL4's order: an
unmapped PML4 cap, or one whose ASID no longer names it (any lookup
failure included), `InvalidCapability 0`; no header `TruncatedMessage`;
reserved header bits, op 0 or depth outside 1..64 `InvalidArgument 0`; fewer
words than the entries need `TruncatedMessage`; no extra cap
`TruncatedMessage`; extra cap 0 not a CNode `InvalidCapability 1`; the
destination CNode (extra cap 1 for a copy, if given, else extra cap 0) not a
CNode `InvalidCapability 2`. -/
def decodeFrameBatch (args : List Data) (cap : ArchCap) (extraCaps : List (Cap × CslotPtr)) :
    SEMonad Z Fl4FrameBatchInvocation :=
  match cap with
  | .pml4Cap p (some asid) => do
      let vs ← NonDetE.handleE (findVspaceForAsid asid) fun _ => NonDetE.throwError (.invalidCapability 0)
      NonDetE.whenE (vs ≠ p) <| NonDetE.throwError (.invalidCapability 0)
      NonDetE.whenE (args.length < 1) <| NonDetE.throwError .truncatedMessage
      let hdr := the args[0]?
      let n := dataToNat ((hdr >>> 8) &&& 0xff#64)
      let depth := dataToNat ((hdr >>> 16) &&& 0x7f#64)
      let op ← match fbOpOf (dataToNat (hdr &&& 0x3#64)) with
        | some op =>
          if hdr &&& ~~~fbDefined ≠ 0 ∨ depth = 0 ∨ depth > 64
          then NonDetE.throwError (.invalidArgument 0) else NonDetE.returnOk op
        | none => NonDetE.throwError (.invalidArgument 0)
      NonDetE.whenE (args.length < 1 + op.words * n) <| NonDetE.throwError .truncatedMessage
      NonDetE.whenE (extraCaps.length < 1) <| NonDetE.throwError .truncatedMessage
      let cnode := (the extraCaps[0]?).1
      NonDetE.unlessE (isCnodeCap cnode) <| NonDetE.throwError (.invalidCapability 1)
      let destCnode := if op = .copyMap ∧ extraCaps.length > 1 then (the extraCaps[1]?).1 else cnode
      NonDetE.unlessE (isCnodeCap destCnode) <| NonDetE.throwError (.invalidCapability 2)
      NonDetE.returnOk
        { vspace := p, asid := asid, op := op, depth := depth,
          mapRights := (hdr >>> 24) &&& 0xf#64, capRights := (hdr >>> 28) &&& 0xf#64,
          attr := (hdr >>> 32) &&& 0x1f#64, deferDelete := decide (hdr &&& (1#64 <<< 40) ≠ 0),
          cnode := cnode, destCnode := destCnode, entries := fbEntries args op.words n }
  | .pml4Cap _ none => NonDetE.throwError (.invalidCapability 0)
  | _ => NonDetE.liftE NonDet.fail

/-- `batch_map`: map the frame cap in `slot` at `vaddr` in the batch's
address space with its rights and attributes: l4v's `X64PageMap`
(`decodePageInvocation`, `performPageInvocation`) after FL4's rejection of
a non-frame or EPT-mapped cap. -/
def fbMap (b : Fl4FrameBatchInvocation) (slot : CslotPtr) (vaddr : Data) : SEMonad Z Unit := do
  let cap ← NonDetE.liftE <| getCap slot
  match cap with
  | .archObjectCap (.pageCap dev p R mt sz m) => do
      NonDetE.whenE (m.isSome ∧ mt = .vmEptMap) <| NonDetE.throwError (.invalidCapability 0)
      let iv ← decodePageInvocation fbPageMapLabel [vaddr, b.mapRights, b.attr] slot
        (.pageCap dev p R mt sz m) [(.archObjectCap (.pml4Cap b.vspace (some b.asid)), slot)]
      match iv with
      | .invokePage pi => do
          let _ ← NonDetE.liftE <| performPageInvocation pi
          NonDetE.returnOk ()
      | _ => NonDetE.liftE NonDet.fail
  | _ => NonDetE.throwError (.invalidCapability 0)

/-- `unmap_page_unflushed`: l4v's `unmapPage` in the address space `vspace`
without its TLB invalidation; whether it cleared an entry. -/
def unmapPageUnflushed (pgsz : VMPageSize) (vspace : ObjRef) (vptr : VSpaceRef) (pptr : ObjRef) :
    SMonad Z Bool :=
  NonDetE.catch (do
    match pgsz with
    | .x64SmallPage => do
        let ptSlot ← lookupPtSlot vspace vptr
        let pte ← NonDetE.liftE (getPte ptSlot)
        NonDetE.unlessE (checkMappingPptr pptr (.vmPTE pte)) <| NonDetE.throwError .invalidRoot
        NonDetE.liftE (storePte ptSlot .invalidPTE)
    | .x64LargePage => do
        let pdSlot ← lookupPdSlot vspace vptr
        let pde ← NonDetE.liftE (getPde pdSlot)
        NonDetE.unlessE (checkMappingPptr pptr (.vmPDE pde)) <| NonDetE.throwError .invalidRoot
        NonDetE.liftE (storePde pdSlot .invalidPDE)
    | .x64HugePage => do
        let pdptSlot ← lookupPdptSlot vspace vptr
        let pdpte ← NonDetE.liftE (getPdpte pdptSlot)
        NonDetE.unlessE (checkMappingPptr pptr (.vmPDPTE pdpte)) <| NonDetE.throwError .invalidRoot
        NonDetE.liftE (storePdpte pdptSlot .invalidPDPTE)
    NonDetE.returnOk true)
    (fun _ => return false)

/-- A syscall error as the reply's error code (`SysError::code`, seL4_Error). -/
def fbCode {α : Type} (m : SEMonad Z α) : NonDetE (State Z) Data α :=
  NonDetE.handleE m fun e => NonDetE.throwError (msgFromSyscallError e).1

/-- `cteDelete(slot, true)` in an entry: a preemption (never reached for a
frame cap) is FL4's `Err(_)`, `IllegalOperation`. -/
def fbDelete (slot : CslotPtr) : NonDetE (State Z) Data Unit :=
  NonDetE.handleE (capDelete slot) fun _ => NonDetE.throwError (msgFromSyscallError .illegalOperation).1

/-- **One entry** (`frame_batch_entry`), its error the reply's error code;
`true` when a deferred delete cleared an entry. -/
def fbEntry (b : Fl4FrameBatchInvocation) (w : Data × Data × Data) : NonDetE (State Z) Data Bool :=
  match b.op with
  | .copyMap => do
      let dest ← fbCode <| lookupTargetSlot b.destCnode (dataToCptr w.2.1) b.depth
      fbCode <| ensureEmpty dest
      let src ← fbCode <| lookupSourceSlot b.cnode (dataToCptr w.1) b.depth
      let srcCap ← NonDetE.liftE <| getCap src
      fbCode <| NonDetE.unlessE (isPageCap srcCap) <| NonDetE.throwError (.invalidCapability 0)
      let newCap ← fbCode <| deriveCap src (maskCap (dataToRights b.capRights) srcCap)
      NonDetE.liftE <| capInsert newCap src dest
      NonDetE.handleE (fbCode <| fbMap b dest w.2.2) fun c => do
        -- all or nothing: drop the unmapped copy
        NonDetE.liftE <| NonDetE.catch (capDelete dest) fun _ => NonDet.pure ()
        NonDetE.throwError c
      NonDetE.returnOk false
  | .remap => do
      let slot ← fbCode <| lookupSourceSlot b.cnode (dataToCptr w.1) b.depth
      fbCode <| fbMap b slot w.2.1
      NonDetE.returnOk false
  | .delete => do
      let slot ← fbCode <| lookupTargetSlot b.cnode (dataToCptr w.1) b.depth
      let c ← NonDetE.liftE <| getCap slot
      match c with
      | .nullCap => NonDetE.returnOk false
      | .archObjectCap (.pageCap dev p R mt sz m) => do
          let cleared ← match m with
            | some (asid', vaddr) =>
              if b.deferDelete ∧ mt = .vmVSpaceMap ∧ dev = false ∧ asid' = b.asid then
                NonDetE.liftE (do
                  let r ← unmapPageUnflushed sz b.vspace vaddr p
                  setCap (.archObjectCap (.pageCap dev p R .vmNoMap sz none)) slot
                  return r)
              else NonDetE.returnOk false
            | none => NonDetE.returnOk false
          fbDelete slot
          NonDetE.returnOk cleared
      | _ => NonDetE.throwError (msgFromSyscallError .illegalOperation).1

/-- The loop (`decode_frame_batch`'s `while`): the entries in order, up to
the first that fails; (entries done, error code or 0, whether a deferred
delete cleared an entry). -/
def fbRun (b : Fl4FrameBatchInvocation) : List (Data × Data × Data) → Nat → Bool → SMonad Z (Nat × Data × Bool)
  | [], done, d => return (done, 0, d)
  | w :: ws, done, d => do
      let r ← (fbEntry b w).run
      match r with
      | .ok d' => fbRun b ws (done + 1) (d || d')
      | .error c => return (done, c, d)

/-- **The batch**: the loop, then one invalidation of the address space if a
deferred delete cleared an entry (FL4's `invalidate_asid`, l4v's
`flush_all`, as `performPml4Flush`); the reply is (entries done, error code
or 0). -/
def performFrameBatch (b : Fl4FrameBatchInvocation) : SMonad Z (List Data) := do
  let (done, err, d) ← fbRun b b.entries 0 false
  NonDet.when (d = true) <| flushAll b.vspace b.asid
  return [BitVec.ofNat 64 done, err]

end

end

end Fl4Spec
