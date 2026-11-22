/-
FL4 differences (PORTING.md, "FL4 differences"): **`seL4_X86_TdxControl`**,
Intel TDX attestation, an FL4 extension with no seL4 / l4v counterpart
(FL4 #68; fl4-core `tdx.rs`, `objects.rs`, `arch/x86_64/boot.rs`).
KENTRY-PLAN "tdx3" gives the design.

**The cap** `tdxControlCap` (X64/Structs `ArchCap`): no object, not
physical, not a device; every copy is one region (`archSameRegionAs`,
FL4's `same_region_as`, objects.rs:125), as the ASID control cap; derived
unchanged (FL4's `derive_cap` keeps it), not revocable, finalised with no
action (FL4's `finalise_cap`: `(Null, Null)`), not a valid fault handler.
FL4 places it in a TD guest only, in the root CNode (`init_tdx_control`).

**The invocations** (labels `fl4TdxGetReportLabel` .. `fl4TdxGetQuoteLabel`,
FL4's numbers 91..93), with FL4's checks in FL4's order
(`decodeTdxInvocation`): the platform must have the TD module
(`tdxActive`, else `IllegalOperation`); then

* `GetReport` (8 words of report data, a frame): fewer than 8 words or no
  extra cap `TruncatedMessage`; the frame must be a writable non-device
  4 KiB frame (`tdxReportFrame`, FL4's `report_frame`), else
  `InvalidCapability 1`;
* `ExtendRTMR` (index, 6 words): fewer than 7 words `TruncatedMessage`; an
  index above 3 `InvalidArgument 0`;
* `GetQuote` (length, a frame): no word or no extra cap `TruncatedMessage`;
  the frame must be a writable device 4 KiB / 2 MiB frame
  (`tdxQuoteFrame`) that the platform shares with the VMM (`tdxDmaRam`,
  FL4's `dma_ram`), else `InvalidCapability 1`; the length must be whole
  pages, at least one, within the frame (`tdxQuoteLenOk`), else
  `InvalidArgument 0`;
* any other label `IllegalOperation`.

The perform (`performTdxInvocation`) is the TDCALL: it changes no kernel
object, CSpace, CDT or page table. It returns one status word, which
`handle_invocation`'s shell replies to a Call (`replyFromKernel (0, [w])`:
MR0, the message info, the badge register) before the caller runs again
(FL4's `tdx::reply` after its `TS_RESTART`), and GetReport / GetQuote write
the frame (the TDREPORT, the quote).

**[P] The platform.** Whether the TD module is present (`tdxActive`) and
whether a range is RAM shared with the VMM (`tdxDmaRam`) are properties of
the platform, not of kernel state: opaque constants of the spec (as l4v's
`consts'` machine values), which FL4's arch queries `tdx_active` / `dma_ram`
answer (a platform obligation of the refinement). They decide decode errors,
so they are values, not choices: a decode's error is its only outcome. The
status word and the bytes written into the frame are outputs of the TD
module: the spec takes them nondeterministically (`NonDet.select`, as
`performTestAndClearAccessed` does for the accessed bit). The frame write
changes the machine's memory in the frame's bytes only (`tdxFrameWrite`).

The ported modules are not changed but by the cap's constructor and its
arms (X64/Structs, X64/VSpace, Decode's l4v arch decoder, which never sees
it); the dispatch is `Ext/Invocation`'s `fl4ArchDecodeInvocation` /
`fl4ArchPerformInvocation`.
-/
import Fl4Spec

namespace Fl4Spec

noncomputable section
open Classical

/-- FL4 extension: the label number of `X86TdxControlGetReport`
(`fl4_abi::label`, in the configuration of `fl4FrameBatchLabel`). -/
def fl4TdxGetReportLabel : Nat := 91
/-- FL4 extension: the label number of `X86TdxControlExtendRTMR`. -/
def fl4TdxExtendRtmrLabel : Nat := 92
/-- FL4 extension: the label number of `X86TdxControlGetQuote`. -/
def fl4TdxGetQuoteLabel : Nat := 93

/-- A decoded TDX invocation. -/
inductive Fl4TdxInvocation where
  /-- `GetReport`: the frame and the 8 words of report data. -/
  | getReport (frame : ObjRef) (data : List Data)
  /-- `ExtendRTMR`: the RTMR index and the 6 words of the extension. -/
  | extendRtmr (index : Data) (data : List Data)
  /-- `GetQuote`: the shared frame and the buffer's length. -/
  | getQuote (frame : ObjRef) (len : Data)
deriving Inhabited

/-- FL4's `report_frame`: a writable non-device 4 KiB frame cap. -/
def tdxReportFrame : Cap → Option ObjRef
  | .archObjectCap (.pageCap false p R _ .x64SmallPage _) => if R = vmReadWrite then some p else none
  | _ => none

/-- FL4's `quote_frame` without the platform's sharing check: a writable
device 4 KiB or 2 MiB frame cap, and its size in bytes. -/
def tdxQuoteFrame : Cap → Option (ObjRef × Nat)
  | .archObjectCap (.pageCap true p R _ .x64SmallPage _) => if R = vmReadWrite then some (p, 0x1000) else none
  | .archObjectCap (.pageCap true p R _ .x64LargePage _) => if R = vmReadWrite then some (p, 0x200000) else none
  | _ => none

/-- FL4's `quote_len_ok`: whole pages, at least one, within the frame. -/
def tdxQuoteLenOk (len : Data) (bytes : Nat) : Prop :=
  0x1000 ≤ unat len ∧ unat len % 0x1000 = 0 ∧ unat len ≤ bytes

/-- [P] The platform: the kernel runs in a TD guest with the TD module (FL4's
`tdx_active`). -/
opaque tdxActive : Bool

/-- [P] The platform: the `bytes` bytes at `frame` are RAM shared with the VMM
(FL4's `dma_ram`). -/
opaque tdxDmaRam : ObjRef → Nat → Bool

section
variable {Z : Type} [StateExt Z]

/-- The decode (module docstring). -/
def decodeTdxInvocation (label : Data) (args : List Data) (extraCaps : List (Cap × CslotPtr)) :
    SEMonad Z Fl4TdxInvocation := do
  NonDetE.unlessE tdxActive <| NonDetE.throwError .illegalOperation
  if dataToNat label = fl4TdxGetReportLabel then do
    NonDetE.whenE (args.length < 8 ∨ extraCaps = []) <| NonDetE.throwError .truncatedMessage
    match tdxReportFrame (the extraCaps[0]?).1 with
    | some p => NonDetE.returnOk (.getReport p (args.take 8))
    | none => NonDetE.throwError (.invalidCapability 1)
  else if dataToNat label = fl4TdxExtendRtmrLabel then do
    NonDetE.whenE (args.length < 7) <| NonDetE.throwError .truncatedMessage
    let index := the args[0]?
    NonDetE.whenE (unat index > 3) <| NonDetE.throwError (.invalidArgument 0)
    NonDetE.returnOk (.extendRtmr index ((args.drop 1).take 6))
  else if dataToNat label = fl4TdxGetQuoteLabel then do
    NonDetE.whenE (args.length < 1 ∨ extraCaps = []) <| NonDetE.throwError .truncatedMessage
    match tdxQuoteFrame (the extraCaps[0]?).1 with
    | some (p, bytes) => do
      NonDetE.unlessE (tdxDmaRam p bytes) <| NonDetE.throwError (.invalidCapability 1)
      let len := the args[0]?
      NonDetE.unlessE (tdxQuoteLenOk len bytes) <| NonDetE.throwError (.invalidArgument 0)
      NonDetE.returnOk (.getQuote p len)
    | none => NonDetE.throwError (.invalidCapability 1)
  else NonDetE.throwError .illegalOperation

end

/-- [P] The TD module writes `n` bytes of the frame at `base`: any bytes
there, every other byte and every other machine field kept. -/
def tdxFrameWrite (base : Word) (n : Nat) : MachineMonad Unit := do
  let m ← NonDet.gets MachineState.underlyingMemory
  let m' ← NonDet.select {m' : Word64 → Word8 | ∀ p, (¬ ∃ i < n, p = base + BitVec.ofNat 64 i) → m' p = m p}
  NonDet.modify fun ms => { ms with underlyingMemory := m' }

section
variable {Z : Type} [StateExt Z]

/-- [P] The TDCALL's status word: a platform output. -/
def tdxStatus : SMonad Z (List Data) := do
  let w ← NonDet.select Set.univ
  return [w]

/-- The perform (module docstring): the TDCALL. -/
def performTdxInvocation : Fl4TdxInvocation → SMonad Z (List Data)
  | .getReport frame _ => do
    doMachineOp (tdxFrameWrite frame 0x1000)
    tdxStatus
  | .extendRtmr _ _ => tdxStatus
  | .getQuote frame len => do
    doMachineOp (tdxFrameWrite frame (unat len))
    tdxStatus

end

end

end Fl4Spec
