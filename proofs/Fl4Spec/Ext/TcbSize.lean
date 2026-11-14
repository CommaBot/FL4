/-
FL4 difference (PORTING.md, "FL4 differences"): **TCB objects are 4 KiB**.

l4v X64 has `tcb_bits = 11` (Arch_Structs_A.X64_A.tcb_bits, ported unchanged in
`Fl4Spec/X64/Structs.lean`). FL4 TCBs are 4 KiB (`fl4_abi::consts::bits::TCB =
12`, crates/fl4-core layout.rs `tcb`): the extra space holds FL4's FPU area,
debug name and l4h fields. So FL4 retypes a TCB with `obj_bits_api TCBObject _
= 12`, which changes the alignment of the new TCBs, the `NotEnoughMemory`
check and the new free index.

The ported modules are not changed. Instead this module gives the untyped
functions that use `obj_bits_api` with the object-size function as a
parameter (`decodeUntypedInvocationWith`, `retypeRegionWith`,
`invokeUntypedWith`, copies of `decode_untyped_invocation`,
`retype_region`, `invoke_untyped` with only `obj_bits_api` replaced); the
port is the instance `objBitsApi` (`*_With_objBitsApi`, by `rfl`), FL4's is
`fl4ObjBitsApi`, which differs from `objBitsApi` only on `TCBObject`.
-/
import Fl4Spec.Decode

namespace Fl4Spec

noncomputable section
open Classical

/-- FL4: `seL4_TCBBits` is 12 (4 KiB TCBs). -/
def fl4TcbBits : Nat := 12

/-- FL4's `obj_bits` (only the TCB differs). -/
def fl4ObjBits : KernelObject → Nat
  | .tcb _ => fl4TcbBits
  | ko => objBits ko

/-- FL4's `obj_bits_api` (only `TCBObject` differs). -/
def fl4ObjBitsApi (type : ApiObjectType) (objSizeBits : Nat) : Nat :=
  match type with
  | .tcbObject => fl4TcbBits
  | t => objBitsApi t objSizeBits

theorem fl4ObjBitsApi_of_ne {t : ApiObjectType} (h : t ≠ .tcbObject) (n : Nat) :
    fl4ObjBitsApi t n = objBitsApi t n := by
  cases t <;> first | exact absurd rfl h | rfl

section
variable {Z : Type} [StateExt Z]

/-- `decode_untyped_invocation` with `obj_bits_api` as a parameter. -/
def decodeUntypedInvocationWith (bitsApi : ApiObjectType → Nat → Nat) (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap)
    (excaps : List Cap) : SEMonad Z UntypedInvocation := do
  NonDetE.unlessE (genInvocationType label = .untypedRetype) <| NonDetE.throwError .illegalOperation
  NonDetE.whenE (args.length < 6) <| NonDetE.throwError .truncatedMessage
  NonDetE.whenE (excaps.length = 0) <| NonDetE.throwError .truncatedMessage
  let rootCap ← NonDetE.returnOk <| the excaps[0]?
  let newType ← dataToObjType (the args[0]?)

  let userObjSize ← NonDetE.returnOk <| dataToNat (the args[1]?)
  let objectSize ← NonDetE.returnOk (bitsApi newType userObjSize)
  NonDetE.unlessE (userObjSize < wordBits ∧ objectSize ≤ untypedMaxBits) <|
    NonDetE.throwError (.rangeError 0 (BitVec.ofNat 64 untypedMaxBits))
  NonDetE.whenE (newType = .capTableObject ∧ userObjSize = 0) <|
    NonDetE.throwError (.invalidArgument 1)
  NonDetE.whenE (newType = .untyped ∧ userObjSize < untypedMinBits) <|
    NonDetE.throwError (.invalidArgument 1)
  NonDetE.whenE (newType = .schedContextObject ∧ userObjSize < minSchedContextBits) <|
    NonDetE.throwError (.invalidArgument 1)
  let nodeIndex ← NonDetE.returnOk <| dataToCptr (the args[2]?)
  let nodeDepth ← NonDetE.returnOk <| dataToNat (the args[3]?)

  let nodeCap ← (if nodeDepth = 0
        then NonDetE.returnOk rootCap
        else do
            let nodeSlot ← lookupTargetSlot
                rootCap nodeIndex nodeDepth
            NonDetE.liftE <| getCap nodeSlot : SEMonad Z Cap)

  if isCnodeCap nodeCap
        then NonDetE.returnOk ()
        else NonDetE.throwError <| .failedLookup false <| .missingCapability nodeDepth

  let nodeOffset ← NonDetE.returnOk <| dataToNat (the args[4]?)
  let nodeWindow ← NonDetE.returnOk <| dataToNat (the args[5]?)
  let radixBits ← NonDetE.returnOk <| bitsOf nodeCap
  let nodeSize ← NonDetE.returnOk (2 ^ radixBits)

  NonDetE.whenE (nodeOffset < 0 ∨ nodeOffset > nodeSize - 1) <|
    NonDetE.throwError <| .rangeError 0 (BitVec.ofNat 64 (nodeSize - 1))

  NonDetE.whenE (nodeWindow < 1 ∨ nodeWindow > unat retypeFanOutLimit) <|
    NonDetE.throwError <| .rangeError 1 retypeFanOutLimit

  NonDetE.whenE (nodeWindow < 1 ∨ nodeWindow > nodeSize - nodeOffset) <|
    NonDetE.throwError <| .rangeError 1 (BitVec.ofNat 64 (nodeSize - nodeOffset))

  let oref ← NonDetE.returnOk <| objRefOf nodeCap
  let offsets ← NonDetE.returnOk <| (List.range' nodeOffset
                           (nodeOffset + nodeWindow - nodeOffset)).map (natToCref radixBits)
  let slots ← NonDetE.returnOk <| offsets.map fun cref => (oref, cref)

  NonDetE.mapMEx ensureEmpty slots

  let reset ← NonDetE.liftE <| constOnFailure false <| (do
    ensureNoChildren slot
    NonDetE.returnOk true : SEMonad Z Bool)

  let freeIndex ← NonDetE.returnOk (if reset then 0 else freeIndexOf cap)
  let freeRef ← NonDetE.returnOk (getFreeRef (objRefOf cap) freeIndex)
  let alignedFreeRef ← NonDetE.returnOk (alignUp freeRef objectSize)
  let untypedFreeBytes ← NonDetE.returnOk (objSize cap - BitVec.ofNat 64 freeIndex)

  let maxCount ← NonDetE.returnOk (untypedFreeBytes >>> objectSize)
  NonDetE.whenE (unat maxCount < nodeWindow) <|
        NonDetE.throwError <| .notEnoughMemory <| untypedFreeBytes

  let notFrame ← NonDetE.returnOk (¬isFrameType newType)
  let (ptr, isDevice) ← match cap with
                        | .untypedCap dev p _n _f => NonDetE.returnOk (p, dev)
                        | _ => NonDetE.liftE NonDet.fail
  NonDetE.whenE (isDevice ∧ notFrame ∧ newType ≠ .untyped) <|
           NonDetE.throwError <| .invalidArgument 1
  NonDetE.returnOk <| .retype slot reset ptr alignedFreeRef newType userObjSize slots isDevice

theorem decodeUntypedInvocationWith_objBitsApi :
    decodeUntypedInvocationWith (Z := Z) objBitsApi = decodeUntypedInvocation := rfl

/-- FL4's `decode_untyped_invocation`. -/
abbrev fl4DecodeUntypedInvocation := decodeUntypedInvocationWith (Z := Z) fl4ObjBitsApi

/-- `retype_region` with `obj_bits_api` as a parameter. -/
def retypeRegionWith (bitsApi : ApiObjectType → Nat → Nat) (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) :
    SMonad Z (List ObjRef) := do
  let objSize ← pure (2 ^ bitsApi type oBits)
  let ptrs ← pure ((List.range numObjects).map fun p => ptrAdd ptr (p * objSize))
  NonDet.when (type ≠ .untyped) (do
    let kh ← NonDet.gets fun s : State Z => s.kheap
    let cd ← NonDet.gets fun s : State Z => s.curDomain
    let kh' ← pure (ptrs.foldr (fun p kh => Function.update kh p (some (defaultObject type dev oBits cd))) kh)
    NonDet.modify fun s => { s with kheap := kh' })
  return ptrs

theorem retypeRegionWith_objBitsApi : retypeRegionWith (Z := Z) objBitsApi = retypeRegion := rfl

/-- `invoke_untyped` with `obj_bits_api` as a parameter. -/
def invokeUntypedWith (bitsApi : ApiObjectType → Nat → Nat) (ui : UntypedInvocation) : PMonad Z Unit :=
  match ui with
  | .retype srcSlot reset base retypeBase newType objSz slots isDevice => do
    NonDetE.whenE reset (resetUntypedCap srcSlot)
    NonDetE.liftE (do
      let cap ← getCap srcSlot
      -- Update the untyped cap to track the amount of space used.
      let totalObjectSize ← pure (BitVec.ofNat 64 slots.length <<< bitsApi newType objSz)
      let freeRef ← pure (retypeBase + totalObjectSize)
      setCap (.untypedCap isDevice base (bitsOf cap) (unat (freeRef - base))) srcSlot
      -- Create new objects.
      let orefs ← retypeRegionWith bitsApi retypeBase slots.length objSz newType isDevice
      initArchObjects newType isDevice retypeBase slots.length objSz orefs
      NonDet.mapMx (createCap newType objSz srcSlot isDevice) (slots.zip orefs))

theorem invokeUntypedWith_objBitsApi : invokeUntypedWith (Z := Z) objBitsApi = invokeUntyped := rfl

/-- FL4's `invoke_untyped`. -/
abbrev fl4InvokeUntyped := invokeUntypedWith (Z := Z) fl4ObjBitsApi

end

end

end Fl4Spec
