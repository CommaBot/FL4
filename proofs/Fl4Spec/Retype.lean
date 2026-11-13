/-
Retyping, untyped invocations, and the x86-64 cap deletion hooks (MCS).

Ports, in theory order:
- `spec/abstract/X64/ArchRetype_A`;
- `spec/abstract/X64/ArchIpcCancel_A`;
- `spec/abstract/Retype_A`.

`ArchIpcCancel_A` imports only CSpaceAcc_A (Sporadic_A on RISCV64 `rt`); it
sits here because Retype_A is the next theory that needs it in FL4's chain.
-/
import Fl4Spec.CSpaceAcc
import Fl4Spec.Invocations

namespace Fl4Spec

open Classical

noncomputable section

/-! ## ArchRetype_A -/

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchRetype_A.X64_A.reserve_region: a placeholder (the spec may later
tag kernel data regions in memory). -/
def reserveRegion (_ptr : ObjRef) (_byteLength : Nat) (_isKernel : Bool) : SMonad Z Unit :=
  return ()

/-- l4v: ArchRetype_A.X64_A.init_arch_objects: initialise
architecture-specific objects. -/
def initArchObjects (newType : ApiObjectType) (_isDevice : Bool) (_ptr : ObjRef) (_numObjects : Nat)
    (_objSz : Nat) (refs : List ObjRef) : SMonad Z Unit :=
  NonDet.when (newType = .archObject .pml4Obj) (NonDet.mapMx copyGlobalMappings refs)

/-- l4v: ArchRetype_A.X64_A.arch_post_reset_untyped: nothing to do after
resetting an untyped region on x86. -/
def archPostResetUntyped (_isDevice : Bool) (_sz : Nat) : SMonad Z Unit := return ()

end

/-- l4v: ArchRetype_A.X64_A.empty_context. -/
def emptyContext : UserContext := ⟨fun _ => 0, fun _ => 0⟩

/-- l4v: ArchRetype_A.X64_A.init_arch_tcb. -/
def initArchTcb : ArchTcb := { tcbContext := emptyContext, tcbCurFpu := false }

/-! ## ArchIpcCancel_A -/

section
variable {Z : Type} [StateExt Z]

/-- l4v: ArchIpcCancel_A.X64_A.set_ioport_mask. -/
def setIoportMask (f l : IoPort) (val : Bool) : SMonad Z Unit := do
  let allocatedPorts ← NonDet.gets fun s : State Z => s.archState.x64AllocatedIoPorts
  let ap' ← pure (fun p => if p ≥ f ∧ p ≤ l then val else allocatedPorts p)
  NonDet.modify fun s => { s with archState := { s.archState with x64AllocatedIoPorts := ap' } }

/-- l4v: ArchIpcCancel_A.X64_A.free_ioport_range. -/
def freeIoportRange (f l : IoPort) : SMonad Z Unit := setIoportMask f l false

/-- l4v: ArchIpcCancel_A.X64_A.arch_post_cap_deletion: actions to be taken
after a cap is deleted. -/
def archPostCapDeletion (ac : ArchCap) : SMonad Z Unit :=
  match ac with
  | .ioPortCap f l => freeIoportRange f l
  | _ => return ()

end

/-- l4v: ArchIpcCancel_A.X64_A.arch_gen_obj_ref: arch-specific generic
object references not covered by the generic ones. -/
inductive ArchGenObjRef where
  | ioPortRef (p : IoPort)
deriving DecidableEq, Repr, Inhabited

/-- l4v: ArchIpcCancel_A.X64_A.arch_gen_obj_refs. -/
def archGenObjRefs (ac : ArchCap) : Set ArchGenObjRef :=
  match ac with
  | .ioPortCap f _ => ArchGenObjRef.ioPortRef '' {f}
  | _ => ∅

/-- l4v: ArchIpcCancel_A.X64_A.arch_cap_cleanup_opt. -/
def archCapCleanupOpt (ac : ArchCap) : Cap :=
  match ac with
  | .ioPortCap f l => .archObjectCap (.ioPortCap f l)
  | _ => .nullCap

/-! ## Retype_A: creating caps -/

/-- l4v: Retype_A.default_cap: the original capability created with a new
object of a given type, address and size. -/
def defaultCap : ApiObjectType → ObjRef → Nat → Bool → Cap
  | .capTableObject, oref, s, _ => .cnodeCap oref s []
  | .untyped, oref, s, dev => .untypedCap dev oref s 0
  | .tcbObject, oref, _, _ => .threadCap oref
  | .endpointObject, oref, _, _ => .endpointCap oref 0 Set.univ
  | .notificationObject, oref, _, _ => .notificationCap oref 0 {.allowRead, .allowWrite}
  | .schedContextObject, oref, s, _ => .schedContextCap oref (s - minSchedContextBits)
  | .replyObject, oref, _, _ => .replyCap oref {.allowGrant, .allowWrite}
  | .archObject aobj, oref, s, dev => .archObjectCap (archDefaultCap aobj oref s dev)

section
variable {Z : Type} [StateExt Z]

/-- l4v: Retype_A.create_cap: create and install a new capability to a newly
created object. -/
def createCap (type : ApiObjectType) (bits : Nat) (untyped : CslotPtr) (isDevice : Bool) :
    CslotPtr × ObjRef → SMonad Z Unit := fun (dest, oref) => do
  let destP ← NonDet.gets fun s : State Z => s.cdt dest
  let cdt ← NonDet.gets fun s : State Z => s.cdt
  setCdt (Function.update cdt dest (some untyped))
  doExtendedOp (createCapExt untyped dest destP)
  setOriginal dest true
  setCap (defaultCap type oref bits isDevice) dest

end

/-! ## Retype_A: creating objects -/

/-- l4v: Retype_A.empty_cnode: the contents of an empty CNode. -/
def emptyCnode (bits : Nat) : CnodeContents := fun x => if x.length = bits then some .nullCap else none

/-- l4v: Retype_A.default_object: the initial state of a new object. -/
def defaultObject (api : ApiObjectType) (dev : Bool) (n : Nat) (d : Domain) : KernelObject :=
  match api with
  | .untyped => undefined
  | .capTableObject => .cnode n (emptyCnode n)
  | .tcbObject => .tcb (defaultTcb d)
  | .endpointObject => .endpoint defaultEp
  | .notificationObject => .notification defaultNotification
  | .schedContextObject => .schedContext defaultSchedContext (n - minSchedContextBits)
  | .replyObject => .reply defaultReply
  | .archObject aobj => .archObj (defaultArchObject aobj dev n)

/-- l4v: Retype_A.obj_bits_api: the size in bits of the objects created
for a given type and size. -/
def objBitsApi (type : ApiObjectType) (objSizeBits : Nat) : Nat :=
  match type with
  | .untyped => objSizeBits
  | .capTableObject => objSizeBits + slotBits
  | .tcbObject => objBits (.tcb (defaultTcb defaultDomain))
  | .endpointObject => objBits (.endpoint undefined)
  | .notificationObject => objBits (.notification undefined)
  | .schedContextObject => objSizeBits
  | .replyObject => objBits (.reply defaultReply)
  | .archObject aobj => objBits (.archObj (defaultArchObject aobj false objSizeBits))

/-! ## Retype_A: the main retype implementation -/

section
variable {Z : Type} [StateExt Z]

/-- l4v: Retype_A.retype_region: create `numObjects` objects from `ptr`,
returning the pointers to them. -/
def retypeRegion (ptr : ObjRef) (numObjects : Nat) (oBits : Nat) (type : ApiObjectType) (dev : Bool) :
    SMonad Z (List ObjRef) := do
  let objSize ← pure (2 ^ objBitsApi type oBits)
  let ptrs ← pure ((List.range numObjects).map fun p => ptrAdd ptr (p * objSize))
  NonDet.when (type ≠ .untyped) (do
    let kh ← NonDet.gets fun s : State Z => s.kheap
    let cd ← NonDet.gets fun s : State Z => s.curDomain
    let kh' ← pure (ptrs.foldr (fun p kh => Function.update kh p (some (defaultObject type dev oBits cd))) kh)
    NonDet.modify fun s => { s with kheap := kh' })
  return ptrs

end

/-! ## Retype_A: invoking untyped capabilities -/

/-- l4v: Retype_A.detype: remove the objects in a region from the heap. -/
def detype {Z : Type} (S : Set ObjRef) (s : State Z) : State Z :=
  { s with kheap := fun x => if x ∈ S then none else s.kheap x }

section
variable {Z : Type} [StateExt Z]

/-- l4v: Retype_A.delete_objects: delete the objects in a region. -/
def deleteObjects (ptr : Word) (bits : Nat) : SMonad Z Unit := do
  doMachineOp (freeMemory ptr bits)
  NonDet.modify (detype {x | ptr ≤ x ∧ x ≤ ptr + 2 ^ bits - 1})

end

/-- l4v: Retype_A.get_free_ref. -/
def getFreeRef (base : ObjRef) (freeIndex : Nat) : ObjRef := base + BitVec.ofNat 64 freeIndex

/-- l4v: Retype_A.get_free_index. -/
def getFreeIndex (base free : ObjRef) : Nat := unat (free - base)

/-- l4v: Retype_A.is_device_untyped_cap (`primrec (nonexhaustive)`). -/
def isDeviceUntypedCap : Cap → Bool
  | .untypedCap isdev _ _ _ => isdev
  | _ => undefined

section
variable {Z : Type} [StateExt Z]

/-- l4v: Retype_A.reset_untyped_cap: clear the region of an untyped cap
progressively, moving its free index back to the start of the cleared part
each time, with preemption points in between. -/
def resetUntypedCap (srcSlot : CslotPtr) : PMonad Z Unit := do
  let cap ← NonDetE.liftE (getCap srcSlot)
  let sz ← NonDetE.returnOk (bitsOf cap)
  let base ← NonDetE.returnOk (objRefOf cap)
  if freeIndexOf cap = 0
  then NonDetE.returnOk ()
  else do
    NonDetE.liftE (deleteObjects base sz)
    let dev ← NonDetE.returnOk (isDeviceUntypedCap cap)
    if dev ∨ sz < resetChunkBits
    then NonDetE.liftE (do
      NonDet.unless dev (doMachineOp (clearMemory base (2 ^ sz)))
      setCap (.untypedCap dev base sz 0) srcSlot)
    else
      NonDetE.mapMEx (fun i => do
          NonDetE.liftE (doMachineOp
            (clearMemory (base + (BitVec.ofNat 64 i <<< resetChunkBits)) (2 ^ resetChunkBits)))
          NonDetE.liftE (setCap (.untypedCap dev base sz (i * 2 ^ resetChunkBits)) srcSlot)
          preemptionPoint)
        ((List.range (2 ^ (sz - resetChunkBits))).filter
          (fun i => decide (i * 2 ^ resetChunkBits < freeIndexOf cap))).reverse
    NonDetE.liftE (archPostResetUntyped dev sz)

/-- l4v: Retype_A.invoke_untyped: clear the region if requested, create new
objects of the requested type, initialise them and install capabilities to
them. -/
def invokeUntyped (ui : UntypedInvocation) : PMonad Z Unit :=
  match ui with
  | .retype srcSlot reset base retypeBase newType objSz slots isDevice => do
    NonDetE.whenE reset (resetUntypedCap srcSlot)
    NonDetE.liftE (do
      let cap ← getCap srcSlot
      -- Update the untyped cap to track the amount of space used.
      let totalObjectSize ← pure (BitVec.ofNat 64 slots.length <<< objBitsApi newType objSz)
      let freeRef ← pure (retypeBase + totalObjectSize)
      setCap (.untypedCap isDevice base (bitsOf cap) (unat (freeRef - base))) srcSlot
      -- Create new objects.
      let orefs ← retypeRegion retypeBase slots.length objSz newType isDevice
      initArchObjects newType isDevice retypeBase slots.length objSz orefs
      NonDet.mapMx (createCap newType objSz srcSlot isDevice) (slots.zip orefs))

end

end

end Fl4Spec
