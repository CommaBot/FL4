/-
The abstract model of CSpace: cap manipulation, address resolution, cap
transfer, deletion, revocation, insertion and CNode invocations (MCS).

Ports `spec/abstract/CSpace_A`. Its `arch_requalify_consts` refer to
`Fl4Spec.KHeap` and `Fl4Spec.X64.VSpace`.

Recursion:
- `resolve_address_bits'` terminates (Isabelle proves it with the measure
  `length cref`); it is well-founded recursion on the same measure here. Its
  `'z itself` argument only fixes the state type in Isabelle and is dropped.
- `rec_del` and `cap_revoke` are Isabelle `function`s without termination
  proofs (partial; l4v proves their termination on reachable states
  separately). Each is the least fixed point (`NonDet.lfp`) of its defining
  functional `recDelF`/`capRevokeF`, a transliteration of the equations with
  the recursive calls as a parameter. See `NonDet.lfp` and PORTING.md.
-/
import Fl4Spec.SchedContext

namespace Fl4Spec

open Classical

noncomputable section

/-! ## Basic capability manipulation -/

/-- l4v: CSpace_A.data_to_rights: a set of rights from a user data word. -/
def dataToRights (data : Data) : CapRights :=
  let w := dataTo16 data
  {x | match x with
    | .allowWrite => testBit w 0 = true
    | .allowRead => testBit w 1 = true
    | .allowGrant => testBit w 2 = true
    | .allowGrantReply => testBit w 3 = true}

section
variable {Z : Type} [StateExt Z]

/-- l4v: CSpace_A.ensure_no_children: the cap in a slot is not the parent of
any other cap. -/
def ensureNoChildren (cslotPtr : CslotPtr) : SEMonad Z Unit := do
  let cdt ← NonDetE.liftE (NonDet.gets fun s : State Z => s.cdt)
  NonDetE.whenE (∃ c, cdt c = some cslotPtr) (NonDetE.throwError .revokeFirst)

end

/-- l4v: CSpace_A.max_free_index. -/
def maxFreeIndex (magnitudeBits : Nat) : Nat := 2 ^ magnitudeBits

/-- l4v: CSpace_A.free_index_update. -/
def freeIndexUpdate (g : Nat → Nat) (cap : Cap) : Cap :=
  match cap with
  | .untypedCap dev ref sz f => .untypedCap dev ref sz (g f)
  | _ => cap

/-- l4v: CSpace_A.untyped_sz_bits (`primrec (nonexhaustive)`). -/
def untypedSzBits : Cap → Nat
  | .untypedCap _ _ sz _ => sz
  | _ => undefined

/-- l4v: CSpace_A.max_free_index_update (`abbreviation`,
`cap⦇free_index := max_free_index (untyped_sz_bits cap)⦈`). -/
abbrev maxFreeIndexUpdate (cap : Cap) : Cap :=
  freeIndexUpdate (fun _ => maxFreeIndex (untypedSzBits cap)) cap

section
variable {Z : Type} [StateExt Z]

/-- l4v: CSpace_A.set_untyped_cap_as_full. -/
def setUntypedCapAsFull (srcCap newCap : Cap) (srcSlot : ObjRef × List Bool) : SMonad Z Unit :=
  if isUntypedCap srcCap ∧ isUntypedCap newCap ∧
     objRefOf srcCap = objRefOf newCap ∧
     capBitsUntyped srcCap = capBitsUntyped newCap
  then setCap (maxFreeIndexUpdate srcCap) srcSlot
  else return ()

/-- l4v: CSpace_A.derive_cap: derive a cap into a form in which it can be
copied. -/
def deriveCap (slot : CslotPtr) (cap : Cap) : SEMonad Z Cap :=
  match cap with
  | .archObjectCap c => archDeriveCap c
  | .untypedCap _ _ _ _ => do ensureNoChildren slot; NonDetE.returnOk cap
  | .zombie _ _ _ => NonDetE.returnOk .nullCap
  | .irqControlCap => NonDetE.returnOk .nullCap
  | _ => NonDetE.returnOk cap

end

/-- l4v: CSpace_A.update_cap_data: transform a cap on request from a user
thread; `preserve` disallows changes that would invalidate CDT
relationships. `size guard''` is the word length of `guard''` (64). -/
def updateCapData (preserve : Bool) (w : Data) (cap : Cap) : Cap :=
  if isEpCap cap then
    if capEpBadge cap = 0 ∧ ¬preserve then badgeUpdate w cap else .nullCap
  else if isNtfnCap cap then
    if capEpBadge cap = 0 ∧ ¬preserve then badgeUpdate w cap else .nullCap
  else if isCnodeCap cap then
    let (oref, bits, _guard) := theCnodeCap cap
    let (guardSize', guard'') := updateCnodeCapData w
    let guard' := (toBl guard'').drop (64 - guardSize')
    if guardSize' + bits > wordBits then .nullCap else .cnodeCap oref bits guard'
  else if isArchCap cap then
    archUpdateCapData preserve w cap.theArchCap
  else
    cap

/-! ## Resolving capability references -/

section
variable {Z : Type} [StateExt Z]

/-- l4v: CSpace_A.resolve_address_bits': look up a capability address by
walking the CNodes until all address bits are used or there are no further
CNodes. -/
def resolveAddressBits' (p : Cap × CapRef) : LFMonad Z (CslotPtr × CapRef) :=
  match p.1 with
  | .cnodeCap oref radixBits guard =>
    if _h0 : radixBits + guard.length = 0 then
      NonDetE.liftE NonDet.fail -- nothing is translated: table broken
    else do
      NonDetE.whenE (¬guard <+: p.2)
        -- guard does not match
        (NonDetE.throwError (.guardMismatch p.2.length guard))
      NonDetE.whenE (p.2.length < radixBits + guard.length)
        -- not enough bits to resolve: table malformed
        (NonDetE.throwError (.depthMismatch p.2.length (radixBits + guard.length)))
      let offset ← NonDetE.returnOk ((p.2.drop guard.length).take radixBits)
      let rest := p.2.drop (radixBits + guard.length)
      if _hr : rest = [] then
        NonDetE.returnOk ((oref, offset), [])
      else do
        let nextCap ← NonDetE.liftE (getCap (oref, offset))
        if isCnodeCap nextCap then
          resolveAddressBits' (nextCap, rest)
        else
          NonDetE.returnOk ((oref, offset), rest)
  | _ => NonDetE.throwError .invalidRoot
termination_by p.2.length
decreasing_by
  simp only [List.length_drop]
  have : p.2.length ≠ 0 := by
    intro h; apply _hr; simp [rest, List.drop_eq_nil_of_le, h]
  omega

/-- l4v: CSpace_A.resolve_address_bits. -/
def resolveAddressBits : Cap × CapRef → LFMonad Z (CslotPtr × CapRef) := resolveAddressBits'

/-- l4v: CSpace_A.lookup_slot_for_thread. -/
def lookupSlotForThread (thread : ObjRef) (cref : CapRef) : LFMonad Z (CslotPtr × CapRef) := do
  let tcb ← NonDetE.liftE (NonDet.getsThe (getTcb thread))
  resolveAddressBits (tcb.tcbCtable, cref)

/-- l4v: CSpace_A.lookup_cap_and_slot. -/
def lookupCapAndSlot (thread : ObjRef) (cptr : CapRef) : LFMonad Z (Cap × CslotPtr) := do
  let (slot, _cr) ← lookupSlotForThread thread cptr
  let cap ← NonDetE.liftE (getCap slot)
  NonDetE.returnOk (cap, slot)

/-- l4v: CSpace_A.lookup_cap. -/
def lookupCap (thread : ObjRef) (ref : CapRef) : LFMonad Z Cap := do
  let (ref', _) ← lookupSlotForThread thread ref
  NonDetE.liftE (getCap ref')

/-- l4v: CSpace_A.lookup_slot_for_cnode_op. -/
def lookupSlotForCnodeOp (isSource : Bool) (croot : Cap) (ptr : CapRef) (depth : Nat) :
    SEMonad Z CslotPtr :=
  if isCnodeCap croot then do
    NonDetE.whenE (depth < 1 ∨ depth > wordBits) <|
      NonDetE.throwError (.rangeError 1 (BitVec.ofNat 64 wordBits))
    lookupErrorOnFailure isSource (do
      let ptrbitsForDepth ← NonDetE.returnOk (ptr.drop (ptr.length - depth))
      let (slot, rem) ← resolveAddressBits (croot, ptrbitsForDepth)
      match rem with
      | [] => NonDetE.returnOk slot
      | _ => NonDetE.throwError (.depthMismatch rem.length 0))
  else
    NonDetE.throwError (.failedLookup isSource .invalidRoot)

/-- l4v: CSpace_A.lookup_source_slot. -/
def lookupSourceSlot : Cap → CapRef → Nat → SEMonad Z CslotPtr := lookupSlotForCnodeOp true

/-- l4v: CSpace_A.lookup_target_slot. -/
def lookupTargetSlot : Cap → CapRef → Nat → SEMonad Z CslotPtr := lookupSlotForCnodeOp false

/-- l4v: CSpace_A.lookup_pivot_slot. -/
def lookupPivotSlot : Cap → CapRef → Nat → SEMonad Z CslotPtr := lookupSlotForCnodeOp true

/-! ## Transferring capabilities -/

/-- l4v: CSpace_A.captransfer_from_words. -/
def captransferFromWords (ptr : Word) : SMonad Z CapTransfer := do
  let w0 ← doMachineOp (loadWord ptr)
  let w1 ← doMachineOp (loadWord (ptr + BitVec.ofNat 64 wordSize))
  let w2 ← doMachineOp (loadWord (ptr + 2 * BitVec.ofNat 64 wordSize))
  return { ctReceiveRoot := dataToCptr w0,
           ctReceiveIndex := dataToCptr w1,
           ctReceiveDepth := w2 }

/-- l4v: CSpace_A.load_cap_transfer. -/
def loadCapTransfer (buffer : ObjRef) : SMonad Z CapTransfer := do
  let offset ← pure (msgMaxLength + msgMaxExtraCaps + 2)
  captransferFromWords (buffer + BitVec.ofNat 64 offset * BitVec.ofNat 64 wordSize)

/-- l4v: CSpace_A.get_receive_slots. -/
def getReceiveSlots : ObjRef → Option ObjRef → SMonad Z (List CslotPtr)
  | thread, some buffer => do
    let ct ← loadCapTransfer buffer
    emptyOnFailure (do
      let cnode ← unifyFailure (lookupCap thread ct.ctReceiveRoot)
      let slot ← unifyFailure (lookupTargetSlot cnode ct.ctReceiveIndex (unat ct.ctReceiveDepth))
      let cap ← NonDetE.liftE (getCap slot)
      NonDetE.whenE (cap ≠ .nullCap) (NonDetE.throwError ())
      NonDetE.returnOk [slot])
  | _, none => return []

/-- l4v: CSpace_A.fast_finalise: finalise a cap that can be finalised
immediately (a simplified `finalise_cap`). -/
def fastFinalise : Cap → Bool → SMonad Z Unit
  | .nullCap, _ => return ()
  | .replyCap r _, final =>
      NonDet.when final <| do
        let tptr ← getReplyTcb r
        match tptr with
        | none => return ()
        | some tp => do
          let state ← getThreadState tp
          match state with
          | .blockedOnReply r => replyRemove tp r
          | _ => cancelIpc tp
  | .endpointCap r _ _, final => NonDet.when final <| cancelAllIpc r
  | .notificationCap r _ _, final =>
      NonDet.when final <| do
        schedContextMaybeUnbindNtfn r
        unbindMaybeNotification r
        cancelAllSignals r
  | _, _ => NonDet.fail

/-- l4v: CSpace_A.cap_delete_one: delete a cap that fast finalisation
suffices for. -/
def capDeleteOne (slot : CslotPtr) : SMonad Z Unit := do
  let cap ← getCap slot
  NonDet.unless (cap = .nullCap) <| do
    let final ← isFinalCap cap
    fastFinalise cap final
    emptySlot slot .nullCap

end

/-! ## Revoking and deleting capabilities -/

/-- l4v: CSpace_A.long_running_delete: deleting the final cap to these
objects is a long-running operation. -/
def longRunningDelete (cap : Cap) : Bool :=
  match cap with
  | .cnodeCap _ _ _ => true
  | .zombie _ _ _ => true
  | .threadCap _ => true
  | _ => false

section
variable {Z : Type} [StateExt Z]

/-- l4v: CSpace_A.slot_cap_long_running_delete. -/
def slotCapLongRunningDelete (slot : CslotPtr) : SMonad Z Bool := do
  let cap ← getCap slot
  match cap with
  | .nullCap => return false
  | _ => do
    let final ← isFinalCap cap
    return (final && longRunningDelete cap)

/-- l4v: CSpace_A.cap_swap: swap the contents of two slots; the cap
arguments are the new caps (they may be transformed in the swap). -/
def capSwap (cap1 : Cap) (slot1 : CslotPtr) (cap2 : Cap) (slot2 : CslotPtr) : SMonad Z Unit := do
  setCap cap2 slot1
  setCap cap1 slot2
  let slot1P ← NonDet.gets fun s : State Z => s.cdt slot1
  let slot2P ← NonDet.gets fun s : State Z => s.cdt slot2
  let cdt ← NonDet.gets fun s : State Z => s.cdt
  -- update children:
  let cdt' ← pure (fun n => if cdt n = some slot1 then some slot2
                            else if cdt n = some slot2 then some slot1
                            else cdt n)
  -- update parents:
  setCdt (Function.update (Function.update cdt' slot1 (cdt' slot2)) slot2 (cdt' slot1))
  doExtendedOp (capSwapExt slot1 slot2 slot1P slot2P)
  let isOriginal ← NonDet.gets fun s : State Z => s.isOriginalCap
  setOriginal slot1 (isOriginal slot2)
  setOriginal slot2 (isOriginal slot1)

/-- l4v: CSpace_A.cap_move: move a cap (possibly transformed) to another
slot. -/
def capMove (newCap : Cap) (srcSlot destSlot : CslotPtr) : SMonad Z Unit := do
  setCap newCap destSlot
  setCap .nullCap srcSlot
  let srcP ← NonDet.gets fun s : State Z => s.cdt srcSlot
  let destP ← NonDet.gets fun s : State Z => s.cdt destSlot
  let cdt ← NonDet.gets fun s : State Z => s.cdt
  let parent ← pure (cdt srcSlot)
  let cdt' ← pure (Function.update (Function.update cdt destSlot parent) srcSlot none)
  setCdt (fun r => if cdt' r = some srcSlot then some destSlot else cdt' r)
  doExtendedOp (capMoveExt srcSlot destSlot srcP destP)
  let isOriginal ← NonDet.gets fun s : State Z => s.isOriginalCap
  setOriginal destSlot (isOriginal srcSlot)
  setOriginal srcSlot false

/-- l4v: CSpace_A.cap_swap_for_delete: swap two slots without changing
their caps. -/
def capSwapForDelete (slot1 slot2 : CslotPtr) : SMonad Z Unit :=
  NonDet.when (slot1 ≠ slot2) <| do
    let cap1 ← getCap slot1
    let cap2 ← getCap slot2
    capSwap cap1 slot1 cap2 slot2

end

/-- l4v: CSpace_A.rec_del_call: the kinds of recursive delete calls. -/
inductive RecDelCall where
  | cTEDeleteCall (slot : CslotPtr) (exposed : Bool)
  | finaliseSlotCall (slot : CslotPtr) (exposed : Bool)
  | reduceZombieCall (cap : Cap) (slot : CslotPtr) (exposed : Bool)
deriving Inhabited

/-- l4v: CSpace_A.locate_slot: the `n`th slot beyond a base slot. -/
def locateSlot : CslotPtr → Nat → CslotPtr := fun (a, b) n =>
  (a, (toBl (ofBl b + BitVec.ofNat 32 n : Word32)).drop (32 - b.length))

section
variable {Z : Type} [StateExt Z]

/-- l4v: CSpace_A.deleting_irq_handler: before deleting an IRQ handler
cap. -/
def deletingIrqHandler (irq : Irq) : SMonad Z Unit := do
  let slot ← getIrqSlot irq
  capDeleteOne slot

/-- l4v: CSpace_A.finalise_cap: the actions taken when a cap is deleted.
Returns the cap to put back in the slot (a Zombie for long-running
deletions) and a cap describing post-deletion actions (`NullCap` for none). -/
def finaliseCap : Cap → Bool → SMonad Z (Cap × Cap)
  | .nullCap, _ => return (.nullCap, .nullCap)
  | .untypedCap _ _ _ _, _ => return (.nullCap, .nullCap)
  | .replyCap r _, final =>
      NonDet.liftM (fun _ => (Cap.nullCap, Cap.nullCap)) <| NonDet.when final <| do
        let tptr ← getReplyTcb r
        match tptr with
        | none => return ()
        | some tp => do
          let state ← getThreadState tp
          match state with
          | .blockedOnReply r => replyRemove tp r
          | _ => cancelIpc tp
  | .endpointCap r _ _, final =>
      NonDet.liftM (fun _ => (Cap.nullCap, Cap.nullCap)) <| NonDet.when final <| cancelAllIpc r
  | .notificationCap r _ _, final =>
      NonDet.liftM (fun _ => (Cap.nullCap, Cap.nullCap)) <| NonDet.when final <| do
        schedContextMaybeUnbindNtfn r
        unbindMaybeNotification r
        cancelAllSignals r
  | .cnodeCap r bits _, final =>
      return (if final then .zombie r (some bits) (2 ^ bits) else .nullCap, .nullCap)
  | .threadCap r, final => do -- can be in any thread state
      NonDet.when final <| unbindNotification r
      NonDet.when final <| unbindFromSc r
      -- suspend sets the TS to Inactive
      NonDet.when final <| suspend r
      NonDet.when final <| prepareThreadDelete r
      return (if final then .zombie r none 5 else .nullCap, .nullCap)
  | .domainCap, _ => return (.nullCap, .nullCap)
  | .schedContextCap sc _, final => do
      NonDet.when final <| schedContextUnbindAllTcbs sc
      NonDet.when final <| schedContextUnbindNtfn sc
      NonDet.when final <| schedContextUnbindReply sc
      NonDet.when final <| schedContextUnbindYieldFrom sc
      NonDet.when final <| schedContextSetInactive sc
      return (.nullCap, .nullCap)
  | .schedControlCap, _ => return (.nullCap, .nullCap)
  | .zombie r b n, final => do
      NonDet.assert final
      return (.zombie r b n, .nullCap)
  | .irqControlCap, _ => return (.nullCap, .nullCap)
  | .irqHandlerCap irq, final =>
      if final then do
        deletingIrqHandler irq
        return (.nullCap, .irqHandlerCap irq)
      else return (.nullCap, .nullCap)
  | .archObjectCap a, final => archFinaliseCap a final

end

/-- l4v: CSpace_A.can_fast_finalise. (l4v's lemma `fast_finalise_def2`
relating it to `finalise_cap` is not ported.) -/
def canFastFinalise (cap : Cap) : Bool :=
  match cap with
  | .replyCap _ _ => true
  | .endpointCap _ _ _ => true
  | .notificationCap _ _ _ => true
  | .nullCap => true
  | _ => false

/-- l4v: CSpace_A.cap_removeable (`primrec (nonexhaustive)`): finalisation is
finished for Null caps and for Zombies covering no slots or only the slot
they are in. -/
def capRemoveable : Cap → CslotPtr → Prop
  | .nullCap, _ => True
  | .zombie slot' bits n, slot =>
      n = 0 ∨ (n = 1 ∧ (slot', List.replicate (zombieCteBits bits) false) = slot)
  | _, _ => undefined

/-- l4v: CSpace_A.cap_cyclic_zombie: a Zombie referring to the CNode or TCB it
is stored in. -/
def capCyclicZombie (cap : Cap) (slot : CslotPtr) : Prop :=
  match cap with
  | .zombie slot' bits _ => (slot', List.replicate (zombieCteBits bits) false) = slot
  | _ => False

section
variable {Z : Type} [StateExt Z]

/-- The defining equations of l4v `CSpace_A.rec_del`, with the recursive
calls as the parameter `recDel`. -/
def recDelF (recDel : RecDelCall → PMonad Z (Bool × Cap)) : RecDelCall → PMonad Z (Bool × Cap)
  | .cTEDeleteCall slot exposed => do
      let (success, cleanupInfo) ← recDel (.finaliseSlotCall slot exposed)
      withoutPreemption <| NonDet.when (exposed ∨ success) <| emptySlot slot cleanupInfo
      NonDetE.returnOk undefined
  | .finaliseSlotCall slot exposed => do
      let cap ← withoutPreemption <| getCap slot
      if cap = .nullCap
      then NonDetE.returnOk (true, .nullCap)
      else do
        let isFinal ← withoutPreemption <| isFinalCap cap
        let (remainder, cleanupInfo) ← withoutPreemption <| finaliseCap cap isFinal
        if capRemoveable remainder slot
        then NonDetE.returnOk (true, cleanupInfo)
        else if capCyclicZombie remainder slot ∧ ¬exposed
        then do
          withoutPreemption <| setCap remainder slot
          NonDetE.returnOk (false, .nullCap)
        else do
          withoutPreemption <| setCap remainder slot
          let _ ← recDel (.reduceZombieCall remainder slot exposed)
          preemptionPoint
          recDel (.finaliseSlotCall slot exposed)
  | .reduceZombieCall (.zombie ptr bits (n + 1)) slot false => do
      let cn ← NonDetE.returnOk (firstCslotOf (.zombie ptr bits (n + 1)))
      NonDetE.assertE (cn ≠ slot)
      withoutPreemption <| capSwapForDelete cn slot
      NonDetE.returnOk undefined
  | .reduceZombieCall (.zombie ptr bits (n + 1)) slot true => do
      let endSlot ← NonDetE.returnOk (ptr, natToCref (zombieCteBits bits) n)
      let _ ← recDel (.cTEDeleteCall endSlot false)
      let newCap ← withoutPreemption <| getCap slot
      if newCap = .zombie ptr bits (n + 1)
      then withoutPreemption <| setCap (.zombie ptr bits n) slot
      else NonDetE.assertE (newCap = .nullCap ∨
                            isZombie newCap ∧ firstCslotOf newCap = slot
                              ∧ firstCslotOf (.zombie ptr bits (n + 1)) ≠ slot)
      NonDetE.returnOk undefined
  | .reduceZombieCall _ _ _ => NonDetE.liftE NonDet.fail

/-- l4v: CSpace_A.rec_del: the complete recursive delete operation (a partial
`function (sequential)` in Isabelle; the least fixed point of `recDelF`). -/
def recDel : RecDelCall → PMonad Z (Bool × Cap) :=
  NonDet.lfp (σ := State Z) (α := Except Unit (Bool × Cap)) fun r c => recDelF r c

/-- l4v: CSpace_A.cap_delete: delete a cap with the recursive delete. -/
def capDelete (slot : CslotPtr) : PMonad Z Unit := do
  let _ ← recDel (.cTEDeleteCall slot true)
  NonDetE.returnOk ()

/-- l4v: CSpace_A.finalise_slot: prepare the cap in a slot for deletion
without deleting it. -/
def finaliseSlot (p : CslotPtr) (e : Bool) : PMonad Z (Bool × Cap) := recDel (.finaliseSlotCall p e)

end

/-- l4v: CSpace_A.exposed_rdcall. -/
def exposedRdcall : RecDelCall → Bool
  | .cTEDeleteCall _ exposed => exposed
  | .finaliseSlotCall _ exposed => exposed
  | .reduceZombieCall _ _ exposed => exposed

/-- l4v: CSpace_A.isCTEDeleteCall. -/
def isCTEDeleteCall : RecDelCall → Bool
  | .cTEDeleteCall _ _ => true
  | .finaliseSlotCall _ _ => false
  | .reduceZombieCall _ _ _ => false

/-- l4v: CSpace_A.slot_rdcall. -/
def slotRdcall : RecDelCall → CslotPtr
  | .cTEDeleteCall slot _ => slot
  | .finaliseSlotCall slot _ => slot
  | .reduceZombieCall _ slot _ => slot

section
variable {Z : Type} [StateExt Z]

/-- The defining equation of l4v `CSpace_A.cap_revoke`, with the recursive
call as the parameter `capRevoke`. -/
def capRevokeF (capRevoke : CslotPtr → PMonad Z Unit) (slot : CslotPtr) : PMonad Z Unit := do
  let cap ← withoutPreemption <| getCap slot
  let cdt ← withoutPreemption <| NonDet.gets fun s : State Z => s.cdt
  let descendants ← NonDetE.returnOk (descendantsOf slot cdt)
  NonDetE.whenE (cap ≠ .nullCap ∧ descendants ≠ ∅) (do
    let child ← withoutPreemption <| selectExt (nextRevokeCap slot) descendants
    let cap ← withoutPreemption <| getCap child
    NonDetE.assertE (cap ≠ .nullCap)
    capDelete child
    preemptionPoint
    capRevoke slot)

/-- l4v: CSpace_A.cap_revoke: revoke the derived caps of a cap, deleting
them all (a partial `function` in Isabelle; the least fixed point of
`capRevokeF`). -/
def capRevoke : CslotPtr → PMonad Z Unit :=
  NonDet.lfp (σ := State Z) (α := Except Unit Unit) fun r c => capRevokeF r c

end

/-! ## Inserting and moving capabilities -/

/-- l4v: CSpace_A.get_badge. -/
def getBadge (cap : Cap) : Option Badge :=
  match cap with
  | .notificationCap _ badge _ => some badge
  | .endpointCap _ badge _ => some badge
  | _ => none

/-- l4v: CSpace_A.is_physical. -/
def isPhysical (cap : Cap) : Bool :=
  match cap with
  | .nullCap => false
  | .domainCap => false
  | .schedControlCap => false
  | .irqControlCap => false
  | .irqHandlerCap _ => false
  | .archObjectCap c => archIsPhysical c
  | _ => true

/-- l4v: CSpace_A.same_region_as: whether the second cap is to the same
object as, or an object in the region of, the first. -/
def sameRegionAs : Cap → Cap → Prop
  | .nullCap, _ => False
  | .untypedCap _ r bits _, c' =>
      isPhysical c' ∧
      r ≤ objRefOf c' ∧
      objRefOf c' ≤ objRefOf c' + objSize c' - 1 ∧
      objRefOf c' + objSize c' - 1 ≤ r + ((1 : Word) <<< bits) - 1
  | .endpointCap r _ _, c' => isEpCap c' ∧ objRefOf c' = r
  | .notificationCap r _ _, c' => isNtfnCap c' ∧ objRefOf c' = r
  | .cnodeCap r bits _, c' => isCnodeCap c' ∧ objRefOf c' = r ∧ bitsOf c' = bits
  | .replyCap n _, c' => ∃ cr', c' = .replyCap n cr'
  | .threadCap r, c' => isThreadCap c' ∧ objRefOf c' = r
  | .schedContextCap sc n, c' => isSchedContextCap c' ∧ objRefOf c' = sc ∧ bitsOf c' = n
  | .schedControlCap, c' => c' = .schedControlCap
  | .zombie _ _ _, _ => False
  | .irqControlCap, c' =>
      c' = .irqControlCap ∨
      (∃ n, c' = .irqHandlerCap n) ∨
      (isArchCap c' ∧ isIrqControlDescendant c'.theArchCap)
  | .domainCap, c' => c' = .domainCap
  | .irqHandlerCap n, c' => c' = .irqHandlerCap n
  | .archObjectCap a, c' =>
      match c' with
      | .archObjectCap a' => archSameRegionAs a a'
      | _ => False

/-- l4v: CSpace_A.same_object_as: whether two caps are to the same object. -/
def sameObjectAs (cp cp' : Cap) : Prop :=
  match cp, cp' with
  | .untypedCap _ _ _ _, _ => False
  | .irqControlCap, _ => False
  | .archObjectCap ac, .archObjectCap ac' => sameAobjectAs ac ac'
  | _, _ => sameRegionAs cp cp'

/-- l4v: CSpace_A.should_be_parent_of: whether an existing cap `c` should be
the parent of a cap `c'` to be inserted: `c` is original and covers the
same region; a badged endpoint or notification cap is the parent only of
non-original caps with the same badge. -/
def shouldBeParentOf (c : Cap) (original : Bool) (c' : Cap) (original' : Bool) : Prop :=
  original ∧
  sameRegionAs c c' ∧
  (match c with
   | .endpointCap _ badge _ => badge ≠ 0 → capEpBadge c' = badge ∧ ¬original'
   | .notificationCap _ badge _ => badge ≠ 0 → capEpBadge c' = badge ∧ ¬original'
   | .archObjectCap ac => shouldBeArchParentOf ac c'.theArchCap original'
   | _ => True)

/-- l4v: CSpace_A.is_cap_revocable: whether the new cap counts as the
original cap to its object (newly badged endpoint caps, IRQ handlers,
untyped caps, some arch caps). -/
def isCapRevocable (newCap srcCap : Cap) : Prop :=
  match newCap with
  | .archObjectCap _ => archIsCapRevocable newCap srcCap
  | .endpointCap _ _ _ => capEpBadge newCap ≠ capEpBadge srcCap
  | .notificationCap _ _ _ => capEpBadge newCap ≠ capEpBadge srcCap
  | .irqHandlerCap _ => srcCap = .irqControlCap
  | .untypedCap _ _ _ _ => True
  | _ => False

section
variable {Z : Type} [StateExt Z]

/-- l4v: CSpace_A.cap_insert: insert a cap as a sibling or child of an
existing cap (`should_be_parent_of` decides which). -/
def capInsert (newCap : Cap) (srcSlot destSlot : CslotPtr) : SMonad Z Unit := do
  let srcCap ← getCap srcSlot
  let destOriginal ← pure (decide (isCapRevocable newCap srcCap))
  let oldCap ← getCap destSlot
  NonDet.assert (oldCap = .nullCap)
  setUntypedCapAsFull srcCap newCap srcSlot
  setCap newCap destSlot
  let isOriginal ← NonDet.gets fun s : State Z => s.isOriginalCap
  let srcParent ← pure (decide (shouldBeParentOf srcCap (isOriginal srcSlot) newCap destOriginal))
  let srcP ← NonDet.gets fun s : State Z => s.cdt srcSlot
  let destP ← NonDet.gets fun s : State Z => s.cdt destSlot
  updateCdt fun cdt => Function.update cdt destSlot (if srcParent then some srcSlot else cdt srcSlot)
  doExtendedOp (capInsertExt srcParent srcSlot destSlot srcP destP)
  setOriginal destSlot destOriginal

end

/-- l4v: CSpace_A.has_cancel_send_rights. -/
def hasCancelSendRights (cap : Cap) : Prop :=
  match cap with
  | .endpointCap _ _ R => R = allRights
  | _ => False

/-- l4v: CSpace_A.tcb_registers_caps_merge: overwrite the caps of a TCB,
keeping its registers and other fields. -/
def tcbRegistersCapsMerge (regtcb captcb : Tcb) : Tcb :=
  { regtcb with tcbCtable := captcb.tcbCtable,
                tcbVtable := captcb.tcbVtable,
                tcbIpcframe := captcb.tcbIpcframe }

/-! ## Invoking CNode capabilities -/

section
variable {Z : Type} [StateExt Z]

/-- l4v: CSpace_A.invoke_cnode. -/
def invokeCnode (i : CnodeInvocation) : PMonad Z Unit :=
  match i with
  | .revokeCall destSlot => capRevoke destSlot
  | .deleteCall destSlot => capDelete destSlot
  | .insertCall cap srcSlot destSlot => withoutPreemption <| capInsert cap srcSlot destSlot
  | .moveCall cap srcSlot destSlot => withoutPreemption <| capMove cap srcSlot destSlot
  | .rotateCall cap1 cap2 slot1 slot2 slot3 =>
      withoutPreemption <|
        if slot1 = slot3 then
          capSwap cap1 slot1 cap2 slot2
        else do
          capMove cap2 slot2 slot3
          capMove cap1 slot1 slot2
  | .cancelBadgedSendsCall (.endpointCap ep b _) =>
      withoutPreemption <| NonDet.when (b ≠ 0) <| cancelBadgedSends ep b
  | .cancelBadgedSendsCall _ => NonDetE.liftE NonDet.fail

end

/-! ## Cap classification used to define invariants -/

/-- l4v: CSpace_A.capclass: `PhysicalClass` for caps to objects that use
physical memory (anything retyped from untyped), `OtherCapClass` for the
rest. -/
inductive Capclass where
  | physicalClass
  | otherCapClass
deriving DecidableEq, Repr, Inhabited

end

end Fl4Spec
