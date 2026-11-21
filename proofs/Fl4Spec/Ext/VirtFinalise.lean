/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization,
retype and finalisation of VCPU and EPT objects, and TCBSetEPTRoot**
(proofs/VIRT-PLAN.md §5.2, §5.4, §5.5).

Finalisation (FL4 `objects.rs` `finalise_cap` / `finalise_cap_object`):
`finaliseCapV` is l4v's `finalise_cap` (CSpace_A, ported unchanged as
`finaliseCap`) with these hooks, the ported behaviour otherwise:

* a final VCPU cap (FL4 `vcpu::finalise`): its thread, if any, is detached
  (`vcpuDetach`: a `runningVM` thread first gets its report);
* a final mapped EPT table cap (level 39/30/21, FL4 `ept::finalise`):
  `guestUnmap` of its entry; a final mapped EPT root is the ported
  `arch_finalise_cap` (its `deleteAsid` of the guest-tagged entry);
* an EPT-mapped frame cap (final or not, FL4 `is_ept`): `guestUnmap` of
  its entry (the ported `unmapPage` looks for a native root and would find
  none);
* an I/O-port cap (final or not): `ioPortRevoke` (`Ext/VirtVcpu`, the
  owner adapter of decision Q2), then the ported behaviour;
* a final thread cap: `vcpuDetach` of the thread first (FL4
  `objects.rs:336`), then the ported thread finalisation.

l4v's recursive delete and revoke call `finalise_cap` directly, so the
extension has its own copies, transliterated with `finaliseCapV` for
`finaliseCap`: `recDelFV`/`recDelV` (`rec_del`), `capDeleteV`,
`capRevokeFV`/`capRevokeV`, and their callers `invokeCnodeV`
(`invoke_cnode`), `installTcbCapV`, `installTcbFrameCapV` and
`invokeTcbV` (`invoke_tcb`; only the two thread-control invocations
delete caps).

Retype (FL4 `untyped.rs:42`, `arch/x86_64/objects.rs`
`create_arch_object`): `fl4DecodeUntypedInvocationV` refuses the five
VT-x object types with `InvalidArgument 0` when `virtKind = none`, at
FL4's place (after the length and extra-cap checks, before the type
decode); `fl4InvokeUntypedV` is `fl4InvokeUntyped` followed by FL4's
`vcpu::init` (`initVcpu virtKind`) on each new VCPU.

TCBSetEPTRoot (FL4 `tcb.rs:406`, seL4 `decodeSetEPTRoot`): no extra cap
`TruncatedMessage`; not a mapped level-0 EPT cap `IllegalOperation`; the
derived cap replaces the target's sixth slot (`cte_delete` then
`cap_insert`).

The ported modules are not changed.
-/
import Fl4Spec.Ext.VirtEptInv
import Fl4Spec.Ext.Invocation

namespace Fl4Spec

noncomputable section
open Classical

/-- FL4's label number of `TCBSetEPTRoot`. -/
def fl4SetEptRootLabel : Nat := 88

/-- The VT-x object types (FL4 `ot::X86Vcpu ..< ot::Count`: 14..18). -/
def isVtxObjectTypeNum (n : Nat) : Bool := decide (14 ≤ n ∧ n ≤ 18)

section
variable {Z : Type} [StateExt Z]

/-! ## Finalisation -/

/-- **`finalise_cap` with the virtualization hooks** (module docstring). -/
def finaliseCapV (cap : Cap) (final : Bool) : SMonad Z (Cap × Cap) :=
  match cap with
  | .archObjectCap (.vcpuCap v) =>
    if final then do
      let st ← getVcpu v
      match st.tcb with
      | some t => vcpuDetach t
      | none => pure ()
      return (.nullCap, .nullCap)
    else return (.nullCap, .nullCap)
  | .archObjectCap (.eptCap ptr level (some (a, gpa))) =>
    if final ∧ level ≠ 0 then do
      guestUnmap a gpa ptr level true
      return (.nullCap, .nullCap)
    else finaliseCap cap final
  | .archObjectCap (.pageCap _ p _ .vmEptMap sz (some (a, gpa))) => do
    NonDet.when (a ≠ 0) <| guestUnmap a gpa p (pageBitsForSize sz) false
    return (.nullCap, .nullCap)
  | .archObjectCap (.ioPortCap f l) => do
    ioPortRevoke (.ioPortCap f l)
    finaliseCap cap final
  | .threadCap t => do
    NonDet.when final <| vcpuDetach t
    finaliseCap cap final
  | _ => finaliseCap cap final

/-- l4v `CSpace_A.rec_del`'s equations (`recDelF`) with `finaliseCapV`. -/
def recDelFV (recDel : RecDelCall → PMonad Z (Bool × Cap)) : RecDelCall → PMonad Z (Bool × Cap)
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
        let (remainder, cleanupInfo) ← withoutPreemption <| finaliseCapV cap isFinal
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

/-- l4v `rec_del` with `finaliseCapV` (the least fixed point, as `recDel`). -/
def recDelV : RecDelCall → PMonad Z (Bool × Cap) :=
  NonDet.lfp (σ := State Z) (α := Except Unit (Bool × Cap)) fun r c => recDelFV r c

/-- l4v `cap_delete` with `recDelV`. -/
def capDeleteV (slot : CslotPtr) : PMonad Z Unit := do
  let _ ← recDelV (.cTEDeleteCall slot true)
  NonDetE.returnOk ()

/-- l4v `cap_revoke`'s equation (`capRevokeF`) with `capDeleteV`. -/
def capRevokeFV (capRevoke : CslotPtr → PMonad Z Unit) (slot : CslotPtr) : PMonad Z Unit := do
  let cap ← withoutPreemption <| getCap slot
  let cdt ← withoutPreemption <| NonDet.gets fun s : State Z => s.cdt
  let descendants ← NonDetE.returnOk (descendantsOf slot cdt)
  NonDetE.whenE (cap ≠ .nullCap ∧ descendants ≠ ∅) (do
    let child ← withoutPreemption <| selectExt (nextRevokeCap slot) descendants
    let cap ← withoutPreemption <| getCap child
    NonDetE.assertE (cap ≠ .nullCap)
    capDeleteV child
    preemptionPoint
    capRevoke slot)

/-- l4v `cap_revoke` with `capDeleteV`. -/
def capRevokeV : CslotPtr → PMonad Z Unit :=
  NonDet.lfp (σ := State Z) (α := Except Unit Unit) fun r c => capRevokeFV r c

/-- l4v `invoke_cnode` with `capRevokeV` / `capDeleteV`. -/
def invokeCnodeV (i : CnodeInvocation) : PMonad Z Unit :=
  match i with
  | .revokeCall destSlot => capRevokeV destSlot
  | .deleteCall destSlot => capDeleteV destSlot
  | i => invokeCnode i

/-- l4v `Tcb_A.install_tcb_cap` with `capDeleteV`. -/
def installTcbCapV (target : ObjRef) (slot : CslotPtr) (n : Nat) (slotOpt : Option (Cap × CslotPtr)) :
    PMonad Z Unit :=
  match slotOpt with
  | none => NonDetE.returnOk ()
  | some (newCap, srcSlot) => do
    capDeleteV (target, tcbCnodeIndex n)
    NonDetE.unlessE (newCap = .nullCap) <|
      NonDetE.liftE <| checkCapAt newCap srcSlot
        <| checkCapAt (.threadCap target) slot
        <| capInsert newCap srcSlot (target, tcbCnodeIndex n)

/-- l4v `Tcb_A.install_tcb_frame_cap` with `capDeleteV`. -/
def installTcbFrameCapV (target : ObjRef) (slot : CslotPtr)
    (buffer : Option (VSpaceRef × Option (Cap × CslotPtr))) : PMonad Z Unit :=
  match buffer with
  | none => NonDetE.returnOk ()
  | some (ptr, frame) => do
    capDeleteV (target, tcbCnodeIndex 2)
    NonDetE.liftE <| threadSet (fun t => { t with tcbIpcBuffer := ptr }) target
    NonDetE.liftE <| match frame with
      | none => return ()
      | some (newCap, srcSlot) =>
          checkCapAt newCap srcSlot
            <| checkCapAt (.threadCap target) slot
            <| capInsert newCap srcSlot (target, tcbCnodeIndex 2)
    let cur ← NonDetE.liftE <| NonDet.gets fun s : State Z => s.curThread
    NonDetE.liftE <| NonDet.when (target = cur) rescheduleRequired

/-- l4v `Tcb_A.invoke_tcb` with `installTcbCapV` / `installTcbFrameCapV`
(the two thread-control cases; the others are l4v's). -/
def invokeTcbV : TcbInvocation → PMonad Z (List Data)
  | .threadControlCaps target slot faultHandler timeoutHandler croot vroot buffer => do
      installTcbCapV target slot 3 faultHandler
      installTcbCapV target slot 4 timeoutHandler
      installTcbCapV target slot 0 croot
      installTcbCapV target slot 1 vroot
      installTcbFrameCapV target slot buffer
      NonDetE.returnOk []
  | .threadControlSched target slot faultHandler mcp priority sc => do
      installTcbCapV target slot 3 faultHandler
      NonDetE.liftE <| NonDet.maybeM (fun (newmcp, _) => setMcpriority target newmcp) mcp
      NonDetE.liftE <| NonDet.maybeM (fun (prio, _) => setPriority target prio) priority
      NonDetE.liftE <| NonDet.maybeM (fun scopt =>
          match scopt with
          | none => do
              let scPtrOpt ← getTcbObjRef Tcb.tcbSchedContext target
              let scPtr ← NonDet.assertOpt scPtrOpt
              schedContextUnbindTcb scPtr
          | some scPtr => schedContextBindTcb scPtr target) sc
      NonDetE.returnOk []
  | i => invokeTcb i

/-! ## TCBSetEPTRoot -/

/-- TCBSetEPTRoot's invocation: the target, the derived root cap and its
source slot. -/
structure SetEptRootInvocation where
  target : ObjRef
  newCap : Cap
  srcSlot : CslotPtr
deriving Inhabited

/-- **TCBSetEPTRoot's decoder** (module docstring). -/
def decodeSetEptRoot (target : ObjRef) (excaps : List (Cap × CslotPtr)) :
    SEMonad Z SetEptRootInvocation :=
  match excaps with
  | [] => NonDetE.throwError .truncatedMessage
  | (c, src) :: _ =>
    match c with
    | .archObjectCap (.eptCap _ 0 (some _)) => do
      let derived ← deriveCap src c
      NonDetE.returnOk ⟨target, derived, src⟩
    | _ => NonDetE.throwError .illegalOperation

/-- **TCBSetEPTRoot** (FL4 `cdt::delete` of the target's slot 5, then
`cdt::insert`). -/
def invokeSetEptRoot (i : SetEptRootInvocation) : PMonad Z Unit := do
  capDeleteV (i.target, tcbCnodeIndex 5)
  NonDetE.liftE <| capInsert i.newCap i.srcSlot (i.target, tcbCnodeIndex 5)

/-! ## Retype -/

/-- The condition of FL4's VT-x retype refusal (`untyped.rs:42`). -/
def untypedVtxGate (label : Data) (args : List Data) (excaps : List Cap) : Prop :=
  genInvocationType label = .untypedRetype ∧ 6 ≤ args.length ∧ excaps ≠ [] ∧
    isVtxObjectTypeNum (dataToNat (args.getD 0 0)) = true ∧ virtKind = .none

/-- **FL4's untyped decoder with the VT-x gate** (module docstring). -/
def fl4DecodeUntypedInvocationV (label : Data) (args : List Data) (slot : CslotPtr) (cap : Cap)
    (excaps : List Cap) : SEMonad Z UntypedInvocation :=
  if untypedVtxGate label args excaps then NonDetE.throwError (.invalidArgument 0)
  else fl4DecodeUntypedInvocation label args slot cap excaps

/-- The objects a retype creates (`retypeRegionWith`'s addresses). -/
def retypeAddrs (bitsApi : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n : Nat) (oBits : Nat)
    (type : ApiObjectType) : List ObjRef :=
  (List.range n).map fun p => ptrAdd ptr (p * 2 ^ bitsApi type oBits)

/-- **FL4's untyped invocation with `vcpu::init`** (module docstring). -/
def fl4InvokeUntypedV (ui : UntypedInvocation) : PMonad Z Unit := do
  fl4InvokeUntyped ui
  match ui with
  | .retype _ _ _ retypeBase newType objSz slots _ =>
    NonDetE.liftE <| NonDet.when (newType = .archObject .vcpuObj) <|
      NonDet.mapMx (fun v => setVcpu v (initVcpu virtKind))
        (retypeAddrs fl4ObjBitsApi retypeBase slots.length objSz newType)

end

end

end Fl4Spec
