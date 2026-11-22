/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization,
the VCPU invocations** (proofs/VIRT-PLAN.md §5.1).

l4v has no x86 VCPU; the structure is l4v ARM_HYP's `VCPU_A`
(`decode_vcpu_invocation` returning a `vcpu_invocation`,
`perform_vcpu_invocation` returning the reply words, `associate_vcpu_tcb`,
`dissociate_vcpu_tcb`), the checks and effects are FL4's
(`crates/fl4-core/src/vcpu.rs` `decode`, which decodes and performs in one
function; every check precedes the first write, so the split is exact).
The labels are FL4's ABI numbers (`fl4_abi::label`); x86 has no
`InjectIRQ` label (a VMM injects through VMEnter's MR2 or WriteVMCS of
`CONTROL_ENTRY_INTERRUPTION_INFO` / WriteVMCB of `EVENTINJ`).

Arguments: FL4 reads `f` = MR0 when the length is at least 1 and `x` =
MR1 when it is at least 2 (else 0). The ported `get_mrs` list `args` has
exactly the message's length (FL4 clamps it as `get_mrs` does), so `f` is
`args.getD 0 0` and `x` is `args.getD 1 0`.

Replies: FL4's `reply` (MR0 := value, badge 0, message info (0,0,0,1),
caller `Running`) and ReadVMCB's loop are l4v `handle_invocation`'s tail
on the returned list (`reply_from_kernel` (0, list) when calling, then
`Running`); invocations that return `[]` are FL4's `TS_RESTART` ones.

Not modelled (no abstract effect, VIRT-PLAN.md §3.4): `vcpu::stall` (the
VCPU's thread on another core is interrupted; its guest state is already
in the VCPU), FlushTLB's `SVM_CPU := 0` (the SVM ASID retention), the
ASID flush requests of WriteVMCB to CR0/CR3/CR4/EFER/G_PAT.

The I/O-port owner of a cap (FL4 `Cap::IoPort.vcpu`, seL4
`capIOPortVPID`) is read through the adapter `ioPortOwner`, `none` for now
(decision Q2 of 2026-11-21: the `ArchCap.ioPortCap` shape change waits for
the IO-port invariant work; VIRT-PLAN.md §3.3.1 lists the change).

Decision Q4 (2026-11-21): ReadVMCB reads the SVM host-cache words 0x058
and 0x0c0 as 0 (`Svm.hiddenRead`). -- FL4 code differs until V3.

The ported modules are not changed.
-/
import Fl4Spec.Ext.VirtGuest

namespace Fl4Spec

noncomputable section
open Classical

/-- The VCPU labels (FL4's ABI). -/
inductive VcpuLabel where
  | setTcb | readVmcs | writeVmcs | flushTlb | readVmcb | writeVmcb
  | enableIoPort | disableIoPort | writeRegisters | readMsr | writeMsr
deriving DecidableEq, Repr, Inhabited

/-- FL4's label numbers (`fl4_abi::label::X86VCPU*`). -/
def VcpuLabel.num : VcpuLabel → Nat
  | .readMsr => 49
  | .writeMsr => 50
  | .setTcb => 73
  | .readVmcs => 74
  | .writeVmcs => 75
  | .flushTlb => 76
  | .readVmcb => 77
  | .writeVmcb => 78
  | .enableIoPort => 79
  | .disableIoPort => 80
  | .writeRegisters => 81

/-- The VCPU label of a message label, if any. -/
def vcpuLabelOf (label : Data) : Option VcpuLabel :=
  [VcpuLabel.setTcb, .readVmcs, .writeVmcs, .flushTlb, .readVmcb, .writeVmcb, .enableIoPort,
    .disableIoPort, .writeRegisters, .readMsr, .writeMsr].find? fun l => decide (dataToNat label = l.num)

/-- **The I/O-port owner adapter** (module docstring): the VCPU an I/O
port cap's range was granted to. `none` until `ArchCap.ioPortCap` gets
its owner field (VIRT-PLAN.md §3.3.1, decision Q2): then this becomes the
field's projection. -/
def ioPortOwner (_c : ArchCap) : Option ObjRef := none

/-- The I/O bitmap with the ports `lo..hi` set to `deny` (FL4
`vcpu::ports`; `lo`, `hi` below 2^16). -/
def VcpuState.setPorts (lo hi : Word) (deny : Bool) (st : VcpuState) : VcpuState :=
  { st with ioDenied := fun p => if lo.toNat ≤ p.toNat ∧ p.toNat ≤ hi.toNat then deny else st.ioDenied p }

/-- The GPRs set (WriteRegisters); GPRs are canonical on both backends
(SVM's VMCB RAX is GPR 0). -/
def VcpuState.setGprs (vals : Fin 15 → Word) (st : VcpuState) : VcpuState :=
  { st with fields := fun f => match f with
    | .gpr i => vals i
    | f => st.fields f }

/-- A decoded VCPU invocation (l4v ARM_HYP `vcpu_invocation`, FL4's
labels). Write values are already sanitized. -/
inductive VcpuInvocation where
  | setTcb (v t : ObjRef)
  | writeRegisters (v : ObjRef) (vals : Fin 15 → Word)
  | flushTlb (v : ObjRef)
  | readVmcs (v : ObjRef) (f : Word)
  | writeVmcs (v : ObjRef) (f val : Word)
  | readVmcb (v : ObjRef) (off n : Word)
  | writeVmcb (v : ObjRef) (off val : Word)
  | readMsr (v : ObjRef) (m : Word)
  | readVmxMisc
  | writeMsr (v : ObjRef) (m val : Word)
  | enableIoPort (v : ObjRef) (lo hi : Word) (portCap : ArchCap) (portSlot : CslotPtr)
  | disableIoPort (v : ObjRef) (lo hi : Word)
deriving Inhabited

section
variable {Z : Type} [StateExt Z]

/-- **The VMEnter report** (FL4 `vcpu::report t badge`; VIRT-PLAN.md
§5.3): the 30 MRs of `vmenterReport` (registers, then the IPC buffer if
any), the VCPU's pending flag cleared, the message-info register 1 for a
VMM exit and 0 otherwise, the badge register, the thread `Running`. Used
for a pending exit and for a VCPU removed under a `runningVM` thread; a
notification ends a VMEnter by `vmNotifyComplete` (`Ext/VirtEntry`). -/
def vmReport (t : ObjRef) (badge : Word) : SMonad Z Unit := do
  let vo ← getTcbVcpu t
  let st ← match vo with
    | none => pure none
    | some v => do
      let s ← getVcpu v
      pure (some s)
  let r ← pure (vmenterReport virtKind st badge)
  let buf ← lookupIpcBuffer true t
  let _ ← setMrs t buf ((List.finRange 30).map r.mrs)
  match vo with
  | some v => vcpuUpdate v VcpuState.reported
  | none => pure ()
  asUser t (setRegister msg_info_register r.msgInfo)
  asUser t (setRegister badge_register r.badge)
  setThreadState t .running

/-- FL4 `vcpu::detach t` (l4v ARM_HYP `dissociate_vcpu_tcb`): if `t` has a
VCPU, a `runningVM` `t` first gets its report (badge 0), then the binding
is removed. -/
def vcpuDetach (t : ObjRef) : SMonad Z Unit := do
  let vo ← getTcbVcpu t
  match vo with
  | none => return ()
  | some v => do
    let st ← getThreadState t
    NonDet.when (st = .runningVM) <| vmReport t 0
    vcpuUpdate v fun s => { s with tcb := none }

/-- FL4 SetTCB's effect (l4v ARM_HYP `associate_vcpu_tcb`): the target's
old VCPU and the VCPU's old thread are detached, then `v ↔ t`. -/
def associateVcpuTcb (v t : ObjRef) : SMonad Z Unit := do
  vcpuDetach t
  let st ← getVcpu v
  match st.tcb with
  | some old => vcpuDetach old
  | none => pure ()
  vcpuUpdate v fun s => { s with tcb := some t }

/-- The revocation of an I/O-port cap's grant (FL4 `vcpu::revoke_ports`,
seL4 `clearVPIDIOPortMappings`): if the cap's owner (`ioPortOwner`) is a
live VCPU, its range is denied there. With the adapter's `none` it does
nothing (decision Q2). -/
def ioPortRevoke (c : ArchCap) : SMonad Z Unit :=
  match ioPortOwner c, c with
  | some w, .ioPortCap first last => do
    let live ← NonDet.gets fun σ : State Z => (vcpuAt σ w).isSome
    NonDet.when live <| vcpuUpdate w (VcpuState.setPorts (BitVec.setWidth 64 first)
      (BitVec.setWidth 64 last) true)
  | _, _ => return ()

/-- **The VCPU decoder** (module docstring; VIRT-PLAN.md §5.1): FL4's
checks in FL4's order. -/
def decodeVcpuInvocation (label : Data) (args : List Data) (v : ObjRef)
    (extraCaps : List (Cap × CslotPtr)) : SEMonad Z VcpuInvocation :=
  let amd := decide (virtKind = .svm)
  let len := args.length
  let f := args.getD 0 0
  let x := args.getD 1 0
  match vcpuLabelOf label with
  | some .setTcb =>
    match extraCaps with
    | [] => NonDetE.throwError .truncatedMessage
    | (c, _) :: _ => match c with
      | .threadCap t => NonDetE.returnOk (.setTcb v t)
      | _ => NonDetE.throwError .illegalOperation
  | some .writeRegisters =>
    if len < 15 then NonDetE.throwError .truncatedMessage
    else NonDetE.returnOk (.writeRegisters v fun i => args.getD i.val 0)
  | some .flushTlb => NonDetE.returnOk (.flushTlb v)
  | some .readVmcs =>
    if amd then NonDetE.throwError .illegalOperation
    else if len < 1 then NonDetE.throwError .illegalOperation
    else if ¬ Vmx.readable f then NonDetE.throwError .illegalOperation
    else NonDetE.returnOk (.readVmcs v f)
  | some .writeVmcs =>
    if amd then NonDetE.throwError .illegalOperation
    else if len < 2 then NonDetE.throwError .illegalOperation
    else match sanitizeVmcs f x with
      | .error e => NonDetE.throwError e
      | .ok val => NonDetE.returnOk (.writeVmcs v f val)
  | some .readVmcb =>
    if ¬ amd then NonDetE.throwError .illegalOperation
    else if len < 2 then NonDetE.throwError .truncatedMessage
    else if f &&& 7 ≠ 0 ∨ f ≥ Svm.svmEnd ∨ x = 0 ∨ x > 64 ∨ x > (Svm.svmEnd - f) / 8 then
      NonDetE.throwError (.invalidArgument 0)
    else NonDetE.returnOk (.readVmcb v f x)
  | some .writeVmcb =>
    if ¬ amd then NonDetE.throwError .illegalOperation
    else if len < 2 then NonDetE.throwError .truncatedMessage
    else do
      let st ← NonDetE.liftE <| getVcpu v
      let old := if f < Svm.svmEnd ∧ f &&& 7 = 0 then st.get virtKind (.vmcb f) else 0
      match sanitizeVmcb f old x with
      | .error e => NonDetE.throwError e
      | .ok val => NonDetE.returnOk (.writeVmcb v f val)
  | some .readMsr =>
    if len < 1 then NonDetE.throwError .illegalOperation
    else if f = msrVmxMisc then NonDetE.returnOk .readVmxMisc
    else if f ∉ vcpuMsrs then NonDetE.throwError .illegalOperation
    else NonDetE.returnOk (.readMsr v f)
  | some .writeMsr =>
    if len < 2 then NonDetE.throwError .illegalOperation
    else match checkMsrWrite f x with
      | .error e => NonDetE.throwError e
      | .ok () => NonDetE.returnOk (.writeMsr v f x)
  | some .enableIoPort =>
    if amd then NonDetE.throwError .illegalOperation
    else if len < 2 then NonDetE.throwError .truncatedMessage
    else if f &&& 0xffff > x &&& 0xffff then NonDetE.throwError (.invalidArgument 0)
    else match extraCaps with
      | [] => NonDetE.throwError .truncatedMessage
      | (c, slot) :: _ => match c with
        | .archObjectCap (.ioPortCap first last) =>
          if f &&& 0xffff < BitVec.setWidth 64 first ∨ x &&& 0xffff > BitVec.setWidth 64 last then
            NonDetE.throwError (.invalidArgument 0)
          else NonDetE.returnOk (.enableIoPort v (f &&& 0xffff) (x &&& 0xffff) (.ioPortCap first last) slot)
        | _ => NonDetE.throwError .illegalOperation
  | some .disableIoPort =>
    if amd then NonDetE.throwError .illegalOperation
    else if len < 2 then NonDetE.throwError .truncatedMessage
    else if f &&& 0xffff > x &&& 0xffff then NonDetE.throwError (.invalidArgument 0)
    else NonDetE.returnOk (.disableIoPort v (f &&& 0xffff) (x &&& 0xffff))
  | none => NonDetE.throwError .illegalOperation

/-- **The VCPU invocations** (l4v ARM_HYP `perform_vcpu_invocation`; FL4's
effects): the reply words. -/
def performVcpuInvocation : VcpuInvocation → SMonad Z (List Data)
  | .setTcb v t => do
    associateVcpuTcb v t
    return []
  | .writeRegisters v vals => do
    vcpuUpdate v (VcpuState.setGprs vals)
    return []
  | .flushTlb _ => return []
  | .readVmcs v f => do
    let st ← getVcpu v
    return [if Vmx.readSupported f then st.get virtKind (.vmcs f) else 0]
  | .writeVmcs v f val => do
    vcpuUpdate v fun s => s.set virtKind (.vmcs f) val
    return [val]
  | .readVmcb v off n => do
    let st ← getVcpu v
    -- FL4 code differs until V3 (`hiddenRead` includes 0x058 and 0x0c0).
    return (List.range n.toNat).map fun i =>
      let o := off + BitVec.ofNat 64 (i * 8)
      if Svm.hiddenRead o then 0 else st.get virtKind (.vmcb o)
  | .writeVmcb v off val => do
    vcpuUpdate v fun s => s.set virtKind (.vmcb off) val
    return [val]
  | .readMsr v m => do
    let st ← getVcpu v
    return [st.get virtKind (.msr m)]
  | .readVmxMisc => return [if virtKind = .svm then 0 else vcpuCapability msrVmxMisc]
  | .writeMsr v m val => do
    vcpuUpdate v fun s => s.set virtKind (.msr m) val
    return [val]
  | .enableIoPort v lo hi c _slot => do
    -- The cap's previous grant is revoked; the cap's owner then becomes
    -- `v` (FL4 `ex[0].set_cap`), which needs the shape change of
    -- VIRT-PLAN.md §3.3.1 (decision Q2): until then the cap is unchanged.
    ioPortRevoke c
    vcpuUpdate v (VcpuState.setPorts lo hi false)
    return []
  | .disableIoPort v lo hi => do
    vcpuUpdate v (VcpuState.setPorts lo hi true)
    return []

end

end

end Fl4Spec
