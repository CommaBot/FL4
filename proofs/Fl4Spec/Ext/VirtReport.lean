/-
FL4 differences (PORTING.md, "FL4 differences"): **x86 virtualization,
the VMEnter report as FL4 main 279c8261 does it** (FL4 #80 / #81 / #85;
proofs/VIRT-PLAN.md §5.3; `Ext/VirtEntry`'s docstring lists them as "not
yet modelled").

l4v has no x86 VCPU. The model is seL4's `vcpu_sysvmenter_reply_to_user`
/ `Arch_leaveVMAsyncTransfer` (x86 `vcpu.c`, `CONFIG_VTX`) as FL4 extends
it for l4h's full-state wrapper (seL4 patches 0039/0040), read from
`crates/fl4-core/src/vcpu.rs` (`report` l. 1180-1301, `finish_notification`
l. 1157-1177, `full_reply` l. 1068-1070, `check` l. 1125-1141, `enter`
l. 1073-1119, `detach` l. 723-735, `signal_completes` l. 1145-1151) and
`notification.rs` `send_signal` l. 80-137.

`vmReportF t badge` is FL4 `vcpu::report t badge` exactly:

* *full* (`full_reply`): the thread's message-info register is
  `NUM_MRS` = 30 (l4h's full-state wrapper leaves its reply length there
  until the VMEnter completes);
* neither a pending exit nor full: MR0..2 := the entry state (RIP,
  controls, injection; 0 without VCPU), **only these three** (seL4
  `vcpu_sysvmenter_reply_to_user`), message info 0, the badge;
* otherwise all 30 MRs (`vmenterFullMrs`): the exit record if there is a
  pending or saved exit (else 0), the entry state, GPRs, RFLAGS,
  interruptibility, CR3, CR2 if no saved exit; when full, MR2 masked to
  32 bits (#85: the 32-bit entry descriptor), and without a pending exit
  `finish_notification`: MR3 := the notification reason (1 on VMX, 0x60
  on SVM), MR4/6/25/26 := 0, MR5 := 0 unless an event was being
  delivered (exit MR27 bit 31, #80); message info 1 and badge 0 with a
  pending exit (cleared), else message info 0 and the badge;
* in every case **FaultIP := NextIP** (#81: a completed VMEnter is not
  restarted by a later timeout fault) and the thread `Running`.

FL4 writes FaultIP before the state change; here it is the last step
(different TCB fields: the final state is the same). The pure part is
`vmenterReportF`; on a pending exit without full state it is the old
`vmenterReport` (the P3 lemma `vmenterReportF_pending`).

On top of it, as FL4: `vmCheckF` (`check`), `vmEnterF` (`enter`, with
#85's SVM full-state EVENTINJ upper half and the already-active full
case reporting with the badge register), `vcpuDetachF` (`detach`),
`associateVcpuTcbF`, `vmSignalCompletes` / `sendSignalVF`
(`signal_completes`, #80: a full-state caller is also completed from
another core once it is not that core's current thread; the spec has no
per-core current thread, so that fact is the parameter `remoteCur`, fixed
for the entry like `onCore`).

The existing `vmReport` / `vmCheck` / `vmEnter` / `vcpuDetach` /
`sendSignalV` and every statement about them are unchanged.

The ported modules are not changed.
-/
import Fl4Spec.Ext.VirtEntry

namespace Fl4Spec

noncomputable section
open Classical

/-- FL4 `finish_notification`'s reason word (MR3): `0x60` (SVM
`VMEXIT_INTR`) on SVM, 1 (VMX external interrupt) otherwise. -/
def vmNotifyReason (k : VirtKind) : Word := if k = .svm then 0x60 else 1

/-- The 30 MRs of FL4 `vcpu::report`'s full branch (module docstring):
`full` is `full_reply`. Without VCPU (`none`) only reached when `full`:
every MR 0 but MR3, the reason. -/
def vmenterFullMrs (k : VirtKind) (sto : Option VcpuState) (full : Bool) : Fin 30 → Word :=
  match sto with
  | none => fun i => if i = vmenterMrReason then vmNotifyReason k else 0
  | some v =>
    let pending := v.exit.pending
    let valid := v.exit.valid
    let vectoring : Bool := valid && decide (v.exit.mrs 27 &&& (1 <<< 31) ≠ 0)
    fun i =>
      let base : Word :=
        if ¬ valid ∧ i = vmenterMrIp then v.entryIp k
        else if ¬ valid ∧ i = vmenterMrCtl then v.entryCtl k
        else if ¬ valid ∧ i = vmenterMrIntr then v.entryIntr k
        else if h : ¬ valid ∧ 10 ≤ i.val ∧ i.val < 25 then
          v.get k (.gpr ⟨i.val - 10, by have := h.2.2; omega⟩)
        else if ¬ valid ∧ i = vmenterMrRflags then
          (if k = .svm then v.get k (.vmcb Svm.rflags) else v.get k (.vmcs Vmx.guestRflags))
        else if ¬ valid ∧ i = vmenterMrGuestInt then
          (if k = .svm then v.get k (.vmcb Svm.intState) else v.get k (.vmcs Vmx.guestInterruptability))
        else if ¬ valid ∧ i = vmenterMrCr3 then
          (if k = .svm then v.get k (.vmcb Svm.cr3) else 0)
        else if ¬ valid ∧ i = vmenterMrCr2 then v.get k (.msr msrCr2)
        else if pending ∨ valid then v.exit.mrs i
        else 0
      let m2 : Word := if full ∧ i = vmenterMrIntr then base &&& 0xffff_ffff else base
      if full ∧ ¬ pending then
        if i = vmenterMrReason then vmNotifyReason k
        else if i = vmenterMrQual ∨ i = vmenterMrGpa ∨ i.val = 25 ∨ i.val = 26 then 0
        else if i = vmenterMrInsnLen ∧ vectoring = false then 0
        else m2
      else m2

/-- The entry-state MRs of FL4 `report`'s first branch (MR0..2; zero
without VCPU). -/
def vmenterEntryMrs (k : VirtKind) : Option VcpuState → List Word
  | none => [0, 0, 0]
  | some v => [v.entryIp k, v.entryCtl k, v.entryIntr k]

/-- The result of FL4 `vcpu::report`: the MRs written (a prefix: 3 or
30), message info, badge register, whether `PENDING` is cleared. -/
structure VmenterResultF where
  mrs : List Word
  msgInfo : Word
  badge : Word
  clearPending : Bool

/-- **FL4 `vcpu::report`, pure part** (module docstring). -/
def vmenterReportF (k : VirtKind) (sto : Option VcpuState) (full : Bool) (badge : Word) :
    VmenterResultF :=
  let pending := match sto with
    | some v => v.exit.pending
    | none => false
  if ¬ pending ∧ ¬ full then ⟨vmenterEntryMrs k sto, 0, badge, false⟩
  else if pending then ⟨(List.finRange 30).map (vmenterFullMrs k sto full), 1, 0, true⟩
  else ⟨(List.finRange 30).map (vmenterFullMrs k sto full), 0, badge, false⟩

/-- FL4 `vcpu::enter`'s staging (#85): on SVM a full-state entry keeps
EVENTINJ's upper (error-code) half and takes the low 32 bits from MR2;
otherwise `VcpuState.enter`. (`Svm.rip`, `Svm.interceptExc` and
`Svm.eventInj` are distinct words, so EVENTINJ read before or after the
first two writes is the same.) -/
def VcpuState.enterF (k : VirtKind) (full : Bool) (v : VcpuState) (ip ctl intr : Word) : VcpuState :=
  v.enter k ip ctl
    (if k = .svm ∧ full then
      (v.get k (.vmcb Svm.eventInj) &&& ~~~0xffff_ffff) ||| (intr &&& 0xffff_ffff)
    else intr)

section
variable {Z : Type} [StateExt Z]

/-- FL4 `full_reply t`: the message-info register is `NUM_MRS` = 30. -/
def vmFullReply (t : ObjRef) : SMonad Z Bool := do
  let mi ← asUser t (getRegister msg_info_register)
  pure (decide (mi = 30))

/-- FL4 #81: `FAULT_IP := NEXT_IP` (the completed VMEnter is not
restarted). -/
def vmFaultIpNext (t : ObjRef) : SMonad Z Unit :=
  asUser t (NonDet.bind (getRegister nextInstructionRegister)
    (fun n => setRegister faultRegister n))

/-- **The VMEnter report as FL4 does it** (FL4 `vcpu::report t badge`;
module docstring). Same shape as `vmReport` (`Ext/VirtVcpu`), with
`full_reply`, the result of `vmenterReportF` and FaultIP := NextIP. -/
def vmReportF (t : ObjRef) (badge : Word) : SMonad Z Unit := do
  let vo ← getTcbVcpu t
  let st ← match vo with
    | none => pure none
    | some v => do
      let s ← getVcpu v
      pure (some s)
  let full ← vmFullReply t
  let r ← pure (vmenterReportF virtKind st full badge)
  let buf ← lookupIpcBuffer true t
  let _ ← setMrs t buf r.mrs
  match vo, r.clearPending with
  | some v, true => vcpuUpdate v VcpuState.reported
  | _, _ => pure ()
  asUser t (setRegister msg_info_register r.msgInfo)
  asUser t (setRegister badge_register r.badge)
  setThreadState t .running
  vmFaultIpNext t

/-- FL4 `vcpu::detach t` with `vmReportF` (else `vcpuDetach`). -/
def vcpuDetachF (t : ObjRef) : SMonad Z Unit := do
  let vo ← getTcbVcpu t
  match vo with
  | none => return ()
  | some v => do
    let st ← getThreadState t
    NonDet.when (st = .runningVM) <| vmReportF t 0
    vcpuUpdate v fun s => { s with tcb := none }

/-- `associateVcpuTcb` with `vcpuDetachF` (FL4 SetTCB). -/
def associateVcpuTcbF (v t : ObjRef) : SMonad Z Unit := do
  vcpuDetachF t
  let st ← getVcpu v
  match st.tcb with
  | some old => vcpuDetachF old
  | none => pure ()
  vcpuUpdate v fun s => { s with tcb := some t }

/-- **The VCPU check as FL4 does it** (FL4 `vcpu::check`): a `runningVM`
thread with a pending exit gets `report t 0`; else an active bound
notification becomes idle and the VMEnter completes by `report t badge`
(full-state callers get 30 MRs, FL4 #80); else a thread without VCPU
gets `report t 0`. The `possibleSwitchTo` of a thread that is not the
current one is `vmCheck`'s (FL4 calls `check` only on the current
thread, where it does nothing). -/
def vmCheckF (t : ObjRef) : SMonad Z Unit := do
  let st ← getThreadState t
  NonDet.when (st = .runningVM) <| do
    let vo ← getTcbVcpu t
    let pending ← match vo with
      | some v => do
        let s ← getVcpu v
        pure s.exit.pending
      | none => pure false
    if pending then vmReportF t 0
    else do
      let nOpt ← getTcbObjRef Tcb.tcbBoundNotification t
      let nb ← match nOpt with
        | some n => do
          let ntfn ← getNotification n
          pure (match ntfn.ntfnObj with
            | .activeNtfn b => some (n, ntfn, b)
            | _ => none)
        | none => pure none
      match nb with
      | some (n, ntfn, b) => do
        setNotification n <| ntfnObjUpdate (fun _ => .idleNtfn) ntfn
        vmReportF t b
        let cur ← NonDet.gets fun s : State Z => s.curThread
        NonDet.when (t ≠ cur) <| possibleSwitchTo t
      | none => NonDet.when (vo = none) <| vmReportF t 0

/-- **VMEnter as FL4 does it** (FL4 `vcpu::enter`): `vmEnter` with the
full-state staging (`VcpuState.enterF`, #85) and, when a bound
notification is already active, `completeSignal` then, for a full-state
caller, `report t (badge register)` (#80), else message info 0. -/
def vmEnterF (t : ObjRef) : SMonad Z Unit := do
  let vo ← getTcbVcpu t
  match vo with
  | none => asUser t (setRegister msg_info_register 0)
  | some v => do
    let ip ← asUser t (getRegister (the msg_registers[0]?))
    let ctl ← asUser t (getRegister (the msg_registers[1]?))
    let intr ← asUser t (getRegister (the msg_registers[2]?))
    let full ← vmFullReply t
    vcpuUpdate v fun st => st.enterF virtKind full ip ctl intr
    let nOpt ← getTcbObjRef Tcb.tcbBoundNotification t
    let active ← match nOpt with
      | some n => do
        let ntfn ← getNotification n
        pure (match ntfn.ntfnObj with
          | .activeNtfn _ => true
          | _ => false)
      | none => pure false
    match nOpt, active with
    | some n, true => do
      completeSignal n t
      let full' ← vmFullReply t
      if full' then do
        let b ← asUser t (getRegister badge_register)
        vmReportF t b
      else asUser t (setRegister msg_info_register 0)
    | _, _ => setThreadState t .runningVM

/-- FL4 `vcpu::signal_completes t` (given `runningVM`): a VCPU without a
pending exit, and the thread on this core, or a full-state caller that
is not the current thread of its own core (`remoteCur t`, #80). -/
def vmSignalCompletes (onCore remoteCur : ObjRef → Bool) (t : ObjRef) : SMonad Z Bool := do
  let vo ← getTcbVcpu t
  match vo with
  | none => pure false
  | some v => do
    let s ← getVcpu v
    let full ← vmFullReply t
    pure (decide (s.exit.pending = false ∧ (onCore t = true ∨ (full = true ∧ remoteCur t = false))))

/-- **seL4 `sendSignal` with `CONFIG_VTX` as FL4 does it** (FL4
`notification::send_signal`): an idle notification bound to a
`runningVM` thread whose VMEnter `vmSignalCompletes` is completed by
`vmReportF` with the badge, then MCS donation, `possibleSwitchTo` and the
sporadic refill check (as `sendSignalV`, but skipped when the thread is in
the release queue, `inReleaseQueue`: FL4 #114, fl4-core notification.rs
l. 106-120 `&& !sched::in_release_queue(s, t)` — a `runningVM` thread can sit
in the release queue, and moving its head refill there would unsort it);
otherwise the ported `sendSignal` (FL4 `set_active`; its `kick_guest` has
no abstract effect). -/
def sendSignalVF (onCore remoteCur : ObjRef → Bool) (ntfnptr : ObjRef) (badge : Badge) :
    SMonad Z Unit := do
  let ntfn ← getNotification ntfnptr
  match ntfn.ntfnObj, ntfn.ntfnBoundTcb with
  | .idleNtfn, some tcb => do
    let st ← getThreadState tcb
    let comp ← vmSignalCompletes onCore remoteCur tcb
    if st = .runningVM ∧ comp = true then do
      vmReportF tcb badge
      maybeDonateSc tcb ntfnptr
      let sched ← NonDet.gets (schedulable tcb)
      NonDet.when sched <| possibleSwitchTo tcb
      let scOpt ← getTcbObjRef Tcb.tcbSchedContext tcb
      NonDet.maybeM (fun scp => do
          let active ← getScActive scp
          NonDet.when active <| do
            let sc ← getSchedContext scp
            let ntfnScp ← getNtfnObjRef Notification.ntfnSc ntfnptr
            let curScPtr ← NonDet.gets fun s : State Z => s.curSc
            let inRq ← NonDet.gets (inReleaseQueue tcb)
            NonDet.when (scOpt = ntfnScp ∧ sc.scSporadic ∧ scp ≠ curScPtr ∧ inRq = false) <| refillUnblockCheck scp)
        scOpt
    else sendSignal ntfnptr badge
  | _, _ => sendSignal ntfnptr badge

end

end

end Fl4Spec
