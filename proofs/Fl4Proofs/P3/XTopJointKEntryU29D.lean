/-
P3 (FL4 #71 / PR #66, line lcd; KENTRY-PLAN `lcd`): **a declined local entry, then the general
entry**: `kernel_entry_reachU29D`.

fl4-sync runs a syscall or a VM fault first beside its serial gate (`handle_syscall_local`,
`handle_reply_recv_vm_local`, `handle_ioport_local`, `handle_invocation_local`,
`handle_vm_fault_local`). One that returns `false` has written either nothing, or the current
thread's `FAULT_IP` (syscall entries; the value `syscall` writes again) and one
`update_timestamp`, i.e. one clock reading (P1 FastLocalDecline's decline shapes); fl4-sync then
runs the general entry (`handle_syscall`, `handle_vm_fault`) from that state.

**The declined case relates to `tick σ`** (`Fl4Spec.fl4ClockTick`, Ext/Tick: an environment step
that only consumes one clock-oracle reading, the hardware clock advancing). With a clock
reading `n1` (`arI.now a = ok (n1, a')`), the general entry from the declined state runs exactly
as from the entry state `s` with the Arch value `a'` (P1 `handle_syscall_pre_same` /
`vm_pre_same`: its own timestamp update supersedes the prefix's), and `(s, a', tick σ)` is a
`JReachU17` state (`jreachU17_tick`): the joint relation reads the Arch value only through
`AR` (kept by `now`, `ARKeep`) and `MR` (`MachPlat.now`: `MR a' (gctState σ.ms)`, and
`tick σ`'s machine state is `gctState σ.ms`), and the invariants read the clock fields only
through `ValidMachineTime` (`vmt_tick`: the clock does not go back). So U29's clause for the
entry, at `(s, a', tick σ)`, is the postcondition of the general run from the declined state.
The spec event therefore starts from `tick σ`, not from `σ`: the general run reads the clock a
second time, and the spec's oracle counts readings (with `σ` itself the statement would ask the
two readings to agree, i.e. a clock that does not advance; KENTRY-PLAN `lcd`).

A decline before any write leaves `(s, a)`; there U29's clause at `σ` itself applies (`DeclAt`'s
first case).

* `vmt_tick`, `sinvA_tick`, `sinvX_tick`, `sinvIP_tick`: the spec invariants at `tick σ`.
* `jreachU17_tick`: `JReachU17 s a σ → arI.now a = ok (n1, a1) → JReachU17 s a1 (tick σ)`
  (through `JReachU3.start`; no premise).
* `SysClU29` / `SysUClU29` / `VmClU29`: U29's syscall / unknown-syscall / VM-fault clauses (their
  text, verbatim) for a given run; `DeclAt`, `DeclSysU29`, `DeclVmU29`: the declined case.
* `declSys_of`, `declVm_of`, and the top **`kernel_entry_reachU29D`**: U29's premises verbatim,
  nothing added.
-/
import Fl4Proofs.P3.XTopJointKEntryU29
import Fl4Proofs.P1.FastLocalDecline
import Fl4Spec.Ext.Tick
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

/-! ## The spec state after one clock reading -/

/-- `tick σ`'s machine state is the one `getCurrentTime` leaves. -/
theorem tick_eq (σ : Fl4Spec.State Unit) :
    Fl4Spec.fl4ClockTick σ = { σ with machineState := gctState σ.machineState } := rfl

/-- `getCurrentTime` from `σ`'s machine state ends at `tick σ`'s. -/
theorem getCurrentTime_tick (σ : Fl4Spec.State Unit) :
    Fl4Spec.getCurrentTime σ.machineState =
      ({(gctVal σ.machineState, (Fl4Spec.fl4ClockTick σ).machineState)}, False) :=
  getCurrentTime_eq σ.machineState

/-! ## U29's clauses for a given run, and the declined case -/

end

end Fl4Proofs.P3.SInvR.G5
