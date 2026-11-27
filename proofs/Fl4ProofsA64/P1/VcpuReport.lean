/-
P1 (AArch64): `vcpu.report`.

On x86_64, `vcpu::report` completes a `SysVMEnter` caller's VM run when a signal reaches it
(`Fl4Proofs/P1/VcpuReport.lean`: message registers, `MSG_INFO` / `BADGE` / `FAULT_IP`, the VCPU's `PENDING`
word, and the thread made running; `vcpu.report.gen` proves it from those four step kinds). On AArch64 it is
the identity: a signal to a thread in `ARMVCPURun` stalls the VCPU's caller instead (`kick_guest` →
`remote_tcb_stall`, crates/fl4-core/src/notification.rs), and the run's completion is `vcpu::complete_run`
(the run's exit), not part of the signal. So this module replaces x86_64's with:

* `vcpu.report.id`: `vcpu.report st ar s a t badge = ok s`;
* `vcpu.report.keep`: it keeps every predicate of the state.

Callers that x86_64 proves through `vcpu.report.gen` (QueueSignal's VM branch, QueueFootS, TimerRBSig)
need AArch64 statements of their own: the thread is *not* made running by the signal.

No premises.
-/
import Fl4ProofsA64.P0.Auto
import Fl4ProofsA64.P1.Store
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} {A : Type _} {ar : machine.Arch A}

/-- AArch64's `vcpu.report` writes nothing. -/
theorem vcpu.report.id (s : S) (a : A) (t : obj.Tcb) (badge : U64) :
    vcpu.report st ar s a t badge = ok s := by
  unfold vcpu.report; rfl

/-- AArch64's `vcpu.report` keeps every predicate of the state. -/
theorem vcpu.report.keep {P : S → Prop} {s : S} {a : A} {t : obj.Tcb} {badge : U64} (h : P s) :
    vcpu.report st ar s a t badge ⦃ P ⦄ := by
  rw [vcpu.report.id]; exact (WP.spec_ok _).2 h

end

end Fl4ProofsA64.P1
