/-
P3 (DESIGN.md §9), invariant lines G1 / G3 (ctq20): **`kernel_entryJ30D`** =
`kernel_entryJ30C` with `hS : SInvCQ σ` replaced by `hS : SInvCR σ`
(SpecInvAllR: `SInvCQ ∧ RS`, `RS σ := σ.schedulerAction = resumeCurThread`)
and `hni : Entered σ` replaced by `hct : σ.curThread ≠ σ.idleThread` ([S], l4v
`ct_active` at a syscall entry: a syscall comes from a user thread). `Entered`'s
action half is `SInvCR`'s `RS` (`SInvCR.entered`).

`RS` holds at boot (`boot_sinvCR`) and at every kernel exit given rd's `CAx`
at that exit (`kentry_sinvCR_ofCA` / `kcall_sinvCR_ofCA`, or rd10's
hypotheses: `*_ofRd`); see SpecInvAllR. The rest are J / [P] / [S] / spec
exactly as in `kernel_entryJ30C` (`hE : EpQAll σ`, `hB : OffReady …` are the rd
line's). No premise added; no cone edit.
-/
import Fl4Proofs.P3.XTopJointKEntry29
import Fl4Proofs.P3.SpecInvAllQ
import Fl4Proofs.P3.SpecInvAllR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvAll

/-- **`Entered`** (l4v `ct_running` ∧ `schact_is_rct`) from `SInvCR` and `ct ≠ idle`. -/
theorem SInvCR.entered {σ : Fl4Spec.State Unit} (h : SInvCR σ) (hct : σ.curThread ≠ σ.idleThread) :
    Entered σ :=
  And.intro hct h.2

end Fl4Proofs.P3.SInvAll

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

end

end Fl4Proofs.P3
