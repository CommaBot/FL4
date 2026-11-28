/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr5): **`kernel_entryJ15P`**,
XTopJointKEntry14P's `kernel_entryJ14P` without `KDispHyps13P.vmt` [J]
(mr4 NEXT (4)).

* `budget_vmt_at`: `ValidMachineTime` holds at every spec state the entry
  dispatches from (`BudgetAt σ σb true`), with no premise at the entry: the
  time stamp sets `curTime` to the clock value and the last machine time to
  the same value (`validMachineTime_gct`), and a `check_budget_restart` that
  answers `true` changes nothing (ScEntryRd's `checkBudgetRestart_true`: the
  timeout-fault path of `checkBudget` only runs on `false`).
* `KDispHypsKV K`: `KDispHypsK K` without its `vmt` field; `kernel_entryJ15P`
  takes it (the field from `budget_vmt_at`).
-/
import Fl4Proofs.P3.XTopJointKEntry14P
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **`ValidMachineTime` at the spec's budget outcome `true`** (module
docstring). -/
theorem budget_vmt_at (hnd : Fl4Spec.numDomains = 1) {σ0 σb : Fl4Spec.State Unit}
    (hmem : (true, σb) ∈ ((Fl4Spec.updateTimeStamp (Z := Unit) >>= fun _ => Fl4Spec.checkBudgetRestart) σ0).1) :
    ValidMachineTime σb := by
  have hE := Sched.updateTimeStamp_eq' hnd (doMachineOp_single (getCurrentTime_eq σ0.machineState))
  obtain ⟨⟨u, σu⟩, hu, h2⟩ := hmem
  rw [hE] at hu
  have e : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  have hb : σb = σu := Sched.checkBudgetRestart_true h2 rfl
  rw [hb, e]
  exact ⟨(validMachineTime_gct σ0).1, (validMachineTime_gct σ0).2⟩

/-- `ValidMachineTime` at a dispatch state of the entry. -/
theorem BudgetAt.vmt (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} (h : BudgetAt σ σb true) :
    ValidMachineTime σb := by
  obtain ⟨σ0, -, hb⟩ := h
  exact budget_vmt_at hnd hb

end

end Fl4Proofs.P3
