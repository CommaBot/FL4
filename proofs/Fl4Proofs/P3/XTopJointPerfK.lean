/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN sch28): **`kernel_entryJ25MP`:
`kernel_entryJ25M` with `JMidPerfHypQ` [W] replaced by the two [J] facts**
`MidRun.JPerfRegHyp` (XTopJointPerfW: the Untyped / ASID control region
avoids ct and every bound SC) and `MidRun.JPerfIrqSlotHyp` (XTopJointPerfI:
the IRQ node slots hold null or notification caps), both at the `MidPerfAt`
states only.

* `BudgetAt.enteredP`: the dispatch state `σb` of the entry is `Entered` when
  the entry state is (the `FaultIP` write changes only ct's TCB, the time
  stamp only the machine state and the clock, and a `check_budget_restart`
  answering `true` nothing: ScEntryRd's `checkBudgetRestart_true`). This is
  sch26's missing export (KEntry.lean derived it inline from the J-side
  budget post).
* `KDispHyps25MP`: `KDispHyps25M` with `mid`'s `JMidPerfHypQ` [W] replaced
  by `JPerfRegHyp ∧ JPerfIrqSlotHyp` [J]; `.to25M` (from `JAtZ` and
  `Entered` at the dispatch state: `JAtZ.midCQ` gives `CQ ∧ NQ`, then
  `MidRun.jMidPerfHypQ_of2`).
* NEW TOP `kernel_entryJ25MP`.
-/
import Fl4Proofs.P3.XTopJointKEntry25MD
import Fl4Proofs.P3.XTopJointPerfI
import Fl4Proofs.P3.XTopJointMachRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **The entry's dispatch state is `Entered`** (module docstring). -/
theorem BudgetAt.enteredP (hnd : Fl4Spec.numDomains = 1) {σ σb : Fl4Spec.State Unit} (hni : Entered σ)
    (h : BudgetAt σ σb true) : Entered σb := by
  obtain ⟨σ0, h0, hb⟩ := h
  have e0 : σ0.curThread = σ.curThread ∧ σ0.idleThread = σ.idleThread ∧
      σ0.schedulerAction = σ.schedulerAction := by
    cases hk : σ.kheap σ.curThread with
    | none =>
      exfalso
      unfold Fl4Spec.fl4SyscallFaultIP Fl4Spec.asUser at h0
      obtain ⟨y, hy, -⟩ := h0
      have := MidRun.getTcb_some (MidRun.mem_getsThe' hy).1
      rw [hk] at this; cases this
    | some o =>
      cases o with
      | tcb x =>
        rw [fl4SyscallFaultIP_eq hk] at h0
        obtain rfl := congrArg Prod.snd (Set.mem_singleton_iff.1 h0)
        exact ⟨rfl, rfl, rfl⟩
      | _ =>
        exfalso
        unfold Fl4Spec.fl4SyscallFaultIP Fl4Spec.asUser at h0
        obtain ⟨y, hy, -⟩ := h0
        have := MidRun.getTcb_some (MidRun.mem_getsThe' hy).1
        rw [hk] at this; cases this
  have hE := Sched.updateTimeStamp_eq' hnd (doMachineOp_single (getCurrentTime_eq σ0.machineState))
  obtain ⟨⟨u, σu⟩, hu, h2⟩ := hb
  rw [hE] at hu
  have e : σu = _ := congrArg Prod.snd (Set.mem_singleton_iff.1 hu)
  have hb' : σb = σu := Sched.checkBudgetRestart_true h2 rfl
  rw [hb', e]
  show σ0.curThread ≠ σ0.idleThread ∧ σ0.schedulerAction = .resumeCurThread
  rw [e0.1, e0.2.1, e0.2.2]
  exact hni

end

end Fl4Proofs.P3
