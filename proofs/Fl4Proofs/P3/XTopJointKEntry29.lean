/-
P3 (DESIGN.md §9), invariant line G3 (INV-PLAN §4, KENTRY-PLAN g3d):
**`kernel_entryJ29` = `kernel_entryJ28` (g3b: no `hNS` / `hNSR`) with g3c's
discharges (`kernel_entryJ27b`: `JPerfRegHyp`, `JPerfIrqSlotHyp`, `JMidVfhHyp`,
`JEntryAt.epQ`)**, and **`kernel_entryJ29G`** = `kernel_entryJ29` with the two
∀-ghost premises `hK` / `hFin` re-scoped (INV-PLAN §3 / "Top risks" 5).

* `kernel_entryJ29`: a wrapper over J28 (`KDispHypsKV27b.to27`); premises J28's
  plus `hE : EpQAll σ` [J], with `hK` asking `KDispHypsKV27b`.
* Re-scoping. J28's body (`kernel_entryJ13PUN`) applies `hK` once, at the dispatch
  state σb, at the ghosts `Z.mv Z.G V0`, `H`, `Cs` (`V0` from the `FaultIP` write,
  `Ac' Lst' D'` from `budgetOkB`) and at the FL4 state `(s2, a1)` the passing
  `budget_ok` returns; and `hFin` three times, at the FL4 state `finish` starts
  from (`budget_ok`'s stopping outcome, or `dispatch_syscall`'s outcome after a
  passing one, also on the preemption path). As stated, `hK` / `hFin` quantify
  over EVERY FL4 state `s'` (and every ghost) jointly related to σb / the front
  outcome by `JAtZ` / `JAtZR`; their fields that `JAtZ` does not determine
  (`JEntryAtR2.flags`, `handlers`, `vsTyp`, …, `KFinAtR27.hd`'s FL4 word, `tail`)
  are then asked at FL4 states the run never reaches, so no per-state invariant
  can discharge them. `kernel_entryJ13PUG` is `kernel_entryJ13PUN` (same body)
  with `hK` asked only at the carried ghosts and at FL4 states `KFrontB` (the
  current thread's `FaultIP` write, then a passing `budget_ok`), and `hFin` only at
  FL4 states `KFrontF` (the same write, `budget_ok`, then `dispatch_syscall` when it
  passes): the FL4 side's counterpart of `BudgetAt` / `specFront`. The value
  written to `FAULT_IP` is left universally quantified (any `v`); everything else
  is the actual run. The equations come from `Sched.spec_and_eq` on the two
  calls; `kPreFinAtG` is `kPreFinHypJI_ofN` at one FL4 state.
* `kernel_entryJ29G`: J29's premises with the re-scoped `hK` / `hFin`
  (strictly weaker hypotheses: J29 follows from it).
-/
import Fl4Proofs.P3.XTopJointKEntry28
import Fl4Proofs.P3.XTopJointKEntry27b
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## J28 with g3c's discharges -/

/-! ## The FL4 front: the states the run reaches -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **FL4's dispatch states** (module docstring): the current thread's `FAULT_IP`
written (any value), then a passing `budget_ok`. The FL4 side of `BudgetAt σ σb true`. -/
def KFrontB (s : S) (a : A) (s' : S) (a' : A) : Prop :=
  ∃ ct v, sched.cur_thread st s = ok ct ∧
    syscall.budget_ok st arI (L.wr s (regA ct layout.reg.FAULT_IP) v) a = ok (true, s', a')

/-- **FL4's front-end outcomes** (module docstring): the `FAULT_IP` write, `budget_ok`,
and `dispatch_syscall` when it passes; the state `finish` starts from. The FL4 side of
`specFront`. -/
def KFrontF (n : I64) (s : S) (a : A) (s' : S) (a' : A) : Prop :=
  ∃ ct v b s2 a2, sched.cur_thread st s = ok ct ∧
    syscall.budget_ok st arI (L.wr s (regA ct layout.reg.FAULT_IP) v) a = ok (b, s2, a2) ∧
    ((b = false ∧ s' = s2 ∧ a' = a2) ∨ (b = true ∧ syscall.dispatch_syscall st arI s2 a2 n = ok (s', a')))

end

/-! ## `kernel_entryJ13PUN` with `hK` / `hFin` at the run's FL4 states -/

/-! ## The re-scoped top -/

end

end Fl4Proofs.P3
