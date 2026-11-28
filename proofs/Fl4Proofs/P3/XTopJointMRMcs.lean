/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr1): **the preemption path's
non-schedulable branch with `MR`**: `mcs_preemption_point` when the current
thread is not schedulable charges the consumed time with no timeout fault
(`charge_budget c false`); FL4 keeps the arch state (`JHole.chargeBudgetJ`)
and the spec's `chargeBudget consumed false` keeps `MR`'s machine fields
(`mf_chargeBudgetF`), so `MR` holds after it and `afterInv_of_mcsJM` takes the
pending line by `MachPlat.takeAt`.

* `JHole.mcsPPJZM_ns`: XTopJointPreemptZ's `mcsPPJZ` (covered holes) for a
  non-schedulable current thread, with `MR r.2 σ'.ms` after (an adapted copy of
  its first branch: the original's post hides the arch equality).
* `JHole.afterInvJZJM_ns`: `after_invocation (Err)` from such a hole under
  `MachPlat` + `MR a σ.ms`, ending in `PPQJ`, no `IrqPlat.take`.
* `JAtPreM`: `JAtPre` with `MR` + `ValidMachineTime` at the preemption point's
  pre-state; `jAtPreM_hole`: such a state is a `JHole` with `MR` and
  `ValidMachineTime` (`JAtZ.ppJHM`), the start of the MR-threaded preemption
  path.
-/
import Fl4Proofs.P3.XTopJointMRPP
import Fl4Proofs.P3.MachFieldKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

variable (arI) in
/-- **`JAtPre` with `MR` at the preemption point's pre-state** (mr1): the
interface the invocations' preemption points must produce once `MR` is
threaded through them (KENTRY-PLAN mr1 NEXT): `MR a0 σ0.ms` and
`ValidMachineTime σ0` where the preempting `preemption_point` starts. -/
def JAtPreM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (s0 : S) (a0 : A) (σ0 : Fl4Spec.State Unit),
    (JAt (L := L) arI AR s0 a0 σ0 ∧ Vs.NoSwitch σ0 ∧ PPR0 σ0 ∧ MR a0 σ0.machineState ∧ ValidMachineTime σ0) ∧
    sched.preemption_point st arI s0 a0 = ok (.Err .Preempted, s, a) ∧
    (.error (), σ) ∈ ((Fl4Spec.preemptionPoint (Z := Unit)).run σ0).1

theorem JAtPreM.toPre {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JAtPreM (L := L) arI AR MR s a σ) :
    JAtPre (L := L) arI AR s a σ :=
  by
  obtain ⟨s0, a0, σ0, ⟨hJ, hns, hp, -, -⟩, hpp, hσ⟩ := h
  exact ⟨s0, a0, σ0, ⟨hJ, hns, hp⟩, hpp, hσ⟩

end

end

end Fl4Proofs.P3
