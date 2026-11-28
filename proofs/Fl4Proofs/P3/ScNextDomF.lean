/-
P3 (DESIGN.md §9), scheduler: **the domain switch up to the FPU**
(KENTRY-PLAN.md sch4 (A)): ScNextDomB's `ArchNd` [P] is false whenever the
spec has an FPU owner (its `ArchKeeps` keeps the heap; l4v
`arch_prepare_next_domain = switch_local_fpu_owner None` saves the machine
FPU image into the owner's TCB and clears its `tcbCurFpu`). Restated:

* `ArchNdF` [P]: at a state whose FPU owner is a TCB (`FpuOwnOK` [J],
  ScArchF), the spec's `arch_prepare_next_domain` has one outcome, with
  `SchedRel`/`NtfnStateRel` kept at FL4's unchanged store, `ArchKeepsF`
  (the heap up to the old owner's saved FPU image and `tcbCurFpu`,
  registers kept), the domain list/index/start kept and no FPU owner after.
  True at reachable states (`valid_cur_fpu`; the opaque `enableFpu`/
  `disableFpu`/`readFpuState` machine operations with one outcome, as for
  every arch premise). FL4 has no FPU step at a domain switch (its lazy
  owner stays live; harmless with `numDomains = 1`, and no relation reads
  the spec's FPU fields).
* `scnt_refines0F`: ScNextDomB's `scnt_refines0` with `ArchSwF`, `ArchNdF`,
  `FpuOwnOK σ`, and `HeapEqUpToFpu σ σ'` in the post (supersedes it).
-/
import Fl4Proofs.P3.ScNextDomB
import Fl4Proofs.P3.ScScheduleF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched Fl4Proofs.P3.Notif

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}

/-- **`arch_prepare_next_domain` up to the FPU** [P] (module docstring). -/
def ArchNdF (st : machine.Store S) [L : P1.LawfulStore st] (N T C : Set U64) (c : U64) : Prop :=
  ∀ (s : S) (σ : Fl4Spec.State Unit), SchedRel st N T C c s σ → NtfnStateRel N T (L.mem s) σ → FpuOwnOK σ →
    ∃ σ1, Fl4Spec.archPrepareNextDomain (Z := Unit) σ = ({((), σ1)}, False) ∧ SchedRel st N T C c s σ1 ∧
      NtfnStateRel N T (L.mem s) σ1 ∧ ArchKeepsF σ σ1 ∧ σ1.domainList = σ.domainList ∧
      σ1.domainIndex = σ.domainIndex ∧ σ1.domainStartIndex = σ.domainStartIndex ∧
      σ1.archState.x64CurrentFpuOwner = none

end

end

end Fl4Proofs.P3
