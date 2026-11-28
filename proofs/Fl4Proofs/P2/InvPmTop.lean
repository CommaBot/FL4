/-
# P2 (line pte, generation 10): the PageMap slot in the invocation-index family over W11

The PageMap slot family `pmPathsB` (`P2/InvPmLP.lean`'s `pmPaths` with its obligations bundled as `PmObl`) as the
`LQ` of `serializable_fl4_localW11PRI` (`P2/E2EPW11RI.lean`), a standalone `PathsP (I64 × localinv.Plan)` so that it
can be summed with the invj line's Delete-with-PTE slot at integration.

* `StartPm`: the slot's start fact — the core started `handle_invocation_local` with syscall number and plan `j`
  from a state `σ` of the current chain with the PageMap entry facts `PmQ` (the plan, the arm, the plan's locks held),
  the glue's lock set, memory as the model's on aligned non-user words;
* **`pm_hSFQ`**: `StartPm` gives `StartAt` of the slot (`hSFQ` of `serializable_fl4_localW11PRI` discharged): the
  `SlJAt` conjunct from the chain (`ChainLay.bun`), `GateEp` from the epoch data that `execP_of_WPRI` hands over
  (the convention `K.ptes = ptesR K s1.mem`, no VCPU, the start memory equal to `s1`'s on the gate words);
* **`serializable_fl4_localW11PRIPm`**: every `ExecWPR` over W11's eight slots plus the PageMap slot, at a state
  with no local path in progress, ran as some serial order of its completed entries.

With `GateEp` in `Pre`, the leaf the decode writes is a locked PTE word of `K` (`pm_leaf_locked`, `InvPmLP`): the
reachability convention (`ptesR_of_run`) and the plan's lock (`plan_with_mapF`) meet at the start state, so the
leaf half of the start facts is satisfiable for a PageMap whose root the ASID names.

Premises: `serializable_fl4_localW11PR`'s, plus `B : PmObl` (the slot's obligations: [W] `acc`, `dec`, `mv`, `ra`,
`ro`; [J] `uf`, `pr`; module docstring of `InvPmLP`). No existing statement or file changed.
-/
import Fl4Proofs.P2.InvPmLP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)

noncomputable section

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **The PageMap slot's obligations**, per index and layout (premises of `pmPaths`, `InvPmLP`). -/
structure PmObl (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) : Prop where
  /-- [W] `acc`. -/
  acc : ∀ (j : I64 × localinv.Plan) K m, PmAccW st ar j.1 j.2 K Locks (PmPre st Cs Ω Sg Ac Locks j.2 K m)
  /-- [W] `dec_alt`. -/
  dec : ∀ (j : I64 × localinv.Plan) K m, PmDecW st ar j.1 j.2 K Locks m (PmPre st Cs Ω Sg Ac Locks j.2 K m)
  /-- [W] `move`. -/
  mv : ∀ (j : I64 × localinv.Plan) K m, PmMoveW st ar j.1 j.2 K Locks m (PmPre st Cs Ω Sg Ac Locks j.2 K m)
  /-- [W] `read_aligned` of declining entries. -/
  ra : ∀ (j : I64 × localinv.Plan) K m, PmRaW st ar j.1 j.2 K Locks m (PmPre st Cs Ω Sg Ac Locks j.2 K m)
  /-- [J] user writes keep `SlJAt`, `PmQ`, the locks and the sets. -/
  uf : ∀ (j : I64 × localinv.Plan) (K : KLayoutP) m s b v, PmPre st Cs Ω Sg Ac Locks j.2 K m s →
      b ∈ K.user → Aligned b →
      (SlJAt (L := L) K.toKLayout (L.wr s b v) ∧ PmQ st Cs Ω Sg Ac Locks j.2 K m (L.wr s b v)) ∧
        Locks (L.wr s b v) = Locks s ∧
        PmRS st K Locks (L.wr s b v) = PmRS st K Locks s ∧
        PmWS st K Locks (L.wr s b v) = PmWS st K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s
  /-- [J] the body is the pruned one. -/
  pr : ∀ (j : I64 × localinv.Plan) K m, PmPrune st ar j.1 j.2 K Locks m (PmPre st Cs Ω Sg Ac Locks j.2 K m)
  /-- [W] `ReadOnce` of the tree at declining entries. -/
  ro : ∀ (j : I64 × localinv.Plan) K m,
    PmRoW st ar j.1 j.2 K Locks m (R.invBodyPmG j.1 j.2) (PmPre st Cs Ω Sg Ac Locks j.2 K m)

variable {st ar}

variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end slot

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EP
