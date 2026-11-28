/-
# P2 (line pte, generation 11): the PageMap slot with `pr`, `dec`, `ra`, `ro` proved and `uf` reduced

`serializable_fl4_localW11PRIPm` (`P2/InvPmTop.lean`) took the bundle `PmObl` (seven fields). Here, at the start
fact narrowed by the plan's lookup (`PmQF = PmQ ∧ InvLk`, `P2/InvPmDec.lean`; satisfiable: `pmQF_of_plan`, and
the leaf half by `pm_leaf_locked`, whose hypotheses `PmPreF` implies):

* `pr`, `dec`, `ra`, `ro` are theorems (`pm_prune`, `pm_dec`, `pm_ra`, `pm_ro`, `P2/InvPmDec.lean`);
* **`pm_huf`**: `uf` from three smaller premises, the ones the CNode arm's `hufQL_of` (`P2/InvHuf.lean`) takes:
  [J] `iw` (`IoPre` survives a user-word write at a bundle state; `io_pathsKQ`'s `hIw`), [J] `pdw` (the plan
  `InvPlanD` survives it: `plan_with`'s PageMap arm reads the slot cap, the `extra[0]` cap, `R10` and the page-table
  walk — no user word, but P3 does not export that for the paging-structure words, as for `hufQL_of`'s `hPDw`) and
  [P] `lk` (the glue's locks are determined by kernel words, `hlk_of_kernelDetU`); `SlJAt`, `IoQ`, `PmArm`, the
  plan's locks, `InvLk` (`invLk_wr`), `GateEp` and the sets `PmRS` / `PmWS` / `IoDS` (`ownP` reads no user word:
  `own` by `E2E.ownDep`, no VCPU, a PTE word's owner is fixed) are proved;
* `PmObl2` (what is left: [W] `acc`, [W] `mv`, and `iw`, `pdw`, `lk`), `pmPathsF`, `StartPmF`, **`pm_hSFQF`**,
  **`serializable_fl4_localW11PRIPm2`**.

Premises of `serializable_fl4_localW11PRIPm2` beyond `serializable_fl4_localW11PR`'s: `B : PmObl2` — [W] `acc`,
[W] `mv` (the decode block on the guarded / move-checked store), [J] `iw`, [J] `pdw`, [P] `lk`.
No existing statement or file changed.
-/
import Fl4Proofs.P2.InvPmDec
import Fl4Proofs.P2.InvPmTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)

noncomputable section

section huf
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

variable (st) in
/-- [J] **`IoPre` survives a user-word write** at a bundle state (`io_pathsKQ`'s / `hufQL_of`'s `hIw`). -/
def PmIw (Cs Ω Sg Ac : Set U64) : Prop :=
  ∀ (K : OwnMap.KLayout) s b v, SlJAt (L := L) K s →
    IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s →
    b ∈ K.user → Aligned b →
    IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac (L.wr s b v)

variable (st) in
/-- [J] **The PageMap plan survives a user-word write** at a `PmPreF` state (`hufQL_of`'s `hPDw` for this arm). -/
def PmPdw (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) : Prop :=
  ∀ (j : I64 × localinv.Plan) (K : KLayoutP) m s b v, PmPreF st Cs Ω Sg Ac Locks j.2 K m s → b ∈ K.user →
    Aligned b → InvPlanD st j.2 (L.wr s b v)

variable (st) in
/-- [P] **The glue's locks are not changed by a user-word write** (`hufQL_of`'s `hlk`). -/
def PmLk (Locks : S → U64 → Prop) : Prop :=
  ∀ (K : OwnMap.KLayout) s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s

end huf

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **What is left of the PageMap slot's obligations** (module docstring). -/
structure PmObl2 (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) : Prop where
  /-- [W] `acc`. -/
  acc : ∀ (j : I64 × localinv.Plan) K m, PmAccW st ar j.1 j.2 K Locks (PmPreF st Cs Ω Sg Ac Locks j.2 K m)
  /-- [W] `move`. -/
  mv : ∀ (j : I64 × localinv.Plan) K m, PmMoveW st ar j.1 j.2 K Locks m (PmPreF st Cs Ω Sg Ac Locks j.2 K m)
  /-- [J] `IoPre` survives a user write. -/
  iw : PmIw st Cs Ω Sg Ac
  /-- [J] the plan survives a user write. -/
  pdw : PmPdw st Cs Ω Sg Ac Locks
  /-- [P] the locks survive a user write. -/
  lk : PmLk st Locks

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
