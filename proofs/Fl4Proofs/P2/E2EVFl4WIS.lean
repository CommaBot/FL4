/-
P2 (line invj, gen 3): **the frame-cap invocation slot's start facts are satisfiable at chain states**
(`StartP3WI`'s `.vq (.inr j)` case, P2/E2EVFl4WI.lean), as `ioEntJ9_sat` for io.

At a chain state with a non-idle current thread (`NonIdle` [P], the input `loc_chain_all` clauses 4 / 8 take) whose
syscall is planned as a local invocation (`localinv.plan st s n = ok (some p)`, clause 8's input) on the
CNodeDelete arm with no page-table-entry lock (`InvArm`: label `CNodeDelete`, `p.n ≤ p.pte`), some index meets
the slot's record `InvPremW` and its entry fact `InvQF` at the state's own memory:

* `IoQ`: `IoPre` from the bundle (`bunIx_of`, `IoEntJ7.of_bun` with `run` from the chain, `chain_run`, then
  `IoEntJ7.toJ` / `IoEntJ.pre`, iolay gen 1), the affinity words at the state's own memory (`rfl`);
* `InvPlanD`: `planD_of_plan`; `InvArm`: the hypothesis; the plan's locks held: the index's lock set is the plan's
  own (`planLocks p`, which a user write keeps, so `InvPremW.lk` holds by `rfl`); `InvLk`: `invLk_of_plan`.

**Reachability of `InvArm`** (checked against `crates/fl4-core/src/localinv.rs`, `plan_with`'s Delete arm): the
plan takes a PTE lock (`add_pte`, so `pte < n`) only for a frame cap with `mapped = true`, `asid ≠ 0` and a found
`small_page_entry`; every other small RAM frame cap (never mapped, ASID 0, or a stale mapping whose root is gone)
gets `pte = MAX_LOCKS ≥ n`. So `InvArm` holds exactly for those Deletes: the slot is not vacuous (deleting an unmapped
frame cap is the common case), and it does not cover the Delete of a frame cap with a live mapping (the PTE arm).

* **`invStartW_sat`**: the record and the entry fact at every such chain state (premises: `nv : K.vcpus = ∅` as the
  other P3 slots, `hIoa` [P] / `P` as `chain_run`, `hct` [P], `hp`, `harm`). What `StartP3WI` asks beyond them is
  `GlueAt` [P], as for every other slot.

No existing statement changes.
-/
import Fl4Proofs.P2.E2EVFl4WI
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY region TcbSlot InW InNode)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section

/-- The plan's locks as a lock predicate (independent of the state). -/
def planLocks {S : Type} (p : localinv.Plan) : S → U64 → Prop :=
  fun _ x => ∃ i : Nat, i < p.n.val ∧ p.locks.val[i]? = some x

end
end Fl4Proofs.P2.E2EV
