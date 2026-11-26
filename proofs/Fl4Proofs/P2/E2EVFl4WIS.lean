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

section sat
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- (invj gen 3) **The frame-cap invocation slot's record and entry fact hold at every chain state with a non-idle
current thread whose CNodeDelete invocation is planned with no PTE lock** (module docstring). -/
theorem invStartW_sat (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {σe : S}
    {K : KLayoutV} {Ch : S → Prop} (hC : ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (nv : K.vcpus = ∅)
    {s : S} (hs : Ch s) (hct : NonIdle st arI AR MR s) {n : I64} {p : localinv.Plan}
    (hp : localinv.plan st s n = ok (some p)) (harm : InvArm st p s) :
    ∃ Ac : Set U64, ∀ j : InvArg S, j.Cs = {c : U64 | c.val < K.ncores} → j.Ω = K.heap.omega →
      j.Sg = K.heap.frame → j.Ac = Ac → j.p = p → j.Locks = planLocks p →
      InvPremW st j K (L.mem s) ∧ InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout (L.mem s) s := by
  obtain ⟨Ac, BI⟩ := bunIx_of (L := L) (ChainOf.bun hC s hs)
  refine ⟨Ac, fun j e1 e2 e3 e4 e5 e6 => ?_⟩
  have hrun := chain_run P hIoa hC hs hct
  let i : IoArg S := ⟨n, j.Cs, j.Ω, j.Sg, j.Ac, j.Locks, fun _ _ _ => True⟩
  have BI' : BunIx (L := L) K.toKLayout K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits i.Ac s := by
    show BunIx (L := L) K.toKLayout K.heap.tcbs j.Cs j.Ω K.heap j.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits j.Ac s
    rw [e1, e2, e3, e4]; exact BI
  have hP := (IoEntJ7.of_bun st BI' hrun).toJ.pre
  refine ⟨⟨nv, ⟨s, BI'.ac⟩, fun _ _ _ _ _ _ _ => by rw [e6]; rfl⟩, ?_⟩
  rw [e5, e6]
  exact ⟨⟨⟨hP, fun _ _ => rfl⟩, planD_of_plan hp, harm, fun k x hk hx => ⟨k, hk, hx⟩⟩, invLk_of_plan hp⟩

end sat

end
end Fl4Proofs.P2.E2EV
