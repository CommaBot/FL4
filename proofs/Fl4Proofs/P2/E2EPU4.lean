/-
# P2 (line glue, gen 1): `serializable_fl4_localU4` — U2 with every start fact at the serial-prefix memory

audU F1: every start fact of `serializable_fl4_localU2` (`StartV2`, all of whose slots end in a `GlueAt` with
`Ch σ`) asks a P3 chain state agreeing with the **physical** memory at the start step. While another core's body is
mid-way (e.g. `fastpath.rs` between `ep.set_queue` and `dest.set_state(TS_RUNNING)`) the physical memory breaks
P3's joint invariant, so no core can start a body there: such executions are not `ExecWPR`, and U2 says nothing
about them. The `[P]` "fl4-sync calls the body on the one physical memory" is false exactly at those points.

Here the start facts are asked at the **serial-prefix memory** `H` (Serial's history memory: the completed
entries run one after another in completion order, carried as a ghost index, `SerialH.NextH`):

* `Fl4StepWPRH` / `ExecWPRH`: `Fl4StepWPR` / `ExecWPR` with `start : ∃ i, SF Ch K H hK hU c hs k i` (was
  `SF Ch K s.mem …`); every other field unchanged.
* `execPH_of_WPRHG`: `execP_of_WPRG` (E2EPU1) for the ghost executions; the start's epoch data (`GateW` agreement
  with the epoch start) carries to `H`, which equals the memory on every gate word (`SerialH.xsafeRunH_agree`).
  The per-slot conversion `hSF` is the same hypothesis, used at `{ s with mem := H }`.
* **`serializable_fl4_localU4`**: U2's family, U2's start facts `StartV2` (now at `H`), U2's `hSF` proof
  verbatim. Soundness through `serializable_e2ePH` → `SerialH.serializable_safeXH`: at a start the core's view of
  `H` and of the physical memory agrees (`VEq`, **proved**: `SerialH.veq_start` from Serial's `InvH`, the new
  ownership invariant `OwnInv` and `SW`), so the body started from a store state agreeing with `H` is `Safe` at the
  physical memory (`E2E.body_safeH`).

## Premises (vs `serializable_fl4_localU2`)
Identical list; one changes meaning:
* `ExecWPRH.start` [P]: each slot's `GlueAt` now links its store state `σ` to `H` instead of to `s.mem`.
  What it states: the serial-prefix memory, on aligned kernel words, is a state of the epoch's P3 chain (`Ch σ`),
  with the slot's record facts there. Justification: after the epoch's serial exit `H` is the exit memory
  (`NextH`: a serial body's memory); after a completed accepted local run `H' = mix W s.mem H` is that run from `H`
  (`InvH.loc.sim`), a `JReachSt.loc` step from a chain state; on every word the starting core holds or the gate owns
  (the words fl4-sync's glue reads and checks: locked objects, its own core's words, gate words) `H` is the
  physical memory (`VEq`, proved), so the glue's checks read `H`. Not derived here: the chain property of `H`
  (an induction over the execution using P3's `loc_chain_all` per accepted run, and `JReachU17` closure for
  declines' writes). Unlike U2's start [P], this one is not false at any reachable point we know of.
* Every other premise (`P : LocPlat`, `hIoa`, `h0`, `hA0`, `hB`, `hc0`, `hM0`, `arm`, `serX`, `serC`, `serG`,
  `keep`, `HwStepP`, `hq`, the slot records inside `StartV2`, `yb` [J]) is U2's, unchanged.

No new [W] or [J]. No per-path obligation is re-proved. No existing statement or file changed except the root
import list.
-/
import Fl4Proofs.P2.E2EPU2P
import Fl4Proofs.P2.E2EPH
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH xsafeRunH_inv
  xsafeRunH_agree)

noncomputable section
open Classical

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **A step of FL4 with the glue premises named, the start fact at the serial-prefix memory `H`.** -/
structure Fl4StepWPRH (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (H : U64 → U64) (Ch : S → Prop) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) (Ch' : S → Prop) : Prop where
  /-- [P] an armed program is pure glue. -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start fact, **at the serial-prefix memory `H`** (module docstring). -/
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ i, SF Ch K H hK hU c (fun l => s.lk l = some c) k i
  /-- [P] the serial exit's ghost choice. -/
  serX : SerStep s c → SerExitW P K'.toKLayoutV Ch'
  /-- The glue's layout convention at the serial exit: no VCPU, the PTE set `ptesR` of the exit memory. -/
  serC : SerStep s c → K'.vcpus = ∅ ∧ K'.ptes = ptesR K' s'.mem
  /-- [P] the exit ghost with rule 8. -/
  serG : SerStep s c → MapsP K' s'
  /-- Layout and chain change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

/-- **An execution of FL4 with the reachability-convention glue steps and its serial-prefix memory** (ghost). -/
inductive ExecWPRH (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (U64 → U64) → (S → Prop) → Prop
  | refl : ExecWPRH LP SF P s0 K0 Ch0 s0 K0 s0.mem Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {H : U64 → U64} {Ch Ch' : S → Prop} {c : U64} :
      ExecWPRH LP SF P s0 K0 Ch0 s K H Ch → Step s c s' → Fl4StepWPRH LP SF P s K H Ch c s' K' Ch' →
      ExecWPRH LP SF P s0 K0 Ch0 s' K' (NextH s c s' H) Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {H : U64 → U64} {Ch : S → Prop} {v a x : U64} :
      ExecWPRH LP SF P s0 K0 Ch0 s K H Ch → HwStepP K s v a x →
      ExecWPRH LP SF P s0 K0 Ch0 (hwCfg s a x) K (Function.update H a x) Ch

end exec

/-! ## The top -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EP
