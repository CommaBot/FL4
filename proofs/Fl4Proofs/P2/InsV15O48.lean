/-
# P2 (line p3mc, gen 48): `InsV15NO` [J] narrowed to the starts still open after gen 48; the new A/D top

* `Open48 s K c ρ k0 i`: gen 47's `Open47` without the st starts whose target is homed (`StHPm`, P2/InsV15StH).
* **`insV15NO47_of_48`**: for `ExecCfg.nativePmKAD B`, `InsV15NO … Open48` gives `InsV15NO … Open47`
  (`insAP_stH_view` at the closed starts); **`insV15NO48_of_47`**: the converse (`Open48 ⊆ Open47`). The two
  premises are equivalent.
* **`serializable_fl4_V15_pmKADH`**: gen 47's `serializable_fl4_V15_pmKADV` with `InsV15NO … Open48` [J] for
  `InsV15NO … Open47` [J]; **`serializable_fl4_V15_pmKADVofH`**: gen 47's statement follows from it.

Named premises: `InsV15NO … Open48` [J] (replaces `InsV15NO … Open47` [J] on the new top; justification as `InsV15`
[J], P2/E2EPV15AD). New module; no existing statement changed.

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `insV15NO47_of_48`,
`insV15NO48_of_47`, `serializable_fl4_V15_pmKADH`, `serializable_fl4_V15_pmKADVofH`.
-/
import Fl4Proofs.P2.InsV15StH
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll VEq InsAP)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent)

noncomputable section
open Classical

section pm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- **The view starts at which `InsV15N` is still asked after gen 48** (module docstring). -/
def Open48 (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (c : U64) (ρ : U64 → U64) (k0 : SP) (i : IxV13Pm S) :
    Prop :=
  Open47 s K c ρ k0 i ∧ ¬ StHPm (S := S) c ρ i

end pm

end
end Fl4Proofs.P2.E2EP
