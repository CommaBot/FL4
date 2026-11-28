/-
# P2 (line p3mc, gen 47): `InsV15N` [J] narrowed to the starts still open; the new A/D top

* `InsV15NO cfg Op` [J]: `InsV15N cfg` asked only at the view starts `(s, K, c, ρ, k0, i)` with `Op s K c ρ k0 i`;
  **`insV15NO_of_N`**: `InsV15N` gives it at any `Op`.
* `Open47 c ρ i` (the starts still open after gen 47): every index but the vx ones (`VxPm`, P2/InsV15Vx), the vt
  ones (`VtPm`, P2/InsV15Vt) and the st ones whose target is, in `ρ`, another core's (`StFPm`, P2/InsV15St).
* **`insV15N_of_NO`**: for `ExecCfg.nativePmKAD B`, `InsV15NO … Open47` gives `InsV15N` (`insAP_vx_view`,
  `insAP_vt_view`, `insAP_stF_view` at the closed starts). With `insV15NO_of_N` the two premises are equivalent.
* **`serializable_fl4_V15_pmKADV`**: gen 46's `serializable_fl4_V15_pmKADN` with `InsV15NO … Open47` [J] for
  `InsV15N` [J]; **`serializable_fl4_V15_pmKADNofV`**: gen 46's statement follows from it.

Named premises: `InsV15NO … Open47` [J] (replaces `InsV15N` [J] on the new top; justification as `InsV15` [J],
P2/E2EPV15AD). New module; no existing statement changed.

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `insV15NO_of_N`, `insV15N_of_NO`,
`serializable_fl4_V15_pmKADV`, `serializable_fl4_V15_pmKADNofV`.
-/
import Fl4Proofs.P2.InsV15Vt
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

section opn
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

variable (arI AR MR) in
/-- **[J] `InsV15N` asked only at the view starts `Op`** (module docstring; justification as `InsV15` [J]). -/
def InsV15NO {ι : Type} (cfg : ExecCfg S ι)
    (Op : Cfg U64 U64 U64 U64 → KLayoutP → U64 → (U64 → U64) → SP → ι → Prop) : Prop :=
  ∀ (Ch : S → Prop) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (E : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (c : U64) (k0 : SP) (ρ : U64 → U64) (i : ι), Op s K c ρ k0 i →
    (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) → EpochJV K E s → MapsP K s →
    VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem →
    cfg.SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k0 i →
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if cfg.NoV i then annV s K c ρ k0 else k0)

end opn

section pm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- **The view starts at which `InsV15N` is still asked after gen 47** (module docstring). -/
def Open47 (_s : Cfg U64 U64 U64 U64) (_K : KLayoutP) (c : U64) (ρ : U64 → U64) (_k0 : SP) (i : IxV13Pm S) :
    Prop :=
  ¬ VxPm (S := S) i ∧ ¬ VtPm (S := S) i ∧ ¬ StFPm (S := S) c ρ i

end pm

end
end Fl4Proofs.P2.E2EP
