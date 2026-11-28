/-
# P2 (line p3mc, gen 46): `InsV15` [J] narrowed to the armed program (`InsV15N` [J])

`InsV15 cfg` (P2/E2EPV15AD) asks `InsAP` at every CoreView start for the body `k0` where `¬ NoV i` **and** for its
re-annotation `annV s K c ρ k0` at every index. By `insAP_annV` (P2/InsV15Cert: the re-annotation keeps `InsAP`),
the re-annotation's obligation follows from `k0`'s wherever `k0`'s is asked. So the premise narrows to
**`InsV15N cfg`** [J]: at every CoreView start, `InsAP` of the *one* program the glue arms there — `k0` where
`¬ NoV i`, `annV … k0` where `NoV i`.

* **`insV15_of_N`**: `InsV15N cfg → InsV15 cfg`.
* **`serializable_fl4_V15_adN`** / **`serializable_fl4_V15_pmKADN`**: gen 45's A/D tops with `InsV15N` [J] in place of
  `InsV15` [J]; the old statements follow (`…_ad`, `…_pmKAD` take the stronger premise).
* `insV15N_of`: the converse (`InsV15` gives `InsV15N`), so the two premises are equivalent: the narrowing removes a
  redundant obligation, it does not weaken the conclusion.

Named premises: `InsV15N` [J] (replaces `InsV15` [J] on the new tops). New module; no existing statement changes.

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `insV15_of_N`,
`serializable_fl4_V15_adN`, `serializable_fl4_V15_pmKADN`.
-/
import Fl4Proofs.P2.InsV15Cert
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

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

variable (arI AR MR) in
/-- **[J] The armed program is insensitive to the walker's A/D writes** (module docstring): `InsV15` asked only of the
program the glue arms at the start — the body `k0` where `¬ NoV i`, its re-annotation `annV` where `NoV i`. -/
def InsV15N (cfg : ExecCfg S ι) : Prop :=
  ∀ (Ch : S → Prop) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (E : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (c : U64) (k0 : SP) (ρ : U64 → U64) (i : ι),
    (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) → EpochJV K E s → MapsP K s →
    VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem →
    cfg.SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k0 i →
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if cfg.NoV i then annV s K c ρ k0 else k0)

/-- **`InsV15` gives `InsV15N`**: the two premises are equivalent. -/
theorem insV15N_of {cfg : ExecCfg S ι} (h : InsV15 (L := L) arI AR MR cfg) : InsV15N (L := L) arI AR MR cfg := by
  intro Ch s K E hK hU c k0 ρ i hC J hM hVq hi
  by_cases hn : cfg.NoV i
  · rw [if_pos hn]; exact h Ch s K E hK hU c _ k0 ρ i hC J hM hVq hi (Or.inr rfl)
  · rw [if_neg hn]; exact h Ch s K E hK hU c _ k0 ρ i hC J hM hVq hi (Or.inl ⟨rfl, hn⟩)

end

section pm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

end pm

end
end Fl4Proofs.P2.E2EP
