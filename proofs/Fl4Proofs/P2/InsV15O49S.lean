/-
# P2 (line p3mc, gen 49): the open set without the sl starts; the new A/D top

After P2/InsV15O49 (every vmF and vmR start closed), P2/InsV15FhS closes `InsV15V`'s obligation of `nativePmKAD B` at
**every** sl start without a VCPU (`insAP_sl_view`: the homed starts by gen 48's `sl_insA_annV_h`, the others by the
foreign-handler pattern). So all eight W11 slots but io and irq are closed.

* `Open49S s K c ρ k0 i := Open49 … ∧ ¬ SlPm i`.
* **`insV15NOV49S_of_49`** (any `B`; `Open49S ⊆ Open49`), **`insV15NOV49_of_49S`** (from `P`, `hIoa`, `B`; at the sl
  starts by `insAP_sl_view`): the two premises are equivalent for `nativePmKAD B`.
* **`serializable_fl4_V15_pmKADS`** (authoritative): `serializable_fl4_V15_pmKADF` with `InsV15NOV … Open49S` [J] for
  `InsV15NOV … Open49` [J], all other premises unchanged; **`serializable_fl4_V15_pmKADFofS`**: the previous statement
  from it.

Named premises: `InsV15NOV … Open49S` [J] (replaces `InsV15NOV … Open49` [J]; justification as `InsV15` [J],
P2/E2EPV15AD). New module; no existing statement changed.

Gen 56 (handoff p3mc §61) retired, with `ExecWPRV10–12` and the V15 stepping stones: `insV15NOV49S_of_49`,
`serializable_fl4_V15_pmKADS`, `serializable_fl4_V15_pmKADFofS`.
-/
import Fl4Proofs.P2.InsV15O49
import Fl4Proofs.P2.InsV15FhS
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

/-- **The view starts at which the obligation is still asked after gen 49's sl step, at layouts without a VCPU**
(module docstring). -/
def Open49S (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (c : U64) (ρ : U64 → U64) (k0 : SP) (i : IxV13Pm S) :
    Prop :=
  Open49 st s K c ρ k0 i ∧ ¬ SlPm (S := S) i

set_option maxHeartbeats 4000000 in
/-- **`insV15NOV49_of_49S` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem insV15NOV49_of_49S_C (P : LocPlatCR st arI AR MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks)
    (h : InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open49S st)) :
    InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open49 st) := by
  intro Ch s K E hK hU c k0 ρ i nv hO hC J hM hVq hi
  by_cases hl : SlPm (S := S) i
  · exact insAP_sl_view_C st ar hA a0 P B E nv hl hC J hM hVq hi
  exact h Ch s K E hK hU c k0 ρ i nv ⟨hO, hl⟩ hC J hM hVq hi

set_option maxHeartbeats 4000000 in
/-- **`InsV15NOV … Open49S` gives `InsV15NOV … Open49`** for `nativePmKAD B` (module docstring). -/
theorem insV15NOV49_of_49S (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks)
    (h : InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open49S st)) :
    InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open49 st) :=
  insV15NOV49_of_49S_C st ar hA a0 (locPlatCR_of P hIoa) B h

/-- **`serializable_fl4_V15_pmKADS` on the re-based platform**
(gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem serializable_fl4_V15_pmKADS_C (P : LocPlatCR st arI AR MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks)
    (hI : InsV15NOV (L := L) arI AR MR (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) (Open49S st))
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitC P.toC K0.toKLayoutV (Ch0 e))
    (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecV15C (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) P.toC s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_fl4_V15_pmKADF_C st ar hA a0 P B (insV15NOV49_of_49S_C st ar hA a0 P B hI) h0 hA0 hB hc0 hM0 h
    hq

end pm

end
end Fl4Proofs.P2.E2EP
