/-
P2 (line lvm, gen 5): **what lifting the existing paths to `ownV` needs, and the top theorem with both families**.

Gen 4 lifted an `own` local path to `ownV` (`E2EV.LocalPath.liftV`) under `NoVcpuRd` [W]; gen 5 weakens
`NoVcpuRd` to the non-binding VCPU words (`E2EV.VData`: a binding word `TCB` / `NEXT` / `PREV` is the gate's under
both maps, `E2EV.rpermV_of_own_nd`). The lead asked to discharge it once from the layout. That is not possible
for the paths as they stand:

* **`not_noVcpuRd`**: a path whose `ReadSet` contains every aligned kernel word that is gate-only under `own`
  (the maximal sets every existing path uses: `MaxR` = `RPerm (own K) … ∧ Aligned`, `IoRS`, `SlRS`, all of the
  form `… RPerm (own K) …`) fails `NoVcpuRd` as soon as one aligned non-binding VCPU word exists (`own` gives
  every VCPU word to the gate, `OwnMapV.own_vcpu`). `NoVcpuRd` is a property of the read **set**, and those sets
  were chosen maximal; what the code actually reads is only visible inside each path's `acc` / `dec_alt` /
  `ReadOnce` proofs.
* **`rsV`**, **`noVcpuRd_rsV`**: the cut read set `RS ∧ ¬ VData`; a path built on it satisfies `NoVcpuRd` by
  definition, so `liftV` needs nothing more. Rebuilding an existing path on `rsV K RS` re-proves its `acc` (its
  read callbacks: each word it reads is not a non-binding VCPU word, from `RegionOKV.none` and the word's
  region), `dec_alt` / `ReadOnce` / `PathSide.read_aligned` (for `Alt` over the smaller set). That is per-path
  work for each existing path's owner line, not a layout fact (handoff §14).
* **`serializable_e2eV_lift`** (decision 4): the lifted existing paths beside the VM paths (`PathsV.sum`) give
  `serializable_e2eV`; `serializable_e2e` stays unchanged. Premises: those of `serializable_e2eV` (`RegionOKV` /
  `UserOKV` [J], `Fl4StepV` [P]/[J], `HwStepV` [P], per path `LocalPath`'s) and `NoVcpuRd` [W] of each lifted path.
-/
import Fl4Proofs.P2.E2EV
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2E Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

section
variable {K : KLayoutV} {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64} {User : U64 → Prop}

/-- **A maximal `own` read set fails `NoVcpuRd`** (module docstring): if the path's `ReadSet` at an entry state
contains every aligned non-user word that is gate-only under `own`, any aligned non-binding VCPU word is in it. -/
theorem not_noVcpuRd (hK : RegionOKV K) {P : LocalPath (OwnMap.own K.toKLayout) cls ko User}
    (hmax : ∀ s x, P.Pre s → Aligned x → ¬ User x →
      GateOnly (OwnMap.own K.toKLayout) (@LawfulStore.mem _ P.st P.L s) x → P.RS s x)
    {s : P.S} (hs : P.Pre s) {x : U64} (hx : VData K x) (ha : Aligned x) (hu : ¬ User x) :
    ¬ NoVcpuRd K P := by
  intro hN
  obtain ⟨v, hv, hg⟩ := hx
  exact hN s x hs (hmax s x hs ha hu (own_vcpu hK hv)) hu ⟨v, hv, hg⟩

/-- The read set `RS` cut to words that are not non-binding VCPU words. -/
def rsV {S : Type} (K : KLayoutV) (RS : S → U64 → Prop) (s : S) (x : U64) : Prop :=
  RS s x ∧ ¬ VData K x

/-- A path whose `ReadSet` avoids the non-binding VCPU words (e.g. one built on `rsV K RS`) satisfies
`NoVcpuRd`. -/
theorem noVcpuRd_of {P : LocalPath (OwnMap.own K.toKLayout) cls ko User}
    (h : ∀ s x, P.RS s x → ¬ VData K x) : NoVcpuRd K P :=
  fun s x _ hr _ => h s x hr

theorem noVcpuRd_rsV {P : LocalPath (OwnMap.own K.toKLayout) cls ko User} {RS : P.S → U64 → Prop}
    (h : P.RS = rsV K RS) : NoVcpuRd K P :=
  noVcpuRd_of fun s x hr => by rw [h] at hr; exact hr.2

end

/-- **End to end with the existing paths lifted and the VM paths beside them** (decision 4): an execution
over `PathsV.sum (PathsV.ofPaths LP hN) LQ` (the existing `own` paths `LP`, each with `NoVcpuRd` [W], lifted by
`LocalPath.liftV`; the VM paths `LQ`, stated for `ownV`) and the hardware's steps is serializable where no local
path is in progress. `serializable_e2e` is kept as it is. -/
theorem serializable_e2eV_lift {ι κ : Type} (LP : Paths ι)
    (hN : ∀ i (K : KLayoutV) m (hK : RegionOKV K) (hU : UserOKV K), NoVcpuRd K (LP i K.toKLayout m hK.base hU.base))
    (LQ : PathsV κ) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV} (h0 : Init s0) (hA0 : ArmInv s0)
    (hK0 : RegionOKV K0) (hU0 : UserOKV K0) (hM0 : MapsV K0 s0)
    (h : ExecV (PathsV.sum (PathsV.ofPaths LP hN) LQ) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_e2eV _ h0 hA0 hK0 hU0 hM0 h hq

end
end Fl4Proofs.P2.E2EV
