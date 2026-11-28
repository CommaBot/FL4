/-
# P2 (line p3mc, gen 41): V15's base — one execution `ExecV15 cfg` over an `ExecCfg`, V13 as its native instance

The Architect's V15 plan (handoff `architect-contracts.md`): one execution parameterised by an `ExecCfg`, with V12 /
V13 the native instance and no new `ExecWPRV*` suffix forks. This module builds the part that does not depend on the
mmuAD line's A/D serialization theory (`SerialAD` / `SerialADR` / `SerialADP`, `MmuADWalk`, `MmuADEpoch`: not on
`par/p3mc`).

## `ExecCfg ι`
* `Fam : PathsP ι` (the slot family), `NoV : ι → Prop` (the paths armed re-annotated: V12's `¬ IoIx`), `SF` (the
  glue's start facts) — what V12 / V13 already take as parameters;
* `VcpuOK : KLayoutP → (U64 → U64) → Prop`: the layout convention at the start and at every serial exit (native:
  `vcpus = ∅`); the PTE convention `K.ptes = ptesR K m` stays fixed beside it;
* `HwStep` is not a field: it is always `HwStepP` (`ExecCfg.HwStep`, agreed round 2);
* `AdStep : KLayoutP → (U64 → U64) → (U64 → U64) → U64 → U64 → Prop`: the walker's environment write at layout `K`,
  epoch memory `E`, memory `m`, word `a := x` (`False` without A/D; mmuAD's instance is `MmuAD (PWE K E) m a x`).

## `ExecV15 cfg`
One inductive, per-core `CoreView.view` start facts and one P3 chain per core exactly as V13's execution, plus the epoch
memory `E` (the memory at the last serial step, as mmuAD's `ExecVX4e`) and an `ad` constructor for `cfg.AdStep`.
Steps: `Fl4StepV15` = V13's step with `serC` reading `cfg.VcpuOK`.

## Proved
* **`SlotOblV15 cfg`**: the per-slot obligations at the CoreView (the native analogue of mmuAD's `InsA`): the
  start fact gives `StartAt` at the physical memory (`sf`), `VSafe` at the starts arming the plain body (`vs`), the
  re-annotated body `Safe` at the others (`fh`).
* **`execPV9_of_V15C`** (gen 56): with `SlotOblV15 cfg`, no A/D step (`NoAd cfg`) and `VcpuOK ⊆ {vcpus = ∅}`, an
  `ExecV15C cfg P` over the re-based platform (`P : LocPlatC`) is U9's `ExecPV9 cfg.Fam`, the exits keeping
  `SerExitC` and the layout convention. Until gen 55 this went `ExecV15 → ExecWPRV12 → 11 → 10` and
  `execPV9_of_WPRV10S`; those executions are retired.
* **`serializable_fl4_V15_exact_C`** / **`serializable_fl4_V15_perm_C`** (gen 56): `SlotOblV15 cfg`, `NoAd cfg`,
  `VcpuOK ⊆ {vcpus = ∅}`, `P : LocPlatC`, an `ExecV15C` ⇒ `RunAll s.log s0.mem s.mem` (resp. with `ℓ = s.log`).
  **`serializable_fl4_V15_exact`** / **`serializable_fl4_V15_perm`** (statements unchanged; `P : LocPlat`, an
  `ExecV15`) are their one-line corollaries at `P.toC`, `ExecV15.toC`. The A/D content (PageMap slots with
  `InsAP`) needs `SerialADP`, not on this branch.
* Native instance **`ExecCfg.native`** (`Fam := fl4LocV13`, `NoV := ¬ IoIx`, `SF := StartV13`, `VcpuOK := vcpus =
  ∅`, `AdStep := False`), `native_noAd`, `native_vcpuNone`. Gen 56 retired `execV15_native_iff`,
  `serializable_fl4_V15_native` and `serializable_fl4_localV13ofV15` with `ExecWPRV12` (handoff §61).
* `execV15_vcpus`, **`hwV15_dead`**: `hw_dead` as a derived lemma (no `HwStepP` step at a VCPU-free layout).

No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.E2EPV13
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP)

noncomputable section
open Classical

/-! ## The configuration -/

/-- **An execution configuration** (module docstring). -/
structure ExecCfg (S : Type) (ι : Type) where
  /-- The slot family. -/
  Fam : PathsP ι
  /-- The paths whose armed program is the re-annotated body (V12's `¬ IoIx`). -/
  NoV : ι → Prop
  /-- [P] The glue's start facts. -/
  SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop
  /-- The layout convention for VCPUs at the start and at serial exits. -/
  VcpuOK : KLayoutP → (U64 → U64) → Prop
  /-- [P] The walker's A/D write at layout `K`, epoch memory `E`, memory `m`: `a := x`. -/
  AdStep : KLayoutP → (U64 → U64) → (U64 → U64) → U64 → U64 → Prop

/-- The hardware step of every configuration: `HwStepP`. -/
abbrev ExecCfg.HwStep {S ι : Type} (_cfg : ExecCfg S ι) : KLayoutP → Cfg U64 U64 U64 U64 → U64 → U64 → U64 → Prop :=
  HwStepP

/-- No A/D step. -/
def ExecCfg.NoAd {S ι : Type} (cfg : ExecCfg S ι) : Prop := ∀ K E m a x, ¬ cfg.AdStep K E m a x

/-- The VCPU convention implies no VCPU. -/
def ExecCfg.VcpuNone {S ι : Type} (cfg : ExecCfg S ι) : Prop := ∀ K m, cfg.VcpuOK K m → K.vcpus = ∅

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **A step of FL4 under `cfg`**: V13's step fields, the serial exit's layout convention `cfg.VcpuOK`. -/
structure Fl4StepV15 (cfg : ExecCfg S ι) (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutP)
    (Ch : U64 → S → Prop) (c : U64) (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) (Ch' : U64 → S → Prop) : Prop where
  /-- [P] an armed program is pure glue. -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start fact at `c`'s view. -/
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ ρ : U64 → U64, VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem ∧
      ∃ i k0, cfg.SF (Ch c) K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k0 i ∧
        ((k = k0 ∧ ¬ cfg.NoV i) ∨ k = annV s K c ρ k0)
  /-- [P] the serial exit's ghost choice, one P3 chain per core. -/
  serX : SerStep s c → ∀ e, SerExitW P K'.toKLayoutV (Ch' e)
  /-- The layout convention at the serial exit. -/
  serC : SerStep s c → cfg.VcpuOK K' s'.mem ∧ K'.ptes = ptesR K' s'.mem
  /-- [P] the exit ghost with rule 8. -/
  serG : SerStep s c → MapsP K' s'
  /-- Layout and chains change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

/-- **The execution of V15** (module docstring): core steps, hardware steps, A/D steps; `E` the epoch memory. -/
inductive ExecV15 (cfg : ExecCfg S ι) (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP)
    (Ch0 : U64 → S → Prop) : Cfg U64 U64 U64 U64 → KLayoutP → (U64 → S → Prop) → (U64 → U64) → Prop
  | refl : ExecV15 cfg P s0 K0 Ch0 s0 K0 Ch0 s0.mem
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : U64 → S → Prop} {c : U64} {E : U64 → U64} :
      ExecV15 cfg P s0 K0 Ch0 s K Ch E → Step s c s' → Fl4StepV15 cfg P s K Ch c s' K' Ch' →
      ExecV15 cfg P s0 K0 Ch0 s' K' Ch' (if SerStep s c then s'.mem else E)
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : U64 → S → Prop} {E : U64 → U64} {v a x : U64} :
      ExecV15 cfg P s0 K0 Ch0 s K Ch E → cfg.HwStep K s v a x → ExecV15 cfg P s0 K0 Ch0 (hwCfg s a x) K Ch E
  | ad {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : U64 → S → Prop} {E : U64 → U64} {a x : U64} :
      ExecV15 cfg P s0 K0 Ch0 s K Ch E → cfg.AdStep K E s.mem a x → ExecV15 cfg P s0 K0 Ch0 (hwCfg s a x) K Ch E

/-- **`Fl4StepV15` on the re-based platform** (gen 54): the serial exit's ghost choice is `SerExitC P` for
`P : LocPlatC`; every other field is `Fl4StepV15`'s. -/
structure Fl4StepV15C (cfg : ExecCfg S ι) (P : LocPlatC st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutP)
    (Ch : U64 → S → Prop) (c : U64) (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) (Ch' : U64 → S → Prop) : Prop where
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ ρ : U64 → U64, VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem ∧
      ∃ i k0, cfg.SF (Ch c) K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k0 i ∧
        ((k = k0 ∧ ¬ cfg.NoV i) ∨ k = annV s K c ρ k0)
  serX : SerStep s c → ∀ e, SerExitC P K'.toKLayoutV (Ch' e)
  serC : SerStep s c → cfg.VcpuOK K' s'.mem ∧ K'.ptes = ptesR K' s'.mem
  serG : SerStep s c → MapsP K' s'
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

/-- **`ExecV15` on the re-based platform** (gen 54): the same constructors over `Fl4StepV15C`. -/
inductive ExecV15C (cfg : ExecCfg S ι) (P : LocPlatC st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP)
    (Ch0 : U64 → S → Prop) : Cfg U64 U64 U64 U64 → KLayoutP → (U64 → S → Prop) → (U64 → U64) → Prop
  | refl : ExecV15C cfg P s0 K0 Ch0 s0 K0 Ch0 s0.mem
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : U64 → S → Prop} {c : U64} {E : U64 → U64} :
      ExecV15C cfg P s0 K0 Ch0 s K Ch E → Step s c s' → Fl4StepV15C cfg P s K Ch c s' K' Ch' →
      ExecV15C cfg P s0 K0 Ch0 s' K' Ch' (if SerStep s c then s'.mem else E)
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : U64 → S → Prop} {E : U64 → U64} {v a x : U64} :
      ExecV15C cfg P s0 K0 Ch0 s K Ch E → cfg.HwStep K s v a x → ExecV15C cfg P s0 K0 Ch0 (hwCfg s a x) K Ch E
  | ad {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : U64 → S → Prop} {E : U64 → U64} {a x : U64} :
      ExecV15C cfg P s0 K0 Ch0 s K Ch E → cfg.AdStep K E s.mem a x → ExecV15C cfg P s0 K0 Ch0 (hwCfg s a x) K Ch E

/-- **Every `ExecV15` over the base platform is an `ExecV15C` over `P.toC`** (`SerExitW P = SerExitC P.toC`
definitionally). -/
theorem ExecV15.toC {cfg : ExecCfg S ι} {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h : ExecV15 cfg P s0 K0 Ch0 s K Ch E) :
    ExecV15C cfg P.toC s0 K0 Ch0 s K Ch E := by
  induction h with
  | refl => exact .refl
  | step _ hS g ih => exact .step ih hS ⟨g.arm, g.start, g.serX, g.serC, g.serG, g.keep⟩
  | hw _ hH ih => exact .hw ih hH
  | ad _ hA ih => exact .ad ih hA

/-- **The VCPU set stays empty along an `ExecV15` whose convention has no VCPU.** -/
theorem execV15_vcpus {cfg : ExecCfg S ι} (hV : cfg.VcpuNone) {P : LocPlat st arI AR MR}
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} {E : U64 → U64}
    (h : ExecV15 cfg P s0 K0 Ch0 s K Ch E) (h0 : K0.vcpus = ∅) : K.vcpus = ∅ := by
  induction h with
  | refl => exact h0
  | @step s s' K K' Ch Ch' c _ _ _ g ih =>
    by_cases hs : SerStep s c
    · exact hV _ _ (g.serC hs).1
    · rw [(g.keep hs).1]; exact ih
  | hw _ _ ih => exact ih
  | ad _ _ ih => exact ih

/-- No hardware step at a layout without VCPU. -/
theorem hwStepP_noVcpu {K : KLayoutP} (hv : K.vcpus = ∅) {s : Cfg U64 U64 U64 U64} {v a x : U64} :
    ¬ HwStepP K s v a x := by
  intro H
  rcases H.frame a (by simpa using H.chg) with h | ⟨⟨hv', -⟩, -⟩
  · exact H.kern h
  · have : v ∈ (∅ : Set U64) := hv ▸ hv'
    exact this

/-- **`hw_dead`, derived for `ExecV15`**: no hardware step fires along an execution whose convention has no VCPU. -/
theorem hwV15_dead {cfg : ExecCfg S ι} (hV : cfg.VcpuNone) {P : LocPlat st arI AR MR}
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} {E : U64 → U64}
    (h : ExecV15 cfg P s0 K0 Ch0 s K Ch E) (hc0 : cfg.VcpuOK K0 s0.mem) {v a x : U64} :
    ¬ cfg.HwStep K s v a x :=
  hwStepP_noVcpu (execV15_vcpus hV h (hV _ _ hc0))

/-! ## The per-slot obligations and the two tops -/

/-- **The per-slot obligations at the CoreView** (module docstring; `execPV9_of_V15C`'s hypotheses). -/
structure SlotOblV15 (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)
    (cfg : ExecCfg S ι) : Prop where
  /-- The start fact gives `StartAt` at the physical memory. -/
  sf : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
    (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) → EpochPteN K s.mem →
    cfg.SF Ch K s.mem hK hU c hs q i → StartAt (cfg.Fam i K s.mem hK hU) c hs s.mem q
  /-- `VSafe` where the plain body is armed. -/
  vs : ∀ (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) c k ρ i, MapsP K s →
    VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem → ¬ cfg.NoV i → VSafe cfg.Fam s K c k hK hU ρ i
  /-- The re-annotated body is `Safe` where it is armed. -/
  fh : ∀ (Ch : S → Prop) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) c k ρ i,
    (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) → EpochPteN K (CoreView.view K.toKLayout c ρ) →
    cfg.SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i → MapsP K s →
    VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem → cfg.NoV i →
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k)

/-- **An `ExecV15C` with no A/D step and no VCPU is U9's execution `ExecPV9` of its family** (gen 56: directly,
not through `ExecWPRV12 → 11 → 10`): each start step's start fact gives `StartAt` at the view (`O.sf`), the plain
body `VSafe` (`O.vs`), the re-annotated one `Safe` (`O.fh`) or `VSafe9` (`O.vs`); the serial exits keep the chains
and the layout convention; between them the gate words keep the last exit's values. -/
theorem execPV9_of_V15C {cfg : ExecCfg S ι} (O : SlotOblV15 (L := L) arI AR MR cfg) (hAd : cfg.NoAd)
    (hV : cfg.VcpuNone) (P : LocPlatC st arI AR MR) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : ∀ e, SerExitC P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecV15C cfg P s0 K0 Ch0 s K Ch E) :
    ExecPV9 cfg.Fam s0 K0 s K ∧ (∀ e, SerExitC P K.toKLayoutV (Ch e)) ∧
      ∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x := by
  obtain ⟨hK0, hU0⟩ := okP_R_C (hB 0#u64) hc0
  induction h with
  | refl => exact ⟨.refl, hB, s0, hc0, fun _ _ => rfl⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ _ hS g ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    obtain ⟨H1, hR, -, -, hM⟩ := exec_safeRunPV9 h0 hA0 hK0 hU0 hM0 hE
    have hst : Fl4StepPV9 cfg.Fam s1 K1 c1 s1' K1' := by
      refine ⟨g.arm, fun p0 k W hph hK hU => ?_, fun hs => ?_, fun hn => (g.keep hn).1⟩
      · obtain ⟨ρ, hVq, i, k0, hi, hvs⟩ := g.start p0 k W hph hK hU
        have hρg : ∀ x, GateW K1 x → ρ x = e1.mem x := fun x hx =>
          (hVq.2.1 x (by rw [hM.own, hx s1.mem]; exact Or.inr rfl)).trans (hk1 x hx)
        have hEv : EpochPteN K1 (CoreView.view K1.toKLayout c1 ρ) :=
          epochPteN_view c1 (epochPteN_of ⟨e1, hCe, hρg⟩)
        refine ⟨ρ, hVq, i, k0, O.sf (Ch1 c1) _ { s1 with mem := CoreView.view K1.toKLayout c1 ρ } _ _ _ _ _ i
          (hX c1).chainOf hEv hi, ?_⟩
        rcases hvs with ⟨hk, hn⟩ | hk
        · exact Or.inl ⟨hk, O.vs s1 K1 hK hU c1 k0 ρ i hM hVq hn⟩
        · refine Or.inr ⟨hk, ?_⟩
          by_cases hn : cfg.NoV i
          · exact fun _ _ => O.fh (Ch1 c1) s1 K1 hK hU c1 k0 ρ i (hX c1).chainOf hEv hi hM hVq hn
          · exact vSafe9_of_vSafe (O.vs s1 K1 hK hU c1 k0 ρ i hM hVq hn)
      · have hP := okP_R_C (g.serX hs 0#u64) ⟨hV _ _ (g.serC hs).1, (g.serC hs).2⟩
        exact ⟨hP.1, hP.2, g.serG hs⟩
    refine ⟨.step hE hS hst, ?_, ?_⟩
    · by_cases hs : SerStep s1 c1
      · exact g.serX hs
      · obtain ⟨e1, e2⟩ := g.keep hs
        rw [e1, e2]; exact hX
    · by_cases hs : SerStep s1 c1
      · exact ⟨s1', ⟨hV _ _ (g.serC hs).1, (g.serC hs).2⟩, fun _ _ => rfl⟩
      · obtain ⟨eK, -⟩ := g.keep hs
        subst eK
        obtain ⟨-, -, -, hSI, -⟩ := Fl4Proofs.P2.Serial.xsafeRunH_inv h0 hA0 hR
        refine ⟨e1, hCe, fun x hx => ?_⟩
        rw [← hk1 x hx]
        exact step_gate_keep hM (Fl4Proofs.P2.Serial.allowed_of_sinv hSI c1) hS hs hx
  | @hw s1 K1 Ch1 _ v a y _ hH ih =>
    obtain ⟨hE, hX, e1, hCe, hk1⟩ := ih
    obtain ⟨H1, -, hK, -, hM⟩ := exec_safeRunPV9 h0 hA0 hK0 hU0 hM0 hE
    refine ⟨.hw hE hH, hX, e1, hCe, fun x hx => ?_⟩
    rw [← hk1 x hx]
    exact hw_gate_keep hK hM hH hx
  | ad _ hA _ => exact absurd hA (hAd _ _ _ _ _)

/-- **V15, exact form, on the re-based platform** (gen 56; module docstring): `P : LocPlatC`, the execution an
`ExecV15C`. -/
theorem serializable_fl4_V15_exact_C {cfg : ExecCfg S ι} (O : SlotOblV15 (L := L) arI AR MR cfg)
    (hAd : cfg.NoAd) (hV : cfg.VcpuNone) (P : LocPlatC st arI AR MR) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : ∀ e, SerExitC P K0.toKLayoutV (Ch0 e)) (hc0 : cfg.VcpuOK K0 s0.mem ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecV15C cfg P s0 K0 Ch0 s K Ch E) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  have hc0' : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem := ⟨hV _ _ hc0.1, hc0.2⟩
  obtain ⟨hK0, hU0⟩ := okP_R_C (hB 0#u64) hc0'
  exact serializable_e2ePV9 _ h0 hA0 hK0 hU0 hM0 (execPV9_of_V15C O hAd hV P h0 hA0 hB hc0' hM0 h).1 hq

/-- **V15, exact form** (module docstring). -/
theorem serializable_fl4_V15_exact {cfg : ExecCfg S ι} (O : SlotOblV15 (L := L) arI AR MR cfg) (hAd : cfg.NoAd)
    (hV : cfg.VcpuNone) (P : LocPlat st arI AR MR) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : cfg.VcpuOK K0 s0.mem ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecV15 cfg P s0 K0 Ch0 s K Ch E) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_V15_exact_C O hAd hV P.toC h0 hA0 hB hc0 hM0 h.toC hq

/-- **V15, permuted form, on the re-based platform** (gen 56): the exact form's conclusion with `ℓ = s.log`. -/
theorem serializable_fl4_V15_perm_C {cfg : ExecCfg S ι} (O : SlotOblV15 (L := L) arI AR MR cfg)
    (hAd : cfg.NoAd) (hV : cfg.VcpuNone) (P : LocPlatC st arI AR MR) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : ∀ e, SerExitC P K0.toKLayoutV (Ch0 e)) (hc0 : cfg.VcpuOK K0 s0.mem ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecV15C cfg P s0 K0 Ch0 s K Ch E) (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  ⟨s.log, List.Perm.refl _, serializable_fl4_V15_exact_C O hAd hV P h0 hA0 hB hc0 hM0 h hq⟩

/-- **V15, permuted form** (module docstring): the exact form's conclusion with `ℓ = s.log`. -/
theorem serializable_fl4_V15_perm {cfg : ExecCfg S ι} (O : SlotOblV15 (L := L) arI AR MR cfg) (hAd : cfg.NoAd)
    (hV : cfg.VcpuNone) (P : LocPlat st arI AR MR) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : cfg.VcpuOK K0 s0.mem ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecV15 cfg P s0 K0 Ch0 s K Ch E) (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  serializable_fl4_V15_perm_C O hAd hV P.toC h0 hA0 hB hc0 hM0 h.toC hq

end exec

/-! ## The native instance: V13 -/

section native
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- V13's family: U18's with the invocation summands. -/
abbrev fl4LocV13 :=
  PathsP.sum (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0)
    (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
      (cmSlotU st ar hA (masksWr_plain st)))

/-- **The native configuration** (module docstring). -/
def ExecCfg.native : ExecCfg S (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) where
  Fam := fl4LocV13 st ar hA a0
  NoV := fun i => ¬ IoIx (S := S) i
  SF := StartV13 st ar hA a0 arI AR MR
  VcpuOK := fun K _ => K.vcpus = ∅
  AdStep := fun _ _ _ _ _ => False

theorem native_noAd : (ExecCfg.native st ar hA a0 arI AR MR).NoAd := fun _ _ _ _ _ h => h

theorem native_vcpuNone : (ExecCfg.native st ar hA a0 arI AR MR).VcpuNone := fun _ _ h => h

variable {arI AR MR}

end native

end
end Fl4Proofs.P2.E2EP
