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
One inductive, per-core `CoreView.view` start facts and one P3 chain per core exactly as `ExecWPRV12`, plus the epoch
memory `E` (the memory at the last serial step, as mmuAD's `ExecVX4e`) and an `ad` constructor for `cfg.AdStep`.
Steps: `Fl4StepV15` = `Fl4StepWPRV12` with `serC` reading `cfg.VcpuOK`.

## Proved
* **`execWPRV12_of_V15`**: with no A/D step (`NoAd cfg`) and `VcpuOK ⊆ {vcpus = ∅}`, an `ExecV15 cfg` is an
  `ExecWPRV12 cfg.Fam cfg.NoV cfg.SF`; **`execV15_of_WPRV12`**: conversely when `{vcpus = ∅} ⊆ VcpuOK`;
  **`execV15_native_iff`**: for the native configuration the two executions coincide (`∃ E`).
* **`SlotOblV15 cfg`**: the per-slot obligations at the CoreView (the native analogue of mmuAD's `InsA`): the
  start fact gives `StartAt` at the physical memory (`sf`), `VSafe` at the starts arming the plain body (`vs`), the
  re-annotated body `Safe` at the others (`fh`) — `execPV9_of_WPRV10S`'s three hypotheses.
* **`serializable_fl4_V15_exact`**: `SlotOblV15 cfg`, `NoAd cfg`, `VcpuOK ⊆ {vcpus = ∅}` ⇒ `RunAll s.log s0.mem
  s.mem`; **`serializable_fl4_V15_perm`**: the same with the permuted conclusion (`ℓ = s.log`) — the form mmuAD's
  AD tops have; its A/D content (PageMap slots with `InsAP`) needs `SerialADP`, not on this branch.
* Native instance **`ExecCfg.native`** (`Fam := fl4LocV13`, `NoV := ¬ IoIx`, `SF := StartV13`, `VcpuOK := vcpus =
  ∅`, `AdStep := False`): **`serializable_fl4_V15_native`** (from V13) and **`serializable_fl4_localV13ofV15`**
  (V13's exact statement from the native top): V13 is recovered losslessly.
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

/-- **A step of FL4 under `cfg`**: `Fl4StepWPRV12`'s fields, the serial exit's layout convention `cfg.VcpuOK`. -/
structure Fl4StepV15 (cfg : ExecCfg S ι) (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutP)
    (Ch : U64 → S → Prop) (c : U64) (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) (Ch' : U64 → S → Prop) : Prop where
  /-- [P] an armed program is pure glue. -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start fact at `c`'s view (as `Fl4StepWPRV12.start`). -/
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

/-- **Without A/D steps and with no VCPU, an `ExecV15` is an `ExecWPRV12`.** -/
theorem execWPRV12_of_V15 {cfg : ExecCfg S ι} (hAd : cfg.NoAd) (hV : cfg.VcpuNone) {P : LocPlat st arI AR MR}
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} {E : U64 → U64}
    (h : ExecV15 cfg P s0 K0 Ch0 s K Ch E) : ExecWPRV12 cfg.Fam cfg.NoV cfg.SF P s0 K0 Ch0 s K Ch := by
  induction h with
  | refl => exact .refl
  | step _ hS g ih =>
    exact .step ih hS ⟨g.arm, g.start, g.serX, fun hs => ⟨hV _ _ (g.serC hs).1, (g.serC hs).2⟩, g.serG, g.keep⟩
  | hw _ hH ih => exact .hw ih hH
  | ad _ hA _ => exact absurd hA (hAd _ _ _ _ _)

/-- **An `ExecWPRV12` is an `ExecV15`** whenever `vcpus = ∅` meets the configuration's VCPU convention. -/
theorem execV15_of_WPRV12 {cfg : ExecCfg S ι} (hV : ∀ K m, K.vcpus = ∅ → cfg.VcpuOK K m)
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop}
    (h : ExecWPRV12 cfg.Fam cfg.NoV cfg.SF P s0 K0 Ch0 s K Ch) : ∃ E, ExecV15 cfg P s0 K0 Ch0 s K Ch E := by
  induction h with
  | refl => exact ⟨_, .refl⟩
  | step _ hS g ih =>
    obtain ⟨E, ih⟩ := ih
    exact ⟨_, .step ih hS ⟨g.arm, g.start, g.serX, fun hs => ⟨hV _ _ (g.serC hs).1, (g.serC hs).2⟩, g.serG,
      g.keep⟩⟩
  | hw _ hH ih =>
    obtain ⟨E, ih⟩ := ih
    exact ⟨E, .hw ih hH⟩

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

/-- **The per-slot obligations at the CoreView** (module docstring; `execPV9_of_WPRV10S`'s hypotheses). -/
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

/-- **V15, exact form** (module docstring). -/
theorem serializable_fl4_V15_exact {cfg : ExecCfg S ι} (O : SlotOblV15 (L := L) arI AR MR cfg) (hAd : cfg.NoAd)
    (hV : cfg.VcpuNone) (P : LocPlat st arI AR MR) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : cfg.VcpuOK K0 s0.mem ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecV15 cfg P s0 K0 Ch0 s K Ch E) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  have hc0' : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem := ⟨hV _ _ hc0.1, hc0.2⟩
  obtain ⟨hK0, hU0⟩ := okP_R (hB 0#u64) hc0'
  have h10 : ExecWPRV10 cfg.Fam cfg.NoV (fun _ _ _ _ _ i => cfg.NoV i) cfg.SF P s0 K0 Ch0 s K Ch :=
    execWPRV10_of_11 (fun _ _ _ _ _ _ hn => hn) (execWPRV11_of_12 (execWPRV12_of_V15 hAd hV h))
  exact serializable_e2ePV9 _ h0 hA0 hK0 hU0 hM0
    (execPV9_of_WPRV10S O.sf O.vs (fun Ch s K hK hU c k ρ i hC hE hsf hM hVq hn => O.fh Ch s K hK hU c k ρ i hC hE
      hsf hM hVq hn) P h0 hA0 hB hc0' hM0 h10).1 hq

/-- **V15, permuted form** (module docstring): the exact form's conclusion with `ℓ = s.log`. -/
theorem serializable_fl4_V15_perm {cfg : ExecCfg S ι} (O : SlotOblV15 (L := L) arI AR MR cfg) (hAd : cfg.NoAd)
    (hV : cfg.VcpuNone) (P : LocPlat st arI AR MR) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : cfg.VcpuOK K0 s0.mem ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecV15 cfg P s0 K0 Ch0 s K Ch E) (hq : NoLoc s) :
    ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem :=
  ⟨s.log, List.Perm.refl _, serializable_fl4_V15_exact O hAd hV P h0 hA0 hB hc0 hM0 h hq⟩

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

/-- **The native execution is V13's** (both directions). -/
theorem execV15_native_iff {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    {Ch0 Ch : U64 → S → Prop} :
    (∃ E, ExecV15 (ExecCfg.native st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch E) ↔
      ExecWPRV12 (fl4LocV13 st ar hA a0) (fun i => ¬ IoIx (S := S) i) (StartV13 st ar hA a0 arI AR MR) P s0 K0 Ch0
        s K Ch :=
  ⟨fun ⟨_, h⟩ => execWPRV12_of_V15 (native_noAd st ar hA a0 arI AR MR) (native_vcpuNone st ar hA a0 arI AR MR) h,
    fun h => execV15_of_WPRV12 (cfg := ExecCfg.native st ar hA a0 arI AR MR) (fun _ _ h => h) h⟩

/-- **V15's native top** (from V13). -/
theorem serializable_fl4_V15_native (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecV15 (ExecCfg.native st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localV13 st ar hA a0 P hIoa h0 hA0 hB hc0 hM0
    ((execV15_native_iff st ar hA a0).1 ⟨E, h⟩) hq

/-- **V13's exact statement from V15's native top** (V13 is recovered losslessly). -/
theorem serializable_fl4_localV13ofV15 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV12 (PathsP.sum (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (StartV13 st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨E, h'⟩ := (execV15_native_iff st ar hA a0).2 h
  exact serializable_fl4_V15_native st ar hA a0 P hIoa h0 hA0 hB hc0 hM0 h' hq

end native

end
end Fl4Proofs.P2.E2EP
