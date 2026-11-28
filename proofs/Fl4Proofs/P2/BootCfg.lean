/-
# P2 (line p3mc, gen 36): **the initial configuration at the boot, and every premise of V12 / V13 at once**
Gen 35 (`P2/BootJAtZ`) made `P`, `hIoa`, `hB` of `serializable_fl4_localV12` jointly satisfiable under `OpaqueH`.
This module adds the start-side premises and an execution:
* **`s0B O`**: the serial machine's initial configuration. Memory = the boot store's words `memB` (the memory `sB`
  is built from), gate open, no ticket holder, no lock held, every core idle, empty log; the ghost maps are rule 8's
  for the boot layout `KB O` (`ownP`, `OwnMap.cls`, `OwnMap.ko` at `memB`). It is `cfg0 (KB O) memB`: the
  configurations `cfg0 … cfg7` and the execution `exec_cfg` are stated for an abstract layout `K` and memory `m`
  (with `hB`, `hc0` as hypotheses), so that no `rfl` unfolds `chainC`'s choice.
* **`KB_ksb`**: whatever layout `chainC` picks at the boot, its kernel base is `kbB` (`chainC_spec`: it is a
  `layoutJ … (L.ksb sB) …`). **`namedM_B`**: no VSpace root is named in `memB` (the 2048 ASID-table words are 0,
  `wordB_zero_of`), so **`ptesR_B`**: `ptesR (KB O) memB = ∅`, and **`hc0_B`**: `(KB O).vcpus = ∅ ∧ (KB O).ptes =
  ptesR (KB O) memB` — for every choice `chainC` makes (only `ksb` is read). `KB O` is used unchanged.
* **`init_B`** (`Init`), **`armInv_B`** (`ArmInv`), **`mapsP_B`** (`MapsP`), **`noLoc_B`**.
* **`exec_B`**: a non-empty execution from `s0B O` (gen 56: an `ExecV15 cfg` for every configuration whose VCPU
  convention admits the VCPU-free layout; until gen 55 an `ExecWPRV12` for every path family / start fact): core 0
  arms the empty glue `.done`, enters, leaves (log `[.done]`), takes the ticket,
  scans itself, drains, and runs the empty serial body, releasing with the gate open (log `[.done, .done]`). Every
  step's `Fl4StepV15` fields hold: `arm` (`PureGlue.done`), `serX` (gen 35's `serExitW_B`), `serC` (`hc0_B`),
  `serG` (the serial step installs `ownP (KB O)` again), `keep`; `start` is not reached (no `.start` marker).
  The end state `c7B O` satisfies `NoLoc` (`hq`).
* The concrete instance (store `bst`, arch `archT` for both `ar` and `arI`, `hA := archT_total`, `AR := ART`,
  `MR := modelMR`) is applied to V15 in P2/BootV15 (`runAllV15_B`); gen 55 / 56 retired the V12 / V13 forms
  (`premisesV12_B`, `premisesV13_B`, `runAllV12_B`, `runAllV13_B`).

## What the witness does not exercise
* The step field `start` [P] of the step (and so `StartV2C`'s / `StartV13`'s contents, V13's [J] `ybw` and
  `anch` inside `StartV13`, and every path family's start obligations): the execution never runs a `.start` marker,
  so no local path body starts. A witness that runs one needs the glue's start fact at a real view (U-level
  `StartAt`), not attempted here.
* `HwStepP` steps: `KB O` has no VCPU, so none can occur.
No premise added. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootJAtZ
import Fl4Proofs.P2.E2EPV15Base
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical
open Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2EV Fl4Proofs.P2.OwnMapP Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.E2EP
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue Phase Gate Prog Run release)
open Fl4Proofs.P2.E2E (SerStep SP)

noncomputable section

/-! ## The layout's kernel base and the PTE convention at `memB` -/

/-- **The layout `chainC` picks at the boot has kernel base `kbB`** (for every choice). -/
theorem KB_ksb (O : LocPlatM.OpaqueH) : (KB O).ksb = kbB := by
  obtain ⟨Z, H, Cx, nc, hK, -⟩ := chainC_spec (LocPlatM.locPlat_archT O bs_ext) jReach_B
  exact (congrArg OwnMap.KLayout.ksb hK).trans rfl

/-- **No VSpace root is named in `memB`**: the ASID table is empty. -/
theorem namedM_B {r : U64} : ¬ NamedM memB kbB r := by
  rintro ⟨hi, hh, hne, -⟩
  apply hne
  show wordB (Vs.atA kbB hi).val = 0#u64
  rw [Vs.atA_val (by rw [kbB_val]; norm_num) hh, kbB_val]
  exact wordB_zero_of (by omega)

/-- **No leaf PTE is reachable in `memB`** (for every choice of `chainC`). -/
theorem ptesR_B (O : LocPlatM.OpaqueH) : ptesR (KB O) memB = ∅ := by
  ext e
  constructor
  · intro he
    obtain ⟨⟨r, hr, -⟩, -⟩ := he
    rw [KB_ksb] at hr
    exact (namedM_B hr).elim
  · intro he
    exact False.elim he

/-- **`hc0` at the boot layout and memory.** -/
theorem hc0_B (O : LocPlatM.OpaqueH) : (KB O).vcpus = ∅ ∧ (KB O).ptes = ptesR (KB O) memB :=
  ⟨rfl, (ptesR_B O).symm⟩

/-! ## The initial configuration and the execution, for an abstract layout and memory -/

section gen
variable (K : KLayoutP) (m : U64 → U64)

/-- The serial machine at rest: memory `m`, gate open, nothing held, every core idle, rule 8's ghosts for `K`. -/
def cfg0 : Cfg U64 U64 U64 U64 where
  mem := m
  gate := .opn
  holder := none
  seen := ∅
  lk := fun _ => none
  ph := fun _ => .idle
  own := ownP K
  cls := OwnMap.cls K.toKLayout
  ko := OwnMap.ko K.toKLayout m
  log := []

/-- Core 0 armed with the empty glue. -/
def cfg1 : Cfg U64 U64 U64 U64 := { cfg0 K m with ph := Function.update (cfg0 K m).ph 0#u64 (.arm .done) }
/-- Core 0 in the (empty) local path. -/
def cfg2 : Cfg U64 U64 U64 U64 := { cfg1 K m with ph := Function.update (cfg1 K m).ph 0#u64 (.loc .done .done ∅) }
/-- The local path left. -/
def cfg3 : Cfg U64 U64 U64 U64 :=
  { cfg2 K m with lk := release (cfg2 K m).lk 0#u64, ph := Function.update (cfg2 K m).ph 0#u64 .idle,
                  log := (cfg2 K m).log ++ [.done] }
/-- Core 0 holds the ticket; the gate drains. -/
def cfg4 : Cfg U64 U64 U64 U64 :=
  { cfg3 K m with holder := some 0#u64, seen := ∅, ph := Function.update (cfg3 K m).ph 0#u64 (.ser .done),
                  gate := if (cfg3 K m).gate = .opn then .draining else (cfg3 K m).gate }
/-- Core 0 scanned itself. -/
def cfg5 : Cfg U64 U64 U64 U64 := { cfg4 K m with seen := insert 0#u64 (cfg4 K m).seen }
/-- The gate closed. -/
def cfg6 : Cfg U64 U64 U64 U64 := { cfg5 K m with gate := .closed }
/-- The empty serial body ran; the gate opens again. -/
def cfg7 : Cfg U64 U64 U64 U64 :=
  { cfg6 K m with mem := (cfg6 K m).mem, holder := none, ph := Function.update (cfg6 K m).ph 0#u64 .idle,
                  gate := if false then .closed else .opn, log := (cfg6 K m).log ++ [.done],
                  own := ownP K, cls := OwnMap.cls K.toKLayout, ko := OwnMap.ko K.toKLayout (cfg6 K m).mem }

theorem cfg0_ph (d : U64) : (cfg0 K m).ph d = .idle := rfl
theorem cfg1_ph0 : (cfg1 K m).ph 0#u64 = .arm .done := by simp [cfg1]
theorem cfg2_ph0 : (cfg2 K m).ph 0#u64 = .loc .done .done ∅ := by simp [cfg2]
theorem cfg3_ph0 : (cfg3 K m).ph 0#u64 = .idle := by simp [cfg3]
theorem cfg4_ph0 : (cfg4 K m).ph 0#u64 = .ser .done := by simp [cfg4]
theorem cfg5_ph0 : (cfg5 K m).ph 0#u64 = .ser .done := cfg4_ph0 K m
theorem cfg6_ph0 : (cfg6 K m).ph 0#u64 = .ser .done := cfg4_ph0 K m
theorem cfg7_ph0 : (cfg7 K m).ph 0#u64 = .idle := by simp [cfg7]

/-- Every other core stays idle. -/
theorem cfg6_ph {d : U64} (hd : d ≠ 0#u64) : (cfg6 K m).ph d = .idle := by
  show Function.update (Function.update (Function.update (Function.update (cfg0 K m).ph 0#u64 (.arm .done)) 0#u64
    (.loc .done .done ∅)) 0#u64 .idle) 0#u64 (.ser .done) d = .idle
  simp only [Function.update_of_ne hd, cfg0_ph]

theorem cfg7_ph (d : U64) : (cfg7 K m).ph d = .idle := by
  by_cases hd : d = 0#u64
  · subst hd; exact cfg7_ph0 K m
  · exact (Function.update_of_ne hd _ _).trans (cfg6_ph K m hd)

theorem cfg_init : Init (cfg0 K m) := ⟨rfl, fun d h => by rw [cfg0_ph] at h; exact h⟩

theorem cfg_armInv : ArmInv (cfg0 K m) := fun c p h => by rw [cfg0_ph] at h; cases h

theorem cfg_noLoc : NoLoc (cfg7 K m) := fun d h => by rw [cfg7_ph] at h; exact h

theorem cfg7_mem : (cfg7 K m).mem = m := rfl

theorem mapsP_cfg0 : MapsP K (cfg0 K m) := ⟨rfl, rfl, rfl⟩
theorem mapsP_cfg1 : MapsP K (cfg1 K m) := ⟨rfl, rfl, rfl⟩
theorem mapsP_cfg2 : MapsP K (cfg2 K m) := ⟨rfl, rfl, rfl⟩
theorem mapsP_cfg3 : MapsP K (cfg3 K m) := ⟨rfl, rfl, rfl⟩
theorem mapsP_cfg4 : MapsP K (cfg4 K m) := ⟨rfl, rfl, rfl⟩
theorem mapsP_cfg5 : MapsP K (cfg5 K m) := ⟨rfl, rfl, rfl⟩
theorem mapsP_cfg6 : MapsP K (cfg6 K m) := ⟨rfl, rfl, rfl⟩
theorem mapsP_cfg7 : MapsP K (cfg7 K m) := ⟨rfl, rfl, rfl⟩

theorem cfg_steps :
    Step (cfg0 K m) 0#u64 (cfg1 K m) ∧ Step (cfg1 K m) 0#u64 (cfg2 K m) ∧ Step (cfg2 K m) 0#u64 (cfg3 K m) ∧
    Step (cfg3 K m) 0#u64 (cfg4 K m) ∧ Step (cfg4 K m) 0#u64 (cfg5 K m) ∧ Step (cfg5 K m) 0#u64 (cfg6 K m) ∧
    Step (cfg6 K m) 0#u64 (cfg7 K m) :=
  ⟨Step.arm .done rfl, Step.enter (cfg1_ph0 K m) rfl, Step.leave (cfg2_ph0 K m), Step.take .done (cfg3_ph0 K m) rfl,
    Step.scan 0#u64 rfl rfl (by rw [cfg4_ph0]; exact id),
    Step.drain rfl rfl (fun d => by
      by_cases hd : d = 0#u64
      · subst hd; exact Or.inl (show (0#u64 : U64) ∈ insert 0#u64 (cfg4 K m).seen from Set.mem_insert _ _)
      · exact Or.inr (cfg6_ph K m hd)),
    Step.serial false _ _ _ rfl rfl (cfg6_ph0 K m) (Run.done _)⟩

end gen

section exec
variable {ι : Type} {cfg : ExecCfg BS ι}
  {P : LocPlat bst LocPlatM.archT LocPlatM.ART modelMR} {K : KLayoutP} {Ch0 : U64 → BS → Prop} {m : U64 → U64}

theorem noArm_idle {s' : Cfg U64 U64 U64 U64} {c : U64} (h : s'.ph c = .idle) :
    ∀ p, s'.ph c = .arm p → PureGlue p := fun p h' => by rw [h] at h'; cases h'

theorem noSt_idle {s : Cfg U64 U64 U64 U64} {c : U64} (h : s.ph c = .idle) :
    ∀ p0 k W, s.ph c ≠ .loc p0 (.start k) W := fun p0 k W h' => by rw [h] at h'; cases h'

/-- A step keeping the layout and chain at a configuration with memory `m` and rule 8's ghosts: every field of
`Fl4StepV15` from the phases at `c`. -/
theorem stepW_keep (hB : ∀ e, SerExitW P K.toKLayoutV (Ch0 e)) (hc : cfg.VcpuOK K m ∧ K.ptes = ptesR K m)
    {s s' : Cfg U64 U64 U64 U64} {c : U64}
    (harm : ∀ p, s'.ph c = .arm p → PureGlue p)
    (hst : ∀ p0 k W, s.ph c ≠ .loc p0 (.start k) W) (hm : s'.mem = m) (hM : MapsP K s') :
    Fl4StepV15 cfg P s K Ch0 c s' K Ch0 where
  arm := harm
  start p0 k W h := absurd h (hst p0 k W)
  serX _ := hB
  serC _ := by rw [hm]; exact hc
  serG _ := hM
  keep _ := ⟨rfl, rfl⟩

theorem execE {s0 s s' : Cfg U64 U64 U64 U64} {E : U64 → U64} (he : ExecV15 cfg P s0 K Ch0 s K Ch0 E)
    (hS : Step s 0#u64 s') (g : Fl4StepV15 cfg P s K Ch0 0#u64 s' K Ch0) : ∃ E', ExecV15 cfg P s0 K Ch0 s' K Ch0 E' :=
  ⟨_, .step he hS g⟩

/-- **The seven-step execution** (module docstring), for any layout / chain satisfying `hB` and `hc0`. -/
theorem exec_cfg (hB : ∀ e, SerExitW P K.toKLayoutV (Ch0 e)) (hc : cfg.VcpuOK K m ∧ K.ptes = ptesR K m) :
    ∃ E, ExecV15 cfg P (cfg0 K m) K Ch0 (cfg7 K m) K Ch0 E := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := cfg_steps K m
  obtain ⟨_, e1⟩ := execE (cfg := cfg) (P := P) (s0 := cfg0 K m) (s := cfg0 K m) .refl h1
    (stepW_keep hB hc (fun p h => by rw [cfg1_ph0] at h; cases h; exact .done) (noSt_idle (cfg0_ph K m _)) rfl
      (mapsP_cfg1 K m))
  obtain ⟨_, e2⟩ := execE e1 h2 (stepW_keep hB hc (fun p h => by rw [cfg2_ph0] at h; cases h)
      (fun p0 k W h => by rw [cfg1_ph0] at h; cases h) rfl (mapsP_cfg2 K m))
  obtain ⟨_, e3⟩ := execE e2 h3 (stepW_keep hB hc (noArm_idle (cfg3_ph0 K m))
      (fun p0 k W h => by rw [cfg2_ph0] at h; cases h) rfl (mapsP_cfg3 K m))
  obtain ⟨_, e4⟩ := execE e3 h4 (stepW_keep hB hc (fun p h => by rw [cfg4_ph0] at h; cases h)
      (noSt_idle (cfg3_ph0 K m)) rfl (mapsP_cfg4 K m))
  obtain ⟨_, e5⟩ := execE e4 h5 (stepW_keep hB hc (fun p h => by rw [cfg5_ph0] at h; cases h)
      (fun p0 k W h => by rw [cfg4_ph0] at h; cases h) rfl (mapsP_cfg5 K m))
  obtain ⟨_, e6⟩ := execE e5 h6 (stepW_keep hB hc (fun p h => by rw [cfg6_ph0] at h; cases h)
      (fun p0 k W h => by rw [cfg5_ph0] at h; cases h) rfl (mapsP_cfg6 K m))
  exact execE e6 h7 (stepW_keep hB hc (noArm_idle (cfg7_ph0 K m))
      (fun p0 k W h => by rw [cfg6_ph0] at h; cases h) rfl (mapsP_cfg7 K m))

end exec

/-! ## At the boot -/

/-- **The initial configuration at the boot** (module docstring). -/
abbrev s0B (O : LocPlatM.OpaqueH) : Cfg U64 U64 U64 U64 := cfg0 (KB O) memB
/-- The end of the execution. -/
abbrev c7B (O : LocPlatM.OpaqueH) : Cfg U64 U64 U64 U64 := cfg7 (KB O) memB

theorem init_B (O : LocPlatM.OpaqueH) : Init (s0B O) := cfg_init _ _
theorem armInv_B (O : LocPlatM.OpaqueH) : ArmInv (s0B O) := cfg_armInv _ _
theorem mapsP_B (O : LocPlatM.OpaqueH) : MapsP (KB O) (s0B O) := mapsP_cfg0 _ _
theorem noLoc_B (O : LocPlatM.OpaqueH) : NoLoc (c7B O) := cfg_noLoc _ _

/-- **A non-empty execution from `s0B O`** (module docstring), for every configuration whose VCPU convention
admits the VCPU-free layout. -/
theorem exec_B {ι : Type} {cfg : ExecCfg BS ι} (O : LocPlatM.OpaqueH) (hv : ∀ K m, K.vcpus = ∅ → cfg.VcpuOK K m) :
    ∃ E, ExecV15 cfg (LocPlatM.locPlat_archT O bs_ext) (s0B O) (KB O) (fun _ => ChB O) (c7B O) (KB O)
      (fun _ => ChB O) E :=
  exec_cfg (fun _ => serExitW_B O) ⟨hv _ _ (hc0_B O).1, (hc0_B O).2⟩

end
end Fl4Proofs.P2.BootSt
