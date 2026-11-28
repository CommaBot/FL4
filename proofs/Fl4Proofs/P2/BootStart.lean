/-
# P2 (line p3mc, gen 37): **an execution from the boot that runs a `.start` marker**, the start fact proved

Gen 36 (`P2/BootCfg`) gave every premise of V12 / V13 at one concrete instance, but its execution never reached a
`.start` marker, so the step field `start` [P] (hence `StartV2C` / `StartV13`) was never
exercised. This module runs one.

* **The path**: the timer interrupt (`irq`, `fl4-sync` `local_timer_irq`, `crates/fl4-sync/src/lib.rs` l.632–662,
  body `localtimer::handle_timer_irq_local`), the cheapest index of `famB`: its start clause (`StartP3W4`'s irq
  clause, reached from `StartV2C` through `StartU2C` … `StartP3W11JV`) asks only `LkC`, the slot's record
  `IrqPremK2B` (`bun`, `lt`, `kd` [P], `pl` [P]) and a `GlueAt` whose entry fact is `Ch σ` — no `NonIdle` [P] and no
  `yb` / `ybw` [J] (those are only in the vmF / vmR / sl clauses, see below).
* **The index `jB`**: IRQ 2 (the timer IRQ, `IrqPremK2B.lt`'s docstring), lock set `∅` (`fun _ _ => False`), and the
  plan `planB` with no due timer (`ntfn = ep = reply = 0`, `n = 0`: `plan_timer_irq`, `crates/fl4-core/src/
  localtimer.rs` l.333–367, names no object when no timer is due), so `PlanLk` holds with no lock taken.
* **The view is the identity at the boot** (`homed_B`, `view_B`): at `sB` (a state of the boot chain `ChB O`,
  `chB_sB`) every TCB of the layout is homed on core 0 (`GlueCross.slJAt_aff`), every SC has `CORE = 0`
  (`SchedRel.core` with `JAtZ.hscC`), and the only nonzero words of `memB` lie below core 1's node
  (`kbB + 17856`), so `CoreView.Homed (KB O) 0 memB` and `view (KB O) 0 memB = memB` — for every choice `chainC`
  makes (only `ksb`, `RegionOK` and the bundle at `sB` are read). `sB_mem`: `bsL.mem sB = memB` (all 15 nonzero
  words are aligned).
* **`startIrq_B`** / **`startIrqV13_B`**: the irq start fact of `StartV2C` / `StartV13` at core 0's view of `memB`,
  the boot chain `ChB O`, lock set `∅`, for the program `k0B` = the PTE cut of the lifted irq path's body
  `(pathB O hK hU).body sB a` (the extracted `handle_timer_irq_local` at the store state `sB` and Arch state `a`):
  `GlueAt` with `σ = sB` (`Ch sB`, core 0, no lock, memory = `memB` on every word).
* **The execution** (`exec_start`, `execStartV13_B`; gen 56: an `ExecV15` of the native configuration, until gen
  55 an `ExecWPRV12`, with `execStartV12_B` for V12's start fact, now retired): from `s0B O`,
  core 0 arms the glue
  `.start kB` (`PureGlue.start`), enters, and takes the `.start` step to `.loc (.start kB) kB ∅` (`dfg3_ph0`). `kB`
  is the re-annotated body `annV … k0B` (gen 29's narrowing: irq is not an io index, so the armed program is
  `annV k0`; `kB_eq`). The `start` field of that step is proved (`g3_gen`) from `startIrq_B` with `ρ := memB`
  (`VEq` reflexive) — not vacuously: the hypothesis `s.ph 0 = .loc p0 (.start k) W` holds. P2/BootRun runs the
  body to the end; gen 56 retired `startReachedV12_B` / `startReachedV13_B` (V12 / V13's premises up to `hq`).

## The vmF / vmR / sl starts (the clauses carrying `yb` / `ybw` [J]) at the boot memory
* **`nonIdle_false_B`**: `NonIdle` [P] (a field of `VmFEntJ14` / `VmREntU` / `SlEntU` and of V13's `VmFEntV13` /
  `VmREntV13` / `SlEntV13`) is **false at `sB`**: `jReach_B` is a `JReachU17` at `sB` with `σB.curThread =
  σB.idleThread`. So at the boot memory (current thread = the idle thread) no vmF / vmR / sl start fact holds with
  `σ = sB`, and V13's `ybw` cannot be reached by an execution starting there before a serial step installs a user
  thread (a new P3 exit with a non-idle current thread: not attempted).
* **`ybw_B`**: `ybw` [J] itself (`YBW (KB O) sB`) holds at the boot state (no TCB's `YIELD_TO` word is nonzero:
  TCBs are 4 KiB-aligned and no nonzero word of `memB` sits at offset 3472).
* `anch` is not part of `StartV13` (it is V14's anchored start, P2/E2EVFl4W14); nothing here exhibits it.

## No VCPU
Gen 56 retired `execWPRV12_vcpus` / `hwStepP_false` / `hw_dead` with `ExecWPRV12`: their V15 forms are
`execV15_vcpus`, `hwStepP_noVcpu`, `hwV15_dead` (P2/E2EPV15Base).

No premise added. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootCfg
import Fl4Proofs.P2.E2EPU6
import Fl4Proofs.P2.GlueCross
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical
open Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2EV Fl4Proofs.P2.OwnMapP Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.E2EP
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue Phase Gate Prog Run release VEq)
open Fl4Proofs.P2.E2E (SerStep SP)

noncomputable section

/-! ## The boot memory, chain and view -/

/-- **The boot store's word map is `memB`** (unaligned words are 0 in both). -/
theorem sB_mem : bsL.mem sB = memB := by
  funext a
  by_cases ha : Aligned a
  · exact memB_mem ha
  · show (if Aligned a then memB a else 0#u64) = memB a
    rw [if_neg ha]
    show 0#u64 = wordB a.val
    unfold Aligned at ha
    exact (wordB_zero_of (by omega)).symm

theorem chB_spec (O : LocPlatM.OpaqueH) :
    ChainOf (L := bsL) LocPlatM.archT LocPlatM.ART modelMR sB (KB O).toKLayout (ChB O) :=
  chainC_spec (LocPlatM.locPlat_archT O bs_ext) jReach_B

/-- **The boot state is on the boot chain.** -/
theorem chB_sB (O : LocPlatM.OpaqueH) : ChB O sB := by
  obtain ⟨Z, H, Cx, nc, -, -, -, -, h⟩ := chB_spec O
  exact h

theorem chB_lay (O : LocPlatM.OpaqueH) : ChainLay (L := bsL) (KB O).toKLayout (ChB O) := by
  obtain ⟨Z, H, Cx, nc, -, -, -, h, -⟩ := chB_spec O
  exact h

/-- **The boot state is a bundle state of the boot layout.** -/
theorem slJAt_sB (O : LocPlatM.OpaqueH) : SlJAt (L := bsL) (KB O).toKLayout sB :=
  (chB_lay O).bun sB (chB_sB O)

theorem region_node_inv' {K : OwnMap.KLayout} {b d : U64} (h : OwnMap.region K b = .node d) :
    OwnMap.InNode K d b := by
  unfold OwnMap.region at h
  split_ifs at h with h1 h2 h3 h4 h5 h6
  cases h; exact Classical.choose_spec h1

/-- **`memB` is homed on core 0 at the boot layout** (module docstring). -/
theorem homed_B (O : LocPlatM.OpaqueH) : CoreView.Homed (KB O).toKLayout 0#u64 memB := by
  have hJ := slJAt_sB O
  refine ⟨fun t ht => ?_, fun p b hb => ?_, fun d b hb hd _ => ?_⟩
  · obtain ⟨-, -, e⟩ := GlueCross.slJAt_aff hJ ht
    rw [sB_mem] at e
    exact e
  · obtain ⟨z, hp, -⟩ := OwnMap.region_sc_inv hb
    obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
    have hpC := B.j.hscC p z hp
    have e1 := B.j.xtop.fin.1.1.1.core p hpC
    obtain ⟨Q, R0, hcq, -⟩ := B.j.xtop.fin.1.1.1.lists
    have e2 := hcq.cur
    rw [sB_mem] at e1
    exact e1.trans e2.symm
  · obtain ⟨-, h1, -⟩ := region_node_inv' hb
    have hk : (KB O).toKLayout.ksb = kbB := KB_ksb O
    have hd1 : d.val ≠ 0 := fun h0 => hd (UScalar.eq_of_val_eq (by simp [h0]))
    rw [hk, kbB_val] at h1
    show wordB b.val = 0#u64
    exact wordB_zero_of (by omega)

/-- **Core 0's view of the boot memory is the boot memory.** -/
theorem view_B (O : LocPlatM.OpaqueH) : CoreView.view (KB O).toKLayout 0#u64 memB = memB :=
  CoreView.view_eq_self (chB_lay O).hK (homed_B O)

/-! ## The timer-interrupt index and its path at the boot -/

/-- A timer-IRQ plan with no due timer (no notification, endpoint or reply object named). -/
def planB : localtimer.TimerIrqPlan :=
  { tm := 0#u64, ntfn := 0#u64, waiter := 0#u64, ep := 0#u64, reply := 0#u64,
    objects := Array.repeat 3#usize (0#u64, 0#u64), n := 0#usize }

/-- **The index**: IRQ 2 (the timer), the plan `planB`, no lock held. -/
def jB : IrqArg BS := { irq := 2#u64, pl := planB, lk := fun _ _ => False }

/-- **The irq slot's record at the boot layout** (`K.vcpus = ∅` and `IrqPremK2B`). -/
theorem irqPrem_B (O : LocPlatM.OpaqueH) (m : U64 → U64) :
    (irqSlotP3W bst LocPlatM.archT LocPlatM.archT_total (masksWr_plain bst)).Prem jB (KB O).toKLayoutV m :=
  ⟨rfl, ⟨⟨sB, slJAt_sB O⟩, by decide, fun s _ => (lkC_const (S := BS) _).kernDetS _ s,
    fun _ => ⟨fun h => absurd rfl h, fun h => absurd rfl h, fun h => absurd rfl h⟩⟩⟩

/-- The lifted timer-IRQ path at the boot layout and memory. -/
def pathB (O : LocPlatM.OpaqueH) (hK : RegionOKP (KB O)) (hU : UserOKP (KB O)) :=
  (irqSlotP3W bst LocPlatM.archT LocPlatM.archT_total (masksWr_plain bst)).liftAt jB (KB O).toKLayoutV memB
    hK.base hU.base (irqPrem_B O memB)

/-- **The started program**: the PTE cut of the path's body from `sB` and the Arch state `a`. -/
def k0B (O : LocPlatM.OpaqueH) (a : Fl4Spec.MachineState) (hK : RegionOKP (KB O)) (hU : UserOKP (KB O)) : SP :=
  cutP (· ∈ (KB O).ptes) (· ∈ (KB O).user) (OwnMap.cls (KB O).toKLayout) (OwnMap.ko (KB O).toKLayout memB) 0#u64
    ((pathB O hK hU).body sB a) ∅

/-- **The irq start fact of `StartV2C` at the boot** (module docstring). -/
theorem startIrq_B (O : LocPlatM.OpaqueH) (a0 a : Fl4Spec.MachineState) (hK : RegionOKP (KB O))
    (hU : UserOKP (KB O)) (hs : U64 → Prop) (hhs : (fun _ => False) = hs) :
    StartV2C bst LocPlatM.archT LocPlatM.archT_total a0 LocPlatM.archT LocPlatM.ART modelMR (ChB O) (KB O) memB hK hU
      0#u64 hs (k0B O a hK hU) (.inl (.irq jB)) := by
  subst hhs
  exact ⟨lkC_const _, fun _ => ⟨(pathB O hK hU).body sB a,
    ⟨irqPrem_B O memB, sB, a, chB_sB O, rfl, rfl, fun x _ _ => congrFun sB_mem x, rfl⟩, rfl⟩⟩

/-- **The irq start fact of `StartV13` at the boot** (V13's irq clause is `StartU2C`'s, as V12's). -/
theorem startIrqV13_B (O : LocPlatM.OpaqueH) (a0 a : Fl4Spec.MachineState) (hK : RegionOKP (KB O))
    (hU : UserOKP (KB O)) (hs : U64 → Prop) (hhs : (fun _ => False) = hs) :
    StartV13 bst LocPlatM.archT LocPlatM.archT_total a0 LocPlatM.archT LocPlatM.ART modelMR (ChB O) (KB O) memB hK hU
      0#u64 hs (k0B O a hK hU) (.inl (.irq jB)) :=
  startIrq_B O a0 a hK hU hs hhs

/-! ## The configurations of the start, for an abstract layout, memory and body -/

section gen
variable (K : KLayoutP) (m : U64 → U64) (k : SP)

/-- Core 0 armed with the glue `.start k`. -/
def dfg1 : Cfg U64 U64 U64 U64 := { cfg0 K m with ph := Function.update (cfg0 K m).ph 0#u64 (.arm (.start k)) }
/-- Core 0 entered its local path. -/
def dfg2 : Cfg U64 U64 U64 U64 :=
  { dfg1 K m k with ph := Function.update (dfg1 K m k).ph 0#u64 (.loc (.start k) (.start k) ∅) }
/-- Core 0 took the `.start` step: the body `k` is to run. -/
def dfg3 : Cfg U64 U64 U64 U64 :=
  { dfg2 K m k with ph := Function.update (dfg2 K m k).ph 0#u64 (.loc (.start k) k ∅) }

theorem dfg1_ph0 : (dfg1 K m k).ph 0#u64 = .arm (.start k) := by simp [dfg1]
theorem dfg2_ph0 : (dfg2 K m k).ph 0#u64 = .loc (.start k) (.start k) ∅ := by simp [dfg2]
theorem dfg3_ph0 : (dfg3 K m k).ph 0#u64 = .loc (.start k) k ∅ := by simp [dfg3]

theorem dfg_steps :
    Step (cfg0 K m) 0#u64 (dfg1 K m k) ∧ Step (dfg1 K m k) 0#u64 (dfg2 K m k) ∧
    Step (dfg2 K m k) 0#u64 (dfg3 K m k) :=
  ⟨Step.arm (.start k) rfl, Step.enter (dfg1_ph0 K m k) rfl, Step.start (dfg2_ph0 K m k)⟩

theorem mapsP_dfg1 : MapsP K (dfg1 K m k) := ⟨rfl, rfl, rfl⟩
theorem mapsP_dfg2 : MapsP K (dfg2 K m k) := ⟨rfl, rfl, rfl⟩
theorem mapsP_dfg3 : MapsP K (dfg3 K m k) := ⟨rfl, rfl, rfl⟩

/-- No lock is held in the start's configurations. -/
theorem dfg2_lk : (fun _ : U64 => False) = fun l => (dfg2 K m k).lk l = some 0#u64 :=
  funext fun _ => propext ⟨False.elim, fun h => by change (none : Option U64) = some 0#u64 at h; cases h⟩

end gen

section exec
variable {ι : Type} {cfg : ExecCfg BS ι}
  {P : LocPlat bst LocPlatM.archT LocPlatM.ART modelMR} {K : KLayoutP} {Ch0 : U64 → BS → Prop} {m : U64 → U64}

/-- **The three-step execution to a `.start` step**, given the `start` step's fields `g3`. -/
theorem exec_start {k : SP} (hB : ∀ e, SerExitW P K.toKLayoutV (Ch0 e))
    (hc : cfg.VcpuOK K m ∧ K.ptes = ptesR K m)
    (g3 : Fl4StepV15 cfg P (dfg2 K m k) K Ch0 0#u64 (dfg3 K m k) K Ch0) :
    ∃ E, ExecV15 cfg P (cfg0 K m) K Ch0 (dfg3 K m k) K Ch0 E := by
  obtain ⟨h1, h2, h3⟩ := dfg_steps K m k
  obtain ⟨_, e1⟩ := execE (cfg := cfg) (P := P) (s0 := cfg0 K m) (s := cfg0 K m) .refl h1
    (stepW_keep hB hc (fun p h => by rw [dfg1_ph0] at h; cases h; exact .start k) (noSt_idle (cfg0_ph K m _)) rfl
      (mapsP_dfg1 K m k))
  obtain ⟨_, e2⟩ := execE e1 h2 (stepW_keep hB hc (fun p h => by rw [dfg2_ph0] at h; cases h)
      (fun p0 k' W h => by rw [dfg1_ph0] at h; cases h) rfl (mapsP_dfg2 K m k))
  exact execE e2 h3 g3

end exec

/-! ## The `.start` step at the boot -/

/-- The index type of `famB`. -/
abbrev IxB := Fl4IxW (S := BS) ⊕ ((InvArg BS ⊕ InvArg BS) ⊕ InvArg BS)

/-- **The armed body**: the re-annotated started program (`annV`), at any `RegionOKP` / `UserOKP` proofs. -/
def kB (O : LocPlatM.OpaqueH) (a : Fl4Spec.MachineState) : SP :=
  if h : RegionOKP (KB O) ∧ UserOKP (KB O) then annV (cfg0 (KB O) memB) (KB O) 0#u64 memB (k0B O a h.1 h.2)
  else .done

/-- **The armed body is the re-annotation of the started program** at every start's proofs. -/
theorem kB_eq (O : LocPlatM.OpaqueH) (a : Fl4Spec.MachineState) (hK : RegionOKP (KB O)) (hU : UserOKP (KB O)) :
    kB O a = annV (dfg2 (KB O) memB (kB O a)) (KB O) 0#u64 memB (k0B O a hK hU) := by
  unfold kB
  rw [dif_pos ⟨hK, hU⟩]
  rfl

/-- **The `.start` step's fields** for any configuration whose start fact holds at the irq index (module
docstring) and whose VCPU convention holds at the boot layout. -/
theorem g3_gen (O : LocPlatM.OpaqueH) (a : Fl4Spec.MachineState) {cfg : ExecCfg BS IxB}
    (hSF : ∀ (hK : RegionOKP (KB O)) (hU : UserOKP (KB O)),
      cfg.SF (ChB O) (KB O) memB hK hU 0#u64 (fun l => (dfg2 (KB O) memB (kB O a)).lk l = some 0#u64)
        (k0B O a hK hU) (.inl (.irq jB)))
    (hv : cfg.VcpuOK (KB O) memB) :
    Fl4StepV15 cfg (LocPlatM.locPlat_archT O bs_ext)
      (dfg2 (KB O) memB (kB O a)) (KB O) (fun _ => ChB O) 0#u64 (dfg3 (KB O) memB (kB O a)) (KB O)
      (fun _ => ChB O) where
  arm p h := by rw [dfg3_ph0] at h; cases h
  start p0 k W h hK hU := by
    rw [dfg2_ph0] at h
    injection h with e1 e2 e3
    injection e2 with e2
    subst e2
    refine ⟨memB, ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, .inl (.irq jB), k0B O a hK hU, ?_,
      Or.inr (kB_eq O a hK hU)⟩
    show cfg.SF (ChB O) (KB O) (CoreView.view (KB O).toKLayout 0#u64 memB) hK hU 0#u64 _ _ _
    rw [view_B O]
    exact hSF hK hU
  serX _ := fun _ => serExitW_B O
  serC _ := ⟨hv, (hc0_B O).2⟩
  serG _ := mapsP_dfg3 _ _ _
  keep _ := ⟨rfl, rfl⟩

/-- **The native V15 configuration (V13's family and start fact): an execution from the boot whose last step is
the `.start` of the timer-IRQ path.** -/
theorem execStartV13_B (O : LocPlatM.OpaqueH) (a0 a : Fl4Spec.MachineState) :
    ∃ E, ExecV15 (ExecCfg.native bst LocPlatM.archT LocPlatM.archT_total a0 LocPlatM.archT LocPlatM.ART modelMR)
      (LocPlatM.locPlat_archT O bs_ext) (s0B O) (KB O) (fun _ => ChB O) (dfg3 (KB O) memB (kB O a)) (KB O)
      (fun _ => ChB O) E :=
  exec_start (fun _ => serExitW_B O) (hc0_B O)
    (g3_gen O a (cfg := ExecCfg.native bst LocPlatM.archT LocPlatM.archT_total a0 LocPlatM.archT LocPlatM.ART
      modelMR) (fun hK hU => startIrqV13_B O a0 a hK hU _ (dfg2_lk _ _ _)) (hc0_B O).1)

/-! ## The vmF / vmR / sl clauses at the boot memory -/

/-- **`NonIdle` is false at the boot state** (its current thread is the idle thread). -/
theorem nonIdle_false_B : ¬ NonIdle (st := bst) LocPlatM.archT LocPlatM.ART modelMR sB :=
  fun h => h _ _ jReach_B rfl

/-- **`ybw` holds at the boot state** (no `YIELD_TO` word of a TCB is nonzero in `memB`). -/
theorem ybw_B (O : LocPlatM.OpaqueH) : YBW bst (KB O).toKLayout sB := by
  intro t ht h0
  exfalso
  apply h0
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := slJAt_sB O
  have hT : t ∈ Zx.T := by rw [B.j.tcbs_eq.1]; exact ht
  obtain ⟨Q, R0, hcq, -⟩ := B.j.xtop.fin.1.1.1.lists
  have hta : TcbAddr t := hcq.tcbs t hT
  have hv : (yieldA t).val = t.val + 3472 := Notif.tfield_val hta (by decide)
  rw [sB_mem]
  show wordB (yieldA t).val = 0#u64
  rw [hv]
  have := hta.align
  exact wordB_zero_of (by omega)

end
end Fl4Proofs.P2.BootSt
