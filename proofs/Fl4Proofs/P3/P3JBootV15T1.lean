/-
P3 (p3J gen 61): **V15 at BootSt's two boot starts on `archT1`, sharing `_sysLzzP`'s instance; `OpaqueH` modelled
jointly; every native syscall closed at `(sR, σR)`** (Architect ruling 2026-11-28 14:44Z).

Platform: store `bst`, arch `archT1` (gen 59: BootSt's `archT` with one IOAPIC of 24 pins) for both the
configuration's arch and `arI`, `ART`, `modelMR`, record **`locPlat_archT1 O bs_ext`** (the one gen 60's
`sysLzzP_RT1_yield` uses).

* **Item 1, V15 on `archT1`.** `jReach_BT1` / `jReach_RT1` (`JReachU17`, the first component of gen 60's
  `jReachU40_BT1` / `jReachU40_RT1`); the layouts / chains `chainC` picks there, **`KB1 O` / `ChB1 O`** and **`KR1 O` /
  `ChR1 O`** (as BootSt's `KB` / `ChB`, `KR` / `ChR`), `KB1_ksb` / `KR1_ksb`, **`serExitW_BT1`** / **`serExitW_RT1`**,
  `hc0_BT1` / `hc0_RT1` (P2's `ptesR_memB_of` / `ptesR_memR_of`), `chR1_sR`; **`mrKeepIoapic_archT1`**; the native and
  PageMap configurations **`cfgNatBT1`** / **`cfgPmBT1`** (as `cfgNatB` / `cfgPmB` at `archT1`). Then
  **`runAllV15_BT1 (O) a0`** (from `cfg0 (KB1 O) memB`) and **`runAllV15_RT1 (O) a0`** (from `cfg0 (KR1 O) memR`, the
  second boot start's memory and chain) — `runAllV15_B`'s statement at `locPlat_archT1 O bs_ext`, proved by P2's
  `exec_cfgG` and `v15_of_native` (both `OpaqueH`-free); `(O : OpaqueH)` enters only through `locPlat_archT1 O bs_ext`.
  **`v15_sysLzzP_RT1 (O) hFpu hFW a0`**: one instance `(locPlat_archT1 O bs_ext, sR / σR)` for both — the V15
  execution of `runAllV15_RT1` over the chain `ChR1 O`, `sR` on that chain, `RunMcWKR` at `(sR, σR)` and the closed
  `_sysLzzP` instance for `SysYield` there.
* **Gen 62, the vmF start on `archT1`.** P2/BootRVmF's start chain is arch-parametric since gen 62 (`jRP`, `kRP`,
  `runEndV13_RP`, …; the `archT` forms its instances). Here: `chR1_lay`, `slJAt_RT1`, the index **`jRT1 O`**
  (+ `jRT1_spec`: no lock, `ChR1 O sR`, `VmFEntV13` at `archT1` with `ybw` [J] and `NonIdle` [P] proved), the armed
  body **`kRT1 O a`**, **`runEndV13_RT1`**, and **`topV15_RT1 (O) a0 a`** — `topV15_R`'s statement at
  `locPlat_archT1 O bs_ext`, `KR1 O`, `ChR1 O`. **`topV15_sysLzzP_RT1 (O) hFpu hFW a0 a`** (sibling of
  `v15_sysLzzP_RT1`): that vmF execution, `ChR1 O sR`, `RunMcWKR` at `(sR, σR)` and `_sysLzzP` at `(sR, σR)` for
  every native syscall, on the one instance `(locPlat_archT1 O bs_ext, sR / σR)`.
* **`opaqueH_model`**: values of every opaque constant `OpaqueH` and `FpuDet` read (`kernelConfig`, `timeConsts`,
  `maxTicksToUs`, `irqOracle`, `setDeadlineImpl`, `enableFpuImpl`, `disableFpuImpl`, `writeFpuStateImpl`,
  `in8Val` / `in16Val` / `in32Val`) meeting all their facts at once (`pin0` through `pin0_of_val0`).
* **Item 2, `SysK6` at `(sR, σR)`.** **`lookAt_σR_false`**: at every dispatch state `σb` of an entry from `σR`
  (`BudgetAt σR σb true`), no cap lookup succeeds — every TCB's CSpace root is the null cap or `threadCap tRp`
  (`capOpt_σR`), never a CNode cap, so `resolveAddressBits` answers `invalidRoot` (l4v `resolve_address_bits`), and a
  non-TCB has no CSpace root. Hence **`sysK6_σR`**: `SysK6` holds at `σR` for every syscall, ghost set and arch, by
  the failed lookup: no invocation at `σR` reaches the K6 case, so no `SysK6` instance at `σR` is non-vacuous (the
  Architect's item 2 is not attainable at `σR`). **`sysLzzP_RT1_native (O) hFpu hFW`**: `_sysLzzP` closed at
  `(sR, σR)` for every native syscall, and **`sysLzzP_RT1_call`** its `SysCall` instance.

Named premises: `OpaqueH` [P], `FpuImplDet` [P], `FpuWriteDet` [P] (existing; hypotheses of the witnesses only).
`BootV15` / `V15_*` are untouched and `OpaqueH`-free. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JBootT1
import Fl4Proofs.P2.BootV15
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical
open Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Mc
open Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2EV Fl4Proofs.P2.OwnMapP Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.E2EP
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll Run)
open Fl4Proofs.P2.E2E (SP)
open Fl4Proofs.P2.LocPlatM (archT1 ART)

noncomputable section

/-! ## Item 1: V15 on `archT1` -/

/-- (p3J gen 61) **`hIoa` on `archT1`** (its IOAPIC map operations are `archT`'s). -/
theorem mrKeepIoapic_archT1 : MRKeepIoapic archT1 modelMR where
  map _ _ _ _ _ _ _ h := by okc
  mapr _ _ _ _ _ _ _ _ h := by okc

/-- (p3J gen 61) The boot's P3 start on `archT1` (`JReachU17` of `jReachU40_BT1`). -/
theorem jReach_BT1 : JReachU17 (L := bsL) archT1 ART modelMR sB (σB (Z := Unit)).machineState (σB (Z := Unit)) :=
  jReachU40_BT1.1.1

/-- (p3J gen 61) The second boot start's P3 start on `archT1` (`JReachU17` of `jReachU40_RT1`). -/
theorem jReach_RT1 : JReachU17 (L := bsL) archT1 ART modelMR sR (σR (Z := Unit)).machineState (σR (Z := Unit)) :=
  jReachU40_RT1.1.1

/-- (p3J gen 61) The layout `chainC` picks at the boot start on `archT1` (no VCPU, no PTE word). -/
def KB1 (O : LocPlatM.OpaqueH) : KLayoutP :=
  { toKLayoutV := { toKLayout := (chainC (LocPlatM.locPlat_archT1 O bs_ext) jReach_BT1).1, vcpus := ∅ }, ptes := ∅ }

/-- (p3J gen 61) The chain `chainC` picks at the boot start on `archT1`. -/
def ChB1 (O : LocPlatM.OpaqueH) : BS → Prop := (chainC (LocPlatM.locPlat_archT1 O bs_ext) jReach_BT1).2

/-- (p3J gen 61) The layout `chainC` picks at the second boot start on `archT1`. -/
def KR1 (O : LocPlatM.OpaqueH) : KLayoutP :=
  { toKLayoutV := { toKLayout := (chainC (LocPlatM.locPlat_archT1 O bs_ext) jReach_RT1).1, vcpus := ∅ }, ptes := ∅ }

/-- (p3J gen 61) The chain `chainC` picks at the second boot start on `archT1`. -/
def ChR1 (O : LocPlatM.OpaqueH) : BS → Prop := (chainC (LocPlatM.locPlat_archT1 O bs_ext) jReach_RT1).2

/-- (p3J gen 61) **`hB` at `KB1 O`, `ChB1 O`.** -/
theorem serExitW_BT1 (O : LocPlatM.OpaqueH) :
    SerExitW (LocPlatM.locPlat_archT1 O bs_ext) (KB1 O).toKLayoutV (ChB1 O) :=
  ⟨sB, _, _, jReach_BT1, rfl⟩

/-- (p3J gen 61) **`hB` at `KR1 O`, `ChR1 O`.** -/
theorem serExitW_RT1 (O : LocPlatM.OpaqueH) :
    SerExitW (LocPlatM.locPlat_archT1 O bs_ext) (KR1 O).toKLayoutV (ChR1 O) :=
  ⟨sR, _, _, jReach_RT1, rfl⟩

theorem KB1_ksb (O : LocPlatM.OpaqueH) : (KB1 O).ksb = kbB := by
  obtain ⟨Z, H, Cx, nc, hK, -⟩ := chainC_spec (LocPlatM.locPlat_archT1 O bs_ext) jReach_BT1
  exact (congrArg OwnMap.KLayout.ksb hK).trans rfl

theorem KR1_ksb (O : LocPlatM.OpaqueH) : (KR1 O).ksb = kbB := by
  obtain ⟨Z, H, Cx, nc, hK, -⟩ := chainC_spec (LocPlatM.locPlat_archT1 O bs_ext) jReach_RT1
  exact (congrArg OwnMap.KLayout.ksb hK).trans rfl

/-- (p3J gen 61) `hc0` at `KB1 O` and `memB`. -/
theorem hc0_BT1 (O : LocPlatM.OpaqueH) : (KB1 O).vcpus = ∅ ∧ (KB1 O).ptes = ptesR (KB1 O) memB :=
  ⟨rfl, (ptesR_memB_of (KB1_ksb O)).symm⟩

/-- (p3J gen 61) `hc0` at `KR1 O` and `memR`. -/
theorem hc0_RT1 (O : LocPlatM.OpaqueH) : (KR1 O).vcpus = ∅ ∧ (KR1 O).ptes = ptesR (KR1 O) memR :=
  ⟨rfl, (ptesR_memR_of (KR1_ksb O)).symm⟩

/-- (p3J gen 61) **The second boot state is on its chain `ChR1 O`.** -/
theorem chR1_sR (O : LocPlatM.OpaqueH) : ChR1 O sR := by
  obtain ⟨Z, H, Cx, nc, -, -, -, -, h⟩ := chainC_spec (LocPlatM.locPlat_archT1 O bs_ext) jReach_RT1
  exact h

/-- (p3J gen 61) The boot instance's native configuration on `archT1`. -/
abbrev cfgNatBT1 (a0 : Fl4Spec.MachineState) :=
  ExecCfg.native bst archT1 LocPlatM.archT1_total a0 archT1 ART modelMR

/-- (p3J gen 61) The boot instance's PageMap configuration on `archT1` (`pmObl7_none`). -/
abbrev cfgPmBT1 (a0 : Fl4Spec.MachineState) :=
  ExecCfg.nativePmKAD bst archT1 LocPlatM.archT1_total a0 archT1 ART modelMR (pmObl7_none bst)

/-- (p3J gen 61) **V15 applied to the empty-start instance at the boot on `archT1`** (`runAllV15_B`'s statement at
`locPlat_archT1 O bs_ext`, layout `KB1 O`). -/
theorem runAllV15_BT1 (O : LocPlatM.OpaqueH) (a0 : Fl4Spec.MachineState) :
    ∃ E : U64 → U64,
      ExecV15 (cfgNatBT1 a0) (LocPlatM.locPlat_archT1 O bs_ext) (cfg0 (KB1 O) memB) (KB1 O) (fun _ => ChB1 O)
        (cfg7 (KB1 O) memB) (KB1 O) (fun _ => ChB1 O) E ∧
      RunAll (cfg7 (KB1 O) memB).log (cfg0 (KB1 O) memB).mem (cfg7 (KB1 O) memB).mem ∧
      ExecV15C (cfgPmBT1 a0) (LocPlatM.locPlat_archT1 O bs_ext).toC (cfg0 (KB1 O) memB) (KB1 O) (fun _ => ChB1 O)
        (cfg7 (KB1 O) memB) (KB1 O) (fun _ => ChB1 O) E ∧
      ∃ ℓ : List SP, ℓ.Perm (cfg7 (KB1 O) memB).log ∧ RunAll ℓ (cfg0 (KB1 O) memB).mem (cfg7 (KB1 O) memB).mem := by
  obtain ⟨E, he⟩ := exec_cfgG (cfg := cfgNatBT1 a0) (fun _ => serExitW_BT1 O) (hc0_BT1 O)
  exact ⟨E, he, v15_of_native bst archT1 LocPlatM.archT1_total a0 (LocPlatM.locPlat_archT1 O bs_ext)
    mrKeepIoapic_archT1 (pmObl7_none bst) (cfg_init _ _) (cfg_armInv _ _) (fun _ => serExitW_BT1 O) (hc0_BT1 O)
    (mapsP_cfg0 _ _) he (cfg_noLoc _ _)⟩

/-- (p3J gen 61) **V15 applied to the empty-start instance at the second boot start on `archT1`** (memory `memR`,
layout `KR1 O`, chain `ChR1 O` through `sR`). -/
theorem runAllV15_RT1 (O : LocPlatM.OpaqueH) (a0 : Fl4Spec.MachineState) :
    ∃ E : U64 → U64,
      ExecV15 (cfgNatBT1 a0) (LocPlatM.locPlat_archT1 O bs_ext) (cfg0 (KR1 O) memR) (KR1 O) (fun _ => ChR1 O)
        (cfg7 (KR1 O) memR) (KR1 O) (fun _ => ChR1 O) E ∧
      RunAll (cfg7 (KR1 O) memR).log (cfg0 (KR1 O) memR).mem (cfg7 (KR1 O) memR).mem ∧
      ExecV15C (cfgPmBT1 a0) (LocPlatM.locPlat_archT1 O bs_ext).toC (cfg0 (KR1 O) memR) (KR1 O) (fun _ => ChR1 O)
        (cfg7 (KR1 O) memR) (KR1 O) (fun _ => ChR1 O) E ∧
      ∃ ℓ : List SP, ℓ.Perm (cfg7 (KR1 O) memR).log ∧ RunAll ℓ (cfg0 (KR1 O) memR).mem (cfg7 (KR1 O) memR).mem := by
  obtain ⟨E, he⟩ := exec_cfgG (cfg := cfgNatBT1 a0) (fun _ => serExitW_RT1 O) (hc0_RT1 O)
  exact ⟨E, he, v15_of_native bst archT1 LocPlatM.archT1_total a0 (LocPlatM.locPlat_archT1 O bs_ext)
    mrKeepIoapic_archT1 (pmObl7_none bst) (cfg_init _ _) (cfg_armInv _ _) (fun _ => serExitW_RT1 O) (hc0_RT1 O)
    (mapsP_cfg0 _ _) he (cfg_noLoc _ _)⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 61) **V15 and `_sysLzzP` on one instance** `(locPlat_archT1 O bs_ext, sR / σR)` (module docstring):
`runAllV15_RT1`'s V15 execution over `ChR1 O`, `sR` on that chain, `RunMcWKR` at `(sR, σR)`, and gen 60's closed
`_sysLzzP` instance for `SysYield` there. -/
theorem v15_sysLzzP_RT1 (O : LocPlatM.OpaqueH) (hFpu : FpuImplDet) (hFW : FpuWriteDet) (a0 : Fl4Spec.MachineState) :
    (∃ E : U64 → U64,
      ExecV15 (cfgNatBT1 a0) (LocPlatM.locPlat_archT1 O bs_ext) (cfg0 (KR1 O) memR) (KR1 O) (fun _ => ChR1 O)
        (cfg7 (KR1 O) memR) (KR1 O) (fun _ => ChR1 O) E ∧
      ExecV15C (cfgPmBT1 a0) (LocPlatM.locPlat_archT1 O bs_ext).toC (cfg0 (KR1 O) memR) (KR1 O) (fun _ => ChR1 O)
        (cfg7 (KR1 O) memR) (KR1 O) (fun _ => ChR1 O) E) ∧
      ChR1 O sR ∧ RunMcWKR (L := bsL) archT1 ART modelMR sR (σR (Z := Unit)).machineState (σR (Z := Unit)) ∧
      syscall.handle_syscall bst archT1 sR (σR (Z := Unit)).machineState fl4_abi.syscall.SysYield ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true .sysYield (σR (Z := Unit))).1 ∧
          RunMcWKR (L := bsL) archT1 ART modelMR r.1 r.2 σ' ⦄ := by
  obtain ⟨E, h1, -, h2, -⟩ := runAllV15_RT1 O a0
  exact ⟨⟨E, h1, h2⟩, chR1_sR O, runMcWKR_RT1, sysLzzP_RT1_yield O hFpu hFW⟩

/-! ## Gen 62: the vmF start on `archT1` (`topV15_RT1`) -/

/-- (p3J gen 62) `ChainLay` of the second boot start's chain on `archT1`. -/
theorem chR1_lay (O : LocPlatM.OpaqueH) : ChainLay (L := bsL) (KR1 O).toKLayout (ChR1 O) := by
  obtain ⟨Z, H, Cx, nc, -, -, -, h, -⟩ := chainC_spec (LocPlatM.locPlat_archT1 O bs_ext) jReach_RT1
  exact h

/-- (p3J gen 62) The second boot state is a bundle state of `KR1 O`. -/
theorem slJAt_RT1 (O : LocPlatM.OpaqueH) : SlJAt (L := bsL) (KR1 O).toKLayout sR := (chR1_lay O).bun sR (chR1_sR O)

/-- (p3J gen 62) **The vmF index on `archT1`** (P2's `jRP` at `KR1 O`, `ChR1 O`, `archT1`; as `jR`). -/
def jRT1 (O : LocPlatM.OpaqueH) : VmFArg BS :=
  jRP (K := KR1 O) rfl (slJAt_RT1 O) (chR1_sR O) archT1 archT1 ART modelMR

theorem jRT1_spec (O : LocPlatM.OpaqueH) : (jRT1 O).Locks = (fun _ _ => False) ∧ ChR1 O sR ∧
    VmFEntV13 bst archT1 archT1 ART modelMR (jRT1 O) (KR1 O).toKLayoutV sR :=
  jRP_spec rfl (slJAt_RT1 O) (chR1_sR O) archT1 archT1 ART modelMR

/-- (p3J gen 62) **The armed vmF body on `archT1`** (P2's `kRP`; as `kR`). -/
def kRT1 (O : LocPlatM.OpaqueH) (a : Fl4Spec.MachineState) : SP :=
  kRP archT1 LocPlatM.archT1_total (jRT1 O) (KR1 O) a

/-- (p3J gen 62) **V13 on `archT1`: the vmF start at `sR`, its whole body, and the leave** (P2's
`runEndV13_RP`; as `runEndV13_R`). -/
theorem runEndV13_RT1 (O : LocPlatM.OpaqueH) (a0 a : Fl4Spec.MachineState) :
    ∃ (s : Cfg U64 U64 U64 U64) (E : U64 → U64),
      ExecV15 (cfgNatBT1 a0) (LocPlatM.locPlat_archT1 O bs_ext) (cfg0 (KR1 O) memR) (KR1 O) (fun _ => ChR1 O) s
        (KR1 O) (fun _ => ChR1 O) E ∧
      NoLoc s ∧ s.log = [.start (kRT1 O a)] :=
  runEndV13_RP archT1 LocPlatM.archT1_total a0 (LocPlatM.locPlat_archT1 O bs_ext) (chR1_lay O) (chR1_sR O)
    (KR1_ksb O) (jRT1_spec O) (serExitW_RT1 O) (hc0_RT1 O) a

/-- (p3J gen 62) **V15 applied to the vmF start at the second boot start on `archT1`** (`topV15_R`'s statement at
`locPlat_archT1 O bs_ext`, layout `KR1 O`, chain `ChR1 O`, body `kRT1 O a`; the start carries `ybw` [J] and
`NonIdle` [P] inside `StartV13`, both proved at `sR`). -/
theorem topV15_RT1 (O : LocPlatM.OpaqueH) (a0 a : Fl4Spec.MachineState) :
    ∃ (s : Cfg U64 U64 U64 U64) (E : U64 → U64),
      ExecV15 (cfgNatBT1 a0) (LocPlatM.locPlat_archT1 O bs_ext) (cfg0 (KR1 O) memR) (KR1 O) (fun _ => ChR1 O) s
        (KR1 O) (fun _ => ChR1 O) E ∧
      ExecV15C (cfgPmBT1 a0) (LocPlatM.locPlat_archT1 O bs_ext).toC (cfg0 (KR1 O) memR) (KR1 O) (fun _ => ChR1 O) s
        (KR1 O) (fun _ => ChR1 O) E ∧
      NoLoc s ∧ s.log = [.start (kRT1 O a)] ∧ Run (.start (kRT1 O a)) memR s.mem ∧
      ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ memR s.mem := by
  obtain ⟨s, E, h1, hq, hl⟩ := runEndV13_RT1 O a0 a
  obtain ⟨hr, h2, hp⟩ := v15_of_native bst archT1 LocPlatM.archT1_total a0 (LocPlatM.locPlat_archT1 O bs_ext)
    mrKeepIoapic_archT1 (pmObl7_none bst) (cfg_init _ _) (cfg_armInv _ _) (fun _ => serExitW_RT1 O) (hc0_RT1 O)
    (mapsP_cfg0 _ _) h1 hq
  rw [hl] at hr
  exact ⟨s, E, h1, h2, hq, hl, runAll_one hr, hp⟩

/-! ## Item 2: `SysK6` at `(sR, σR)` -/

/-- (p3J gen 61) A thread reference that is no TCB makes `lookupSlotForThread` fail (`gets_the` on `none`). -/
theorem lsft_noTcb {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} (h : Fl4Spec.getTcb (Z := Unit) t σ = none)
    (cref : Fl4Spec.CapRef) : ((Fl4Spec.lookupSlotForThread (Z := Unit) t cref).run σ).2 := by
  unfold Fl4Spec.lookupSlotForThread Fl4Spec.NonDetE.liftE
  rw [ExceptT.run_bind, ExceptT.run_lift]
  refine Or.inl (Or.inl ?_)
  show (Fl4Spec.NonDet.getsThe (Fl4Spec.getTcb (Z := Unit) t) σ).2
  unfold Fl4Spec.NonDet.getsThe
  rw [h]
  trivial

/-- (p3J gen 61) **No cap lookup succeeds at a dispatch state of an entry from `σR`** (module docstring): the
CSpace root of every TCB of `σR` is no CNode cap. -/
theorem lookAt_σR_false (hnd : Fl4Spec.numDomains = 1) {σb : Fl4Spec.State Unit}
    (hb : BudgetAt (σR (Z := Unit)) σb true) (ct cptr : U64) (sl : Fl4Spec.CslotPtr) (c : capability.Cap) :
    ¬ LookAt ct cptr σb sl c := by
  intro h
  unfold LookAt at h
  have hl : ((Fl4Spec.lookupSlotForThread (Z := Unit) ct.bv (Fl4Spec.toBl cptr.bv)).run σb).2 ∨
      (Fl4Spec.lookupSlotForThread (Z := Unit) ct.bv (Fl4Spec.toBl cptr.bv)).run σb =
        ({(.error .invalidRoot, σb)}, False) := by
    cases hk : σb.kheap ct.bv with
    | none => exact Or.inl (lsft_noTcb (by simp [Fl4Spec.getTcb, Fl4Spec.readObject, hk]) _)
    | some o =>
      cases o with
      | tcb tcb =>
        refine Or.inr ((lookupSlotForThread_eq hk _).trans (rab_noncnode _ _ _ ?_))
        have h0 : capOpt ((σR (Z := Unit)).kheap ct.bv) (Fl4Spec.tcbCnodeIndex 0) = some tcb.tcbCtable := by
          rw [← budgetAt_capOpt hnd hb, hk]
          exact tcbCnodeMap_ctable tcb
        rcases capOpt_σR h0 with e | ⟨-, -, e⟩ | ⟨-, -, e⟩ <;> rw [e] <;> rfl
      | _ => exact Or.inl (lsft_noTcb (by simp [Fl4Spec.getTcb, Fl4Spec.readObject, hk]) _)
  rcases hl with hf | he
  · have h3 : ((Fl4Spec.lookupCapAndSlot (Z := Unit) ct.bv (Fl4Spec.toBl cptr.bv)).run σb).2 := by
      unfold Fl4Spec.lookupCapAndSlot
      rw [ExceptT.run_bind]
      exact Or.inl hf
    rw [h] at h3
    exact h3
  · unfold Fl4Spec.lookupCapAndSlot at h
    rw [run_bind_error he] at h
    have h4 := congrArg (fun x => ((.error .invalidRoot : Except Fl4Spec.LookupFailure _), σb) ∈ x.1) h
    simp at h4

section
variable {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)

/-- (p3J gen 61) **`SysK6` at `σR`** for every syscall, ghost set and arch (module docstring): vacuous by the
failed lookup (`lookAt_σR_false`). -/
theorem sysK6_σR (hnd : Fl4Spec.numDomains = 1) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (a : A) (n : I64)
    (c : Fl4Spec.Syscall) : SysK6 (L := bsL) arI AR Z H Cs sR a (σR (Z := Unit)) n c := by
  intro σb hb _ _ _ _ _ _ _ _
  refine ⟨fun ct _ _ _ _ _ => ?_, fun ct _ _ _ _ _ => ?_⟩ <;>
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ sl c' _ _ _ _ _ _ _ _ hL _
    exact (lookAt_σR_false hnd hb _ _ sl c' hL).elim

end

set_option maxHeartbeats 4000000 in
/-- (p3J gen 61) **`kernel_entry_runMcWKR_sysLzzP` closed at `(sR, σR)` for every native syscall** on `archT1`
(`SysK6` by `sysK6_σR`); only `OpaqueH`, `FpuImplDet`, `FpuWriteDet` [P] left. -/
theorem sysLzzP_RT1_native (O : LocPlatM.OpaqueH) (hFpu : FpuImplDet) (hFW : FpuWriteDet) (n : I64)
    (c : Fl4Spec.Syscall) (hn : NativeSys n c) :
    syscall.handle_syscall bst archT1 sR (σR (Z := Unit)).machineState n ⦃ r =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c (σR (Z := Unit))).1 ∧
        RunMcWKR (L := bsL) archT1 ART modelMR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzzP (L := bsL) (st := bst) (LocPlatM.locPlat_archT1 O bs_ext) hFpu hFW
    runMcWKR_RT1 n c σR_cur_ne hn sysFlag_R
    (fun Z H Cs _ _ _ _ => sysK6_σR archT1 ART O.nd Z H Cs _ n c)

/-- (p3J gen 61) `SysCall` is a native syscall (its invoking disjunct, `invSysOf true true = .sysCall`). -/
theorem nativeSys_callI : NativeSys fl4_abi.syscall.SysCall .sysCall :=
  Or.inl ⟨true, true, true, Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩), rfl⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 61) **`sysLzzP_RT1_native` at `SysCall`**: an invoking syscall from the root thread at `(sR, σR)`. -/
theorem sysLzzP_RT1_call (O : LocPlatM.OpaqueH) (hFpu : FpuImplDet) (hFW : FpuWriteDet) :
    syscall.handle_syscall bst archT1 sR (σR (Z := Unit)).machineState fl4_abi.syscall.SysCall ⦃ r =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true .sysCall (σR (Z := Unit))).1 ∧
        RunMcWKR (L := bsL) archT1 ART modelMR r.1 r.2 σ' ⦄ :=
  sysLzzP_RT1_native O hFpu hFW _ _ nativeSys_callI

set_option maxHeartbeats 4000000 in
/-- (p3J gen 62) **The vmF V15 top and `_sysLzzP` on one instance** `(locPlat_archT1 O bs_ext, sR / σR)` (sibling of
`v15_sysLzzP_RT1`): `topV15_RT1`'s execution over `ChR1 O` (the vmF `.start` at `sR`, its body and the leave), `sR`
on that chain, `RunMcWKR` at `(sR, σR)`, and `_sysLzzP` closed there for every native syscall
(`sysLzzP_RT1_native`). -/
theorem topV15_sysLzzP_RT1 (O : LocPlatM.OpaqueH) (hFpu : FpuImplDet) (hFW : FpuWriteDet)
    (a0 a : Fl4Spec.MachineState) :
    (∃ (s : Cfg U64 U64 U64 U64) (E : U64 → U64),
      ExecV15 (cfgNatBT1 a0) (LocPlatM.locPlat_archT1 O bs_ext) (cfg0 (KR1 O) memR) (KR1 O) (fun _ => ChR1 O) s
        (KR1 O) (fun _ => ChR1 O) E ∧
      ExecV15C (cfgPmBT1 a0) (LocPlatM.locPlat_archT1 O bs_ext).toC (cfg0 (KR1 O) memR) (KR1 O) (fun _ => ChR1 O) s
        (KR1 O) (fun _ => ChR1 O) E ∧
      NoLoc s ∧ s.log = [.start (kRT1 O a)] ∧ Run (.start (kRT1 O a)) memR s.mem) ∧
      ChR1 O sR ∧ RunMcWKR (L := bsL) archT1 ART modelMR sR (σR (Z := Unit)).machineState (σR (Z := Unit)) ∧
      ∀ (n : I64) (c : Fl4Spec.Syscall), NativeSys n c →
        syscall.handle_syscall bst archT1 sR (σR (Z := Unit)).machineState n ⦃ r =>
          ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c (σR (Z := Unit))).1 ∧
            RunMcWKR (L := bsL) archT1 ART modelMR r.1 r.2 σ' ⦄ := by
  obtain ⟨s, E, h1, h2, hq, hl, hr, -⟩ := topV15_RT1 O a0 a
  exact ⟨⟨s, E, h1, h2, hq, hl, hr⟩, chR1_sR O, runMcWKR_RT1, fun n c hn => sysLzzP_RT1_native O hFpu hFW n c hn⟩

end

end Fl4Proofs.P2.BootSt

namespace Fl4Proofs.P3.JBootQ.M2
open Fl4Spec

/-- (p3J gen 61) **One model of every opaque-constant fact of `OpaqueH` and `FpuDet`** (module docstring): values
of `kernelConfig`, `timeConsts`, `maxTicksToUs`, `irqOracle`, `setDeadlineImpl`, `enableFpuImpl`, `disableFpuImpl`,
`writeFpuStateImpl`, `in8Val`, `in16Val`, `in32Val` meeting `OpaqueH.nd / max / wcetUs / timerUnit / maxP / ipi /
dl`, `pin0`'s sufficient condition (`pin0_of_val0`), `FpuImplDet` and `FpuWriteDet` at once. -/
theorem opaqueH_model :
    ∃ (kc : KernelConfig) (tc : TimeConsts) (mt : Word64) (irq : Nat → Word8)
      (dl : Word64 → MachineRestMonad Unit) (en dis : MachineRestMonad Unit) (wr : FpuState → MachineRestMonad Unit)
      (i8 i16 i32 : MachineState → Word),
      kc.numDomains = 1 ∧ mt = core.num.U64.MAX.bv ∧ tc.kernelWCETUs = 10 ∧ tc.timerUnit = 1 ∧
      tc.maxPeriodUs.toNat < 2 ^ 61 ∧ (∀ n, (irq n).toNat ≠ 126 ∧ (irq n).toNat ≠ 127) ∧
      (∀ d mr (x y : Unit × MachineStateRest), x ∈ (dl d mr).1 → y ∈ (dl d mr).1 → x = y) ∧
      (∀ mr (x y : Unit × MachineStateRest), x ∈ (en mr).1 → y ∈ (en mr).1 → x = y) ∧
      (∀ mr (x y : Unit × MachineStateRest), x ∈ (dis mr).1 → y ∈ (dis mr).1 → x = y) ∧
      (∀ v mr (x y : Unit × MachineStateRest), x ∈ (wr v mr).1 → y ∈ (wr v mr).1 → x = y) ∧
      (∀ ms, i8 ms = 0) ∧ (∀ ms, i16 ms = 0) ∧ (∀ ms, i32 ms = 0) := by
  obtain ⟨kc, tc, mt, dl, en, dis, wr, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := opaqueSysLzz_model
  obtain ⟨irq, hi⟩ := Fl4Proofs.P2.LocPlatM.opaqueH_ipi_model
  obtain ⟨f, hf⟩ := Fl4Proofs.P2.LocPlatM.opaqueH_pin0_model
  exact ⟨kc, tc, mt, irq, dl, en, dis, wr, f, f, f, h1, h2, h3, h4, h5, hi, h6, h7, h8, h9, hf, hf, hf⟩

end Fl4Proofs.P3.JBootQ.M2
