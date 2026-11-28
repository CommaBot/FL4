/-
P3 (p3J gen 60): **BootSt's two boot starts are `RunMcWKR` starts on `archT1`** (Architect ruling 2026-11-28 14:24Z:
BootSt / V15 and `RunMcWKR` / `_sysLzzP` on the shared one-IOAPIC arch `archT1`).

Store `bst` (`bsL`, `bsP`, `bs_ext`), arch `archT1` (gen 59: BootSt's `archT` with one IOAPIC of 24 pins), CR3
relation `ART`, machine relation `modelMR`, platform record **`locPlat_archT1 O bs_ext : LocPlat bst archT1 ART
modelMR`** — BootSt's own platform `locPlat_archT O bs_ext` (V15's, `BootV15`) with the two IOAPIC reads changed.

* **Goal 1, the boot state `(sB, σB)`** (idle thread current): `jKern_bootT1` / `utc_BT1` (the two `JAtZ` fields
  that name the arch, from `jKern_boot` / `utc_B`), **`jAtZ_BT1`** (`jAtZ_B`'s other fields verbatim),
  **`jReachU40_BT1`** (`jReach_B`'s start at `archT1`, `irqCarry_B`, `archT1_ioaRel_B`), and the run facts at `σB`:
  **`cki_B`** (every cap is null), **`khWF_B`** (`kheapB_cases`: idle TCB, idle SC of size 0, three paging
  structures, the IRQ CNodes `cnode 0 (emptyCnode 0)`), **`noSig_B`**, **`irqStS_B`** (every line inactive),
  **`irqCarry_B`** (no IRQ-handler cap), **`rr_B`** (the idle SC has period 0); **`runMcWKR_BT1`**: `RunMcWKR bsL
  archT1 ART modelMR sB σB.machineState σB`, no premise. **`sysLzzP_BT1_sat (O : OpaqueH)`**: `LocPlat bst archT1
  ART modelMR` ∧ that `RunMcWKR` ∧ `IoaRel archT1 σB`. As at jboot's boot (`fInitASt_ct_idle`), `σB` runs the idle
  thread (`σB_ct_idle`), so `_sysLzzP`'s per-call part (`curThread ≠ idleThread`) is vacuous there.
* **Goal 2, the second boot start `(sR, σR)`** (P2/BootRSpec: `σB` with the running root thread `tRp` current,
  BootSt's start of `topV15_R`): `jKern_RT1`, `utc_RT1`, **`jAtZ_RT1`**, `archT1_ioaRel_R`, **`jReachU40_RT1`**,
  `cki_R` (caps null, `threadCap tRp`, `schedContextCap scRp 0`), `khWF_R`, `noSig_R`, `irqCarry_R`, `rr_R` (the
  root SC is the idle SC's record with a new `scTcb`), **`runMcWKR_RT1`** (no premise); **`sysFlag_R`** (the root
  TCB's flags word is 0 in `memR`, the `FAULT_IP` write misses it); **`sysLzzP_RT1_sat (O)`** (`LocPlat` ∧
  `RunMcWKR` ∧ `IoaRel` ∧ `σR.curThread ≠ σR.idleThread`); **`sysLzzP_RT1_yield (O) hFpu hFW`** (closed):
  `kernel_entry_runMcWKR_sysLzzP` for `SysYield` at `(sR, σR)` on BootSt's store and `archT1`, every per-call
  antecedent discharged (`σR_cur_ne`, `nativeSys_yieldI`, `sysFlag_R`, `sysK6_yield`). `σR` is not reached from
  `σB` by a kernel entry: it is BootSt's second start (`JReachU3.start`), as `topV15_R` uses it.
* **FPU bundle**: **`FpuDet`** (a 2-field record of the existing [P] facts `FpuImplDet`, `FpuWriteDet`),
  **`kernel_entry_runMcWKR_sysLzzPF`** (`_sysLzzP` with `F : FpuDet`; one term) and `sysLzzP_RT1_yieldF`.
* **`OpaqueH.pin0`**: **`pin0_of_val0`** — `pin0`'s statement follows from the three port-read value facts
  `in8Val = in16Val = in32Val = 0` (no fact about `in*Impl`: `ignoreFailure` keeps every outcome set non-empty and
  `machineRestLift` leaves `underlyingMemory`); **`opaqueH_pin0_model`**: those facts are consistent with the
  constants' types. With gen 55's `opaqueSysLzz_model` (`nd` / `max` / `wcetUs` / `timerUnit` / `maxP` / `dl`) and
  gen 59's `opaqueH_ipi_model`, every `OpaqueH` field is modelled.

`BootV15` / `V15_*` are untouched: no statement of P2 changes, and nothing here is imported by them (no `OpaqueH`
reaches them through this module). Caveat (as gens 55 / 56 / 59): `ART := fun _ _ => True`, so the CR3-side `LocPlat`
fields and `JAtZ`'s CR3 clauses hold trivially; one core.

Named premises: `OpaqueH` [P] (LocPlatModel), `FpuImplDet` [P] (ScFpuNd), `FpuWriteDet` [P] (ArchSwThr): existing,
hypotheses of the `sat` / `yield` theorems; `FpuDet` bundles the last two (no new fact). No sorry. New module; no
existing statement changed.
-/
import Fl4Proofs.P3.P3JSysLzzT1
import Fl4Proofs.P2.BootRJAtZ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched

/-- (p3J gen 60) **The two FPU determinism facts as one record** [P] (module docstring): `FpuImplDet` (ScFpuNd)
and `FpuWriteDet` (ArchSwThr), unchanged. -/
structure FpuDet : Prop where
  impl : FpuImplDet
  write : FpuWriteDet

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3.Mc
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 60) **`kernel_entry_runMcWKR_sysLzzP` with the FPU facts as one record** `F : FpuDet` (module
docstring; statement otherwise verbatim). -/
theorem kernel_entry_runMcWKR_sysLzzPF [Fl4Proofs.P1.PlainStore st]
    (P : Fl4Proofs.P2.PathObl.LocPlat st arI AR MR) (F : FpuDet)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcWKR (L := L) arI AR MR s a σ) :
    ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c → SysFlag (L := L) s →
      (∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
        JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → SysK6 (L := L) arI AR Z H Cs s a σ n c) →
      syscall.handle_syscall st arI s a n ⦃ r =>
        ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
          RunMcWKR (L := L) arI AR MR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzzP P F.impl F.write hR

end

end Fl4Proofs.P3.Mc

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical
open Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Mc
open Fl4Proofs.P2.LocPlatM (archT1 ART)

noncomputable section

/-! ## Goal 1: the boot state `(sB, σB)` on `archT1` -/

/-- (p3J gen 60) `JKern` at `archT1`: `jKern_boot`'s fields (its TDX clause reads `modelArch`'s `tdx_active` /
`dma_ram`). -/
theorem jKern_bootT1 : JKern (L := bsL) archT1 HB CsB DB thB sB (σB (Z := Unit)) := { jKern_boot with }

/-- (p3J gen 60) **`JAtZ.utc`** at `archT1` (vacuous: no slot of `sB` holds an untyped cap). -/
theorem utc_BT1 : ∀ sl p sb fi dev, AbsSlot thB sl → capAt (bsL.mem sB) (cslotAddr sl) = ok (.Untyped p sb fi dev) →
    dev = false → Sched.UtCapP3 (L := bsL) archT1 thB sB (σB (Z := Unit)) G0 sl p sb fi := by
  intro sl p sb fi dev hs hc _
  rw [slot_capAt hs.isSlot] at hc
  cases ok_inj_ff hc

/-- (p3J gen 60) **`JAtZ` at the boot on `archT1`** (`jAtZ_B` with `kern` / `utc` above). -/
theorem jAtZ_BT1 : JAtZ (L := bsL) archT1 ART (ZB G0) HB CsB AcB LstB DB sB
    (σB (Z := Unit)).machineState (σB (Z := Unit)) :=
  { jAtZ_B with kern := jKern_bootT1, utc := utc_BT1 }

/-- (p3J gen 60) No line of `σB` is `IRQSignal` above `maxIRQ` (every line is inactive). -/
theorem irqStS_B : SInvIB.IrqStS (σB (Z := Unit)) := fun _ _ e => by
  change Fl4Spec.IrqState.irqInactive = _ at e
  cases e

/-- (p3J gen 60) `σB` holds no IRQ-handler cap (every cap is null). -/
theorem noHandler_B (p : Fl4Spec.ObjRef) (cref : Fl4Spec.CnodeIndex) (irq : Fl4Spec.Irq) :
    capOpt ((σB (Z := Unit)).kheap p) cref ≠ some (.irqHandlerCap irq) := fun h => by
  cases capOpt_B h

/-- (p3J gen 60) **irqfix3's carried fact at `σB`.** -/
theorem irqCarry_B : SInvIB.IrqCarry (σB (Z := Unit)) := SInvIB.irqCarry_of_noHandler noHandler_B irqStS_B

/-- (p3J gen 60) **`JReachU40` at the boot on `archT1` / `ART` / `modelMR`** (no premise). -/
theorem jReachU40_BT1 : JReachU40 (L := bsL) archT1 ART modelMR sB (σB (Z := Unit)).machineState (σB (Z := Unit)) :=
  ⟨⟨⟨.start jAtZ_BT1 inferInstance SInvR.G4.boot_sinvX_B sInvIP_B (LocPlatM.modelMR_refl _) utPgR_B,
      SInvGp.boot_gpmOut_B, SInvIV.boot_idleVtS_B, devRangeS_B⟩, irqCarry_B⟩, LocPlatM.archT1_ioaRel_B⟩

/-- (p3J gen 60) **`CKI` at `σB`** (every cap is null). -/
theorem cki_B : SInvCk.CKI (σB (Z := Unit)) := by
  intro p cref c hc
  obtain rfl := capOpt_B hc
  trivial

/-- (p3J gen 60) **No garbage-typed object at `σB`** (module docstring). -/
theorem khWF_B : SInvKt.KhWF (σB (Z := Unit)) := by
  intro o k hk n hn
  have hk' : kheapB o = some k := hk
  rcases kheapB_cases hk' with ⟨-, x, rfl⟩ | ⟨-, y, m, rfl⟩ | ⟨-, a, rfl⟩ | ⟨-, rfl⟩
  · simp [Fl4Spec.aType] at hn
  · obtain ⟨-, -, rfl⟩ := kheapB_sc hk'
    simp only [Fl4Spec.aType] at hn
    rw [if_pos (by unfold Fl4Spec.validSchedContextSize Fl4Spec.minSchedContextBits Fl4Spec.untypedMaxBits; decide)]
      at hn
    cases hn
  · simp [Fl4Spec.aType] at hn
  · simp only [Fl4Spec.aType] at hn
    rw [if_pos (by unfold Fl4Spec.wellFormedCnodeN Fl4Spec.emptyCnode Fl4Spec.dom; ext x; simp)] at hn
    cases hn

/-- (p3J gen 60) **No signal line at `σB`** (every line is inactive). -/
theorem noSig_B : SInvNs.NoSig (σB (Z := Unit)) := fun _ e => by
  change Fl4Spec.IrqState.irqInactive = _ at e
  cases e

/-- (p3J gen 60) **Every SC of `σB` is round-robin** (the idle SC, period 0). -/
theorem rr_B : SInvRr.RR (σB (Z := Unit)) := by
  funext o
  unfold SInvRr.rpV
  cases hk : (σB (Z := Unit)).kheap o with
  | none => rfl
  | some k =>
    have hk' : kheapB o = some k := hk
    rcases kheapB_cases hk' with ⟨-, x, rfl⟩ | ⟨-, y, m, rfl⟩ | ⟨-, a, rfl⟩ | ⟨-, rfl⟩
    · rfl
    · obtain ⟨-, rfl, -⟩ := kheapB_sc hk'
      rfl
    · rfl
    · rfl

/-- (p3J gen 60) **`RunMcWKR` at BootSt's boot state on `archT1` / `ART` / `modelMR`**, no premise (module
docstring). -/
theorem runMcWKR_BT1 : RunMcWKR (L := bsL) archT1 ART modelMR sB (σB (Z := Unit)).machineState (σB (Z := Unit)) :=
  ⟨⟨⟨⟨⟨jReachU40_BT1, cki_B⟩,
    jAtMcW_of_one jAtZ_BT1 inferInstance (fun c hc => by rw [sB_cpu]; exact hc)⟩, khWF_B⟩, noSig_B⟩, rr_B⟩

/-- (p3J gen 60) `σB` runs the idle thread (so `_sysLzzP`'s per-call part is vacuous there). -/
theorem σB_ct_idle : (σB (Z := Unit)).curThread = (σB (Z := Unit)).idleThread := rfl

/-- (p3J gen 60) **BootSt's platform record on `archT1`, `RunMcWKR` and `IoaRel` hold jointly at the boot state**
(`sB`, `σB`) under `OpaqueH` [P] (module docstring). -/
theorem sysLzzP_BT1_sat (O : LocPlatM.OpaqueH) :
    PathObl.LocPlat bst archT1 ART modelMR ∧
      RunMcWKR (L := bsL) archT1 ART modelMR sB (σB (Z := Unit)).machineState (σB (Z := Unit)) ∧
      IoaRel archT1 (σB (Z := Unit)) :=
  ⟨LocPlatM.locPlat_archT1 O bs_ext, runMcWKR_BT1, LocPlatM.archT1_ioaRel_B⟩

/-! ## Goal 2: the second boot start `(sR, σR)` on `archT1` -/

/-- (p3J gen 60) `JKern` at `archT1` for the second boot start: `jKern_R`'s fields. -/
theorem jKern_RT1 : JKern (L := bsL) archT1 HR CsB DB thR sR (σR (Z := Unit)) := { jKern_R with }

/-- (p3J gen 60) **`JAtZ.utc`** at `archT1` for the second boot start (vacuous: no untyped cap). -/
theorem utc_RT1 : ∀ sl p sb fi dev, AbsSlot thR sl → capAt (bsL.mem sR) (cslotAddr sl) = ok (.Untyped p sb fi dev) →
    dev = false → Sched.UtCapP3 (L := bsL) archT1 thR sR (σR (Z := Unit)) GR sl p sb fi := by
  intro sl p sb fi dev hs hc _
  rw [capAt_capV] at hc
  rcases slotR_cases hs.isSlot with e | e | ⟨hn, -⟩
  · rw [e, capV_R_root] at hc; cases ok_inj_ff hc
  · rw [e, capV_R_tmo] at hc; cases ok_inj_ff hc
  · rw [hn] at hc; cases ok_inj_ff hc

/-- (p3J gen 60) **`JAtZ` at the second boot start on `archT1`** (`jAtZ_R` with `kern` / `utc` above). -/
theorem jAtZ_RT1 : JAtZ (L := bsL) archT1 ART ZR HR CsB AcR LstB DB sR
    (σR (Z := Unit)).machineState (σR (Z := Unit)) :=
  { jAtZ_R with kern := jKern_RT1, utc := utc_RT1 }

/-- (p3J gen 60) `IoaRel archT1` at `σR` (its arch state is `σB`'s). -/
theorem archT1_ioaRel_R : IoaRel archT1 (σR (Z := Unit)) := LocPlatM.archT1_ioaRel.frame rfl

/-- (p3J gen 60) `σR` holds no IRQ-handler cap (`capOpt_σR`). -/
theorem noHandler_R (p : Fl4Spec.ObjRef) (cref : Fl4Spec.CnodeIndex) (irq : Fl4Spec.Irq) :
    capOpt ((σR (Z := Unit)).kheap p) cref ≠ some (.irqHandlerCap irq) := fun h => by
  rcases capOpt_σR h with e | ⟨-, -, e⟩ | ⟨-, -, e⟩ <;> cases e

/-- (p3J gen 60) **irqfix3's carried fact at `σR`** (its interrupt states are `σB`'s). -/
theorem irqCarry_R : SInvIB.IrqCarry (σR (Z := Unit)) := SInvIB.irqCarry_of_noHandler noHandler_R irqStS_B

/-- (p3J gen 60) **`JReachU40` at the second boot start on `archT1` / `ART` / `modelMR`** (no premise). -/
theorem jReachU40_RT1 : JReachU40 (L := bsL) archT1 ART modelMR sR (σR (Z := Unit)).machineState (σR (Z := Unit)) :=
  ⟨⟨⟨.start jAtZ_RT1 inferInstance sinvX_R sInvIP_R (LocPlatM.modelMR_refl _) utPgR_R, gpmOut_R, idleVtS_R,
      devRangeS_R⟩, irqCarry_R⟩, archT1_ioaRel_R⟩

/-- (p3J gen 60) **`CKI` at `σR`** (its caps: null, `threadCap tRp`, `schedContextCap scRp 0`). -/
theorem cki_R : SInvCk.CKI (σR (Z := Unit)) := by
  intro p cref c hc
  rcases capOpt_σR hc with rfl | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> trivial

/-- (p3J gen 60) **No garbage-typed object at `σR`** (the root TCB, the root SC of size 0, or `σB`'s). -/
theorem khWF_R : SInvKt.KhWF (σR (Z := Unit)) := by
  intro o k hk n hn
  have hk' : kheapR o = some k := hk
  rcases kheapR_cases hk' with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, h'⟩
  · simp [Fl4Spec.aType] at hn
  · simp only [Fl4Spec.aType] at hn
    rw [if_pos (by unfold Fl4Spec.validSchedContextSize Fl4Spec.minSchedContextBits Fl4Spec.untypedMaxBits; decide)]
      at hn
    cases hn
  · exact khWF_B o k h' n hn

/-- (p3J gen 60) **No signal line at `σR`** (its interrupt states are `σB`'s). -/
theorem noSig_R : SInvNs.NoSig (σR (Z := Unit)) := noSig_B

/-- (p3J gen 60) **Every SC of `σR` is round-robin** (the root SC is the idle SC's record with a new `scTcb`). -/
theorem rr_R : SInvRr.RR (σR (Z := Unit)) := by
  funext o
  unfold SInvRr.rpV
  cases hk : (σR (Z := Unit)).kheap o with
  | none => rfl
  | some k =>
    have hk' : kheapR o = some k := hk
    rcases kheapR_cases hk' with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, h'⟩
    · rfl
    · rfl
    · have e0 := congrFun rr_B o
      unfold SInvRr.rpV at e0
      have h'' : (σB (Z := Unit)).kheap o = some k := h'
      rw [h''] at e0
      exact e0

/-- (p3J gen 60) **`RunMcWKR` at the second boot start on `archT1` / `ART` / `modelMR`**, no premise. -/
theorem runMcWKR_RT1 : RunMcWKR (L := bsL) archT1 ART modelMR sR (σR (Z := Unit)).machineState (σR (Z := Unit)) :=
  ⟨⟨⟨⟨⟨jReachU40_RT1, cki_R⟩,
    jAtMcW_of_one jAtZ_RT1 inferInstance (fun c hc => by rw [sR_cpu]; exact hc)⟩, khWF_R⟩, noSig_R⟩, rr_R⟩

/-- (p3J gen 60) The current thread of `sR` is the root TCB. -/
theorem cur_sR : sched.cur_thread bst sR = ok tRw := by
  rw [cur_thread_eq (L := bsL)]
  exact congrArg ok sR_curW

theorem fip_R : (regA tRw layout.reg.FAULT_IP).val = 18446744071562076552 := by
  unfold regA layout.tcb.REGS layout.reg.FAULT_IP; rfl

theorem tfl_R : (tFlagsWA tRw).val = 18446744071562079616 := by
  unfold tFlagsWA; rfl

/-- (p3J gen 60) **`SysFlag` at the second boot start** (module docstring: the root TCB's flags word is 0). -/
theorem sysFlag_R : SysFlag (L := bsL) sR := by
  intro ct v h
  rw [cur_sR] at h
  obtain rfl := ok_inj_ff h
  rw [Fl4Proofs.P3.flags_eq (L := bsL), WP.spec_ok]
  have hm : bsL.mem (bsL.wr sR (regA tRw layout.reg.FAULT_IP) v) (tFlagsWA tRw) = bsL.mem sR (tFlagsWA tRw) := by
    show (if Aligned (regA tRw layout.reg.FAULT_IP) ∧ regA tRw layout.reg.FAULT_IP = tFlagsWA tRw then v
      else BS.m sR (tFlagsWA tRw)) = BS.m sR (tFlagsWA tRw)
    rw [if_neg]
    rintro ⟨-, e⟩
    have h1 : (regA tRw layout.reg.FAULT_IP).val = (tFlagsWA tRw).val := by rw [e]
    rw [fip_R, tfl_R] at h1
    omega
  rw [hm, memR_mem (show (tFlagsWA tRw).val % 8 = 0 by rw [tfl_R]), tfl_R,
    show wordR 18446744071562079616 = 0#u64 from (wordR_of (by omega)).trans (wordB_zero_of (by omega))]
  unfold fl4_abi.consts.tcb_flag.TRAP_SYSCALLS
  rfl

/-- (p3J gen 60) **`_sysLzzP`'s platform record, run state, `IoaRel` and a non-idle current thread hold jointly
at BootSt's second boot start** (`bst` / `archT1` / `ART` / `modelMR`, state `sR / σR`) under `OpaqueH` [P]. -/
theorem sysLzzP_RT1_sat (O : LocPlatM.OpaqueH) :
    PathObl.LocPlat bst archT1 ART modelMR ∧
      RunMcWKR (L := bsL) archT1 ART modelMR sR (σR (Z := Unit)).machineState (σR (Z := Unit)) ∧
      IoaRel archT1 (σR (Z := Unit)) ∧ (σR (Z := Unit)).curThread ≠ (σR (Z := Unit)).idleThread :=
  ⟨LocPlatM.locPlat_archT1 O bs_ext, runMcWKR_RT1, archT1_ioaRel_R, σR_cur_ne⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 60) **A closed instance of `kernel_entry_runMcWKR_sysLzzP` at BootSt's second boot start on
`archT1`**: `SysYield` at `(sR, σR)`, every antecedent discharged; only `OpaqueH`, `FpuImplDet`, `FpuWriteDet` [P]
left. -/
theorem sysLzzP_RT1_yield (O : LocPlatM.OpaqueH) (hFpu : FpuImplDet) (hFW : FpuWriteDet) :
    syscall.handle_syscall bst archT1 sR (σR (Z := Unit)).machineState fl4_abi.syscall.SysYield ⦃ r =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true .sysYield (σR (Z := Unit))).1 ∧
        RunMcWKR (L := bsL) archT1 ART modelMR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzzP (L := bsL) (st := bst) (LocPlatM.locPlat_archT1 O bs_ext) hFpu hFW
    runMcWKR_RT1 _ _ σR_cur_ne JBootQ.nativeSys_yieldI sysFlag_R
    (fun Z H Cs _ _ _ _ => JBootQ.sysK6_yield archT1 ART Z H Cs _ _ _)

set_option maxHeartbeats 4000000 in
/-- (p3J gen 60) `sysLzzP_RT1_yield` through the FPU record (`kernel_entry_runMcWKR_sysLzzPF`). -/
theorem sysLzzP_RT1_yieldF (O : LocPlatM.OpaqueH) (F : FpuDet) :
    syscall.handle_syscall bst archT1 sR (σR (Z := Unit)).machineState fl4_abi.syscall.SysYield ⦃ r =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true .sysYield (σR (Z := Unit))).1 ∧
        RunMcWKR (L := bsL) archT1 ART modelMR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzzPF (L := bsL) (st := bst) (LocPlatM.locPlat_archT1 O bs_ext) F
    runMcWKR_RT1 _ _ σR_cur_ne JBootQ.nativeSys_yieldI sysFlag_R
    (fun Z H Cs _ _ _ _ => JBootQ.sysK6_yield archT1 ART Z H Cs _ _ _)

end

end Fl4Proofs.P2.BootSt

namespace Fl4Proofs.P2.LocPlatM
open fl4_core Fl4Proofs.P3
open Fl4Spec (MachineState)

/-- (p3J gen 60) A port read `machineOpLift (impl port)` then `gets val` with `val` constantly 0 has an outcome
reading 0 that keeps the memory (`ignoreFailure` keeps the outcome set non-empty). -/
theorem inOp_zero (impl : Fl4Spec.Word16 → Fl4Spec.MachineRestMonad Unit) (val : MachineState → Fl4Spec.Word)
    (hv : ∀ ms, val ms = 0) (port : Fl4Spec.Word16) (ms : MachineState) :
    ∃ ms' : MachineState, ms'.underlyingMemory = ms.underlyingMemory ∧
      ((0#u64 : U64).bv, ms') ∈ (Fl4Spec.NonDet.bind (Fl4Spec.machineOpLift (impl port))
        (fun _ => Fl4Spec.NonDet.gets val) ms).1 := by
  have hx : ∃ x, x ∈ (Fl4Spec.ignoreFailure (impl port) ms.machineStateRest).1 := by
    unfold Fl4Spec.ignoreFailure
    split_ifs with h
    · exact ⟨_, rfl⟩
    · exact Set.nonempty_iff_ne_empty.2 h
  obtain ⟨⟨u, mr'⟩, hx⟩ := hx
  cases u
  refine ⟨{ ms with machineStateRest := mr' }, rfl, ?_⟩
  refine Exists.intro ((), { ms with machineStateRest := mr' }) ⟨?_, ?_⟩
  · refine Exists.intro (ms.machineStateRest, ms) ⟨rfl, ?_⟩
    refine Exists.intro (((), mr'), ms) ⟨⟨hx, rfl⟩, ?_⟩
    exact Exists.intro ((), { ms with machineStateRest := mr' }) ⟨rfl, rfl⟩
  · show _ = _
    rw [hv]
    rfl

/-- (p3J gen 60) `portIn m` has the outcome `[0]` keeping the memory when `m` has an outcome 0 keeping it. -/
theorem portIn_zero (m : Fl4Spec.MachineMonad Fl4Spec.Data) (σ : Fl4Spec.State Unit)
    (hm : ∃ ms' : MachineState, ms'.underlyingMemory = σ.machineState.underlyingMemory ∧
      ((0#u64 : U64).bv, ms') ∈ (m σ.machineState).1) :
    ∃ ms : MachineState, ms.underlyingMemory = σ.machineState.underlyingMemory ∧
      (.ok [(0#u64 : U64).bv], { σ with machineState := ms }) ∈
        ((Fl4Spec.NonDetE.liftE (ε := Unit) (Fl4Spec.portIn (Z := Unit) m)).run σ).1 := by
  obtain ⟨ms', hu, hmem⟩ := hm
  refine ⟨ms', hu, ?_⟩
  refine Exists.intro ([(0#u64 : U64).bv], { σ with machineState := ms' }) ⟨?_, rfl⟩
  refine Exists.intro ((0#u64 : U64).bv, { σ with machineState := ms' }) ⟨?_, rfl⟩
  refine Exists.intro (σ.machineState, σ) ⟨rfl, ?_⟩
  refine Exists.intro (((0#u64 : U64).bv, ms'), σ) ⟨⟨hmem, rfl⟩, ?_⟩
  exact Exists.intro ((), { σ with machineState := ms' }) ⟨rfl, rfl⟩

/-- (p3J gen 60) **`OpaqueH.pin0` from the three port-read values** (module docstring): if the spec's opaque
`in8Val` / `in16Val` / `in32Val` read 0 at every machine state, `pin0`'s statement holds (no fact about the
`in*Impl` operations is needed). -/
theorem pin0_of_val0 (h8 : ∀ ms, Fl4Spec.in8Val ms = 0) (h16 : ∀ ms, Fl4Spec.in16Val ms = 0)
    (h32 : ∀ ms, Fl4Spec.in32Val ms = 0) :
    ∀ (p z : U64) (σ : Fl4Spec.State Unit), ∃ ms : MachineState,
      ms.underlyingMemory = σ.machineState.underlyingMemory ∧
      (.ok [(0#u64 : U64).bv], { σ with machineState := ms }) ∈ ((Fl4Spec.archPerformInvocation (Z := Unit)
        (.invokeIOPort (.ioPortInvocation (BitVec.ofNat 16 p.val) (inData z.val)))).run σ).1 := by
  intro p z σ
  have hd : inData z.val = .ioPortIn8 ∨ inData z.val = .ioPortIn16 ∨ inData z.val = .ioPortIn32 := by
    unfold inData
    split <;> simp
  rcases hd with hd | hd | hd <;> rw [hd]
  · exact portIn_zero _ σ (inOp_zero Fl4Spec.in8Impl Fl4Spec.in8Val h8 _ _)
  · exact portIn_zero _ σ (inOp_zero Fl4Spec.in16Impl Fl4Spec.in16Val h16 _ _)
  · exact portIn_zero _ σ (inOp_zero Fl4Spec.in32Impl Fl4Spec.in32Val h32 _ _)

/-- (p3J gen 60) **The three port-read value facts are consistent with the constants' type** (module docstring). -/
theorem opaqueH_pin0_model : ∃ f : MachineState → Fl4Spec.Word, ∀ ms, f ms = 0 := ⟨fun _ => 0, fun _ => rfl⟩

end Fl4Proofs.P2.LocPlatM
