/-
P3 (p3J gen 59): **`kernel_entry_runMcWKR_sysLzzP` is not vacuous on a BootSt-style platform with one IOAPIC**
(Architect ruling 2026-11-28 14:01Z, item 2): `LocPlat`, the run state `RunMcWKR` (whose `JReachU40` part holds
`IoaRel`) and a non-idle current thread hold jointly at one platform, and `_sysLzzP` closes `SysYield` there.

* **`LocPlatM.archT1`**: BootSt's model arch `archT` (P2/LocPlatModel) with only `num_ioapics` / `ioapic_pins`
  changed — one IOAPIC of 24 pins, as jboot's `warI1` fix of `warI` (JBootIoa) and the spec's `init_arch_state`
  (`x64_num_ioapics = 1`, 24 lines). `archT` / `locPlat_archT` are not changed.
* **`locPlat_archT1 O sx : LocPlat st archT1 ART modelMR`**: `locPlat_archT`'s fields (none of them reads the
  IOAPIC counts), `ArchTotal` re-proved for the two changed operations; same hypotheses `OpaqueH` + `StoreExt`.
* **`archT1_ioaRel`** (`IoaRel archT1` at jboot's boot state), **`archT1_ioaRel_σ1`**, **`archT1_ioaRel_B`**
  (`IoaRel archT1 σB`: BootSt's boot state also meets it at `archT1`).
* **`archT_not_ioaRel_B : ¬ IoaRel archT σB`**: the check asked by the ruling — BootSt's `archT` answers 0
  IOAPICs, `σB.archState = initArchState` has 1, so BootSt's own platform has no `JReachU40` / `RunMcWKR` start;
  `archT1` meets it (`archT1_ioaRel_B`). (A BootSt `RunMcWKR` start would also need `jAtZ_B` at `archT1`, whose
  arch enters only `kern.tdx` / `utc` as below; not done here.)
* At the root-thread witness `JBootQ.w1 / σ1` (store `wst`, `wL`, `wP`; gen 56's state, `σ1_nonIdle`) on
  `archT1` / `ART` / `modelMR`: **`w1_jkernT1`**, **`w1_utcT1`**, **`jAtZ_w1T1`** (the fields of `jAtZ_w1I1`; `JAtZ`
  names the arch only in `kern` (`TdxRel`: `tdx_active` / `dma_ram`, `modelArch`'s in both) and `utc` (vacuous));
  **`jReachU40_w1T1`** (`JReachU3.start` with `modelMR_refl`, then gen 15's state facts verbatim and
  `archT1_ioaRel_σ1`); **`runMcWKR_w1T1`** (gen 56's `RunMcWKR` components `cki_σ1`, `khWF_σ1`, `noSig_σ1`,
  `rr_σ1`; no premise).
* **`sysLzzP_T1_sat (O : OpaqueH)`**: `LocPlat wst archT1 ART modelMR` ∧ `RunMcWKR … w1 σ1` ∧ `IoaRel archT1 σ1` ∧
  `σ1.curThread ≠ σ1.idleThread` — the joint non-vacuity of `_sysLzzP`'s premises other than the two FPU facts.
* **`sysLzzP_T1_yield (O : OpaqueH) hFpu hFW`** (closed): `_sysLzzP` at that platform and state for `SysYield`,
  every per-call antecedent discharged (`σ1_nonIdle`, `nativeSys_yieldI`, `w1_hfl`, `sysK6_yield`).
* **`opaqueH_ipi_model`**: `OpaqueH.ipi` (the one `OpaqueH` field beyond gen 55's `opaqueSysLzz_model`, which
  covers `nd` / `max` / `wcetUs` / `timerUnit` / `maxP` (`< 2^61`) / `dl` and `FpuImplDet` / `FpuWriteDet`) is
  consistent with `irqOracle`'s type. `OpaqueH.pin0` (a port-read outcome at every spec state) stays unmodelled,
  as gen 55's `OpaqueWK.pin`.

Caveat (as gens 55 / 56): `ART := fun _ _ => True`, so the CR3-side `LocPlat` fields and `JAtZ`'s CR3 clauses hold
trivially; `modelMR` keeps no line masked, so `IpiF` comes from `OpaqueH.ipi` (BootSt's choice), not from
`ipiMR`'s masks. One core, one root thread.

Named premises: `OpaqueH` [P] (LocPlatModel), `FpuImplDet` [P] (ScFpuNd), `FpuWriteDet` [P] (ArchSwThr): existing;
none new. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JSysLzzP
import Fl4Proofs.P3.P3JSysLzzW1
import Fl4Proofs.P2.LocPlatModel
import Fl4Proofs.P2.BootSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.LocPlatM
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P2.PathObl Fl4Proofs.P3.SInvR.G5
open Fl4Spec (MachineState)

noncomputable section

/-- (p3J gen 59) **BootSt's model arch with one IOAPIC of 24 pins** (module docstring): `archT` with
`num_ioapics` and `ioapic_pins` set as jboot's `warI1`. -/
def archT1 : machine.Arch MachineState :=
  { archT with
    num_ioapics := fun _ => ok 1#u64
    ioapic_pins := fun _ i => ok (if i.val < 1 then 24#u64 else 0#u64) }

/-- (p3J gen 59) `ArchTotal` for `archT1`: `archT_total`'s fields, the two IOAPIC reads re-proved. -/
theorem archT1_total : P0.ArchTotal archT1 :=
  { archT_total with
    num_ioapics := fun _ => (WP.spec_ok _).2 trivial
    ioapic_pins := fun _ _ => (WP.spec_ok _).2 trivial }

/-- (p3J gen 59) **`LocPlat` for `archT1`** (module docstring): `locPlat_archT`'s fields; only `ArchTotal` reads
the two changed operations. -/
theorem locPlat_archT1 {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] (O : OpaqueH)
    (sx : P1.StoreExt st) : LocPlat st archT1 ART modelMR where
  ari := { archT_ari with }
  tot := archT1_total
  nd := O.nd
  mach := { archT_machPlat O with }
  kd := { archT_kd with }
  io := { archT_io with }
  pa := { archT_pa O with }
  ia := { archT_ia O with }
  t := { archT_time O with }
  max := O.max
  tu _ _ := (WP.spec_ok _).2 rfl
  ref := { archT_ref with }
  pi := archT_pi O
  sx := sx
  dr := archT_dr O

/-- (p3J gen 59) **`IoaRel` for `archT1` at jboot's boot state** (`init_arch_state`: one IOAPIC, 24 lines). -/
theorem archT1_ioaRel : IoaRel archT1 Fl4Proofs.P3.JBoot.fInitASt := by
  refine ⟨1#u64, fun _ => rfl, rfl, fun a i hi => ⟨24#u64, ?_, rfl, by decide⟩⟩
  have e : (1#u64).val = 1 := rfl
  have h1 : i.val < 1 := by omega
  show ok (if i.val < 1 then 24#u64 else 0#u64) = ok 24#u64
  rw [if_pos h1]

/-- (p3J gen 59) **`IoaRel archT1` at BootSt's boot state** (its arch state is `initArchState`). -/
theorem archT1_ioaRel_B : IoaRel archT1 (BootSt.σB (Z := Unit)) := archT1_ioaRel.frame rfl

/-- (p3J gen 59) **BootSt's `archT` does not meet `IoaRel` at `σB`** (module docstring: 0 IOAPICs against the
spec's 1). -/
theorem archT_not_ioaRel_B : ¬ IoaRel archT (BootSt.σB (Z := Unit)) := by
  rintro ⟨nA, hn, hb, -⟩
  have h0 : archT.num_ioapics (BootSt.σB (Z := Unit)).machineState = ok 0#u64 := rfl
  have e : nA = 0#u64 := eq_of_ok_eq ((hn _).symm.trans h0)
  have h1 : (BootSt.σB (Z := Unit)).archState.x64NumIoapics = 1 := rfl
  subst e
  rw [h1] at hb
  exact absurd hb (by decide)

/-- (p3J gen 59) **`OpaqueH.ipi` is consistent with `irqOracle`'s type** (module docstring). -/
theorem opaqueH_ipi_model : ∃ f : Nat → Fl4Spec.Word8, ∀ n, (f n).toNat ≠ 126 ∧ (f n).toNat ≠ 127 :=
  ⟨fun _ => 0, fun _ => (by decide : (0 : Fl4Spec.Word8).toNat ≠ 126 ∧ (0 : Fl4Spec.Word8).toNat ≠ 127)⟩

end

end Fl4Proofs.P2.LocPlatM

namespace Fl4Proofs.P3.JBootQ
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.Vs Fl4Proofs.P3.Mc
open Fl4Proofs.P2.LocPlatM (archT1 ART)

noncomputable section

/-- (p3J gen 59) `JKern` at `archT1`: `w1_jkern`'s fields (its TDX clause reads `tdx_active` / `dma_ram`,
`modelArch`'s). -/
theorem w1_jkernT1 : JKern (L := wL) archT1 Hw1 Csw Dw thW1 w1 σ1 := { w1_jkern with }

/-- (p3J gen 59) **`JAtZ.utc`** at `archT1` (vacuous: no slot of `w1` holds an untyped cap). -/
theorem w1_utcT1 : ∀ sl p sb fi dev, AbsSlot thW1 sl →
    capAt (wL.mem w1) (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
    Sched.UtCapP3 (L := wL) archT1 thW1 w1 σ1 G1 sl p sb fi := by
  intro sl p sb fi dev hs h _
  rw [capAt_capV] at h
  rcases slot1_cases hs.isSlot with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e] at h <;> cases ok_inj h

/-- (p3J gen 59) **The joint invariant at the root-thread witness, arch `archT1`, CR3 relation `ART`**
(`jAtZ_w1I1` with `kern` / `utc` above; its other fields name no arch). -/
theorem jAtZ_w1T1 (a : MachineState) :
    JAtZ (L := wL) archT1 ART Zw1 Hw1 Csw C1 (fun _ => []) Dw w1 a σ1 :=
  { jAtZ_w1I1 a with kern := w1_jkernT1, utc := w1_utcT1 }

/-- (p3J gen 59) `IoaRel archT1` at `σ1` (its arch state is jboot's boot state's). -/
theorem archT1_ioaRel_σ1 : IoaRel archT1 σ1 := Fl4Proofs.P2.LocPlatM.archT1_ioaRel.frame rfl

/-- (p3J gen 59) **`JReachU40` at the root-thread witness on `archT1` / `ART` / `modelMR`** (no premise). -/
theorem jReachU40_w1T1 : JReachU40 (L := wL) archT1 ART modelMR w1 σ1.machineState σ1 :=
  ⟨⟨⟨.start (jAtZ_w1T1 _) Zw1_vx σ1_sinvX σ1_sinvIP (Fl4Proofs.P2.LocPlatM.modelMR_refl _) σ1_utPgR,
      σ1_gpmOut, σ1_idleVtS, σ1_devRangeS⟩, σ1_irqCarry⟩, archT1_ioaRel_σ1⟩

/-- (p3J gen 59) **`RunMcWKR` at the root-thread witness on `archT1` / `ART` / `modelMR`**, no premise (gen 56's
components). -/
theorem runMcWKR_w1T1 : RunMcWKR (L := wL) archT1 ART modelMR w1 σ1.machineState σ1 :=
  ⟨⟨⟨⟨⟨jReachU40_w1T1, cki_σ1⟩,
    jAtMcW_of_one (jAtZ_w1T1 _) Zw1_vx (fun c hc => by rw [cpu_w1]; exact hc)⟩, khWF_σ1⟩, noSig_σ1⟩, rr_σ1⟩

/-- (p3J gen 59) **`_sysLzzP`'s platform record, run state, `IoaRel` and a non-idle current thread hold jointly**
at `wst` / `archT1` / `ART` / `modelMR`, state `w1 / σ1`, under `OpaqueH` [P] (module docstring). -/
theorem sysLzzP_T1_sat (O : Fl4Proofs.P2.LocPlatM.OpaqueH) :
    Fl4Proofs.P2.PathObl.LocPlat wst archT1 ART modelMR ∧
      RunMcWKR (L := wL) archT1 ART modelMR w1 σ1.machineState σ1 ∧ IoaRel archT1 σ1 ∧
      σ1.curThread ≠ σ1.idleThread :=
  ⟨Fl4Proofs.P2.LocPlatM.locPlat_archT1 O wst_ext, runMcWKR_w1T1, archT1_ioaRel_σ1, σ1_nonIdle⟩

set_option maxHeartbeats 4000000 in
/-- (p3J gen 59) **A closed instance of `kernel_entry_runMcWKR_sysLzzP` on `archT1`**: `SysYield` at the
root-thread witness, every antecedent discharged; only `OpaqueH`, `FpuImplDet`, `FpuWriteDet` [P] left. -/
theorem sysLzzP_T1_yield (O : Fl4Proofs.P2.LocPlatM.OpaqueH) (hFpu : FpuImplDet) (hFW : FpuWriteDet) :
    syscall.handle_syscall wst archT1 w1 σ1.machineState fl4_abi.syscall.SysYield ⦃ r =>
      ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true .sysYield σ1).1 ∧
        RunMcWKR (L := wL) archT1 ART modelMR r.1 r.2 σ' ⦄ :=
  kernel_entry_runMcWKR_sysLzzP (L := wL) (st := wst) (Fl4Proofs.P2.LocPlatM.locPlat_archT1 O wst_ext) hFpu hFW
    runMcWKR_w1T1 _ _ σ1_nonIdle nativeSys_yieldI w1_hfl
    (fun Z H Cs _ _ _ _ => sysK6_yield archT1 ART Z H Cs _ _ _)

end

end Fl4Proofs.P3.JBootQ
