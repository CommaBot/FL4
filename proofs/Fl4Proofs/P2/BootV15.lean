/-
# P2 (line p3mc, gen 55): **the boot witnesses on V15** — `serializable_fl4_V15_exact` and
`serializable_fl4_V15_pmKADZ_C` applied to the concrete boot executions

Gens 36–40 checked V12 / V13 against concrete executions from the boot configuration (`runAllV12_B` /
`runAllV13_B`: the empty-start execution `exec_B`; `topV12_B` / `topV13_B`: the timer-IRQ path's `.start`, body and
leave from `s0B O`; `topV13_R`: the vmF path's from `cfg0 (KR O) memR`). V12–V14 are superseded by V15 (handoff §60)
and retired; this module re-states each witness over V15 before they go, so no concrete witness is lost. The
executions are the same ones (`exec_B`, `runEndV13_B`, `runEndV13_R`); since gen 56 they are built as native
`ExecV15` executions directly (until gen 55 as `ExecWPRV12`s, carried over by `execV15_native_iff`).

* **`v15_of_native`** (generic): a native `ExecV15` gives — through `ExecV15.toC`, and the `.inl` embedding
  (`ExecV15.map`) — `serializable_fl4_V15_exact_C`'s conclusion (`slotOblV13_C`, `native_noAd`, `native_vcpuNone`
  at `P.toC`) and the `ExecV15C (ExecCfg.nativePmKAD … B)` over `P.toC` with `serializable_fl4_V15_pmKADZ_C`'s
  (both at `locPlatCR_of P hIoa`).
* **`pmObl7_none`**: the PageMap slot's [P] record `PmObl7` at the empty core set and the empty lock predicate (no
  premise), so the PageMap configuration is concrete too.
* **`runAllV15_B`**, **`topV15_B`**, **`topV15_R`**: `v15_of_native` at `locPlat_archT O bs_ext` /
  `mrKeepIoapic_archT` and `pmObl7_none`, on `exec_B` / `runEndV13_B` / `runEndV13_R`; the timer-IRQ and vmF tops
  also give the sequential run of the started path (`Run (.start k) m s.mem`), as `topV13_B` / `topV13_R` did.

Premises: `OpaqueH` only (as the V13 witnesses). The witnesses are at the boot platform (`bst`, `archT`, `modelMR`);
no execution from a boot configuration at jboot's witness platform (`wst`, `ipiMR`) exists on the branch, so
`serializable_fl4_V15_pmKADZW` has none. No [J] / [P] / [W] added. New module; no existing statement changed except
the root import list.
-/
import Fl4Proofs.P2.BootRVmF
import Fl4Proofs.P2.InsV15Pm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1 Classical
open Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2EV Fl4Proofs.P2.OwnMapP Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.E2EP
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll Run)
open Fl4Proofs.P2.E2E (SP)

noncomputable section

section gen
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **A native V15 execution under both tops** (module docstring): `serializable_fl4_V15_exact_C`'s conclusion
(at `slotOblV13_C`), the `nativePmKAD` `ExecV15C` of the same run and `serializable_fl4_V15_pmKADZ_C`'s
conclusion, both at `locPlatCR_of P hIoa`. -/
theorem v15_of_native (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (B : PmObl7 st Cs Ω Sg Ac Locks)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} {E : U64 → U64} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0) (h : ExecV15 (ExecCfg.native st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch E)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem ∧
      ExecV15C (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) P.toC s0 K0 Ch0 s K Ch E ∧
      ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ s0.mem s.mem := by
  have h2 := ExecV15.map (c2 := ExecCfg.nativePmKAD st ar hA a0 arI AR MR B) Sum.inl
    (fun _ _ _ _ _ _ _ _ _ hi => hi) (fun _ hn => hn) (fun _ _ h => h)
    (fun K E m a x h => (native_noAd st ar hA a0 arI AR MR K E m a x h).elim) h
  exact ⟨serializable_fl4_V15_exact_C (slotOblV13_C st ar hA a0 (locPlatCR_of P hIoa))
      (native_noAd st ar hA a0 arI AR MR) (native_vcpuNone st ar hA a0 arI AR MR) P.toC h0 hA0 hB hc0 hM0 h.toC hq,
    h2.toC, serializable_fl4_V15_pmKADZ_C st ar hA a0 (locPlatCR_of P hIoa) B h0 hA0 hB hc0 hM0 h2.toC hq⟩

/-- **The PageMap slot's [P] record at the empty core set and lock predicate** (no premise). -/
theorem pmObl7_none : PmObl7 st (∅ : Set U64) ∅ ∅ ∅ (fun _ _ => False) :=
  ⟨fun _ h => absurd h (Set.notMem_empty _), fun _ _ _ _ _ _ _ => rfl⟩

end gen

/-- The boot instance's PageMap configuration (`pmObl7_none`). -/
abbrev cfgPmB (a0 : Fl4Spec.MachineState) :=
  ExecCfg.nativePmKAD bst LocPlatM.archT LocPlatM.archT_total a0 LocPlatM.archT LocPlatM.ART modelMR
    (pmObl7_none bst)

/-- The boot instance's native configuration. -/
abbrev cfgNatB (a0 : Fl4Spec.MachineState) :=
  ExecCfg.native bst LocPlatM.archT LocPlatM.archT_total a0 LocPlatM.archT LocPlatM.ART modelMR

/-- **V15 applied to the empty-start instance** (`runAllV13_B`'s execution `exec_B`). -/
theorem runAllV15_B (O : LocPlatM.OpaqueH) (a0 : Fl4Spec.MachineState) :
    ∃ E : U64 → U64,
      ExecV15 (cfgNatB a0) (LocPlatM.locPlat_archT O bs_ext) (s0B O) (KB O) (fun _ => ChB O) (c7B O) (KB O)
        (fun _ => ChB O) E ∧ RunAll (c7B O).log (s0B O).mem (c7B O).mem ∧
      ExecV15C (cfgPmB a0) (LocPlatM.locPlat_archT O bs_ext).toC (s0B O) (KB O) (fun _ => ChB O) (c7B O) (KB O)
        (fun _ => ChB O) E ∧
      ∃ ℓ : List SP, ℓ.Perm (c7B O).log ∧ RunAll ℓ (s0B O).mem (c7B O).mem := by
  obtain ⟨E, he⟩ := exec_B (cfg := cfgNatB a0) O fun _ _ h => h
  exact ⟨E, he, v15_of_native bst LocPlatM.archT LocPlatM.archT_total a0 (LocPlatM.locPlat_archT O bs_ext)
    LocPlatM.mrKeepIoapic_archT (pmObl7_none bst) (init_B O) (armInv_B O) (fun _ => serExitW_B O) (hc0_B O)
    (mapsP_B O) he (noLoc_B O)⟩

/-- **V15 applied to an execution with a real start** (`topV13_B`'s: the timer-IRQ path's `.start`, its body and
the leave, from `s0B O`). -/
theorem topV15_B (O : LocPlatM.OpaqueH) (a0 a : Fl4Spec.MachineState) :
    ∃ (s : Cfg U64 U64 U64 U64) (E : U64 → U64),
      ExecV15 (cfgNatB a0) (LocPlatM.locPlat_archT O bs_ext) (s0B O) (KB O) (fun _ => ChB O) s (KB O)
        (fun _ => ChB O) E ∧
      ExecV15C (cfgPmB a0) (LocPlatM.locPlat_archT O bs_ext).toC (s0B O) (KB O) (fun _ => ChB O) s (KB O)
        (fun _ => ChB O) E ∧
      NoLoc s ∧ s.log = [.start (kB O a)] ∧ Run (.start (kB O a)) memB s.mem ∧
      ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ memB s.mem := by
  obtain ⟨s, E, h1, hq, hl⟩ := runEndV13_B O a0 a
  obtain ⟨hr, h2, hp⟩ := v15_of_native bst LocPlatM.archT LocPlatM.archT_total a0
    (LocPlatM.locPlat_archT O bs_ext) LocPlatM.mrKeepIoapic_archT (pmObl7_none bst) (init_B O) (armInv_B O)
    (fun _ => serExitW_B O) (hc0_B O) (mapsP_B O) h1 hq
  rw [hl] at hr
  exact ⟨s, E, h1, h2, hq, hl, runAll_one hr, hp⟩

/-- **V15 applied to the vmF start at the second boot start** (`topV13_R`'s execution, whose start carries `ybw`
[J] and `NonIdle` [P] inside `StartV13`). -/
theorem topV15_R (O : LocPlatM.OpaqueH) (a0 a : Fl4Spec.MachineState) :
    ∃ (s : Cfg U64 U64 U64 U64) (E : U64 → U64),
      ExecV15 (cfgNatB a0) (LocPlatM.locPlat_archT O bs_ext) (cfg0 (KR O) memR) (KR O) (fun _ => ChR O) s (KR O)
        (fun _ => ChR O) E ∧
      ExecV15C (cfgPmB a0) (LocPlatM.locPlat_archT O bs_ext).toC (cfg0 (KR O) memR) (KR O) (fun _ => ChR O) s
        (KR O) (fun _ => ChR O) E ∧
      NoLoc s ∧ s.log = [.start (kR O a)] ∧ Run (.start (kR O a)) memR s.mem ∧
      ∃ ℓ : List SP, ℓ.Perm s.log ∧ RunAll ℓ memR s.mem := by
  obtain ⟨s, E, h1, hq, hl⟩ := runEndV13_R O a0 a
  obtain ⟨hr, h2, hp⟩ := v15_of_native bst LocPlatM.archT LocPlatM.archT_total a0
    (LocPlatM.locPlat_archT O bs_ext) LocPlatM.mrKeepIoapic_archT (pmObl7_none bst) (cfg_init _ _) (cfg_armInv _ _)
    (fun _ => serExitW_R O) (hc0_R O) (mapsP_cfg0 _ _) h1 hq
  rw [hl] at hr
  exact ⟨s, E, h1, h2, hq, hl, runAll_one hr, hp⟩

end
end Fl4Proofs.P2.BootSt
