/-
P2 (line jboot, gen 5; audit F4): **U2's end-to-end witness with no `irqOracle` premise**: `wit_U2_uncond`
under `OpaqueWK` (wit's `OpaqueW` without `ipi`, int21's JBootU34).

gen 4's `wit_U2_uncond (O : OpaqueW)` needs `OpaqueW.ipi` (the opaque IRQ oracle never yields 126 / 127) only
for `LocPlat`'s `MachPlat` + `IrqPlatA` pair (JBootIpi's `ipi_forces_oracle`). irqfix's fix replaces them by
`MachPlatT` (= `MachPlatF ∧ IpiF`) and `IrqPlatK`, which `warI` meets at `ipiMR` with no oracle fact. U2's proof
is transported onto the fix (P2/WitU34Gen: `Fl4ProofsQ.P2.PathObl.LocPlat` is `LocPlat` with those two records,
`Fl4ProofsQ.P2.Wit.wit_U2_io` / `wit_exec_io` are wit's generic theorems over it). Here:
* `wit_locPlatK (O : OpaqueWK) : Fl4ProofsQ.P2.PathObl.LocPlat wst warI wAR ipiMR` (JBootU34's `u34_w0I` facts);
* `w1_nonIdleI`: gen 4's `w1_nonIdle` at `ipiMR` (same proof);
* **`wit_exec_uncond'`** / **`wit_U2_uncond'`** `(O : OpaqueWK)`: the execution with every U2 hypothesis and U2's
  conclusion `RunAll [.start q] s0.mem s.mem`, at the gen-4 witness `w1` started at `ipiMR`
  (`jReachU34_w1I.1`, JBoot1U34);
* `wit_U2_uncond_of (O : OpaqueW)`: the same from gen 4's premise (`opaqueW_toK`).

**Premises**: `OpaqueWK` [P] only (the opaque Fl4Spec constants: `numDomains = 1`, `maxTicksToUs`,
`kernelWCETUs`, `timerUnit`, `MAX_PERIOD_US < 2^61`, `setDeadlineImpl` determinism, a port-read value). The
`irqOracle` fact is gone. irqfix's `IrqAckU` (the IRQ ack's unmask, [J] in U33) appears only inside the decode
premise `JDecMRLKQ` of the transported tops' syscall clauses, which U2's proof never instantiates; it is not a
premise here.

No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P2.WitU34Gen
import Fl4Proofs.P2.WitUncond
import Fl4Proofs.P3.JBoot1U34
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Wit
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV Fl4Proofs.P2.E2EP
open Fl4Proofs.P2.E2E (LocalPath SP SerStep)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll)
open Fl4Proofs.P3 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBoot

noncomputable section

/-- **The concrete platform meets the fixed `LocPlat`** (irqfix's `MachPlatT` / `IrqPlatK`, at `ipiMR`) under
`OpaqueWK` [P]: no `irqOracle` fact. -/
theorem wit_locPlatK (O : OpaqueWK) : Fl4ProofsQ.P2.PathObl.LocPlat wst warI wAR ipiMR := by
  obtain ⟨hari, htot, hnd, hMF, hIp, hkd, hio, -, -, hIA, hT, hmax, htu, href, hpi, hsx, hdr, -⟩ := u34_w0I O
  exact ⟨hari, htot, hnd, MachPlatF.toT hMF hIp, hkd, hio,
    ⟨fun _ _ _ => (WP.spec_ok _).2 trivial, fun a => (warI_timeAgreeK O).mb a⟩, hIA, hT, hmax, htu, href, hpi,
    hsx, hdr⟩

/-- `MRKeepIoapic` at `ipiMR` (the model's IOAPIC operations leave the state). -/
theorem wit_ioapicI : MRKeepIoapic warI ipiMR :=
  ⟨fun _ _ _ _ _ _ _ h => (WP.spec_ok _).2 h, fun _ _ _ _ _ _ _ _ h => (WP.spec_ok _).2 h⟩

/-- **`NonIdle` at `w1` at `ipiMR`** (gen 4's `w1_nonIdle`, same proof). -/
theorem w1_nonIdleI : NonIdle wst warI wAR ipiMR w1 := by
  intro a τ hJ
  obtain ⟨hc, hi⟩ := Fl4Proofs.P3.JBoot.JAt.curIdle (Fl4Proofs.P3.JBoot.JReachU3.jAt hJ.1)
  rw [hc, hi, cpu_w1, curT_w1, idleT_w1]
  decide

/-- **The io-port execution of U2 from `w1` on the fixed platform** (only `OpaqueWK` [P]). -/
theorem wit_exec_uncond' (O : OpaqueWK) :
    ∃ (s0 s : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : WSt → Prop) (q : SP),
      Init s0 ∧ ArmInv s0 ∧ Fl4ProofsQ.P2.E2EV.SerExitW (wit_locPlatK O) K0.toKLayoutV Ch0 ∧
      (K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem) ∧ MapsP K0 s0 ∧
      Fl4ProofsQ.P2.E2EP.ExecWPR (LPU2 wst warI warI_total wa0) (StartV2 wst warI warI_total wa0 warI wAR ipiMR)
        (wit_locPlatK O) s0 K0 Ch0 s K0 Ch0 ∧ NoLoc s ∧ s.log = [.start q] ∧ s0.mem = wmem w1 :=
  Fl4ProofsQ.P2.Wit.wit_exec_io wst warI warI_total wa0 (wit_locPlatK O) jReachU34_w1I.1 w1_nonIdleI

/-- **U2 non-vacuous with no `irqOracle` premise**: a concrete execution meeting every hypothesis of the
transported `serializable_fl4_localU2`, an io-port body started and completed, and U2's conclusion about it,
under `OpaqueWK` [P] only. -/
theorem wit_U2_uncond' (O : OpaqueWK) :
    ∃ (s0 s : Cfg U64 U64 U64 U64) (q : SP), s.log = [.start q] ∧ s0.mem = wmem w1 ∧ NoLoc s ∧
      RunAll s.log s0.mem s.mem :=
  Fl4ProofsQ.P2.Wit.wit_U2_io wst warI warI_total wa0 (wit_locPlatK O) wit_ioapicI jReachU34_w1I.1 w1_nonIdleI

/-- `wit_U2_uncond'` from gen 4's `OpaqueW` (`OpaqueW → OpaqueWK`). -/
theorem wit_U2_uncond_of (O : OpaqueW) :
    ∃ (s0 s : Cfg U64 U64 U64 U64) (q : SP), s.log = [.start q] ∧ s0.mem = wmem w1 ∧ NoLoc s ∧
      RunAll s.log s0.mem s.mem :=
  wit_U2_uncond' (opaqueW_toK O)

/-! ## The remaining `OpaqueWK` facts -/

/-- A `TimeConsts` value meeting every axiom, with FL4's WCET and timer unit and `maxPeriodUs = 2 ^ 61`. -/
def wTCbig : Fl4Spec.TimeConsts :=
    { maxPeriodUs := 2305843009213693952,
      kernelWCETUs := 10, ticksPerTimerUnit := 1, timerUnit := 1,
      kernelWCET_us_pos2 := by decide
      MIN_BUDGET_le_MAX_PERIOD := by decide
      ticks_per_timer_unit_non_zero := by decide
      MIN_BUDGET_bound := by decide
      getCurrentTime_buffer_bound := by decide
      kernelWCET_pos' := by decide
      MIN_BUDGET_pos' := by decide
      init_domain_time_pos := by decide
      init_domain_time_bound := by decide
      getCurrentTime_buffer_pos := by decide }

/-- **`OpaqueWK.per` is not a consequence of the spec's `TimeConsts` axioms**: a `TimeConsts` with FL4's WCET
(10) and timer unit (1) and `maxPeriodUs = 2 ^ 61` meets every axiom (`getCurrentTime_buffer_bound` gives only
`maxPeriodUs < 2 ^ 64 / 5`), while `TimeAgree.maxPeriod` (FL4's `max_period_us = max_us / 8`, a `u64`) needs
`MAX_PERIOD_US < 2 ^ 61`. So `per` is a genuine fact about the opaque `timeConsts`. -/
theorem per_not_of_timeConsts : ∃ tc : Fl4Spec.TimeConsts, tc.kernelWCETUs = 10 ∧ tc.timerUnit = 1 ∧
    2305843009213693952 ≤ tc.maxPeriodUs.toNat :=
  ⟨wTCbig, rfl, rfl, by decide⟩

end
end Fl4Proofs.P2.Wit
