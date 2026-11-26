/-
P2 (line jboot, gen 4; audit F4): **an end-to-end witness of U2 with no P3 premise.**

wit's `wit_exec_io_conc` / `wit_U2_conc` (WitExec) take a P3 exit `σe` (`JReachU17` on the concrete platform
`wst` / `warI` / `wAR` / `wMR`) and `NonIdle σe` [P] (the io-port entry's fact). jboot gen 4 (P3/JBoot1JAt)
supplies both at the richer witness `w1` (a running root thread with its SC and CSpace root CNode):
* **`w1_nonIdle`**: `NonIdle wst warI wAR wMR w1`, for every arch state and every spec state related to `w1`
  by `JReachU17` (`JReachU3.jAt`, `JAt.curIdle`: the spec's current / idle thread are core 0's `CUR_THREAD` /
  `IDLE_THREAD` words, at `w1` the root TCB and the idle TCB);
* **`wit_exec_uncond`**: `wit_exec_io_conc` at `σe := w1` — `Init s0`, `ArmInv s0`, `SerExitW`, the layout
  facts, `MapsP`, an `ExecWPR` over U2's exact family with `StartV2`, `NoLoc s`, `s.log = [.start q]` with `q`
  the io-port slot's body at `w1` started and run to completion, `s0.mem = wmem w1`;
* **`wit_U2_uncond`**: `wit_U2_conc` at `w1` — `serializable_fl4_localU2` (U2) applied to that execution:
  `RunAll [.start q] s0.mem s.mem`.

**The only remaining premise is `OpaqueW` [P]** (WitPlat: facts about opaque `Fl4Spec` constants and opaque
spec machine operations, which Lean can neither prove nor refute: `numDomains = 1`, `maxTicksToUs`,
`kernelWCETUs`, `timerUnit`, `MAX_PERIOD_US < 2 ^ 61`, the IRQ oracle avoiding 126/127, `setDeadlineImpl`
determinism, port-read values). `NonIdle` and `JReachU17` are discharged.

No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P2.WitExec
import Fl4Proofs.P3.JBoot1JAt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Wit
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV Fl4Proofs.P2.E2EP
open Fl4Proofs.P2.E2E (LocalPath SP SerStep)
open Fl4Proofs.P2.Serial (Cfg Init ArmInv NoLoc RunAll Step PureGlue Phase Prog Gate)
open Fl4Proofs.P3.JBoot

noncomputable section

/-- **`NonIdle` at `w1`** (module docstring): no premise. -/
theorem w1_nonIdle : NonIdle wst warI wAR wMR w1 := by
  intro a τ hJ
  obtain ⟨hc, hi⟩ := Fl4Proofs.P3.JBoot.JAt.curIdle (Fl4Proofs.P3.JBoot.JReachU3.jAt hJ.1)
  rw [hc, hi, cpu_w1, curT_w1, idleT_w1]
  decide

/-- **The io-port execution of U2 from the concrete P3 exit `w1`** (`wit_exec_io_conc` with its P3 premises
discharged; only `OpaqueW` [P] remains). -/
theorem wit_exec_uncond (O : OpaqueW) :
    ∃ (s0 s : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : WSt → Prop) (q : SP),
      Init s0 ∧ ArmInv s0 ∧ SerExitW (wit_locPlat O) K0.toKLayoutV Ch0 ∧
      (K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem) ∧ MapsP K0 s0 ∧
      ExecWPR (LPU2 wst warI warI_total wa0) (StartV2 wst warI warI_total wa0 warI wAR wMR) (wit_locPlat O)
        s0 K0 Ch0 s K0 Ch0 ∧ NoLoc s ∧ s.log = [.start q] ∧ s0.mem = wmem w1 :=
  wit_exec_io_conc O jReachU17_w1 w1_nonIdle

/-- **U2 non-vacuous, unconditionally up to `OpaqueW` [P]**: a concrete execution meeting every hypothesis of
`serializable_fl4_localU2`, with an io-port body started and completed, and U2's conclusion about it. -/
theorem wit_U2_uncond (O : OpaqueW) :
    ∃ (s0 s : Cfg U64 U64 U64 U64) (q : SP), s.log = [.start q] ∧ s0.mem = wmem w1 ∧ NoLoc s ∧
      RunAll s.log s0.mem s.mem :=
  wit_U2_conc O jReachU17_w1 w1_nonIdle

end
end Fl4Proofs.P2.Wit
