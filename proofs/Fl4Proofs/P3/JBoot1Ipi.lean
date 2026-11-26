/-
P3 (line jboot, gen 4): **the boot witnesses at the fixed machine relation `ipiMR`** (JBootIpi, gen 1: `modelMR`
with the IPI lines 126 / 127 masked), so the reachable-state witnesses need no assumption on the opaque
`irqOracle`.

* **`warI_machPlatF`**, **`warI_ipiF`**: wit's concrete arch `warI` meets the fixed platform premises
  (`MachPlatF`, `IpiF`) at `ipiMR`, as `modelArch` does (`modelArch_machPlatF`, `modelArch_ipiF`): no
  `OpaqueW.ipi`.
* **`ipiMR_init`**: the boot machine state is `ipiMR`-related to itself (every line inactive, hence masked:
  `ValidIrqMasks`).
* **`jReachU17_w0_ipi`**, **`jReachU17_w1_ipi`**: `JReachU17` at `ipiMR` for the gen-3 witness `w0` / `fInitASt`
  and the gen-4 witness `w1` / `σ1` (non-idle current thread).

These are the start states for P3's tops once their statements take `MachPlatF` / `IpiF` (statement changes,
not made on this line). No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBoot1JAt
import Fl4Proofs.P3.JBootIpi
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P2.Wit

noncomputable section

/-- **`warI` meets the fixed `MachPlatF` at `ipiMR`** (its clock and interrupt operations are `modelArch`'s). -/
theorem warI_machPlatF : MachPlatF warI ipiMR :=
  ⟨modelArch_machPlatF.now, modelArch_machPlatF.irqPending, modelArch_machPlatF.take, modelArch_machPlatF.mask1,
    modelArch_machPlatF.mask0, modelArch_machPlatF.ack, modelArch_machPlatF.frame⟩

/-- **`warI` meets `IpiF` at `ipiMR`**, with no assumption on `irqOracle`. -/
theorem warI_ipiF : IpiF warI ipiMR := modelArch_ipiF

/-- **The boot machine state is `ipiMR`-related to itself.** -/
theorem ipiMR_init : ipiMR fInitASt.machineState fInitASt.machineState :=
  ⟨fInit_mr, (BootHeap.vim (N := fIrqNode) bootHeap_fInit) 126 rfl,
    (BootHeap.vim (N := fIrqNode) bootHeap_fInit) 127 rfl⟩

theorem ipiMR_σ1 : ipiMR σ1.machineState σ1.machineState := ipiMR_init

/-- **`JReachU17` at `ipiMR` for the gen-3 witness.** -/
theorem jReachU17_w0_ipi : SInvR.G5.JReachU17 (L := wL) warI wAR ipiMR w0 fInitASt.machineState fInitASt :=
  ⟨.start (jAtZ_w0 _) Zw_vx fInit_sinvX fInit_sinvIP ipiMR_init fInit_utPgR, fInit_gpmOut, fInit_idleVtS,
    fInit_devRangeS⟩

/-- **`JReachU17` at `ipiMR` for the gen-4 witness** (non-idle current thread). -/
theorem jReachU17_w1_ipi : SInvR.G5.JReachU17 (L := wL) warI wAR ipiMR w1 σ1.machineState σ1 :=
  ⟨.start (jAtZ_w1 _) Zw1_vx σ1_sinvX σ1_sinvIP ipiMR_σ1 σ1_utPgR, σ1_gpmOut, σ1_idleVtS, σ1_devRangeS⟩

end

end Fl4Proofs.P3.JBoot
