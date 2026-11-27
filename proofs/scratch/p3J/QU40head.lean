/-
P3 (line p3J, gen 7): **a U40 start with FL4's real boot IRQ layout, with no assumption** (namespace `JBootQ`).

* The witness `JBootQ.w0` (= `w0'`): jboot's `w0` except the IRQ-state words, line 125 `IRQ_TIMER` (2) and
  lines 126 / 127 `IRQ_IPI` (3), as FL4's `boot::init_irq_states` writes them (`w0_irqWords`), paired with
  `JBootQ.fInitASt` = irqfix3's `SInvIB.fInitIpiASt` (`fInitASt_eq_ipi`: 125 `irqTimer`, 126 / 127
  `irqReserved`). The jboot proofs (JBootQChar … JBootQJAt, verbatim copies) re-check there; only `IrqRel`
  (`w0_irqRel`) and the image's zero-word lemma (`img_zero`) were re-proved.
* `jAtZ_w0I1`, `jReachU3_w0I1`, **`jReachU17_w0I1`** at arch `warI1` / `ipiMR`; **`jReachU36I_w0I1`**
  (`fInitIpi_irqCarry`); **`jReachU40_w0I1`** (`IoaRel warI1` framed from gen 5's `warI1_ioaRel`);
  **`u40_w0I1 (O : OpaqueWK)`**: every premise of `kernel_entry_reachU40` at `wst` / `warI1` / `wAR` / `ipiMR`
  with this start; `jReachU40_ipi`: the same start stated at `SInvIB.fInitIpiASt`.
* **`not_jReachU34_w0`**: U34 / U38's start fails here (`irqStB_false_of_ipiWord`), so U40's start fix is
  what makes the top apply to FL4's boot IRQ layout.

Named premises: `OpaqueWK` [P] (JBootU34) only. Caveats (jboot's): idle-only boot, one core.
No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBootQJAt
import Fl4Proofs.P3.JBootU40
import Fl4Proofs.P3.JBoot6Find
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBootQ
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs

noncomputable section

/-- **The spec state is irqfix3's `fInitIpiASt`.** -/
theorem fInitASt_eq_ipi : fInitASt = SInvIB.fInitIpiASt := rfl

