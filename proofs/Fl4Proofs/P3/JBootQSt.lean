/-
P3 (line p3J, gen 7): **jboot's spec boot state with FL4's boot IRQ states** (namespace `JBootQ`).

* `ipiIS`: `initASt`'s interrupt states with line 125 `irqTimer` and lines 126 / 127 `irqReserved` (FL4's
  `boot::init_irq_states`: `irq::TIMER` ↦ `IRQ_TIMER`, `REMOTE_CALL_IPI` / `RESCHEDULE_IPI` ↦ `IRQ_IPI`, which
  IntRel's `irqSt` reads as `irqReserved`).
* **`JBootQ.fInitASt`**: jboot's `fInitASt` (heap `fInitKheap`, IRQ node `fIrqNode`) with `ipiIS`; it is
  irqfix3's `SInvIB.fInitIpiASt` (JBootQU40 `fInitASt_eq_ipi`).
No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBootSt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBootQ
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.JBoot

noncomputable section

/-- `initASt`'s interrupt states with FL4's boot layout (module docstring). -/
def ipiIS : Irq → IrqState :=
  Function.update (Function.update (Function.update (initASt (Z := Unit)).interruptStates
    125 .irqTimer) 126 .irqReserved) 127 .irqReserved

/-- **The spec boot state with FL4's boot IRQ states** (module docstring). -/
def fInitASt : State Unit :=
  { (initASt (Z := Unit)) with kheap := fInitKheap, interruptIrqNode := fIrqNode, interruptStates := ipiIS }

/-- **`IrqRel.node` at `fInitASt`, base `fkb`.** -/
theorem fInitASt_irqNode (i : U64) (hi : i.val < 128) :
    fInitASt.interruptIrqNode (BitVec.ofNat 8 i.val) = (nodeA fkb i).bv :=
  fIrqNode_node i hi

end

end Fl4Proofs.P3.JBootQ
