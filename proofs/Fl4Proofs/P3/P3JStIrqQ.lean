/-
P3 (p3J gen 19): **stage Q of the stable-ghost interrupt chain**: P3JStIrq's `irq_entryStU41` transported onto
the 126 / 127 fix by IrqFixGen's `specD` (records `MachPlat` ↦ `MachPlatT`, `IrqPlatA` ↦ `IrqPlatK`, `MaskMR` ↦
`MaskMRF`, …), exactly as IrqFixGen transports `kernel_entry_reachU32`; copies of earlier runs are reused (their
types re-checked). The copy `Fl4ProofsQ.P3.SInvR.G5.irq_entryStU41` is `irq_entryStU41` with those renamings in its
statement. Every copy goes through `addDecl` (kernel-checked). No premise added; no sorry. New module.
-/
import Fl4Proofs.P3.P3JStIrq
import Fl4Proofs.P3.IrqFixGen
open Lean Meta Elab Command

set_option maxRecDepth 200000 in
open Fl4Proofs.P3.IrqFix in
run_cmd liftCoreM do
  let (n, r) ← transport specD [``Fl4Proofs.P3.SInvR.G5.irq_entryStU41]
  logInfo m!"p3J g19 irq Q transport: {n} copied, {r} reused"

#check @Fl4ProofsQ.P3.SInvR.G5.irq_entryStU41
