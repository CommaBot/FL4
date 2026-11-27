/-
P3 (p3J gen 22): **stage Q for P3JStTrap** (as P3JStEvQ): `trap_entryStU41` transported by IrqFixGen's `specD` into
`Fl4ProofsQ…`. Kernel-checked copies; no premise added; no sorry. New module.
-/
import Fl4Proofs.P3.P3JStTrap
import Fl4Proofs.P3.P3JStEvQ
open Lean Meta Elab Command

set_option maxRecDepth 200000 in
open Fl4Proofs.P3.IrqFix in
run_cmd liftCoreM do
  let (n, r) ← transport specD [``Fl4Proofs.P3.SInvR.G5.trap_entryStU41]
  logInfo m!"p3J g22 trap Q transport: {n} copied, {r} reused"

#check @Fl4ProofsQ.P3.SInvR.G5.trap_entryStU41
