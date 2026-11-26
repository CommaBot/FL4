/-
P3 (p3J gen 29): **stage Q for P3JSysSt** (as P3JStTrapQ): `sys_entryStFU41` transported by IrqFixGen's `specD`
into `Fl4ProofsQ…`. Kernel-checked copies; no premise added; no sorry. New module.
-/
import Fl4Proofs.P3.P3JSysSt
import Fl4Proofs.P3.P3JStTrapQ
open Lean Meta Elab Command

set_option maxRecDepth 200000 in
open Fl4Proofs.P3.IrqFix in
run_cmd liftCoreM do
  let (n, r) ← transport specD [``Fl4Proofs.P3.SInvR.G5.sys_entryStFU41]
  logInfo m!"p3J g29 sys Q transport: {n} copied, {r} reused"

#check @Fl4ProofsQ.P3.SInvR.G5.sys_entryStFU41
