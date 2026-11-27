/-
P3 (p3J gen 22): **stage K for P3JStTrap** (as P3JStEvK): the Q copy transported by P3JStIrqK's `specKSt` into
`Fl4ProofsKQ…`. Kernel-checked copies; no premise added; no sorry. New module.
-/
import Fl4Proofs.P3.P3JStTrapQ
import Fl4Proofs.P3.P3JStEvK
open Lean Meta Elab Command

set_option maxRecDepth 200000 in
open Fl4Proofs.P3.P3KX in
run_cmd liftCoreM do
  let (n, r) ← transport specKSt [`Fl4ProofsQ.P3.SInvR.G5.trap_entryStU41]
  logInfo m!"p3J g22 trap K transport: {n} copied, {r} reused"

#check @Fl4ProofsKQ.P3.SInvR.G5.trap_entryStU41
