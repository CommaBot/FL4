/-
P3 (p3J gen 19): **stage Q for P3JStEv** (as P3JStIrqQ): `user_entryStU41`, `vmf_entryStU41`, `sysU_entryStU41`
transported by IrqFixGen's `specD` into `Fl4ProofsQ…`. Kernel-checked copies; no premise added; no sorry. New module.
-/
import Fl4Proofs.P3.P3JStEv
import Fl4Proofs.P3.P3JStIrqQ
open Lean Meta Elab Command

set_option maxRecDepth 200000 in
open Fl4Proofs.P3.IrqFix in
run_cmd liftCoreM do
  let (n, r) ← transport specD [``Fl4Proofs.P3.SInvR.G5.user_entryStU41, ``Fl4Proofs.P3.SInvR.G5.vmf_entryStU41,
    ``Fl4Proofs.P3.SInvR.G5.sysU_entryStU41]
  logInfo m!"p3J g19 ev Q transport: {n} copied, {r} reused"

#check @Fl4ProofsQ.P3.SInvR.G5.user_entryStU41
#check @Fl4ProofsQ.P3.SInvR.G5.vmf_entryStU41
#check @Fl4ProofsQ.P3.SInvR.G5.sysU_entryStU41
