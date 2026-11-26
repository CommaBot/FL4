/-
P3 (p3J gen 19): **stage K for P3JStEv** (as P3JStIrqK): the Q copies transported by P3JStIrqK's `specKSt` into
`Fl4ProofsKQ…`. Kernel-checked copies; no premise added; no sorry. New module.
-/
import Fl4Proofs.P3.P3JStEvQ
import Fl4Proofs.P3.P3JStIrqK
open Lean Meta Elab Command

set_option maxRecDepth 200000 in
open Fl4Proofs.P3.P3KX in
run_cmd liftCoreM do
  let (n, r) ← transport specKSt [`Fl4ProofsQ.P3.SInvR.G5.user_entryStU41, `Fl4ProofsQ.P3.SInvR.G5.vmf_entryStU41,
    `Fl4ProofsQ.P3.SInvR.G5.sysU_entryStU41]
  logInfo m!"p3J g19 ev K transport: {n} copied, {r} reused"

#check @Fl4ProofsKQ.P3.SInvR.G5.user_entryStU41
#check @Fl4ProofsKQ.P3.SInvR.G5.vmf_entryStU41
#check @Fl4ProofsKQ.P3.SInvR.G5.sysU_entryStU41
