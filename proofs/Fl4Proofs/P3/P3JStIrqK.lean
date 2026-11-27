/-
P3 (p3J gen 19): **stage K of the stable-ghost interrupt chain**: P3JStIrqQ's `Fl4ProofsQ.P3.SInvR.G5.irq_entryStU41`
transported onto `ArchSwF'` by P3KGen's `specK` (records `KFinAtR5` / `KFinAtR31` / `KFinAtR27` / `KFinAtR` ↦
P3KFin's `…I`, `ArchSwF` ↦ `ArchSwF'`, the old finish path ↦ P3KFin's hand copies; `specKSt` adds `Fl4ProofsQ.P3.jat_finishJRNMSt` ↦ P3JStIrqKFin's
`jat_finishJRNMStQI`), exactly as P3KGen transports
`kernel_entry_reachU41`; copies of earlier runs are reused (types re-checked). The copy
`Fl4ProofsKQ.P3.SInvR.G5.irq_entryStU41` takes the K copy of `KFinEv41` that U42's `KFinEv42.toK` produces. Every
copy goes through `addDecl` (kernel-checked). No premise added; no sorry. New module.
-/
import Fl4Proofs.P3.P3JStIrqQ
import Fl4Proofs.P3.P3KGen
import Fl4Proofs.P3.P3JStIrqKFin
open Lean Meta Elab Command

namespace Fl4Proofs.P3.P3KX

/-- `specK` with the stable-ghost finish replaced by P3JStIrqKFin's hand copy. -/
def specKSt : Spec := { specK with
  constMap := specK.constMap ++ [(`Fl4ProofsQ.P3.jat_finishJRNMSt, `Fl4Proofs.P3.jat_finishJRNMStQI)] }

end Fl4Proofs.P3.P3KX

set_option maxRecDepth 200000 in
open Fl4Proofs.P3.P3KX in
run_cmd liftCoreM do
  let (n, r) ← transport specKSt [`Fl4ProofsQ.P3.SInvR.G5.irq_entryStU41]
  logInfo m!"p3J g19 irq K transport: {n} copied, {r} reused"

#check @Fl4ProofsKQ.P3.SInvR.G5.irq_entryStU41
