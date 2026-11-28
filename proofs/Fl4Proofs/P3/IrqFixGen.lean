/-
P3 (line irqfix, part D): **`kernel_entry_reachU32`'s proof transported onto the 126 / 127 fix**
(IrqFixXport's kernel-checked copy, second run; IrqFixGenB's copies reused, each type re-checked).

Records `MachPlat` ↦ `MachPlatT`, `IrqPlatA` ↦ `IrqPlatK`; definitions `MaskMR` ↦ `MaskMRF`, `JDecMRLK` ↦
`JDecMRLKQ`, `JDecMRL2` ↦ `JDecMRL2Q` (IrqFixA / IrqFixC); the direct users re-proved by hand (IrqFixA:
the IRQ control issues; IrqFixC: the two `noIpi` sites, the IRQ ack, the decode lemmas carrying
`IrqAckU`) in place of their originals; every other constant of U32's cone mentioning these ↦ its copy.
The copy `Fl4ProofsQ.P3.SInvR.G5.kernel_entry_reachU32` is U32 with those renamings in its statement;
XTopJointKEntryU33 states it. No premise added here; no sorry.
-/
import Fl4Proofs.P3.IrqFixC
open Lean Meta Elab Command

namespace Fl4Proofs.P3.IrqFix

/-- IrqFixGenB's maps, with the decode premises carrying `IrqAckU` and IrqFixC's re-proofs. -/
def specD : Spec where
  recMap := specB.recMap
  defMap := specB.defMap ++
    [(``Fl4Proofs.P3.JDecMRLK, ``Fl4Proofs.P3.JDecMRLKQ), (``Fl4Proofs.P3.JDecMRL2, ``Fl4Proofs.P3.JDecMRL2Q)]
  constMap := specB.constMap ++
    [(``Fl4Proofs.P3.afterInv_of_mcsIMN, ``Fl4Proofs.P3.afterInv_of_mcsIMNQ),
     (``Fl4Proofs.P3.afterInv_of_mcsIMNM, ``Fl4Proofs.P3.afterInv_of_mcsIMNMQ),
     (``Fl4Proofs.P3.jDecMRL_of, ``Fl4Proofs.P3.jDecMRL_ofQ),
     (``Fl4Proofs.P3.jDecMRL2_ofT, ``Fl4Proofs.P3.jDecMRL2_ofTQ),
     (``Fl4Proofs.P3.jDecMRLK_ofU, ``Fl4Proofs.P3.jDecMRLK_ofUQ),
     (``Fl4Proofs.P3.jVtxHypMU_of, ``Fl4Proofs.P3.jVtxHypMU_ofQ)]

end Fl4Proofs.P3.IrqFix

set_option maxRecDepth 200000 in
open Fl4Proofs.P3.IrqFix in
run_cmd liftCoreM do
  let (n, r) ← transport specD [``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU32]
  logInfo m!"irqfix transport D: {n} copied, {r} reused"

#check @Fl4ProofsQ.P3.SInvR.G5.kernel_entry_reachU32
