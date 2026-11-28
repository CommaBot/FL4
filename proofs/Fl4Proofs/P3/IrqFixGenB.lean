/-
P3 (line irqfix, part B): **the helpers of the hand-written re-proofs, transported** (IrqFixXport's
kernel-checked copy, first run).

Records `MachPlat` ↦ `MachPlatT`, `IrqPlatA` ↦ `IrqPlatK` (IrqFixA), definition `MaskMR` ↦ `MaskMRF`, and
IrqFixA's six IRQ control re-proofs in place of their originals. Roots: what IrqFixC's re-proofs of the
two `noIpi` sites (`afterInv_of_mcsIMN`, `…IMNM`) and of the IRQ-ack site (`jDecMRL_of`) call
(`MachPlat.takeAt`, `JAtZ.handleIrqJIAN(M)`, `XCapP.mr(G)`, `mF_mr`, the IRQ control decode), and the two
decode lemmas IrqFixC wraps (`jDecMRL2_ofT`, `jDecMRLK_ofU`). No premise added; no sorry.
-/
import Fl4Proofs.P3.IrqFixA
import Fl4Proofs.P3.IrqFixXport
import Fl4Proofs.P3.XTopJointKEntryU32
open Lean Meta Elab Command

namespace Fl4Proofs.P3.IrqFix

/-- The records, definitions and IRQ control re-proofs of the 126 / 127 fix (IrqFixA). -/
def specB : Spec where
  recMap := [(``Fl4Proofs.P3.MachPlat, ``Fl4Proofs.P3.MachPlatT), (``Fl4Proofs.P3.IrqPlatA, ``Fl4Proofs.P3.IrqPlatK)]
  defMap := [(``Fl4Proofs.P3.MaskMR, ``Fl4Proofs.P3.MaskMRF)]
  constMap :=
    [(``Fl4Proofs.P3.invoke_mrM, ``Fl4Proofs.P3.invoke_mrMQ),
     (``Fl4Proofs.P3.issue_tailM, ``Fl4Proofs.P3.issue_tailMQ),
     (``Fl4Proofs.P3.irq_issue_refinesM, ``Fl4Proofs.P3.irq_issue_refinesMQ),
     (``Fl4Proofs.P3.irq_msi_refinesM, ``Fl4Proofs.P3.irq_msi_refinesMQ),
     (``Fl4Proofs.P3.irq_ioapic_refinesM, ``Fl4Proofs.P3.irq_ioapic_refinesMNQ),
     (``Fl4Proofs.P3.irq_remap_refinesM, ``Fl4Proofs.P3.irq_remap_refinesMNQ)]

end Fl4Proofs.P3.IrqFix

set_option maxRecDepth 200000 in
open Fl4Proofs.P3.IrqFix in
run_cmd liftCoreM do
  let (n, r) ← transport specB
    [``Fl4Proofs.P3.MachPlat.takeAt, ``Fl4Proofs.P3.JAtZ.handleIrqJIAN, ``Fl4Proofs.P3.JAtZ.handleIrqJIANM,
     ``Fl4Proofs.P3.decode_invocation_irq_controlXSM, ``Fl4Proofs.P3.XCapP.mrG, ``Fl4Proofs.P3.XCapP.mr,
     ``Fl4Proofs.P3.mF_mr, ``Fl4Proofs.P3.jDecMRL2_ofT, ``Fl4Proofs.P3.jDecMRLK_ofU]
  logInfo m!"irqfix transport B: {n} copied, {r} reused"

#check @Fl4Proofs.P3.MachPlatT.takeAt
#check @Fl4ProofsQ.P3.JAtZ.handleIrqJIAN
#check @Fl4ProofsQ.P3.JAtZ.handleIrqJIANM
#check @Fl4ProofsQ.P3.decode_invocation_irq_controlXSM
#check @Fl4ProofsQ.P3.XCapP.mrG
#check @Fl4ProofsQ.P3.XCapP.mr
#check @Fl4ProofsQ.P3.mF_mr
#check @Fl4ProofsQ.P3.jDecMRL2_ofT
#check @Fl4ProofsQ.P3.jDecMRLK_ofU
