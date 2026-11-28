/-
P3 (line jboot, gen 5): **the helpers of JBoot5C's re-proofs, transported onto irqfix's fix** (IrqFixXport's
kernel-checked copy; pre-run of P2/WitU34Gen, as irqfix's IrqFixGenB was for IrqFixGen).

Maps: irqfix's run-B maps (records `MachPlat` ↦ `MachPlatT`, `IrqPlatA` ↦ `IrqPlatK`; definition `MaskMR` ↦
`MaskMRF`; IrqFixA's IRQ control re-proofs, the IOAPIC ones `irq_ioapic_refinesM` ↦ `…MNQ`,
`irq_remap_refinesM` ↦ `…MNQ`: collapse A, I wrote the in-range `ArchIrqRel` back, so JBoot5CtlQ's `…MQ0`
re-proofs of the un-narrowed decodes and their map `ctlQ0` are gone). Roots: the un-narrowed `decode_invocation_irq_controlXSM` (used by
`jDecMRL_ofQ0`) and `jDecMRL2_ofT`, `jDecMRLK_ofU` (wrapped by `jDecMRL2_ofTQ0`, `jDecMRLK_ofUQ0`).
irqfix's earlier copies are reused, each type re-checked. No premise added; no sorry.
-/
import Fl4Proofs.P3.IrqFixGen
open Lean Meta Elab Command

namespace Fl4Proofs.P3.JBoot5
open Fl4Proofs.P3.IrqFix

/-- irqfix's run-B maps. -/
def specBW : Spec where
  recMap := specB.recMap
  defMap := specB.defMap
  constMap := specB.constMap

end Fl4Proofs.P3.JBoot5

set_option maxRecDepth 200000 in
open Fl4Proofs.P3.IrqFix in
run_cmd liftCoreM do
  let (n, r) ← transport Fl4Proofs.P3.JBoot5.specBW [``Fl4Proofs.P3.decode_invocation_irq_controlXSM,
    ``Fl4Proofs.P3.jDecMRL2_ofT, ``Fl4Proofs.P3.jDecMRLK_ofU]
  logInfo m!"jboot5 transport B: {n} copied, {r} reused"

#check @Fl4ProofsQ.P3.decode_invocation_irq_controlXSM
#check @Fl4ProofsQ.P3.jDecMRL2_ofT
#check @Fl4ProofsQ.P3.jDecMRLK_ofU
