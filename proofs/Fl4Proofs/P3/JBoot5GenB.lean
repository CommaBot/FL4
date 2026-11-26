/-
P3 (line jboot, gen 5): **the helpers of JBoot5C's re-proofs, transported onto irqfix's fix** (IrqFixXport's
kernel-checked copy; pre-run of P2/WitU34Gen, as irqfix's IrqFixGenB was for IrqFixGen).

Maps: irqfix's run-B maps (records `MachPlat` ↦ `MachPlatT`, `IrqPlatA` ↦ `IrqPlatK`; definition `MaskMR` ↦
`MaskMRF`; IrqFixA's IRQ control re-proofs) plus JBoot5CtlQ's `irq_ioapic_refinesM` ↦ `…MQ0`,
`irq_remap_refinesM` ↦ `…MQ0`. Roots: the un-narrowed `decode_invocation_irq_controlXSM` (used by
`jDecMRL_ofQ0`) and `jDecMRL2_ofT`, `jDecMRLK_ofU` (wrapped by `jDecMRL2_ofTQ0`, `jDecMRLK_ofUQ0`).
irqfix's earlier copies are reused, each type re-checked. No premise added; no sorry.
-/
import Fl4Proofs.P3.IrqFixGen
import Fl4Proofs.P3.JBoot5CtlQ
open Lean Meta Elab Command

namespace Fl4Proofs.P3.JBoot5
open Fl4Proofs.P3.IrqFix

/-- JBoot5CtlQ's re-proofs of the un-narrowed IOAPIC / remapped IRQ control decodes. -/
def ctlQ0 : List (Name × Name) :=
  [(``Fl4Proofs.P3.irq_ioapic_refinesM, ``Fl4Proofs.P3.irq_ioapic_refinesMQ0),
   (``Fl4Proofs.P3.irq_remap_refinesM, ``Fl4Proofs.P3.irq_remap_refinesMQ0)]

/-- irqfix's run-B maps with `ctlQ0`. -/
def specBW : Spec where
  recMap := specB.recMap
  defMap := specB.defMap
  constMap := specB.constMap ++ ctlQ0

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
