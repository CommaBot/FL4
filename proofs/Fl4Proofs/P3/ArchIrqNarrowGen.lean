/-
P3 (p3P gen 2, item 3): **`kernel_entry_reachU31`'s proof transported onto `ArchIrqRelN`**
(ArchIrqNarrow: `map` / `mapr` only at the arguments FL4's IOAPIC decode passes), by
StallNarrowGen's kernel-checked renaming (`Fl4Proofs.X` / `Fl4ProofsN.X` ↦ `Fl4ProofsI.X`):
`ArchIrqRel` (and its generated constants) ↦ `ArchIrqRelN`, the four routing consumers ↦ their
`…N` copies, every constant of the cone mentioning these ↦ its copy. No premise added.
-/
import Fl4Proofs.P3.XTopJointKEntryU31
import Fl4Proofs.P3.ArchIrqNarrow
import Fl4Proofs.P3.StallNarrowGen
open Lean Meta Elab Command

open Fl4Proofs.P3.StallNarrow in
run_cmd liftCoreM do
  let n ← transport ⟨[(``Fl4Proofs.P3.ArchIrqRel, ``Fl4Proofs.P3.ArchIrqRelN)],
    [(``Fl4Proofs.P3.irq_ioapic_refines, ``Fl4Proofs.P3.irq_ioapic_refinesN),
     (``Fl4Proofs.P3.irq_remap_refines, ``Fl4Proofs.P3.irq_remap_refinesN),
     (``Fl4Proofs.P3.irq_ioapic_refinesM, ``Fl4Proofs.P3.irq_ioapic_refinesMN),
     (``Fl4Proofs.P3.irq_remap_refinesM, ``Fl4Proofs.P3.irq_remap_refinesMN)], `Fl4ProofsI⟩
    ``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU31
  logInfo m!"archirq_transport: {n} constants copied"
