/-
P3 (line irqfix, part C): **the direct users of `IrqPlatA.noIpi` and of the IRQ ack's unmask,
re-proved on `MachPlatT` / `IrqPlatK`**, and the IRQ ack's per-entry fact.

* `afterInv_of_mcsIMNQ`, `afterInv_of_mcsIMNMQ` (MRPath / KEntry38, verbatim copies): the preemption
  path's IRQ take, `noIpi` now `MachPlatT.noIpi` (JBootIpi's `IpiF`) at the `MR`-related state `hR1`
  the copies already hold.
* **The IRQ ack's unmask** (`jDecMRL_of`, the IRQ handler cap at `IRQAckIRQ`: FL4's
  `decode_irq_handler` does `mask_irq irq false`). FL4's cap only bounds `irq < 128` (`CapWf`), and
  no invariant carried by U32 bounds a handler cap's line by `maxIRQ`: l4v's `valid_cap` bound is
  SpecInvG5's `SpecIrqH`, whose preservation was never proved (XTopJointKEntry36E dropped it for
  `ValidIrqHandlers`, which has no bound). So the unmask is asked per entry:
  **`IrqAckU`** [J]: at the dispatch state, unmasking the line of a handler cap in a CNode slot keeps
  `MR`. It holds under U32's `MachPlat` (`IrqAckU.of_machPlat`) and, under `MachPlatF`, from l4v's
  `valid_cap` bound `irq ≤ maxIRQ` (`IrqAckU.of_bound`). It travels with the decode premise:
  `JDecMRLKQ` / `JDecMRL2Q` = `JDecMRLK` / `JDecMRL2` `∧ IrqAckU`.
* `jDecMRL_ofQ` (KEntry39 verbatim, on IrqFixGenB's copies), the ack by `IrqAckU`;
  `jDecMRL2_ofTQ`, `jDecMRLK_ofUQ`, `jVtxHypMU_ofQ`: the decode lemmas carrying `IrqAckU` along.
No sorry.
-/
import Fl4Proofs.P3.IrqFixGenB
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
open Fl4Proofs.P1
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}
