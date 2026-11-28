/-
P2 (line jboot, gen 5): **wit's generic U2 theorems transported onto irqfix's 126 / 127 fix** (IrqFixXport's
kernel-checked copy, main run; JBoot5GenB's and irqfix's copies reused, each type re-checked).

Root: `Fl4Proofs.P2.Wit.wit_U2_io` (WitExec: from a P3 exit with a non-idle current thread, an execution meeting
every hypothesis of `serializable_fl4_localU2`, and U2's conclusion about it), hence its whole cone, U2 and the
P3 tops of `kernel_entry_reachU17V`'s lineage included (cone ≈ 98k constants, 236 mention the replaced records,
137 copied here, 88 reused from irqfix / JBoot5GenB).
Maps: irqfix's `specD` (records `MachPlat` ↦ `MachPlatT`, `IrqPlatA` ↦ `IrqPlatK`; definitions `MaskMR` ↦
`MaskMRF`, `JDecMRLK` ↦ `JDecMRLKQ`, `JDecMRL2` ↦ `JDecMRL2Q`; irqfix's hand re-proofs, the two IOAPIC decodes
included since collapse A, I), plus JBoot5C's `jDecMRL_ofQ0`, `jDecMRL2_ofTQ0`, `jDecMRLK_ofUQ0` in place of the un-narrowed
originals this cone uses. Every other constant of the cone mentioning these ↦ its `Fl4ProofsQ` copy, e.g.
`Fl4ProofsQ.P2.PathObl.LocPlat` (= `LocPlat` with `mach : MachPlatT`, `ia : IrqPlatK`),
`Fl4ProofsQ.P2.Wit.wit_U2_io`, `Fl4ProofsQ.P2.Wit.wit_exec_io`.
No premise added (the copies' statements are the originals' with the renamings); no sorry.
-/
import Fl4Proofs.P3.JBoot5C
import Fl4Proofs.P2.WitExec
open Lean Meta Elab Command

namespace Fl4Proofs.P3.JBoot5
open Fl4Proofs.P3.IrqFix

/-- The un-narrowed decode lemmas of U2's cone ↦ JBoot5C's re-proofs. -/
def decQ0 : List (Name × Name) :=
  [(``Fl4Proofs.P3.jDecMRL_of, ``Fl4Proofs.P3.jDecMRL_ofQ0),
   (``Fl4Proofs.P3.jDecMRL2_ofT, ``Fl4Proofs.P3.jDecMRL2_ofTQ0),
   (``Fl4Proofs.P3.jDecMRLK_ofU, ``Fl4Proofs.P3.jDecMRLK_ofUQ0)]

/-- irqfix's run-D maps with `decQ0`. -/
def specM : Spec where
  recMap := specD.recMap
  defMap := specD.defMap
  constMap := specD.constMap ++ decQ0

end Fl4Proofs.P3.JBoot5

set_option maxRecDepth 200000 in
open Fl4Proofs.P3.IrqFix in
run_cmd liftCoreM do
  let (n, r) ← transport Fl4Proofs.P3.JBoot5.specM [``Fl4Proofs.P2.Wit.wit_U2_io]
  logInfo m!"jboot5 transport M: {n} copied, {r} reused"

#check @Fl4ProofsQ.P2.PathObl.LocPlat
#check @Fl4ProofsQ.P2.Wit.wit_exec_io
#check @Fl4ProofsQ.P2.Wit.wit_U2_io
