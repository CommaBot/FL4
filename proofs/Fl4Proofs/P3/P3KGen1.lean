/-
P3 (line p3J, gen 10): **stage 1 of the U41 → U42 transport** (P3KXport): the g7e scheduler chain and
`KFinAtR8` on `ArchSwF'`, so that P3KFin's hand lemmas can name their copies.

Maps (`specK1`, a sub-map of P3KGen's `specK`): `ArchSwF` ↦ `ArchSwF'` (ArchSwIdle); `scnt_refines0FA` ↦
`scnt_refines0FAI`, `sw_refinesFA` ↦ `sw_refinesFAI`. Roots: G7eTail's `kfin_tail_of`, `KFinAtR8` and its
projections, G7eChain's `schedule_refinesWP0FRA`. Every copy is kernel-checked (`addDecl`). No premise
added; no sorry.
-/
import Fl4Proofs.P3.P3KXport
import Fl4Proofs.P3.ArchSwIdle
import Fl4Proofs.P3.XTopJointKEntryU41
open Lean Meta Elab Command

namespace Fl4Proofs.P3.P3KX

/-- Stage 1's maps (module docstring). -/
def specK1 : Spec where
  recMap := []
  defMap := [(`Fl4Proofs.P3.Sched.ArchSwF, `Fl4Proofs.P3.Sched.ArchSwF')]
  constMap :=
    [(`Fl4Proofs.P3.Sched.scnt_refines0FA, `Fl4Proofs.P3.Sched.scnt_refines0FAI),
     (`Fl4Proofs.P3.Sched.sw_refinesFA, `Fl4Proofs.P3.Sched.sw_refinesFAI)]

end Fl4Proofs.P3.P3KX

set_option maxRecDepth 200000 in
open Fl4Proofs.P3.P3KX in
run_cmd liftCoreM do
  let (n, r) ← transport specK1
    [``Fl4Proofs.P3.SInvR.G5.kfin_tail_of, ``Fl4Proofs.P3.SInvR.G5.KFinAtR8,
     ``Fl4Proofs.P3.SInvR.G5.KFinAtR8.hd, ``Fl4Proofs.P3.SInvR.G5.KFinAtR8.arch,
     ``Fl4Proofs.P3.SInvR.G5.KFinAtR8.archNd, ``Fl4Proofs.P3.SInvR.G5.KFinAtR8.idle,
     ``Fl4Proofs.P3.Sched.schedule_refinesWP0FRA]
  logInfo m!"p3K stage 1: {n} copied, {r} reused"

#check @Fl4ProofsK.P3.SInvR.G5.kfin_tail_of
#check @Fl4ProofsK.P3.Sched.schedule_refinesWP0FRA
