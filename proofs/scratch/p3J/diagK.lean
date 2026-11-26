import Fl4Proofs.P3.P3KXport
import Fl4Proofs.P3.ArchSwIdle
import Fl4Proofs.P3.XTopJointKEntryU41
open Lean Meta Elab Command

open Fl4Proofs.P3.P3KX in
def specD : Spec where
  recMap := []
  defMap := [(`Fl4Proofs.P3.Sched.ArchSwF, `Fl4Proofs.P3.Sched.ArchSwF')]
  constMap := [(`Fl4Proofs.P3.Sched.scnt_refines0FA, `Fl4Proofs.P3.Sched.scnt_refines0FAI)]

set_option maxRecDepth 200000 in
open Fl4Proofs.P3.P3KX in
run_cmd liftCoreM do
  let (n, r, bad) ← transportD specD [``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU41]
  IO.println s!"DIAG copied {n} reused {r} bad {bad.size}"
  for (b, m) in bad do
    if !((m.splitOn "unknown constant").length > 1) then
      IO.println s!"BAD {b} :: {m.replace "\n" " "}"
  let unk := bad.filter (fun (_, m) => (m.splitOn "unknown constant").length > 1)
  IO.println s!"DIAG unknown-dep failures {unk.size}"
