import Fl4Proofs.P3.XTopJointKEntryU42
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU42
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU41_of42
#print axioms Fl4ProofsK.P3.SInvR.G5.kernel_entry_reachU41
#print axioms Fl4Proofs.P3.jat_scheduleWP0FZRI
#print axioms Fl4Proofs.P3.jat_finishJRNMQI
#print axioms Fl4Proofs.P3.SInvR.G5.KFinAtR8.to5I
#print axioms Fl4Proofs.P3.SInvR.G5.KFinAtR42.toK
#print axioms Fl4Proofs.P3.Sched.archSwFI_of
-- the non-g7e scheduler chain is out of U42's cone
open Lean in
run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut wl : List Name := [``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU42]
  let mut hit : Array Name := #[]
  let bad := [``Fl4Proofs.P3.Sched.schedule_refinesWP0FR, ``Fl4Proofs.P3.scnt_refines0F,
    ``Fl4Proofs.P3.Sched.ArchSwF, ``Fl4Proofs.P3.jat_scheduleWP0FZR]
  repeat
    match wl with
    | [] => break
    | n :: rest =>
      wl := rest
      if seen.contains n then continue
      seen := seen.insert n
      if bad.contains n then hit := hit.push n
      if let some ci := env.find? n then
        let ds := ci.type.getUsedConstants ++ (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[])
        for d in ds do
          if !seen.contains d then wl := d :: wl
  logInfo m!"U42 cone {seen.size} constants; old-chain/ArchSwF hits: {hit}"
