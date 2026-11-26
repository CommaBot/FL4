import Fl4Proofs.P3.XTopJointKEntryU43
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU43
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU42_of43
#print axioms Fl4Proofs.P3.SInvR.G5.kFinAtR42_of
#print axioms Fl4Proofs.P3.SInvR.G5.kFinEv42_of
#print axioms Fl4Proofs.P3.Sched.archSwFT_of
#print axioms Fl4Proofs.P3.Sched.archSwF'_of
#print axioms Fl4Proofs.P3.Sched.lazy_eq
#print axioms Fl4Proofs.P3.Sched.setVmRoot_one
-- retired names are out of U43's cone; the per-entry records are present only as conclusions of kFin*_of
open Lean in
run_cmd do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut wl : List Name := [``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU43]
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
  logInfo m!"U43 cone {seen.size} constants; old-chain/ArchSwF hits: {hit}"
  -- U43's statement mentions neither ArchSwFT nor the per-entry records
  let ty := (env.find? ``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU43).get!.type.getUsedConstants
  logInfo m!"U43 type mentions ArchSwFT/KFinAtR42/KFinEv42: {ty.filter (fun d => d == ``Fl4Proofs.P3.Sched.ArchSwFT || d == ``Fl4Proofs.P3.SInvR.G5.KFinAtR42 || d == ``Fl4Proofs.P3.SInvR.G5.KFinEv42)}"
