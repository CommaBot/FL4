import Fl4Proofs.P3.XTopJointKEntryU45
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU45
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU44_of45
#print axioms Fl4Proofs.P3.jDecMRLK_ofVtxU
#print axioms Fl4Proofs.P3.JDecMRLK.mono
#print axioms Fl4Proofs.P3.vtxU_vtxK
#print axioms Fl4Proofs.P3.XCapP.mrN
#print axioms Fl4Proofs.P3.specDec_ept_noOk
#print axioms Fl4Proofs.P3.MKE.decode_thread_ept
#print axioms Fl4Proofs.P3.MKE.tcb_decode_ept
#print axioms Fl4Proofs.P3.MKE.cdt_delete_exp
#print axioms Fl4Proofs.P3.MKE.fsi_loop
#print axioms Fl4Proofs.P3.MKE.delete_deferred
#print axioms Fl4Proofs.P3.MKE.fsd_loop
#print axioms Fl4Proofs.P3.MKE.preemption_point
-- cone walk (allowOpaque := true): U45's cone contains U44; U45's type mentions VtxU, not VtxK
open Lean in
run_cmd do
  let env ← getEnv
  let closure (roots : List Name) : NameSet := Id.run do
    let mut seen : NameSet := {}
    let mut wl := roots
    repeat
      match wl with
      | [] => break
      | n :: rest =>
        wl := rest
        if seen.contains n then continue
        seen := seen.insert n
        if let some ci := env.find? n then
          let ds := ci.type.getUsedConstants ++ (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[])
          for d in ds do
            if !seen.contains d then wl := d :: wl
    return seen
  let c := closure [``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU45]
  let c44 := closure [``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU44]
  let ty := (env.find? ``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU45).get!.type.getUsedConstants
  logInfo m!"U44 cone {c44.size}; U45 cone {c.size}; contains U44: {c.contains ``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU44}, jDecMRLK_ofVtxU: {c.contains ``Fl4Proofs.P3.jDecMRLK_ofVtxU}"
  logInfo m!"U45 type: VtxU {ty.contains ``Fl4Proofs.P3.VtxU}, VtxK {ty.contains ``Fl4Proofs.P3.VtxK}"
