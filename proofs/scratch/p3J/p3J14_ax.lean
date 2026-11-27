import Fl4Proofs.P3.XTopJointKEntryU46
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU46
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU45_of46
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU45nv
#print axioms Fl4Proofs.P3.jDecMRLK_ofVtxR
#print axioms Fl4Proofs.P3.jDecMRLK_vtxU_nv
#print axioms Fl4Proofs.P3.jDecMRLK_vtxUE
#print axioms Fl4Proofs.P3.vtxR_vtxU
#print axioms Fl4Proofs.P3.XCapP.mrE
#print axioms Fl4Proofs.P3.MKE.decode_untyped_vtx_err
#print axioms Fl4Proofs.P3.MKE.untyped_vtx_err
#print axioms Fl4Proofs.P3.MKE.retype_shared_vtx
#print axioms Fl4Proofs.P3.shared_frame_spec_vtx
#print axioms Fl4Proofs.P3.noVirt_warI1
#print axioms Fl4Proofs.P3.errKeepA_err
-- cone walk (allowOpaque := true): U46 / U45nv cones contain U45; U46's type mentions VtxR not VtxU; U45nv's mentions no JDecMRLK
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
  let c45 := closure [``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU45]
  let c46 := closure [``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU46]
  let cnv := closure [``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU45nv]
  let t46 := (env.find? ``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU46).get!.type.getUsedConstants
  let tnv := (env.find? ``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU45nv).get!.type.getUsedConstants
  logInfo m!"U45 cone {c45.size}; U46 cone {c46.size} (U45: {c46.contains ``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU45}, ofVtxR: {c46.contains ``Fl4Proofs.P3.jDecMRLK_ofVtxR}); U45nv cone {cnv.size} (U45: {cnv.contains ``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU45}, nv: {cnv.contains ``Fl4Proofs.P3.jDecMRLK_vtxU_nv})"
  logInfo m!"U46 type: VtxR {t46.contains ``Fl4Proofs.P3.VtxR}, VtxU {t46.contains ``Fl4Proofs.P3.VtxU}; U45nv type: JDecMRLK {tnv.contains ``Fl4Proofs.P3.JDecMRLK}, NoVirt {tnv.contains ``Fl4Proofs.P3.NoVirt}"
