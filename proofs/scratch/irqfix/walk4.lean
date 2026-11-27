import Fl4Proofs.P3.XTopJointKEntryU32
import Fl4Proofs.P3.JBootIpi
open Lean Meta Elab Command

def oursQ (n : Name) : Bool :=
  (`Fl4Proofs).isPrefixOf n || (`Fl4ProofsN).isPrefixOf n || (`Fl4ProofsI).isPrefixOf n ||
    (isPrivateName n && (n.toString.startsWith "_private.Fl4Proofs."))

run_cmd liftCoreM do
  let env ← getEnv
  for n in [`Fl4ProofsI.P3.jDecMRL_of, `Fl4Proofs.P3.afterInv_of_mcsIMN, `Fl4Proofs.P3.afterInv_of_mcsIMNM,
            `Fl4Proofs.P3.jVtxHypMU_of, `Fl4ProofsI.P3.jDecMRL2_ofT, `Fl4ProofsI.P3.jDecMRLK_ofU,
            `Fl4ProofsI.P3.KDispHypsKV41.to35] do
    if let some ci := env.find? n then
      let v := match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[]
      IO.println s!"DEPS {n}: {(v.filter oursQ).toList.eraseDups}"
  for n in [`Fl4Proofs.P3.MachPlat, `Fl4Proofs.P3.IrqPlatA, `Fl4Proofs.P3.MaskMR, `Fl4Proofs.P3.JDecMRLK,
            `Fl4Proofs.P3.JDecMRL2, `Fl4Proofs.P3.MachPlatF, `Fl4Proofs.P3.IpiF, `Fl4Proofs.P3.jVtxHypMU_of,
            `Fl4ProofsI.P3.jDecMRL2_ofT, `Fl4ProofsI.P3.jDecMRLK_ofU, `Fl4ProofsI.P3.jDecMRL_of,
            `Fl4Proofs.P3.afterInv_of_mcsIMN, `Fl4Proofs.P3.afterInv_of_mcsIMNM] do
    if let some ci := env.find? n then
      let t ← MetaM.run' (do let fmt ← ppExpr ci.type; pure fmt.pretty)
      IO.println s!"TYPE {n} : {t}"
  pure ()
