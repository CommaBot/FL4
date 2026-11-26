import Fl4Proofs.P3.XTopJointKEntryU35
open Lean Meta Elab Command

def oursQ (n : Name) : Bool :=
  (`Fl4Proofs).isPrefixOf n || (`Fl4ProofsN).isPrefixOf n || (`Fl4ProofsI).isPrefixOf n ||
    (`Fl4ProofsQ).isPrefixOf n || (`Fl4ProofsQN).isPrefixOf n || (`Fl4ProofsQI).isPrefixOf n ||
    (isPrivateName n && (n.toString.startsWith "_private.Fl4Proofs."))

set_option pp.fullNames true in
set_option pp.funBinderTypes true in
run_cmd liftCoreM do
  let env ← getEnv
  for n in [`Fl4ProofsI.P3.handle_invocation_entryJMU, `Fl4ProofsQI.P3.handle_invocation_entryJMUM,
            `Fl4Proofs.P3.handle_invocation_entryJMU, `Fl4Proofs.P3.handle_invocation_entryJMUM] do
    if let some ci := env.find? n then
      let v := match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[]
      IO.println s!"DEPS {n}: {(v.filter oursQ).toList.eraseDups}"
      IO.println s!"TYDEPS {n}: {(ci.type.getUsedConstants.filter oursQ).toList.eraseDups}"
    else IO.println s!"MISSING {n}"
