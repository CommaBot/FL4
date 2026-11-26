import Fl4Proofs.P3.XTopJointKEntryU32
import Fl4Proofs.P3.JBootIpi
open Lean Meta Elab Command

def oursQ (n : Name) : Bool :=
  (`Fl4Proofs).isPrefixOf n || (`Fl4ProofsN).isPrefixOf n || (`Fl4ProofsI).isPrefixOf n ||
    (isPrivateName n && (n.toString.startsWith "_private.Fl4Proofs."))

def depsOfQ (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let v := match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[]
    let k := match ci with
      | .inductInfo ii => ii.ctors.toArray.flatMap (fun c => match env.find? c with
          | some cc => cc.type.getUsedConstants | none => #[])
      | _ => #[]
    ci.type.getUsedConstants ++ v ++ k

run_cmd liftCoreM do
  let env ← getEnv
  let root := ``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU32
  let mut cone : NameSet := {}
  let mut wl : List Name := [root]
  let mut deps : Std.HashMap Name (Array Name) := {}
  repeat
    match wl with
    | [] => break
    | n :: rest =>
      wl := rest
      if cone.contains n then continue
      cone := cone.insert n
      let ds := (depsOfQ env n).filter oursQ
      deps := deps.insert n ds
      for d in ds do
        if !cone.contains d then wl := d :: wl
  let coneL := cone.toList
  let mut rev : Std.HashMap Name (List Name) := {}
  for n in coneL do
    for d in deps.getD n #[] do
      rev := rev.insert d (n :: rev.getD d [])
  -- users of jDecMRL_of, up 4 levels
  let mut lvl : List Name := [`Fl4ProofsI.P3.jDecMRL_of]
  for i in [0:6] do
    let nx := (lvl.flatMap fun n => rev.getD n []).eraseDups
    logInfo m!"UP{i}: {nx}"
    lvl := nx
  -- constants in cone that refer to candidate carriers in value but not in type
  let cands : List Name := [`Fl4Proofs.P3.ValidIrqMasks, `Fl4Proofs.P3.SInvV.ValidIrqMasks, `Fl4Proofs.P3.Endp.NativeScope,
     `Fl4Proofs.P3.SInvX, `Fl4Proofs.P3.SpecIrqH]
  for c in cands do
    let us := rev.getD c []
    let prod := us.filter fun n => match env.find? n with
      | some ci => !(ci.type.getUsedConstants.contains c)
      | none => false
    logInfo m!"CAND {c}: users {us.length}, value-only {prod.length}: {prod.take 40}"
  -- records whose ctor is used in cone, JEntryAt family
  for n in coneL do
    if (n.toString.splitOn "JEntryAt").length > 1 || (n.toString.splitOn "JEntryGlob").length > 1 then
      if let some (.inductInfo _) := env.find? n then
        let us := rev.getD (n ++ `mk) []
        logInfo m!"REC {n}: mk-users {us.length}: {us.take 20}"
  if let some ci := env.find? `Fl4ProofsI.P3.jDecMRL_of then
    logInfo m!"TYPE {ci.type}"
