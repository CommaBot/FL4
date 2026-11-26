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

def projsIn (e : Expr) : Array Name := Id.run do
  let mut out := #[]
  for x in (e.foldConsts #[] fun _ a => a) do out := out.push x
  return out

run_cmd liftCoreM do
  let env ← getEnv
  let root := ``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU32
  let seeds : List Name := [``Fl4Proofs.P3.MachPlat, ``Fl4Proofs.P3.IrqPlatA, ``Fl4Proofs.P3.MaskMR,
    ``Fl4Proofs.P3.JDecMRLK, ``Fl4Proofs.P3.JDecMRL2]
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
  let mut tr : NameSet := {}
  let mut wl2 : List Name := coneL.filter (fun n => seeds.any (·.isPrefixOf n))
  repeat
    match wl2 with
    | [] => break
    | n :: more =>
      wl2 := more
      if tr.contains n then continue
      tr := tr.insert n
      for u in rev.getD n [] do
        if !tr.contains u then wl2 := u :: wl2
  logInfo m!"tr {tr.size}"
  for n in tr.toList do
    let ds := ((deps.getD n #[]).filter (tr.contains ·)).toList.eraseDups
    let mod := match env.getModuleIdxFor? n with | some i => env.header.moduleNames[i.toNat]! | none => `here
    IO.println s!"TR {n} @{mod} <- {ds}"
