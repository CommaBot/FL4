import Fl4Proofs.P3.XTopJointKEntryU35
open Lean Meta Elab Command

def oursQ (n : Name) : Bool :=
  (`Fl4Proofs).isPrefixOf n || (`Fl4ProofsN).isPrefixOf n || (`Fl4ProofsI).isPrefixOf n ||
    (`Fl4ProofsQ).isPrefixOf n || (`Fl4ProofsQN).isPrefixOf n || (`Fl4ProofsQI).isPrefixOf n ||
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
  let root := ``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU35
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
  IO.println s!"CONE {coneL.length}"
  -- seeds: every constant in the cone whose name's last component starts with JPathAt, plus refines lemmas
  let isSeed : Name → Bool := fun n =>
    let s := n.toString
    let last := match n with | .str _ l => l | _ => ""
    (last.startsWith "JPathAt" && !(s.splitOn "._").length.ble 1 == false) || last.startsWith "JPathAt" ||
      last.startsWith "handle_invocation_refines"
  let seeds := coneL.filter isSeed
  IO.println s!"SEEDS {seeds.length}"
  for n in seeds do
    let k := match env.find? n with
      | some (.defnInfo _) => "def" | some (.thmInfo _) => "thm" | some (.inductInfo _) => "ind" | _ => "other"
    IO.println s!"SEED {k} {n}"
  -- closure of users within cone, type-users vs value-only users
  let mut rev : Std.HashMap Name (List Name) := {}
  for n in coneL do
    for d in deps.getD n #[] do
      rev := rev.insert d (n :: rev.getD d [])
  let defSeeds := seeds.filter fun n => match env.find? n with | some (.defnInfo _) => true | _ => false
  let mut tr : NameSet := {}
  let mut wl2 := defSeeds
  repeat
    match wl2 with
    | [] => break
    | n :: rest =>
      wl2 := rest
      for u in rev.getD n [] do
        if !tr.contains u then
          tr := tr.insert u; wl2 := u :: wl2
  IO.println s!"TR {tr.toList.length}"
  -- users whose TYPE mentions a def seed or a Tr inductive (these need new statements)
  let mut tyU : List Name := []
  for n in tr.toList do
    if let some ci := env.find? n then
      let us := ci.type.getUsedConstants
      if us.any (fun d => defSeeds.contains d || (tr.contains d && (match env.find? d with | some (.inductInfo _) => true | some (.defnInfo _) => true | _ => false))) then
        tyU := n :: tyU
  IO.println s!"TYPEUSERS {tyU.length}"
  for n in tyU do
    let k := match env.find? n with
      | some (.defnInfo _) => "def" | some (.thmInfo _) => "thm" | some (.inductInfo _) => "ind" | some (.ctorInfo _) => "ctor" | _ => "other"
    IO.println s!"TU {k} {n}"
