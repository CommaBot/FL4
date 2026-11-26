import Fl4Proofs.P2.WitUncond
import Fl4Proofs.P3.JBoot1U34
import Fl4Proofs.P3.IrqFixGen
open Lean Meta Elab Command

-- jboot gen 5: the cone of `wit_U2_uncond` and its part mentioning U32-platform records.

def oursW (n : Name) : Bool :=
  (`Fl4Proofs).isPrefixOf n || (`Fl4ProofsN).isPrefixOf n || (`Fl4ProofsI).isPrefixOf n ||
    (isPrivateName n && (n.toString.startsWith "_private.Fl4Proofs."))

run_cmd liftCoreM do
  let env ← getEnv
  let roots : List Name := [`Fl4Proofs.P2.Wit.wit_U2_uncond]
  let seeds : List Name := [``Fl4Proofs.P3.MachPlat, ``Fl4Proofs.P3.IrqPlatA, ``Fl4Proofs.P3.MaskMR,
    ``Fl4Proofs.P3.JDecMRLK, ``Fl4Proofs.P3.JDecMRL2]
  let fixedC : List Name := (Fl4Proofs.P3.IrqFix.specD.constMap.map (·.1))
  let mut cone : NameSet := {}
  let mut wl : List Name := roots
  let mut deps : Std.HashMap Name (Array Name) := {}
  repeat
    match wl with
    | [] => break
    | n :: rest =>
      wl := rest
      if cone.contains n then continue
      cone := cone.insert n
      let ds := if fixedC.contains n then #[] else (Fl4Proofs.P3.StallNarrow.depsOf env n).filter oursW
      deps := deps.insert n ds
      for d in ds do
        if !cone.contains d then wl := d :: wl
  IO.println s!"W5 cone {cone.size}"
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
  IO.println s!"W5 tr {tr.size}"
  let mut perMod : Std.HashMap Name Nat := {}
  let mut q := 0
  for n in tr.toList do
    let mod := match env.getModuleIdxFor? n with | some i => env.header.moduleNames[i.toNat]! | none => `here
    perMod := perMod.insert mod (perMod.getD mod 0 + 1)
    let n' := (Fl4Proofs.P3.IrqFix.mapName Fl4Proofs.P3.IrqFix.specD n)
    if env.contains n' then q := q + 1
  IO.println s!"W5 tr already-copied-by-irqfix {q}"
  for (m, k) in perMod.toList do
    IO.println s!"W5 MOD {m} {k}"
  for n in coneL do
    if fixedC.contains n then IO.println s!"W5 FIXED-IN-CONE {n}"
  let watch : List Name := [``Fl4Proofs.P3.IrqPlatA.noIpi, ``Fl4Proofs.P3.MachPlat.mask, ``Fl4Proofs.P3.MachPlat.mk,
    ``Fl4Proofs.P3.IrqPlatA.mk, ``Fl4Proofs.P3.MaskMR, ``Fl4Proofs.P3.JDecMRLK, ``Fl4Proofs.P3.JDecMRL2]
  for n in tr.toList do
    let ds := deps.getD n #[]
    let hits := watch.filter (fun w => ds.contains w)
    let kind := match env.find? n with
      | some (.inductInfo _) => "IND" | some (.defnInfo _) => "DEF" | some (.thmInfo _) => "THM" | _ => "OTH"
    let mod := match env.getModuleIdxFor? n with | some i => env.header.moduleNames[i.toNat]! | none => `here
    if !hits.isEmpty || kind != "THM" || (n.toString.splitOn "kernel_entry_reach").length > 1 then
      IO.println s!"W5 USE {kind} {n} @{mod} {hits}"
