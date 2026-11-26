import Fl4Proofs.P2.WitUncond
import Fl4Proofs.P3.IrqFixGen
import Fl4Proofs.P3.JBoot5CtlQ
open Lean Meta Elab Command

/-! jboot gen 5 (scratch): a dry run of IrqFixXport's transport on `wit_U2_io`'s cone under irqfix's `specD`
(plus `extra`), continuing past failures; prints each constant whose copy fails while all its deps exist. -/

namespace JB5
open Fl4Proofs.P3.IrqFix

def extra : List (Name × Name) :=
  [(``Fl4Proofs.P3.irq_ioapic_refinesM, ``Fl4Proofs.P3.irq_ioapic_refinesMQ0),
   (``Fl4Proofs.P3.irq_remap_refinesM, ``Fl4Proofs.P3.irq_remap_refinesMQ0)]

def specW : Spec where
  recMap := specD.recMap
  defMap := specD.defMap
  constMap := specD.constMap ++ extra

def dry (σ : Spec) (roots : List Name) : CoreM Unit := do
  let env ← getEnv
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
      let ds := if σ.constMap.any (·.1 == n) then #[] else
        (Fl4Proofs.P3.StallNarrow.depsOf env n).filter ours
      deps := deps.insert n ds
      for d in ds do
        if !cone.contains d then wl := d :: wl
  let coneL := cone.toList
  let mut rev : Std.HashMap Name (List Name) := {}
  for n in coneL do
    for d in deps.getD n #[] do
      rev := rev.insert d (n :: rev.getD d [])
  let mut tr : NameSet := {}
  let mut wl2 : List Name := coneL.filter (fun n =>
    σ.recMap.any (fun (a, _) => a.isPrefixOf n) || σ.defMap.any (fun (a, _) => a == n))
  repeat
    match wl2 with
    | [] => break
    | n :: more =>
      wl2 := more
      if tr.contains n then continue
      tr := tr.insert n
      for u in rev.getD n [] do
        if !tr.contains u then wl2 := u :: wl2
  IO.println s!"XD cone {cone.size} tr {tr.size}"
  let mut done : NameSet := {}
  let mut seen : NameSet := {}
  let mut order : Array Name := #[]
  for n0 in tr.toList do
    if done.contains n0 then continue
    let mut stack : List (Name × Bool) := [(n0, false)]
    repeat
      match stack with
      | [] => break
      | (n, exp) :: rest =>
        stack := rest
        if exp then
          if !done.contains n then
            done := done.insert n
            order := order.push n
        else if !seen.contains n then
          seen := seen.insert n
          stack := (n, true) :: stack
          for d in deps.getD n #[] do
            if tr.contains d && !seen.contains d then stack := (d, false) :: stack
  let mut failed : NameSet := {}
  let mut ok := 0
  let mut reused := 0
  for n in order do
    if σ.constMap.any (·.1 == n) || σ.defMap.any (·.1 == n) then continue
    let n' := mapName σ n
    if σ.recMap.any (·.1.isPrefixOf n) && (← getEnv).contains n' then continue
    let some ci := (← getEnv).find? n | IO.println s!"XD MISSING {n}"; continue
    let bad := (deps.getD n #[]).filter (failed.contains ·)
    if !bad.isEmpty then
      failed := failed.insert n
      continue
    if let some ci' := (← getEnv).find? n' then
      let same ← withCurrHeartbeats do pure (ci'.type == (← trE σ tr ci.type))
      if same then reused := reused + 1 else
        IO.println s!"XD REUSE-MISMATCH {n}"
        failed := failed.insert n
      continue
    let mod := match env.getModuleIdxFor? n with | some i => env.header.moduleNames[i.toNat]! | none => `here
    try
      withCurrHeartbeats do
        match ci with
        | .thmInfo v =>
          addDecl (.thmDecl (⟨⟨n', v.levelParams, (← trE σ tr v.type)⟩, (← trE σ tr v.value), [n']⟩ : TheoremVal))
        | .defnInfo v =>
          addDecl (.defnDecl (mkDefinitionValEx n' v.levelParams (← trE σ tr v.type) (← trE σ tr v.value) v.hints v.safety [n']))
        | .opaqueInfo v =>
          addDecl (.opaqueDecl (⟨⟨n', v.levelParams, (← trE σ tr v.type)⟩, (← trE σ tr v.value), v.isUnsafe, [n']⟩ : OpaqueVal))
        | .inductInfo v =>
          unless v.all.length == 1 do throwError "mutual inductive {n}"
          let ctors ← v.ctors.mapM fun k => do
            let some kc := (← getEnv).find? k | throwError "missing constructor {k}"
            pure (⟨mapName σ k, (← trE σ tr kc.type)⟩ : Constructor)
          addDecl (.inductDecl v.levelParams v.numParams [(⟨n', (← trE σ tr v.type), ctors⟩ : InductiveType)] v.isUnsafe)
        | .ctorInfo _ | .recInfo _ => pure ()
        | _ => throwError "unsupported constant {n}"
      ok := ok + 1
    catch e =>
      failed := failed.insert n
      let msg := (← e.toMessageData.toString)
      IO.println s!"XD FAIL {n} @{mod} :: {(msg.take 400).replace "\n" " "}"
  IO.println s!"XD copied {ok} reused {reused} failed {failed.size}"

end JB5

set_option maxRecDepth 200000 in
run_cmd liftCoreM do
  JB5.dry JB5.specW [`Fl4Proofs.P2.Wit.wit_U2_io]
