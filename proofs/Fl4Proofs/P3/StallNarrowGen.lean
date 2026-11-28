/-
P3 (p3P gen 2; collapse A, N): **the kernel-checked constant transport** (`StallNarrow.transport`), the
library ArchIrqNarrowGen and the staged transports (IrqFixXport, P3JXport, P3KXport) build on.

`transport` walks the proof cone of a root (every `Fl4Proofs` constant its type and proof reach), takes the
set `Tr` of constants that mention one of the renamed records (their types, values or constructors,
transitively), and adds for each a copy under `σ.dst` whose type and value are the original's with the
records (and every constant they generated) renamed, the single replacements of `σ.constMap` substituted and
every constant of `Tr` replaced by its copy. Each copy goes through `addDecl`, i.e. the Lean kernel checks it:
no new axiom, no trusted step.

Collapse A, N: the stall narrowing this module ran on `kernel_entry_reachU30` (records `JEntryAt*` ↦
StallNarrowRec's `…N` copies, `stall : ∀ q ∈ Z.T, …`; `decode_invocation_threadJ_stepMM/stepM` ↦ `…MMN/MN`;
copies `Fl4ProofsN.…`) is written back into the base records (`JEntryAt*.stall` is `∀ q ∈ Z.T, …`, the
Thread decode by XTopJointMRTcbL / KEntry40's `…stepMT` / `…stepMMT`), so its run, StallNarrowRec and
StallNarrowTcb are gone; only the library is left.
-/
import Fl4Proofs.P3.XTopJointKEntryU30
open Lean Meta Elab Command

namespace Fl4Proofs.P3.StallNarrow

/-- A constant of this development (`Fl4Proofs.…`, or private to one of its modules). -/
def ours (n : Name) : Bool :=
  (`Fl4Proofs).isPrefixOf n || (`Fl4ProofsN).isPrefixOf n ||
    (isPrivateName n && (n.toString.startsWith "_private.Fl4Proofs."))

/-- A transport: the records renamed (prefix renaming: their generated constants follow), the
single constants replaced by hand-proved ones of the narrowed statement, and the root of the
copies' names. -/
structure Spec where
  recMap : List (Name × Name)
  constMap : List (Name × Name)
  dst : Name

/-- The name of a constant's copy. -/
def mapName (σ : Spec) (n : Name) : Name := Id.run do
  for (a, b) in σ.constMap do
    if n == a then return b
  for (a, b) in σ.recMap do
    if a.isPrefixOf n then return n.replacePrefix a b
  if (`Fl4Proofs).isPrefixOf n then return n.replacePrefix `Fl4Proofs σ.dst
  if (`Fl4ProofsN).isPrefixOf n then return n.replacePrefix `Fl4ProofsN σ.dst
  return σ.dst ++ `priv ++ n

/-- The constants a constant's type, value and (for an inductive) constructors use. -/
def depsOf (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let v := match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[]
    let k := match ci with
      | .inductInfo ii => ii.ctors.toArray.flatMap (fun c => match env.find? c with
          | some cc => cc.type.getUsedConstants | none => #[])
      | _ => #[]
    ci.type.getUsedConstants ++ v ++ k

/-- The constants rewritten: `Tr` and the single replacements (one cached pass, so the proof
terms keep their sharing). -/
def trE (σ : Spec) (tr : NameSet) (e : Expr) : CoreM Expr :=
  Core.transform e (post := fun x => pure <| match x with
    | .const n ls => if tr.contains n || σ.constMap.any (·.1 == n) then .done (.const (mapName σ n) ls) else .done x
    | .proj s i b => if tr.contains s then .done (.proj (mapName σ s) i b) else .done x
    | _ => .done x)

/-- Copy the constants of `Tr` reached from `root`, in dependency order. -/
def stamp (msg : String) : IO Unit := do
  if let some f ← IO.getEnv "FL4_TRANSPORT_LOG" then
    let h ← IO.FS.Handle.mk f .append
    h.putStrLn s!"{← IO.monoMsNow} {msg}"
    h.flush

def transport (σ : Spec) (root : Name) : CoreM Nat := do
  let env ← getEnv
  stamp "start"
  -- the proof cone of `root`
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
      let ds := (depsOf env n).filter ours
      deps := deps.insert n ds
      for d in ds do
        if !cone.contains d then wl := d :: wl
  stamp s!"cone {cone.size}"
  -- `Tr`: the seeds, then every constant of the cone using one (reverse edges as lists: no copying)
  let coneL := cone.toList
  let mut rev : Std.HashMap Name (List Name) := {}
  for n in coneL do
    for d in deps.getD n #[] do
      rev := rev.insert d (n :: rev.getD d [])
  let mut tr : NameSet := {}
  let mut wl2 : List Name := coneL.filter (fun n => σ.recMap.any (fun (a, _) => a.isPrefixOf n))
  repeat
    match wl2 with
    | [] => break
    | n :: more =>
      wl2 := more
      if tr.contains n then continue
      tr := tr.insert n
      for u in rev.getD n [] do
        if !tr.contains u then wl2 := u :: wl2
  stamp s!"tr {tr.size}"
  -- (the single replacements are not seeds: they are rewritten only inside the copies)
  -- dependency order (iterative post-order DFS over `Tr`)
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
  let mut cnt := 0
  let logf? ← IO.getEnv "FL4_TRANSPORT_LOG"
  stamp s!"order {order.size}"
  for n in order do
    let n' := mapName σ n
    if (← getEnv).contains n' then continue
    if let some f := logf? then
      let h ← IO.FS.Handle.mk f .append
      h.putStrLn s!"{cnt} {n}"
      h.flush
    let some ci := (← getEnv).find? n | throwError "transport: missing {n}"
    -- each copy gets the default heartbeat budget of its own, as a declaration of a source file
    withCurrHeartbeats do
      match ci with
      | .thmInfo v =>
        addDecl (.thmDecl (⟨⟨n', v.levelParams, (← trE σ tr v.type)⟩, (← trE σ tr v.value), [n']⟩ : TheoremVal))
      | .defnInfo v =>
        addDecl (.defnDecl (mkDefinitionValEx n' v.levelParams (← trE σ tr v.type) (← trE σ tr v.value) v.hints v.safety [n']))
      | .opaqueInfo v =>
        addDecl (.opaqueDecl (⟨⟨n', v.levelParams, (← trE σ tr v.type)⟩, (← trE σ tr v.value), v.isUnsafe, [n']⟩ : OpaqueVal))
      | .inductInfo v =>
        unless v.all.length == 1 do throwError "transport: mutual inductive {n}"
        let ctors ← v.ctors.mapM fun k => do
          let some kc := (← getEnv).find? k | throwError "transport: missing constructor {k}"
          pure (⟨mapName σ k, (← trE σ tr kc.type)⟩ : Constructor)
        addDecl (.inductDecl v.levelParams v.numParams [(⟨n', (← trE σ tr v.type), ctors⟩ : InductiveType)] v.isUnsafe)
      | .ctorInfo _ | .recInfo _ => pure ()
      | _ => throwError "transport: unsupported constant {n}"
    cnt := cnt + 1
  return cnt

end Fl4Proofs.P3.StallNarrow
