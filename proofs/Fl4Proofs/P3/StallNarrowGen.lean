/-
P3 (p3P gen 2, finding (c) fix): **`kernel_entry_reachU30`'s proof transported onto the narrowed
entry records** (`StallNarrowRec`), by a constant renaming re-checked by the kernel.

`JEntryAt*.stall` asked `remote_tcb_stall` to be the no-op at every word (false at reachable
states, `StallFinding`). The only consumer of that field on U30's proof is the Thread decode
(`decode_invocation_threadJ_stepMM`, at the target and CopyRegisters' source, both TCBs of `Z.T`).

`narrow_transport` (below) walks the proof cone of U30 (every `Fl4Proofs` constant its type and
proof reach), takes the set `Tr` of constants that mention one of the seven stall records (their
types, values or constructors, transitively), and for each adds a copy under `Fl4ProofsN.…`
(`Fl4Proofs.X` ↦ `Fl4ProofsN.X`) whose type and value are the original's with
* the seven records (and every constant they generated: constructor, recursor, projections,
  `casesOn`, …) replaced by StallNarrowRec's `…N` copies, whose `stall` is `∀ q ∈ Z.T, …`;
* `decode_invocation_threadJ_stepMM` / `…stepM` replaced by `…stepMMN` / `…stepMN` (their
  `hstall'` narrowed the same way, proved without it from `JAtZ.stallT`);
* every constant of `Tr` replaced by its copy.
Each copy goes through `addDecl`, i.e. the Lean kernel checks it: no new axiom, no trusted step.
The copies are definitions/theorems with the same statements up to that renaming; in particular
`Fl4ProofsN.P3.SInvR.G5.kernel_entry_reachU30` is U30 with `KDispHypsKVU30` (whose `JEntryAtR7`
asks the narrowed `stall`) — XTopJointKEntryU31 discharges that field and states the new top.
No premise is added.
-/
import Fl4Proofs.P3.StallNarrowRec
open Lean Meta Elab Command

namespace Fl4Proofs.P3.StallNarrow

/-- A constant of this development (`Fl4Proofs.…`, or private to one of its modules). -/
def ours (n : Name) : Bool :=
  (`Fl4Proofs).isPrefixOf n || (isPrivateName n && (n.toString.startsWith "_private.Fl4Proofs."))

/-- The seven records, renamed to their narrowed copies (prefix renaming: their generated
constants follow). -/
def recMap : List (Name × Name) :=
  [(``Fl4Proofs.P3.JEntryAt, ``Fl4Proofs.P3.JEntryAtN),
   (``Fl4Proofs.P3.JEntryAtR, ``Fl4Proofs.P3.JEntryAtRN),
   (``Fl4Proofs.P3.JEntryAtR2, ``Fl4Proofs.P3.JEntryAtR2N),
   (``Fl4Proofs.P3.JEntryAtR3, ``Fl4Proofs.P3.JEntryAtR3N),
   (``Fl4Proofs.P3.JEntryAtR5, ``Fl4Proofs.P3.JEntryAtR5N),
   (``Fl4Proofs.P3.SInvR.G5.JEntryAtR6, ``Fl4Proofs.P3.SInvR.G5.JEntryAtR6N),
   (``Fl4Proofs.P3.SInvR.G5.JEntryAtR7, ``Fl4Proofs.P3.SInvR.G5.JEntryAtR7N)]

/-- Single constants replaced by hand-proved ones of the narrowed statement. -/
def constMap : List (Name × Name) :=
  [(``Fl4Proofs.P3.decode_invocation_threadJ_stepMM, ``Fl4Proofs.P3.decode_invocation_threadJ_stepMMN),
   (``Fl4Proofs.P3.decode_invocation_threadJ_stepM, ``Fl4Proofs.P3.decode_invocation_threadJ_stepMN)]

/-- The name of a constant's copy. -/
def mapName (n : Name) : Name := Id.run do
  for (a, b) in constMap do
    if n == a then return b
  for (a, b) in recMap do
    if a.isPrefixOf n then return n.replacePrefix a b
  if (`Fl4Proofs).isPrefixOf n then return n.replacePrefix `Fl4Proofs `Fl4ProofsN
  return `Fl4ProofsN.priv ++ n

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
def trE (tr : NameSet) (e : Expr) : CoreM Expr :=
  Core.transform e (post := fun x => pure <| match x with
    | .const n ls => if tr.contains n || constMap.any (·.1 == n) then .done (.const (mapName n) ls) else .done x
    | .proj s i b => if tr.contains s then .done (.proj (mapName s) i b) else .done x
    | _ => .done x)

/-- Copy the constants of `Tr` reached from `root`, in dependency order. -/
def stamp (msg : String) : IO Unit := do
  if let some f ← IO.getEnv "FL4_TRANSPORT_LOG" then
    let h ← IO.FS.Handle.mk f .append
    h.putStrLn s!"{← IO.monoMsNow} {msg}"
    h.flush

def transport (root : Name) : CoreM Nat := do
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
  let mut wl2 : List Name := coneL.filter (fun n => recMap.any (fun (a, _) => a.isPrefixOf n))
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
    let n' := mapName n
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
        addDecl (.thmDecl (⟨⟨n', v.levelParams, (← trE tr v.type)⟩, (← trE tr v.value), [n']⟩ : TheoremVal))
      | .defnInfo v =>
        addDecl (.defnDecl (mkDefinitionValEx n' v.levelParams (← trE tr v.type) (← trE tr v.value) v.hints v.safety [n']))
      | .opaqueInfo v =>
        addDecl (.opaqueDecl (⟨⟨n', v.levelParams, (← trE tr v.type)⟩, (← trE tr v.value), v.isUnsafe, [n']⟩ : OpaqueVal))
      | .inductInfo v =>
        unless v.all.length == 1 do throwError "transport: mutual inductive {n}"
        let ctors ← v.ctors.mapM fun k => do
          let some kc := (← getEnv).find? k | throwError "transport: missing constructor {k}"
          pure (⟨mapName k, (← trE tr kc.type)⟩ : Constructor)
        addDecl (.inductDecl v.levelParams v.numParams [(⟨n', (← trE tr v.type), ctors⟩ : InductiveType)] v.isUnsafe)
      | .ctorInfo _ | .recInfo _ => pure ()
      | _ => throwError "transport: unsupported constant {n}"
    cnt := cnt + 1
  return cnt

end Fl4Proofs.P3.StallNarrow

open Fl4Proofs.P3.StallNarrow in
run_cmd liftCoreM do
  let n ← transport ``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU30
  logInfo m!"narrow_transport: {n} constants copied"
