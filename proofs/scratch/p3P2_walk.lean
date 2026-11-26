import Fl4Proofs.P3.XTopJointKEntry35
import Fl4Proofs.P3.XTopJointKEntry36
import Fl4Proofs.P3.XTopJointKEntry36E
import Fl4Proofs.P3.XTopJointKEntry37
import Fl4Proofs.P3.XTopJointKEntry37E
import Fl4Proofs.P3.XTopJointKEntry38
import Fl4Proofs.P3.XTopJointKEntry38E
import Fl4Proofs.P3.XTopJointKEntry39
import Fl4Proofs.P3.XTopJointKEntry40
import Fl4Proofs.P3.XTopJointKEntry41
import Fl4Proofs.P3.XTopJointKEntry41V
import Fl4Proofs.P3.XTopJointKEntryEv
import Fl4Proofs.P3.XTopJointKEntryEv2
import Fl4Proofs.P3.XTopJointKEntryEv3
import Fl4Proofs.P3.XTopJointKEntryEv4
import Fl4Proofs.P3.XTopJointKEntryEv7
import Fl4Proofs.P3.XTopJointKEntryFF
import Fl4Proofs.P3.XTopJointKEntryInvL
import Fl4Proofs.P3.XTopJointKEntryNF
import Fl4Proofs.P3.XTopJointKEntryU
import Fl4Proofs.P3.XTopJointKEntryU10
import Fl4Proofs.P3.XTopJointKEntryU11
import Fl4Proofs.P3.XTopJointKEntryU12
import Fl4Proofs.P3.XTopJointKEntryU13
import Fl4Proofs.P3.XTopJointKEntryU14
import Fl4Proofs.P3.XTopJointKEntryU15
import Fl4Proofs.P3.XTopJointKEntryU16
import Fl4Proofs.P3.XTopJointKEntryU17
import Fl4Proofs.P3.XTopJointKEntryU18
import Fl4Proofs.P3.XTopJointKEntryU19
import Fl4Proofs.P3.XTopJointKEntryU2
import Fl4Proofs.P3.XTopJointKEntryU20
import Fl4Proofs.P3.XTopJointKEntryU21
import Fl4Proofs.P3.XTopJointKEntryU25
import Fl4Proofs.P3.XTopJointKEntryU26
import Fl4Proofs.P3.XTopJointKEntryU27
import Fl4Proofs.P3.XTopJointKEntryU28
import Fl4Proofs.P3.XTopJointKEntryU29
import Fl4Proofs.P3.XTopJointKEntryU29D
import Fl4Proofs.P3.XTopJointKEntryU29I
import Fl4Proofs.P3.XTopJointKEntryU29S
import Fl4Proofs.P3.XTopJointKEntryU29T
import Fl4Proofs.P3.XTopJointKEntryU2F
import Fl4Proofs.P3.XTopJointKEntryU2L
import Fl4Proofs.P3.XTopJointKEntryU3
import Fl4Proofs.P3.XTopJointKEntryU30
import Fl4Proofs.P3.XTopJointKEntryU3L
import Fl4Proofs.P3.XTopJointKEntryU4
import Fl4Proofs.P3.XTopJointKEntryU5
import Fl4Proofs.P3.XTopJointKEntryU6
import Fl4Proofs.P3.XTopJointKEntryU7
import Fl4Proofs.P3.XTopJointKEntryU8
import Fl4Proofs.P3.XTopJointKEntryU9
import Fl4Proofs.P3.XTopJointKEntryUH
import Fl4Proofs.P3.XTopJointKEntryVm
open Lean Meta

def ours (n : Name) : Bool := (`Fl4Proofs).isPrefixOf n

def isStallAll (e : Expr) : Bool := match e with
  | .forallE _ _ b _ => b.isAppOfArity ``Eq 3 &&
      (let l := b.getArg! 1; l.isAppOf ``fl4_core.smp.remote_tcb_stall && l.getAppArgs.back? == some (.bvar 0))
  | _ => false

def isThm (ci : ConstantInfo) : Bool := match ci with | .thmInfo _ => true | _ => false

def depsOf (env : Environment) (n : Name) (thmVal : Bool) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let t := ci.type.getUsedConstants
    let v := if isThm ci && !thmVal then #[] else
      (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[])
    let extra := match ci with
      | .inductInfo ii => ii.ctors.toArray.flatMap (fun c => match env.find? c with
          | some cc => cc.type.getUsedConstants | none => #[])
      | _ => #[]
    (t ++ v ++ extra).filter ours

def cone (env : Environment) (roots : Array Name) (thmVal : Bool) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut wl := roots.toList
  for _ in [0:10000000] do
    match wl with
    | [] => break
    | n :: rest =>
      wl := rest
      if seen.contains n then continue
      seen := seen.insert n
      for d in depsOf env n thmVal do
        if !seen.contains d then wl := d :: wl
  return seen

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => `here

/-- fields (from the constructor) of a one-constructor inductive `n` whose type has a U64 binder and
mentions an fl4_core constant -/
def u64Fields (n : Name) : MetaM (Array (Name × Bool × Format)) := do
  let env ← getEnv
  let some (.inductInfo ii) := env.find? n | return #[]
  let [k] := ii.ctors | return #[]
  let some kc := env.find? k | return #[]
  forallTelescope kc.type fun xs _ => do
    let mut out := #[]
    for x in xs[ii.numParams:] do
      let d ← x.fvarId!.getDecl
      let body := d.type
      let mut hasU := false
      let mut e := body
      for _ in [0:20] do
        match e with
        | .forallE _ dom b _ =>
          if !dom.hasLooseBVars then
            if (← isDefEq dom (mkConst ``Aeneas.Std.U64)) then hasU := true
          e := b
        | _ => break
      let fl := body.getUsedConstants.any (fun c => (`fl4_core).isPrefixOf c)
      if (hasU && fl) || (body.find? isStallAll).isSome then
        out := out.push (d.userName, (body.find? isStallAll).isSome, ← ppExpr body)
    return out

#eval show MetaM Unit from do
  let env ← getEnv
  let u30 := ``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU30
  let tops := env.constants.toList.filterMap (fun (n, ci) =>
    if ours n && isThm ci && (n.toString.splitOn "kernel_entry_reach").length > 1 then some n else none)
  IO.println s!"TOPS {tops.length}"
  -- statement cone of all tops: structures with U64 fields
  let stc := cone env tops.toArray false
  let mut stallS : NameSet := {}
  for n in stc.toList do
    if true then
      let fs ← u64Fields n
      for (f, sq, fmt) in fs do
        IO.println ((s!"FIELD {n}.{f} stallQ={sq} :: {fmt}").replace "\n" " ")
        if sq then stallS := stallS.insert n
  IO.println s!"STALLSTRUCTS {stallS.toList}"
  -- carriers: non-theorem constants whose (type+value+ctor) cone hits stallS
  let pc := cone env #[u30] true
  IO.println s!"PROOFCONE {pc.size}"
  let mut carr : NameSet := stallS
  for _ in [0:50] do
    let mut ch := false
    for n in pc.toList ++ stc.toList do
      if carr.contains n then continue
      let some ci := env.find? n | continue
      if isThm ci then continue
      if (depsOf env n true).any carr.contains then carr := carr.insert n; ch := true
    if !ch then break
  IO.println s!"CARRIERS {carr.toList}"
  for t in tops do
    let some ci := env.find? t | continue
    let c := cone env #[t] false
    let hit := c.toList.filter stallS.contains
    IO.println s!"TOP {t} stall={!hit.isEmpty} via={hit}"
  let mut cnt := 0
  for n in pc.toList do
    let some ci := env.find? n | continue
    if !isThm ci then continue
    let ty := ci.type.getUsedConstants
    if ty.any carr.contains then
      cnt := cnt + 1
      IO.println s!"CARRYTHM {modOf env n} {n}"
    if (ci.type.find? isStallAll).isSome then
      IO.println s!"STALLARG {modOf env n} {n}"
    let v := (ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[]
    if v.any (fun c => c.toString.endsWith ".stall" && stallS.contains c.getPrefix) then
      IO.println s!"USESTALL {modOf env n} {n}"
  IO.println s!"CARRYCOUNT {cnt}"
