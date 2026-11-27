import Fl4ProofsA64.P1.QueueSlotTyIrq
import Fl4ProofsA64.P1.QueueFinRvReply
import Fl4ProofsA64.P1.QueueFinSc
open Lean Meta Elab Command

def P : Name := `Fl4ProofsA64.P1

def valOf : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | _ => none

def famBase : List Name := [`KW, `KWB].map (P ++ ·)

partial def mentions (env : Environment) (fam : NameSet) (e : Expr) : Bool :=
  e.getUsedConstants.any fam.contains

elab "#cone " roots:ident* : command => do
  let env ← getEnv
  -- family defs: defs in P whose value mentions the family, iterated
  let mut fam : NameSet := famBase.foldl NameSet.insert {}
  let cands := env.constants.toList.filter fun (n, ci) => P.isPrefixOf n && (ci matches .defnInfo _)
  for _ in [0:6] do
    for (n, ci) in cands do
      if !fam.contains n then
        if let some v := valOf ci then
          if mentions env fam v || mentions env fam ci.type then fam := fam.insert n
  let mut seen : NameSet := {}
  let mut stack : Array Name := roots.map (·.getId)
  let mut out : Array Name := #[]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    if !(P.isPrefixOf n) then continue
    let tyFam := mentions env fam ci.type || fam.contains n
    if !tyFam then continue
    out := out.push n
    let used := ((valOf ci).map Expr.getUsedConstants).getD #[] ++ ci.type.getUsedConstants
    for u in used do
      if !seen.contains u then stack := stack.push u
  for n in out do
    let mod := (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!) |>.getD `none
    let r ← findDeclarationRanges? n
    let (a, b) := match r with | some r => (r.range.pos.line, r.range.endPos.line) | none => (0, 0)
    logInfo m!"CONE {mod} {a} {b} {n}"

#cone Fl4ProofsA64.P1.fin_endpoint.blk Fl4ProofsA64.P1.fin_ntfn.blk
#cone Fl4ProofsA64.P1.fin_reply.blk
#cone Fl4ProofsA64.P1.fin_sc.blk
#cone Fl4ProofsA64.P1.fin_thread.blk

elab "#uses " r:ident : command => do
  let env ← getEnv
  let some ci := env.find? r.getId | logInfo "none"
  logInfo m!"KIND {match ci with | .thmInfo _ => "thm" | .defnInfo _ => "defn" | .axiomInfo _ => "ax" | .opaqueInfo _ => "opaque" | _ => "other"} HASVAL {(valOf ci).isSome}"
  logInfo m!"USES {((valOf ci).map Expr.getUsedConstants).getD #[]}"
#uses Fl4ProofsA64.P1.fin_ntfn.blk
