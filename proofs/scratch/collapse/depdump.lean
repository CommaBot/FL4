import Fl4Proofs
open Lean

/-! collapse: dump every Fl4* constant with its module, kind and the Fl4* constants its type/value use.
Output: `depdump.tsv` in the cwd (proofs/). -/
def kindOf : ConstantInfo → String
  | .axiomInfo _ => "ax" | .defnInfo _ => "def" | .thmInfo _ => "thm" | .opaqueInfo _ => "opq"
  | .quotInfo _ => "quot" | .inductInfo _ => "ind" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let isOurs (m : Name) : Bool := m.toString.startsWith "Fl4"
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map fun i => mods[i.toNat]!
  let h ← IO.FS.Handle.mk "depdump.tsv" .write
  let mut cnt := 0
  for (n, ci) in env.constants.map₁.toList do
    let some m := modOf n | continue
    unless isOurs m do continue
    let us := ci.getUsedConstantsAsSet.toList.filter fun u => match modOf u with
      | some mu => isOurs mu | none => false
    h.putStrLn s!"{n}\t{m}\t{kindOf ci}\t{" ".intercalate (us.map toString)}"
    cnt := cnt + 1
  IO.println s!"DUMPED {cnt}"
