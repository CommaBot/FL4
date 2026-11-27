import Fl4Proofs
open Lean

/-! collapse: for every Fl4* theorem / def / inductive: its kind, module, the hash of its type, and the Fl4*
constants its *type* uses (statement-level dependencies). Output `tydump.tsv` in the cwd. -/
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map fun i => mods[i.toNat]!
  let isOurs (n : Name) : Bool := match modOf n with | some m => m.toString.startsWith "Fl4" | none => false
  let h ← IO.FS.Handle.mk ((← IO.getEnv "TYOUT").getD "tydump.tsv") .write
  let mut cnt := 0
  for (n, ci) in env.constants.map₁.toList do
    unless isOurs n do continue
    let us := ci.type.getUsedConstantsAsSet.toList.filter isOurs
    h.putStrLn s!"{n}\t{hash ci.type}\t{" ".intercalate (us.map toString)}"
    cnt := cnt + 1
  IO.println s!"TYDUMPED {cnt}"
