import Fl4ProofsA64
open Lean

/-! collapse: full axiom sweep. Every constant of a `Fl4*` module is checked: a constant is *bad* when it
reaches (through the constants its type or value uses) an axiom other than `propext`, `Classical.choice`,
`Quot.sound`. Memoised over the whole environment. Prints the count and the first bad names. -/
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map fun i => mods[i.toNat]!
  let ok : NameSet := NameSet.empty |>.insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound
  let mut memo : Std.HashMap Name Bool := {}
  let mut ours : Nat := 0
  let mut bad : Array Name := #[]
  let mut axSeen : NameSet := {}
  let mut inProg : NameSet := {}
  for (n0, _) in env.constants.map₁.toList do
    let isOurs := match modOf n0 with | some m => m.toString.startsWith "Fl4" | none => false
    unless isOurs do continue
    ours := ours + 1
    -- iterative DFS: (name, expanded?)
    let mut st : Array (Name × Bool) := #[(n0, false)]
    while st.size > 0 do
      let (n, done) := st.back!
      st := st.pop
      if memo.contains n then continue
      if !done && inProg.contains n then continue
      match env.find? n with
      | none => memo := memo.insert n false
      | some ci =>
        if let .axiomInfo _ := ci then
          axSeen := axSeen.insert n
          memo := memo.insert n (!ok.contains n)
        else
          let us := ci.getUsedConstantsAsSet.toList
          if done then
            memo := memo.insert n (us.any fun u => memo.getD u false)
          else
            inProg := inProg.insert n
            st := st.push (n, true)
            for u in us do
              unless memo.contains u do st := st.push (u, false)
    if memo.getD n0 false then bad := bad.push n0
  IO.println s!"AXALLA64 constants {ours} bad {bad.size} axioms-seen {axSeen.toList}"
  IO.println s!"AXALLA64 first-bad {(bad.toList.take 30)}"
