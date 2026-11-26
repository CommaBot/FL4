import Fl4Proofs.P3.XTopJointKEntryU44
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU44
#print axioms Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU43_of44
#print axioms Fl4Proofs.P3.SInvR.G5.KDispHypsKVU44.toU39
#print axioms Fl4Proofs.P3.SInvR.G5.KDispHypsKVU39.toU44
#print axioms Fl4Proofs.P3.SInvR.G5.JPathMEU44.toU30
#print axioms Fl4Proofs.P3.SInvR.G5.JPathMEU30.toU44
#print axioms Fl4Proofs.P3.KCfgFL4.fan'
#print axioms Fl4Proofs.P3.KCfgFL4.rcb'
#print axioms Fl4Proofs.P3.kCfgFL4_consistent
-- (1) U44's cone; (2) the per-entry path record KDispHypsKVU44 no longer reaches the config constants
open Lean in
run_cmd do
  let env ← getEnv
  let closure (roots : List Name) (useVal : Bool) : NameSet := Id.run do
    let mut seen : NameSet := {}
    let mut wl := roots
    repeat
      match wl with
      | [] => break
      | n :: rest =>
        wl := rest
        if seen.contains n then continue
        seen := seen.insert n
        if let some ci := env.find? n then
          let ds := ci.type.getUsedConstants ++ (if useVal then (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[]) else #[])
          for d in ds do
            if !seen.contains d then wl := d :: wl
    return seen
  let c := closure [``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU44] true
  let c43 := closure [``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU43] true
  logInfo m!"allowOpaque=true walk: U43 cone {c43.size}"
  let chain := [``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU43, ``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU42,
    ``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU40, ``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU39,
    ``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU36]
  logInfo m!"U44 proof cone contains U43/U42/U40/U39/U36: {chain.map c.contains}"
  logInfo m!"U44 cone {c.size} constants; KDispHypsKVU39 in U44 type: {(env.find? ``Fl4Proofs.P3.SInvR.G5.kernel_entry_reachU44).get!.type.getUsedConstants.contains ``Fl4Proofs.P3.SInvR.G5.KDispHypsKVU39}"
  let k := closure [``Fl4Proofs.P3.SInvR.G5.KDispHypsKVU44] true
  logInfo m!"KDispHypsKVU44 closure {k.size}; reaches retypeFanOutLimit: {k.contains ``Fl4Spec.retypeFanOutLimit}, resetChunkBits: {k.contains ``Fl4Spec.resetChunkBits}, JPathMEU30: {k.contains ``Fl4Proofs.P3.SInvR.G5.JPathMEU30}"
