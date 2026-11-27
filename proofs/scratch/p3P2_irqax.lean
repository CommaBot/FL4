import Fl4Proofs.P3.ArchIrqNarrowGen
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for t in [``Fl4ProofsI.P3.SInvR.G5.kernel_entry_reachU31] do
    let some ci := env.find? t | IO.println "missing"
    IO.println s!"STMT {t}: {(ci.type.getUsedConstants.filter (fun n => (`Fl4ProofsI).isPrefixOf n)).toList}"
  for n in [``Fl4ProofsI.P3.SInvR.G5.KDispHypsKVU31, ``Fl4ProofsI.P3.SInvR.G5.JEntryAtR7S] do
    let some (.inductInfo ii) := env.find? n | IO.println s!"no {n}"
    for k in ii.ctors do
      let some kc := env.find? k | pure ()
      IO.println s!"CTOR {k}: {(kc.type.getUsedConstants.filter (fun n => (`Fl4ProofsI).isPrefixOf n)).toList}"
#print axioms Fl4ProofsI.P3.SInvR.G5.kernel_entry_reachU31
#print axioms Fl4Proofs.P3.irq_ioapic_refinesN
#print axioms Fl4Proofs.P3.irq_remap_refinesN
#print axioms Fl4Proofs.P3.irq_ioapic_refinesMN
#print axioms Fl4Proofs.P3.irq_remap_refinesMN
