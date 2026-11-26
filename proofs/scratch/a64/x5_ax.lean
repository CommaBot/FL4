import Fl4Proofs.P1.QueueEntryGapsX5
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let extra : List Name := [``Fl4Proofs.P1.WalkOK, ``Fl4Proofs.P1.VaOK, ``Fl4Proofs.P1.VaOK.null,
    ``Fl4Proofs.P1.vspace.unmap_page_table.vs5, ``Fl4Proofs.P1.vspace.unmap_page_directory.vs5,
    ``Fl4Proofs.P1.vspace.unmap_page.vs5]
  let mut n : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  for (c, _) in env.constants.map₁.toList do
    if (`Fl4Proofs.P1.X5).isPrefixOf c || extra.contains c then
      n := n + 1
      let axs ← Lean.collectAxioms c
      for a in axs do
        if !(ok.contains a) then bad := bad.push (c, a)
  logInfo (s!"x86 X5 constants checked: {n}; outside propext/Classical.choice/Quot.sound: {bad.size} {(bad.toList.take 20).map (fun p => (p.1, p.2))}" : String)
#print axioms Fl4Proofs.P1.vspace.unmap_page.vs5
#print axioms Fl4Proofs.P1.X5.fin_vs
#print axioms Fl4Proofs.P1.X5.delGaps_of
#print axioms Fl4Proofs.P1.X5.decGap_cnode2
#print axioms Fl4Proofs.P1.X5.decGap_irqHandler
#print axioms Fl4Proofs.P1.X5.decGap_thread
#print axioms Fl4Proofs.P1.X5.decGap_vspace
#print axioms Fl4Proofs.P1.X5.gaps5
#print axioms Fl4Proofs.P1.X5.kernel_entry.entry_of4
#print axioms Fl4Proofs.P1.X5.kernel_entry.entry_of10
