/-- **`IoaRel` at the witness**: `warI1`'s one IOAPIC of 24 pins is `fInitASt`'s (`init_arch_state`). -/
theorem warI1_ioaRel : IoaRel warI1 fInitASt := by
  refine ⟨1#u64, fun _ => rfl, rfl, fun a i hi => ⟨24#u64, ?_, rfl, by decide⟩⟩
  have e : (1#u64).val = 1 := rfl
  have h1 : i.val < 1 := by omega
  show ok (if i.val < 1 then 24#u64 else 0#u64) = ok 24#u64
  rw [if_pos h1]

/-- **`warI` does not meet `IoaRel` at the witness** (it answers 0 IOAPICs; the spec boots with 1). -/
theorem warI_not_ioaRel : ¬ IoaRel warI fInitASt := by
  rintro ⟨nA, hn, hb, -⟩
  have h0 : warI.num_ioapics fInitASt.machineState = ok 0#u64 := rfl
  have e : nA = 0#u64 := eq_of_ok_eq ((hn _).symm.trans h0)
  have h1 : fInitASt.archState.x64NumIoapics = 1 := rfl
  subst e
  rw [h1] at hb
  exact absurd hb (by decide)

/-- **`JReachU38` at the witness** (arch `warI1`, `ipiMR`). -/
theorem jReachU38_w0I1 : JReachU38 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  ⟨jReachU34_w0I1, warI1_ioaRel⟩

/-- **Every premise of `kernel_entry_reachU38` at the witness platform** (`wst`, `warI1`, `wAR`, `ipiMR`) with
its start state `jReachU38_w0I1`, under `OpaqueWK` [P]. Only U38's per-entry [J]s remain. -/
theorem u38_w0I1 (O : OpaqueWK) :
    ARIface warI1 wAR ∧ P0.ArchTotal warI1 ∧ Fl4Spec.numDomains = 1 ∧ MachPlatF warI1 ipiMR ∧ IpiF warI1 ipiMR ∧
      MRKeepD warI1 ipiMR ∧ MRKeepIo warI1 ipiMR ∧ MRKeepIoapic warI1 ipiMR ∧
      (∀ a c, wAR a c → warI1.irq_pending a ⦃ r => wAR r.2 c ⦄) ∧ IrqPlatK warI1 wAR ∧ TimeAgree warI1 ∧
      Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      (∀ a v, warI1.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) ∧
      ArchRefines warI1 wAR ∧ PortInValMR warI1 ipiMR ∧ P1.StoreExt wst ∧
      SetDlDetR (A := Fl4Spec.MachineState) ipiMR ∧
      JReachU38 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, _⟩ := u34_w0I1 O
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, jReachU38_w0I1⟩

/-- **`IoaMap` at `warI1`**: its routing always answers `true` (`modelArch`'s). -/
theorem warI1_ioaMap : IoaMap warI1 :=
  ⟨fun a _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨a, rfl⟩, fun a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨a, rfl⟩⟩

/-- **Every premise of `kernel_entry_reachU39` at the witness platform** with its start state, under
`OpaqueWK` [P]: U38's (`u38_w0I1`) and `IoaMap` (`warI1_ioaMap`). Only U39's per-entry [J]s remain. -/
theorem u39_w0I1 (O : OpaqueWK) :
    ARIface warI1 wAR ∧ P0.ArchTotal warI1 ∧ Fl4Spec.numDomains = 1 ∧ MachPlatF warI1 ipiMR ∧ IpiF warI1 ipiMR ∧
      MRKeepD warI1 ipiMR ∧ MRKeepIo warI1 ipiMR ∧ MRKeepIoapic warI1 ipiMR ∧
      (∀ a c, wAR a c → warI1.irq_pending a ⦃ r => wAR r.2 c ⦄) ∧ IrqPlatK warI1 wAR ∧ TimeAgree warI1 ∧
      Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      (∀ a v, warI1.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) ∧
      ArchRefines warI1 wAR ∧ PortInValMR warI1 ipiMR ∧ P1.StoreExt wst ∧
      SetDlDetR (A := Fl4Spec.MachineState) ipiMR ∧ IoaMap warI1 ∧
      JReachU38 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := u38_w0I1 O
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, warI1_ioaMap, h18⟩

end

end Fl4Proofs.P3.JBoot
