/-- **The witness starts `JReachU3` at `warI1` / `ipiMR`.** -/
theorem jReachU3_w0I1 : JReachU3 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  .start (jAtZ_w0I1 _) Zw_vx fInit_sinvX fInit_sinvIP JBoot.fInit_ipiMR fInit_utPgR

/-- **`JReachU17` at the witness with FL4's boot IRQ layout.** -/
theorem jReachU17_w0I1 : JReachU17 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  ⟨jReachU3_w0I1, fInit_gpmOut, fInit_idleVtS, fInit_devRangeS⟩

/-- **`JReachU36I` there** (irqfix3's carried fact: `fInitIpi_irqCarry`). -/
theorem jReachU36I_w0I1 : JReachU36I (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  ⟨jReachU17_w0I1, fInitASt_eq_ipi ▸ SInvIB.fInitIpi_irqCarry⟩

/-- `IoaRel warI1` at this spec state (same IOAPIC counts as jboot's). -/
theorem warI1_ioaRelQ : IoaRel warI1 fInitASt := JBoot.warI1_ioaRel.frame rfl

/-- **`JReachU40` at the witness with FL4's boot IRQ layout** (no premise). -/
theorem jReachU40_w0I1 : JReachU40 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  ⟨jReachU36I_w0I1, warI1_ioaRelQ⟩

/-- The same start, stated at irqfix3's `SInvIB.fInitIpiASt`. -/
theorem jReachU40_ipi :
    JReachU40 (L := wL) warI1 wAR ipiMR w0 SInvIB.fInitIpiASt.machineState SInvIB.fInitIpiASt := by
  rw [← fInitASt_eq_ipi]; exact jReachU40_w0I1

/-- **Every premise of `kernel_entry_reachU40` at the witness platform with FL4's boot IRQ layout**, under
`OpaqueWK` [P]. Only U40's per-entry [J]s remain. -/
theorem u40_w0I1 (O : OpaqueWK) :
    ARIface warI1 wAR ∧ P0.ArchTotal warI1 ∧ Fl4Spec.numDomains = 1 ∧ MachPlatF warI1 ipiMR ∧ IpiF warI1 ipiMR ∧
      MRKeepD warI1 ipiMR ∧ MRKeepIo warI1 ipiMR ∧ MRKeepIoapic warI1 ipiMR ∧
      (∀ a c, wAR a c → warI1.irq_pending a ⦃ r => wAR r.2 c ⦄) ∧ IrqPlatK warI1 wAR ∧ TimeAgree warI1 ∧
      Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv ∧
      (∀ a v, warI1.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) ∧
      ArchRefines warI1 wAR ∧ PortInValMR warI1 ipiMR ∧ P1.StoreExt wst ∧
      SetDlDetR (A := Fl4Spec.MachineState) ipiMR ∧ IoaMap warI1 ∧
      JReachU40 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, _⟩ := JBoot.u39_w0I1 O
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, jReachU40_w0I1⟩

/-- **U34 / U38's start fails here** (FL4's line-126 word is `IRQ_IPI`; `irqStB_false_of_ipiWord`). -/
theorem not_jReachU34_w0 {a : MachineState} : ¬ JReachU34 (L := wL) warI1 wAR ipiMR w0 a fInitASt := by
  intro h
  exact irqStB_false_of_ipiWord w0_irqRel (by rw [ksb_w0]; exact w0_irqWords.2.1) h.2

end

end Fl4Proofs.P3.JBootQ
