/-- **The witness starts `JReachU3` at `warI1` / `ipiMR`.** -/
theorem jReachU3_w0I1 : JReachU3 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  .start (jAtZ_w0I1 _) Zw_vx fInit_sinvX fInit_sinvIP fInit_ipiMR fInit_utPgR

/-- **`JReachU34` at the witness, arch `warI1`, at `ipiMR`.** -/
theorem jReachU34_w0I1 : JReachU34 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  ⟨⟨jReachU3_w0I1, fInit_gpmOut, fInit_idleVtS, fInit_devRangeS⟩, fInit_irqStB⟩

