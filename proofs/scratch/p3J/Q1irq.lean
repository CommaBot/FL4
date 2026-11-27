/-- **`IrqRel` at `w1`** (gen 15 re-proof: the three IRQ-state words of FL4's boot layout are not among
`img1`'s twelve changed words, so `w1` reads `w0`'s there and `JBootQ.w0_irqRel` carries over). -/
theorem w1_irqRel : IrqRel (wL.mem w1) (wL.ksb w1) σ1 := by
  refine ⟨fun i hi => ?_, fun i hi => fInitASt_irqNode i hi⟩
  have hv := irqStA_val (kb := fkb) fkb_lt hi
  rw [fkb_val] at hv
  have h0 := w0_irqRel.st i hi
  rw [ksb_w0, mem_al hv (by omega)] at h0
  rw [ksb_w1, mem1_al hv (by omega),
    show img1 (18446744071562133504 + 224 + 8 * i.val) = img (18446744071562133504 + 224 + 8 * i.val) by
      apply img1_old <;> omega]
  exact h0

