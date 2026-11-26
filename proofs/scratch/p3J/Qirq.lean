/-- **`IrqRel` at the witness** (gen 7: lines 125 ↔ `IRQ_TIMER` / `irqTimer`, 126 / 127 ↔ `IRQ_IPI` /
`irqReserved`, every other line zero ↔ inactive; the node: `fInitASt_irqNode`). -/
theorem w0_irqRel : IrqRel (wL.mem w0) (wL.ksb w0) fInitASt := by
  refine ⟨fun i hi => ?_, fun i hi => fInitASt_irqNode i hi⟩
  have hv := irqStA_val (kb := fkb) fkb_lt hi
  rw [fkb_val] at hv
  rw [ksb_w0, mem_al hv (by omega)]
  generalize i.val = n at hi ⊢
  change ipiIS (BitVec.ofNat 8 n) = _
  unfold ipiIS
  rcases (by omega : n = 125 ∨ n = 126 ∨ n = 127 ∨ n < 125) with rfl | rfl | rfl | hlt
  · simp [Function.update_apply, img, irqSt]
  · simp [Function.update_apply, img, irqSt]
  · simp [Function.update_apply, img, irqSt]
  · rw [show img (18446744071562133504 + 224 + 8 * n) = 0#u64 by img0]
    have h5 : BitVec.ofNat 8 n ≠ 125 := by intro h; have := congrArg BitVec.toNat h; simp at this; omega
    have h6 : BitVec.ofNat 8 n ≠ 126 := by intro h; have := congrArg BitVec.toNat h; simp at this; omega
    have h7 : BitVec.ofNat 8 n ≠ 127 := by intro h; have := congrArg BitVec.toNat h; simp at this; omega
    rw [Function.update_of_ne h7, Function.update_of_ne h6, Function.update_of_ne h5]
    simp [irqSt, initASt]

/-- **FL4's boot IRQ-state words** (`boot::init_irq_states`): line 125 `IRQ_TIMER` (2), 126 / 127 `IRQ_IPI` (3). -/
theorem w0_irqWords : wL.mem w0 (irqStA fkb 125#u64) = 2#u64 ∧ wL.mem w0 (irqStA fkb 126#u64) = 3#u64 ∧
    wL.mem w0 (irqStA fkb 127#u64) = 3#u64 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [mem_al (irqStA_val (kb := fkb) fkb_lt (by decide)) (by rw [fkb_val]; omega), fkb_val]
    simp [img]

