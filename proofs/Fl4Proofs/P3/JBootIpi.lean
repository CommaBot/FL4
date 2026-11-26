/-
P3 (line jboot, gen 1): **the IPI vectors 126 / 127 in P3's platform premises** (wit.md finding, `OpaqueW.ipi`).

* **`ipi_forces_oracle`**: `MachPlat` (the platform reports the spec's line; `mask_irq` can unmask *any* line
  `< 256`) and `IrqPlatA.noIpi` (at *every* arch state, `take_pending_irq` never gives 126 / 127) together with one
  `MR`-related pair `(a, ms)` force the spec's opaque `irqOracle` to avoid 126 and 127 at every position from
  `ms.irqState + 1` on. So `kernel_entry_reachU17V`'s platform premises, with a start state (`MR a σ.machineState`
  is part of `JReachU3.start`), silently assume a fact about an `opaque` spec constant.

**Verdict: a modelling bug in P3's platform premises, not a real platform constraint.** The spec's `maxIRQ` is 125:
the spec never has an IRQ handler for 126 / 127 (`IntInv`'s handler bound `irq ≤ maxIRQ`), so the kernel never
unmasks them, and with them masked `getActiveIRQ` never reports them, whatever the oracle. The premises are
over-quantified in two places: `MachPlat.mask` lets the kernel *unmask* every line `< 256`, and `IrqPlatA.noIpi`
holds at every arch state rather than at related ones.

**Proposed fix** (`MachPlatF`, `IpiF`; not yet wired into the P3 tops): split `MachPlat.mask` into `mask1`
(masking, any line `< 256`) and `mask0` (unmasking, lines `≤ maxIRQ` only: the one unmask caller,
XTopJointKEntry39's `IRQAckIRQ`, has a handler cap, whose IRQ is `≤ maxIRQ` by `IntInv`), and state `noIpi` at
`MR`-related states. Then
* **`modelArch_machPlatF`** / **`modelArch_ipiF`**: the model arch with `ipiMR := modelMR ∧ 126, 127 masked` meets
  both, **with no assumption on `irqOracle`** (`OpaqueW.ipi` is not needed);
* `MachPlat.toF` / `IrqPlatA.toIpiF`: the fix only weakens the premises; `MachPlatF.mask` is `MachPlat.mask`'s
  shape for lines `≤ maxIRQ`, what the unmask caller reads.

No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.XTopJointMRPP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Spec

noncomputable section

section
variable {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- The line `w` unmasked in `ms`. -/
def unmaskAt (ms : Fl4Spec.MachineState) (w : U64) : Fl4Spec.MachineState :=
  { ms with irqMasks := Function.update ms.irqMasks (w.bv.setWidth 8) false }

theorem toNat_sw8 (w : U64) (hw : w.val < 256) : (w.bv.setWidth 8).toNat = w.val := by
  rw [BitVec.toNat_setWidth]
  show w.bv.toNat % 2 ^ 8 = w.bv.toNat
  exact Nat.mod_eq_of_lt (by have : w.bv.toNat = w.val := rfl; omega)

theorem sw8_ne {w : U64} {v : Irq} (hw : w.val < 256) (hv : v.toNat ≠ w.val) : w.bv.setWidth 8 ≠ v := by
  intro e
  have e2 := congrArg BitVec.toNat e
  rw [toNat_sw8 w hw] at e2
  exact hv e2.symm

theorem gaiLine_unmask (ms : Fl4Spec.MachineState) (w : U64) (hw : w.val < 255)
    (ho : irqOracle (ms.irqState + 1) = w.bv.setWidth 8) :
    gaiLine true (unmaskAt ms w) = some (w.bv.setWidth 8) := by
  have h1 : w.bv.setWidth 8 ≠ (0xFF : Irq) :=
    sw8_ne (by omega) (by have : (0xFF : Irq).toNat = 255 := rfl; omega)
  have h2 : (w.bv.setWidth 8) ∉ nonKernelIRQs := fun h => h
  unfold gaiLine unmaskAt
  simp only
  rw [ho, Function.update_self]
  rw [if_neg (by simp [h2]; exact h1)]

/-- One position: an `MR`-related pair, unmasking line `w ∈ {126, 127}` and taking, shows the oracle's next line is
not `w`. -/
theorem ipi_forces_oracle1 (hM : MachPlat arI MR) (hI : IrqPlatA arI AR) {a : A} {ms : Fl4Spec.MachineState}
    (hR : MR a ms) (w : U64) (hw : w.val = 126 ∨ w.val = 127) :
    (irqOracle (ms.irqState + 1)).toNat ≠ w.val := by
  intro ho
  have hsw := toNat_sw8 w (by omega)
  have ho' : irqOracle (ms.irqState + 1) = w.bv.setWidth 8 := BitVec.eq_of_toNat_eq (by rw [hsw, ho])
  obtain ⟨a', -, hR'⟩ := spec_exists (hM.mask a w false ms hR (by omega))
  obtain ⟨r, -, ⟨-, hi, -⟩, hn⟩ := spec_exists (WP.spec_and (hM.take a' _ hR') (hI.noIpi a'))
  have hv := hi _ (gaiLine_unmask ms w (by omega) ho')
  omega

/-- **`MachPlat` with `IrqPlatA` forces the opaque oracle to avoid the IPI vectors** (module docstring): from any
`MR`-related pair, at every later oracle position. -/
theorem ipi_forces_oracle (hM : MachPlat arI MR) (hI : IrqPlatA arI AR) :
    ∀ (k : Nat) {a : A} {ms : Fl4Spec.MachineState}, MR a ms →
      (irqOracle (ms.irqState + 1 + k)).toNat ≠ 126 ∧ (irqOracle (ms.irqState + 1 + k)).toNat ≠ 127 := by
  intro k
  induction k with
  | zero =>
    intro a ms hR
    simp only [Nat.add_zero]
    exact ⟨ipi_forces_oracle1 hM hI hR 126#u64 (Or.inl rfl), ipi_forces_oracle1 hM hI hR 127#u64 (Or.inr rfl)⟩
  | succ k ih =>
    intro a ms hR
    obtain ⟨r, -, -, -, hR'⟩ := spec_exists (hM.take a ms hR)
    have h := ih hR'
    have e : (gaiState ms).irqState + 1 + k = ms.irqState + 1 + (k + 1) := by
      show ms.irqState + 1 + 1 + k = _; omega
    rwa [e] at h

/-! ## The proposed fix -/

variable (arI) in
/-- **`MachPlat` with the unmask restricted to the spec's IRQs** (module docstring; proposed replacement). -/
structure MachPlatF (MR : A → Fl4Spec.MachineState → Prop) : Prop where
  now : ∀ a ms, MR a ms → arI.now a ⦃ r => r.1.bv = gctVal ms ∧ MR r.2 (gctState ms) ⦄
  irqPending : ∀ a ms, MR a ms → arI.irq_pending a ⦃ r =>
    (r.1 = true ↔ gaiLine true ms ≠ none) ∧ MR r.2 (gaiState ms) ⦄
  take : ∀ a ms, MR a ms → arI.take_pending_irq a ⦃ r =>
    (r.1 = syscall.NO_IRQ ↔ gaiLine true ms = none) ∧
    (∀ i, gaiLine true ms = some i → r.1.val = i.toNat) ∧ MR r.2 (gaiState ms) ⦄
  /-- Masking: any line. -/
  mask1 : ∀ a (w : U64) ms, MR a ms → w.val < 256 → arI.mask_irq a w true ⦃ a' =>
    MR a' { ms with irqMasks := Function.update ms.irqMasks (w.bv.setWidth 8) true } ⦄
  /-- Unmasking: the spec's IRQs only (`≤ maxIRQ = 125`). -/
  mask0 : ∀ a (w : U64) ms, MR a ms → w.val ≤ 125 → arI.mask_irq a w false ⦃ a' =>
    MR a' { ms with irqMasks := Function.update ms.irqMasks (w.bv.setWidth 8) false } ⦄
  ack : ∀ a w ms, MR a ms → arI.ack_irq a w ⦃ a' => MR a' ms ⦄
  frame : ∀ a ms ms', MR a ms → ms'.irqMasks = ms.irqMasks → ms'.irqState = ms.irqState →
    ms'.timeState = ms.timeState → ms'.lastMachineTime = ms.lastMachineTime → MR a ms'

variable (arI) in
/-- **`IrqPlatA.noIpi` at related states** (module docstring; proposed replacement). -/
def IpiF (MR : A → Fl4Spec.MachineState → Prop) : Prop :=
  ∀ a ms, MR a ms → arI.take_pending_irq a ⦃ r => r.1.val ≠ 126 ∧ r.1.val ≠ 127 ⦄

/-- `MachPlat` gives `MachPlatF` (the fix only weakens the premise). -/
theorem MachPlat.toF (h : MachPlat arI MR) : MachPlatF arI MR :=
  ⟨h.now, h.irqPending, h.take, fun a w ms hR hw => h.mask a w true ms hR hw,
    fun a w ms hR hw => h.mask a w false ms hR (by omega), h.ack, h.frame⟩

/-- `IrqPlatA.noIpi` gives `IpiF`. -/
theorem IrqPlatA.toIpiF (h : IrqPlatA arI AR) : IpiF arI MR := fun a _ _ => h.noIpi a

/-- `MachPlatF`'s mask of an IRQ handler's line (`IntInv`: `irq ≤ maxIRQ`), in `MachPlat.mask`'s shape: what the
unmask caller (XTopJointKEntry39, `IRQAckIRQ`) needs. -/
theorem MachPlatF.mask (h : MachPlatF arI MR) (a : A) (w : U64) (m : Bool) (ms : Fl4Spec.MachineState)
    (hR : MR a ms) (hw : w.val ≤ 125) : arI.mask_irq a w m ⦃ a' =>
      MR a' { ms with irqMasks := Function.update ms.irqMasks (w.bv.setWidth 8) m } ⦄ := by
  cases m
  · exact h.mask0 a w ms hR hw
  · exact h.mask1 a w ms hR (by omega)

end

/-! ## The model meets the fix with no oracle assumption -/

/-- The model's relation with the IPI vectors masked. -/
def ipiMR (a ms : Fl4Spec.MachineState) : Prop :=
  modelMR a ms ∧ ms.irqMasks 126 = true ∧ ms.irqMasks 127 = true

theorem gaiLine_some_unmasked {ms : Fl4Spec.MachineState} {i : Irq} (h : gaiLine true ms = some i) :
    ms.irqMasks i = false := by
  unfold gaiLine at h
  split_ifs at h with hc
  cases h
  simp only [not_or] at hc
  simpa using hc.1

theorem upd_keep (f : Irq → Bool) (w : U64) (m : Bool) (v : Irq) (hv : f v = true) (hw : w.val ≤ 125)
    (hv' : v.toNat = 126 ∨ v.toNat = 127) : Function.update f (w.bv.setWidth 8) m v = true := by
  rw [Function.update_of_ne (sw8_ne (by omega) (by omega)).symm]; exact hv

theorem upd_true (f : Irq → Bool) (x v : Irq) (hv : f v = true) : Function.update f x true v = true := by
  rw [Function.update_apply]; split_ifs <;> simp_all

/-- **The model arch meets `MachPlatF` at `ipiMR`.** -/
theorem modelArch_machPlatF : MachPlatF modelArch ipiMR where
  now a ms := fun ⟨h, h6, h7⟩ => WP.spec_mono (modelArch_machPlat.now a ms h) fun _ ⟨e, hr⟩ => ⟨e, hr, h6, h7⟩
  irqPending a ms := fun ⟨h, h6, h7⟩ =>
    WP.spec_mono (modelArch_machPlat.irqPending a ms h) fun _ ⟨e, hr⟩ => ⟨e, hr, h6, h7⟩
  take a ms := fun ⟨h, h6, h7⟩ =>
    WP.spec_mono (modelArch_machPlat.take a ms h) fun _ ⟨e1, e2, hr⟩ => ⟨e1, e2, hr, h6, h7⟩
  mask1 a w ms := fun ⟨h, h6, h7⟩ hw =>
    WP.spec_mono (modelArch_machPlat.mask a w true ms h hw) fun _ hr =>
      ⟨hr, upd_true _ _ _ h6, upd_true _ _ _ h7⟩
  mask0 a w ms := fun ⟨h, h6, h7⟩ hw =>
    WP.spec_mono (modelArch_machPlat.mask a w false ms h (by omega)) fun _ hr =>
      ⟨hr, upd_keep _ w false 126 h6 hw (Or.inl rfl), upd_keep _ w false 127 h7 hw (Or.inr rfl)⟩
  ack a w ms := fun ⟨h, h6, h7⟩ => WP.spec_mono (modelArch_machPlat.ack a w ms h) fun _ hr => ⟨hr, h6, h7⟩
  frame a ms ms' := fun ⟨h, h6, h7⟩ e1 e2 e3 e4 =>
    ⟨modelArch_machPlat.frame a ms ms' h e1 e2 e3 e4, by rw [e1]; exact h6, by rw [e1]; exact h7⟩

/-- **The model arch meets `IpiF` at `ipiMR`, whatever the oracle** (module docstring). -/
theorem modelArch_ipiF : IpiF modelArch ipiMR := by
  rintro a ms ⟨⟨h1, -, -, -⟩, h6, h7⟩
  show (ok (modelTake a, gaiState a) : Result (U64 × Fl4Spec.MachineState)) ⦃ r => r.1.val ≠ 126 ∧ r.1.val ≠ 127 ⦄
  rw [WP.spec_ok]
  show (modelTake a).val ≠ 126 ∧ (modelTake a).val ≠ 127
  cases e : gaiLine true a with
  | none =>
    rw [modelTake_none e]
    have hn : syscall.NO_IRQ.val = 2 ^ 64 - 1 := by
      show syscall.NO_IRQ.bv.toNat = _
      rw [no_irq_bv, BitVec.toNat_allOnes]
    rw [hn]
    exact ⟨by norm_num, by norm_num⟩
  | some i =>
    rw [(modelTake_some e).2]
    have hm := gaiLine_some_unmasked e
    rw [h1] at hm
    have n6 : i ≠ 126 := fun h => by rw [h, h6] at hm; cases hm
    have n7 : i ≠ 127 := fun h => by rw [h, h7] at hm; cases hm
    exact ⟨fun h => n6 (BitVec.eq_of_toNat_eq (by rw [h]; rfl)),
      fun h => n7 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))⟩

end

end Fl4Proofs.P3
