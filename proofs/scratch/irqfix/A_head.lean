/-
P3 (line irqfix, the 126 / 127 fix wired in, part A): **the platform records of `kernel_entry_reachU33`'s
proof and the IRQ control decode re-proved on them.**

JBootIpi (`ipi_forces_oracle`): `MachPlat` (unmasking any line `< 256`) with `IrqPlatA.noIpi` (no IPI
vector at *any* arch state) and one `MR` pair force the opaque `irqOracle` off 126 / 127. The fix
(JBootIpi's `MachPlatF`, `IpiF`) unmasks only lines `≤ maxIRQ = 125` and asks `noIpi` at `MR`-related
states. This module gives the records the transport (IrqFixGenB, IrqFixGen) puts in place of
`MachPlat`, `IrqPlatA` and IrqCtlMR's `MaskMR`:
* `MachPlatT`: `MachPlat`'s fields in `MachPlat`'s order, `mask` asking `w < 256` for a mask and
  `w < 126` for an unmask (`cond m 256 126`: for a literal `m = true` this is `MachPlat.mask`'s
  hypothesis up to reduction, so every masking user is copied unchanged), plus `noIpi : IpiF arI MR`
  (JBootIpi). `MachPlatF.toT` / `MachPlatT.toF`: it is `MachPlatF ∧ IpiF`.
* `IrqPlatK`: `IrqPlatA` without `noIpi` [P].
* `MaskMRF`: `MaskMR` with the same restriction (`MachPlatT.mask` is one).
The unmasking users of `MaskMR` are FL4's IRQ control issues (`invoke_irq_control`, `IRQ_SIGNAL`),
whose lines the decodes bound by `ISA_MAX = 15` and `USER_MAX = 123`: `invoke_mrMQ` asks `irq < 126`,
and its four callers and `irq_issue_refinesMQ` (IrqCtlMR / ArchIrqNarrow, verbatim copies) pass the
decode's bound (`hz126`, `hirq6`) where the originals passed `z < 256`.

No premise of the tops is added here; no sorry.
-/
import Fl4Proofs.P3.ArchIrqNarrow
import Fl4Proofs.P3.JBootIpi
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {A : Type} {arI : machine.Arch A}

variable (arI) in
/-- **`MachPlat` with unmasking only below 126 and `noIpi` at related states** [P] (module docstring;
the platform record of U33's proof, equal to `MachPlatF ∧ IpiF`). -/
structure MachPlatT (MR : A → Fl4Spec.MachineState → Prop) : Prop where
  now : ∀ a ms, MR a ms → arI.now a ⦃ r => r.1.bv = gctVal ms ∧ MR r.2 (gctState ms) ⦄
  irqPending : ∀ a ms, MR a ms → arI.irq_pending a ⦃ r =>
    (r.1 = true ↔ gaiLine true ms ≠ none) ∧ MR r.2 (gaiState ms) ⦄
  take : ∀ a ms, MR a ms → arI.take_pending_irq a ⦃ r =>
    (r.1 = syscall.NO_IRQ ↔ gaiLine true ms = none) ∧
    (∀ i, gaiLine true ms = some i → r.1.val = i.toNat) ∧ MR r.2 (gaiState ms) ⦄
  /-- Masking any line `< 256`, unmasking a line `≤ maxIRQ = 125`. -/
  mask : ∀ a (w : U64) m ms, MR a ms → w.val < cond m 256 126 → arI.mask_irq a w m ⦃ a' =>
    MR a' { ms with irqMasks := Function.update ms.irqMasks (w.bv.setWidth 8) m } ⦄
  ack : ∀ a w ms, MR a ms → arI.ack_irq a w ⦃ a' => MR a' ms ⦄
  frame : ∀ a ms ms', MR a ms → ms'.irqMasks = ms.irqMasks → ms'.irqState = ms.irqState →
    ms'.timeState = ms.timeState → ms'.lastMachineTime = ms.lastMachineTime → MR a ms'
  /-- JBootIpi's `IpiF`: no IPI vector from an `MR`-related state. -/
  noIpi : IpiF arI MR

variable (arI) in
/-- **`IrqPlatA` without `noIpi`** [P]: `take_pending_irq` and `ack_irq` keep the CR3 relation. -/
structure IrqPlatK (AR : A → Fl4Spec.Cr3 → Prop) : Prop where
  takeAR : ∀ a c, AR a c → arI.take_pending_irq a ⦃ r => AR r.2 c ⦄
  ackAR : ∀ a i c, AR a c → arI.ack_irq a i ⦃ a' => AR a' c ⦄

variable (arI) in
/-- `MachPlatT.mask`'s shape (IrqCtlMR's `MaskMR`, unmasking below 126). -/
def MaskMRF (MR : A → Fl4Spec.MachineState → Prop) : Prop :=
  ∀ a (w : U64) m ms, MR a ms → w.val < cond m 256 126 → arI.mask_irq a w m ⦃ a' =>
    MR a' { ms with irqMasks := Function.update ms.irqMasks (w.bv.setWidth 8) m } ⦄

variable {MR : A → Fl4Spec.MachineState → Prop} {AR : A → Fl4Spec.Cr3 → Prop}

/-- `MachPlatF` and `IpiF` give `MachPlatT`. -/
theorem MachPlatF.toT (h : MachPlatF arI MR) (hI : IpiF arI MR) : MachPlatT arI MR :=
  ⟨h.now, h.irqPending, h.take, fun a w m ms hR hw => by
    cases m
    · exact h.mask0 a w ms hR (by simp at hw; omega)
    · exact h.mask1 a w ms hR (by simpa using hw), h.ack, h.frame, hI⟩

/-- `MachPlatT` gives `MachPlatF`. -/
theorem MachPlatT.toF (h : MachPlatT arI MR) : MachPlatF arI MR :=
  ⟨h.now, h.irqPending, h.take, fun a w ms hR hw => h.mask a w true ms hR (by simpa using hw),
    fun a w ms hR hw => h.mask a w false ms hR (by simp; omega), h.ack, h.frame⟩

/-- `MachPlat` with `IrqPlatA` gives `MachPlatT` (the fix only weakens the premises). -/
theorem MachPlat.toT (h : MachPlat arI MR) (hI : IrqPlatA arI AR) : MachPlatT arI MR :=
  MachPlatF.toT (MachPlat.toF h) (IrqPlatA.toIpiF hI)

/-- `IrqPlatA` gives `IrqPlatK`. -/
theorem IrqPlatA.toK (h : IrqPlatA arI AR) : IrqPlatK arI AR := ⟨h.takeAR, h.ackAR⟩

end

theorem sig_inact_false : decide (interrupt.IRQ_SIGNAL = interrupt.IRQ_INACTIVE) = false := by
  unfold interrupt.IRQ_SIGNAL interrupt.IRQ_INACTIVE; decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {MR : A → Fl4Spec.MachineState → Prop}
