/-
P3 (line irqfix): **`kernel_entry_reachU33`**: `kernel_entry_reachU32` with the 126 / 127 platform
premises fixed (JBootIpi's finding: U32's `MachPlat` and `IrqPlatA` with one `MR` pair force the opaque
`irqOracle` off the IPI vectors, `ipi_forces_oracle`).

**Premise diff U32 → U33**
* `hM : MachPlat arI MR` ↦ `hM : MachPlatF arI MR` [P] (JBootIpi): masking any line `< 256`, unmasking
  only lines `≤ maxIRQ = 125`;
* new `hIp : IpiF arI MR` [P] (JBootIpi): `take_pending_irq` gives no IPI vector from an `MR`-related
  state (was `IrqPlatA.noIpi`, at every arch state);
* `hIA : IrqPlatA arI AR` ↦ `hIA : IrqPlatK arI AR` [P] (IrqFixA): `IrqPlatA` without `noIpi`;
* the syscall clause's per-entry decode premise `JDecMRLK … VtxK …` ↦ `JDecMRLK … VtxK … ∧ IrqAckU …`
  [J] (IrqFixC): at the dispatch state, unmasking the line of an IRQ handler cap in a CNode slot keeps
  `MR`. Needed by the IRQ ack (`IRQAckIRQ`, FL4 `mask_irq irq false`): FL4's handler cap only bounds
  `irq < 128`, and nothing U32 carries bounds it by `maxIRQ` (l4v `valid_cap`; SpecInvG5's `SpecIrqH`
  is not preserved anywhere). `IrqAckU.of_machPlat`: U32's `MachPlat` gives it;
  `IrqAckU.of_bound`: under `MachPlatF`, l4v's bound `irq ≤ 125` gives it.
Every other premise and the conclusion are U32's verbatim. [W] 0.

**U33 is at least as strong as U32**: `kernel_entry_reachU32_of33` proves U32's statement from U33
(`MachPlat.toF`, `IrqPlatA.toIpiF`, `IrqPlatA.toK`, `IrqAckU.of_machPlat`); `u33_premises_of_u32` lists
the premise implications. **The model meets U33's new platform premises with no oracle assumption**
(`modelArch_u33Plat`, at `ipiMR` = `modelMR` with 126, 127 masked: `MachPlatF`, `IpiF`, `MRKeepD`,
`MRKeepIo`, `MRKeepIoapic`; `modelArch_irqAckU` from the handler-cap bound), where U32's `MachPlat` +
`IrqPlatA` at any `MR` pair force the oracle (`ipi_forces_oracle`).

**Proof**: IrqFixGen's kernel-checked transport of U32's proof
(`Fl4ProofsQ.P3.SInvR.G5.kernel_entry_reachU32`), on `MachPlatT` = `MachPlatF ∧ IpiF` (`MachPlatF.toT`).
-/
import Fl4Proofs.P3.IrqFixGen
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- **U32's platform premises give U33's** (`MachPlat.toF`, `IrqPlatA.toIpiF`, `IrqPlatA.toK`,
`IrqAckU.of_machPlat`). -/
theorem u33_premises_of_u32 (hM : MachPlat arI MR) (hIA : IrqPlatA arI AR) :
    MachPlatF arI MR ∧ IpiF arI MR ∧ IrqPlatK arI AR ∧
      ∀ (Z : XSets) (s : S) (a : A) (σ : Fl4Spec.State Unit), IrqAckU (L := L) arI MR Z s a σ :=
  ⟨MachPlat.toF hM, IrqPlatA.toIpiF hIA, IrqPlatA.toK hIA, fun _ _ _ _ => IrqAckU.of_machPlat hM⟩

end

/-- **The model arch meets U33's new platform premises at `ipiMR`, whatever the oracle**
(`MachPlatF`, `IpiF`: JBootIpi; the three keep records: the model's ops leave the state). -/
theorem modelArch_u33Plat :
    MachPlatF modelArch ipiMR ∧ IpiF modelArch ipiMR ∧ MRKeepD modelArch ipiMR ∧
      MRKeepIo modelArch ipiMR ∧ MRKeepIoapic modelArch ipiMR :=
  ⟨modelArch_machPlatF, modelArch_ipiF, modelArch_mrKeepD ipiMR,
    ⟨fun _ _ _ _ h => by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h,
     fun _ _ _ _ _ h => by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h⟩,
    ⟨fun _ _ _ _ _ _ _ h => by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h,
     fun _ _ _ _ _ _ _ _ h => by show (ok _ : Result _) ⦃ _ ⦄; rw [WP.spec_ok]; exact h⟩⟩

/-- **`IrqAckU` for the model at `ipiMR`** from l4v `valid_cap`'s handler bound (`irq ≤ maxIRQ`). -/
theorem modelArch_irqAckU {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {Z : XSets} {s : S}
    {a : Fl4Spec.MachineState} {σ : Fl4Spec.State Unit}
    (hB : ∀ (sl : Fl4Spec.CslotPtr) (irq : U64), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
      capAt (L.mem s) (cslotAddr sl) = ok (.IrqHandler irq) → irq.val ≤ 125) :
    IrqAckU (L := L) modelArch ipiMR Z s a σ :=
  IrqAckU.of_bound modelArch_machPlatF hB

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)
