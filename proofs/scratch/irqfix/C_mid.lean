section
open Fl4Proofs.P3.SInvR.G4
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **[J] The IRQ ack's unmask at an entry state** (module docstring): unmasking the line of an IRQ
handler cap held in a CNode slot keeps `MR`. Under U32's `MachPlat` it holds (`IrqAckU.of_machPlat`);
under `MachPlatF` it is l4v `valid_cap`'s `irq ≤ maxIRQ` for the handler caps (`IrqAckU.of_bound`). -/
def IrqAckU (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (s : S) (ar : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ (sl : Fl4Spec.CslotPtr) (irq : U64), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
    capAt (L.mem s) (cslotAddr sl) = ok (.IrqHandler irq) → irq.val < 128 → MR ar σ.machineState →
    arI.mask_irq ar irq false ⦃ a' =>
      MR a' { σ.machineState with irqMasks := Function.update σ.machineState.irqMasks (irq.bv.setWidth 8) false } ⦄

/-- `JDecMRLK` with the IRQ ack's `IrqAckU`. -/
def JDecMRLKQ (K : capability.Cap → U64 → List U64 → Prop) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  JDecMRLK (L := L) arI K AR MR Z H Cs D s ar σ ct ∧ IrqAckU (L := L) arI MR Z s ar σ

/-- `JDecMRL2` with the IRQ ack's `IrqAckU`. -/
def JDecMRL2Q (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) (Z : XSets) (H : P1.Heap)
    (Cs D : Set U64) (s : S) (ar : A) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  JDecMRL2 (L := L) arI AR MR Z H Cs D s ar σ ct ∧ IrqAckU (L := L) arI MR Z s ar σ

variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

variable {arI} in
/-- **`IrqAckU` under U32's `MachPlat`** (any line `< 256` may be unmasked). -/
theorem IrqAckU.of_machPlat (hM : MachPlat arI MR) {s : S} {ar : A} {σ : Fl4Spec.State Unit} :
    IrqAckU (L := L) arI MR Z s ar σ :=
  fun _ irq _ _ h128 hR => hM.mask ar irq false _ hR (by omega)

variable {arI} in
/-- **`IrqAckU` under `MachPlatF` from l4v `valid_cap`'s bound** (every handler cap's line `≤ maxIRQ`). -/
theorem IrqAckU.of_bound (hM : MachPlatF arI MR) {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (hB : ∀ (sl : Fl4Spec.CslotPtr) (irq : U64), (∃ p, sl.1 = p.bv ∧ Z.th p = some (.cnode sl.2.length)) →
      capAt (L.mem s) (cslotAddr sl) = ok (.IrqHandler irq) → irq.val ≤ 125) :
    IrqAckU (L := L) arI MR Z s ar σ :=
  fun sl irq hsl hc _ hR => hM.mask0 ar irq _ hR (hB sl irq hsl hc)
