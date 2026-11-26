/-
P3 (line p3J, gen 6): **`kernel_entry_reachU40`** = `kernel_entry_reachU39` with irqfix gen 3's start condition:
one top with irqfix3's boot-state fix and p3J's narrowings (U35 … U39).

* **`JReachU40 s a σ := JReachU36I s a σ ∧ IoaRel arI σ`** (`JReachU36I := JReachU17 ∧ IrqCarry`,
  XTopJointKEntryU36I; `IoaRel` [P] start condition, XTopJointKEntryU38).
* **Proof**: as irqfix3's `kernel_entry_reachU36I` (from U33, start `JReachU17`; `IrqCapBound` and the decode
  premise's `IrqAckU` from `IrqCarry`), but from the p3J transport's copy
  `Fl4ProofsJ.P3.SInvR.G5.kernel_entry_reachU33` (P3JGen: U33 on the narrowed path premises `JPathAtMU35`), the
  syscall clause's `KDispHypsKVU39` brought to the copy's `KDispHypsKVU32` by U39 → U38 (`IoaMap`) → U36
  (`IoaRel` at the dispatch state) → the copy's U35 (`toJ`) → the copy's U32 (`hA`). Exits: `IrqCarry` and
  `IoaRel` kept by every spec step (`SInvIB.kentry_irqCarry`, `EvOut.irqCarry`; `SInvIox.kentry_ioxV`,
  `EvOut.ioaRel`).

**Premise diff U39 → U40**: `hJ : JReachU38` ↦ `hJ : JReachU40` (`JReachU34 ∧ IoaRel` ↦ `JReachU36I ∧ IoaRel`;
weaker: `JReachU36I.of_U34`); conclusion U39's with every exit's `JReachU38` ↦ `JReachU40`. Every other premise
verbatim. New premises: none. [W] 0.

* **`kernel_entry_reachU39_of40`**: U39's statement, verbatim, from U40 (start by `IrqStB ⇒ IrqCarry`; exits'
  `IrqStB` by the spec-only preservation `SInvIB.kentry_irqStB` / `EvOut.irqStB`, as irqfix3's
  `kernel_entry_reachU34_of36I`).
* **`kernel_entry_reachU36I_of40`**: U36I's statement with two more hypotheses, `hMap : IoaMap arI` and
  `hIR : IoaRel arI σ` (U36I asks both only per entry, inside its syscall clause; as gen 4's
  `kernel_entry_reachU36_of38`). The syscall clause by `KDispHypsKVU32.toU35.toU36.toU38.toU39`.
* **`JReachU40.of_fInitIpi`**, **`fInitIpi_ioaStart`**: at irqfix3's `fInitIpiASt` (jboot's boot state with line
  125 `irqTimer`, 126 / 127 `irqReserved`, where `IrqStB` fails) the start's spec half `IrqCarry ∧ IoaRel` holds
  (`fInitIpi_irqCarry`; `IoaRel` framed from `fInitASt`, same `ioxV`); a `JReachU17` there gives `JReachU40`.

Named premises: U39's (XTopJointKEntryU39: U34's global platform [P]s, `IoaMap` [P], the start `JReachU40`
with `IoaRel` [P], the per-entry syscall [J]s `KDispHypsKVU39` / `JDecMRLK` / `KFinAtR13`, the events'
`KFinEv13`). No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU39
import Fl4Proofs.P3.XTopJointKEntryU36I
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states with irqfix3's carried IRQ fact and the backend's IOAPIC counts** (module
docstring). -/
abbrev JReachU40 (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  JReachU36I (L := L) arI AR MR s a σ ∧ IoaRel arI σ

variable {arI AR MR} in
/-- Every U39 start state is a U40 start state. -/
theorem JReachU40.of_U38 {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU38 (L := L) arI AR MR s a σ) :
    JReachU40 (L := L) arI AR MR s a σ := ⟨⟨hJ.1.1, Or.inl hJ.1.2⟩, hJ.2⟩

variable {arI} in
/-- **The start's spec half at irqfix3's boot-like state** (126 / 127 reserved): `IrqCarry` and `IoaRel`
(this one from `fInitASt`'s: `fInitIpiASt` changes only the interrupt states). -/
theorem fInitIpi_ioaStart (h : IoaRel arI JBoot.fInitASt) :
    SInvIB.IrqCarry SInvIB.fInitIpiASt ∧ IoaRel arI SInvIB.fInitIpiASt :=
  ⟨SInvIB.fInitIpi_irqCarry, h.frame rfl⟩

variable {arI AR MR} in
/-- **`JReachU17` at `fInitIpiASt` gives the U40 start** under the backend's `IoaRel` at `fInitASt`. -/
theorem JReachU40.of_fInitIpi {s : S} {a : A} (hJ : JReachU17 (L := L) arI AR MR s a SInvIB.fInitIpiASt)
    (h : IoaRel arI JBoot.fInitASt) : JReachU40 (L := L) arI AR MR s a SInvIB.fInitIpiASt :=
  ⟨⟨hJ, SInvIB.fInitIpi_irqCarry⟩, h.frame rfl⟩

