/-
P3 (line irqfix, gen 2): **`kernel_entry_reachU34`**: `kernel_entry_reachU33` without its per-entry [J]
`IrqAckU`, by l4v `valid_cap`'s IRQ handler bound carried with the reachable states.

* **`JReachU34 s a σ := JReachU17 s a σ ∧ IrqStB σ`** (a new top-level wrapper; `JReachU17` unchanged):
  every IRQ line above `maxIRQ` is inactive (SpecInvIrqBoundKit). With `SInvX`'s `ValidIrqHandlers` it gives
  **`IrqCapBound σ`** (l4v `valid_cap` for `IRQHandlerCap`, Invariants_AI `valid_cap_def`: `irq ≤ maxIRQ`),
  stated in U34's entry conjunct. `IrqStB` is kept by every spec entry (SpecInvIrqBound: `kentry_irqStB`,
  `kcall_irqStB`, the FaultIP write and the budget front: `EvOut.irqStB`, `BudgetAt.irqStB`) and holds at
  boot (`initASt` / jboot's `fInitASt`: every line inactive; `fInit_irqCapBound`: no handler cap at all).
* **`irqAckU_of_capBound`**: at a `JAtZ` state, `IrqCapBound` bounds FL4's handler cap in a CNode slot
  (`StateRel.abs_cap`: the slot's spec cap is `absCap (.IrqHandler irq) = irqHandlerCap (ofNat 8 irq)`,
  `CapWf`: `irq < 128`), so `IrqAckU.of_bound` gives `IrqAckU` under `MachPlatF`.

**Premise diff U33 → U34**: the syscall clause's `JDecMRLK … ∧ IrqAckU …` [J] ↦ `JDecMRLK …` (U32's form);
`hJ : JReachU17` ↦ `hJ : JReachU34` (start condition `IrqStB`, true at boot). Conclusion: U33's with
`IrqCapBound σ` added after `SInvX σ` and every exit's `JReachU17` ↦ `JReachU34`. Every other premise verbatim
([P] `MachPlatF`, `IpiF`, `IrqPlatK` as U33). [W] 0.
No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU33
import Fl4Proofs.P3.SpecInvIrqBound
import Fl4Proofs.P3.JBootSt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- **`IrqCapBound` at jboot's witness `fInitASt`**: it holds no IRQ handler cap (its objects are `initASt`'s
and empty IRQ CNodes). -/
theorem fInit_irqCapBound : SInvIB.IrqCapBound JBoot.fInitASt := by
  intro p cref irq hc
  exfalso
  have hb : ∀ q, capOpt (Fl4Spec.initKheap q) cref ≠ some (.irqHandlerCap irq) :=
    fun q h => SInvV.boot_vih q cref irq h rfl
  change capOpt (JBoot.fInitKheap p) cref = some (.irqHandlerCap irq) at hc
  simp only [JBoot.fInitKheap, Function.update_apply] at hc
  split_ifs at hc
  all_goals first
    | exact hb _ hc
    | (simp only [capOpt, Fl4Spec.emptyCnode] at hc; split_ifs at hc <;> simp_all; done)
    | (simp [capOpt] at hc; done)

/-- `IrqStB` at jboot's witness (every line inactive, as `initASt`). -/
theorem fInit_irqStB : SInvIB.IrqStB JBoot.fInitASt := fun _ _ => rfl

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- **`IrqAckU` from l4v's handler bound** at a `JAtZ` state (module docstring). -/
theorem irqAckU_of_capBound (hM : MachPlatF arI MR) {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hB : SInvIB.IrqCapBound σ) :
    IrqAckU (L := L) arI MR Z s a σ :=
  IrqAckU.of_bound hM fun sl irq hsl hc => by
    have hAs : AbsSlot Z.th sl := by
      obtain ⟨p', hp, hth⟩ := hsl; exact ⟨p', hp, Or.inl hth⟩
    have hwf : irq.val < 128 := (slot_cap_wf J.xtop hAs (capV_of_capAt hc)).1
    obtain ⟨c', ac, hc', hcr, hg⟩ := J.xtop.rel.2.1.1.abs_cap hAs
    rw [hc] at hc'; cases eq_of_ok_eq hc'
    have hco : capOpt (σ.kheap sl.1) sl.2 = some ac :=
      (getCap_set_iff σ sl.1 sl.2 ac).1 (congrArg Prod.fst hg)
    have hco' : capOpt (σ.kheap sl.1) sl.2 = some (.irqHandlerCap (BitVec.ofNat 8 irq.val)) :=
      hco.trans (by rw [← hcr.2]; try rfl)
    have h1 := hB _ _ _ hco'
    have h2 : irq.val % 256 ≤ 125 := by
      have := h1; rw [BitVec.le_def, BitVec.toNat_ofNat] at this; exact this
    omega

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states with the IRQ line bound** (module docstring). -/
abbrev JReachU34 (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  JReachU17 (L := L) arI AR MR s a σ ∧ SInvIB.IrqStB σ

/-- `IrqCapBound` at every `JReachU34` state with `SInvX` (`ValidIrqHandlers` ∧ `IrqStB`). -/
theorem JReachU34.irqCapBound {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU34 (L := L) arI AR MR s a σ)
    (hX : SInvX σ) : SInvIB.IrqCapBound σ :=
  SInvIB.irqCapBound_of hX.sb.1.1.vih hJ.2

/-- **JReachU34's extra start fact at the boot states** (`initASt`, jboot's `fInitASt`): `JReachU17` at a
boot state gives `JReachU34`. -/
theorem JReachU34.of_boot {s : S} {a : A} (hJ : JReachU17 (L := L) arI AR MR s a JBoot.fInitASt) :
    JReachU34 (L := L) arI AR MR s a JBoot.fInitASt := ⟨hJ, fInit_irqStB⟩

end

end

end Fl4Proofs.P3.SInvR.G5
