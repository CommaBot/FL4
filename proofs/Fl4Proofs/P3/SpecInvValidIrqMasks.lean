/-
P3 (DESIGN.md §9), the invariant line (INV-PLAN §4 G1, invB): **`ValidIrqMasks`
(l4v `valid_irq_masks`) as a spec-only invariant** (spec side only; outside the
`JAtZ` cone).

* `ValidIrqMasks σ`: an inactive line is masked. The same body as
  XTopJointMRPath's `ValidIrqMasks` (premise `hVI` of `kernel_entryJ26P`), which
  is in the `JAtZ` cone.
* Its leaves but the ack (`vim_view`, `vim_uts`, `vim_sis`, `vim_msk`):
  `updateTimeStamp` keeps the table and the masks (`uts_out`), `setIrqState`
  masks exactly the lines it makes inactive (l4v `set_irq_state` with
  `maskInterrupt`), and the machine operations of the kernel entry only mask
  (`MaskT`: `getActiveIRQ`, `maskInterrupt true`, the timer/port/memory
  operations).
* **FINDING** `readFpu_breaks_vim`: the spec's ReadFPU (`fpuStep`,
  SpecInvValidMachineTime) sets the whole machine state, so it can unmask an
  inactive line; the rest of the entry only masks. Trace as
  `readFpu_breaks_vmt`, from any state with an inactive line (most lines are
  never issued). Stopped on this field.
* A second gap, independent of ReadFPU: the IRQ ack (`archInvokeIrqHandler
  (.aCKIrq irq)`, `maskInterrupt false`) unmasks without reading the line's
  state. l4v keeps `valid_irq_masks` there from `valid_irq_handlers` (every
  `IRQHandlerCap irq` in the CSpace has `irq` issued) and decode's lookup of
  the cap in the current state; neither is carried yet (`WL.ack` is not
  provable for `ValidIrqMasks` alone).
* `boot_vim`: the spec's initial state (every line inactive and masked).
-/
import Fl4Proofs.P3.SpecInvValidMachineTime

open Classical

namespace Fl4Proofs.P3.SInv
open Fl4Spec Fl4Proofs.P3.Vs

noncomputable section

/-- **[J] l4v `valid_irq_masks`** (module docstring). -/
def ValidIrqMasks (σ : Fl4Spec.State Unit) : Prop :=
  ∀ i, σ.interruptStates i = .irqInactive → σ.machineState.irqMasks i = true

theorem vim_view : ∀ σ σ', vw σ' = vw σ → ValidIrqMasks σ → ValidIrqMasks σ' := by
  intro σ σ' e h i hi
  unfold vw at e; simp only [Prod.mk.injEq] at e
  rw [e.2.2.1] at hi; rw [e.2.2.2]; exact h i hi

theorem vim_uts : IK ValidIrqMasks (updateTimeStamp (Z := Unit)) := by
  intro σ h x hx i hi
  obtain ⟨-, -, e3, e4⟩ := uts_out hx
  rw [e3] at hi; rw [e4]; exact h i hi

theorem dmo_mask_out {σ : State Unit} {x : Unit × State Unit} (b : Bool) (i : Irq)
    (hx : x ∈ (doMachineOp (Z := Unit) (maskInterrupt b i) σ).1) :
    x.2.machineState.irqMasks = Function.update σ.machineState.irqMasks i b ∧
      x.2.interruptStates = σ.interruptStates := by
  have e : maskInterrupt b i σ.machineState =
      ({((), { σ.machineState with irqMasks := Function.update σ.machineState.irqMasks i b })}, False) := rfl
  rw [dmo_single e] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact ⟨rfl, rfl⟩

theorem vim_sis (st : IrqState) (i : Irq) : IK ValidIrqMasks (setIrqState (Z := Unit) st i) := by
  intro σ h x hx j hj
  unfold setIrqState at hx
  rw [sv_bind_modify] at hx
  obtain ⟨e1, e2⟩ := dmo_mask_out _ i hx
  rw [e2] at hj; rw [e1]
  dsimp only at hj ⊢
  by_cases e : j = i
  · subst e
    simp only [Function.update_self] at hj ⊢
    simp [hj]
  · rw [Function.update_of_ne e] at hj ⊢
    exact h j hj

theorem vim_msk {α : Type} (mop : NonDet MachineState α) (hm : MaskT mop) :
    IK ValidIrqMasks (doMachineOp (Z := Unit) mop) := by
  intro σ h x hx j hj
  unfold doMachineOp at hx
  obtain ⟨⟨ms0, s1⟩, h1, ⟨⟨r, ms'⟩, s2⟩, h2, ⟨u, s3⟩, h3, hx⟩ := hx
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h1)
  obtain ⟨h2a, e2⟩ := h2
  dsimp only at e2 h2a
  subst e2
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h3)
  rw [Set.mem_singleton_iff.1 hx] at hj ⊢
  rcases (hm _ _ h2a).2 j with e | e
  · exact e.trans (h j hj)
  · exact e

/-- **FINDING (invB): the spec's ReadFPU breaks `ValidIrqMasks`.** From a
state with an inactive line `i` (at boot every line is), `fpuStep` (ReadFPU's
perform) has an outcome with every IRQ mask cleared (module docstring). -/
theorem readFpu_breaks_vim (σ : State Unit) (i : Irq) (hi : σ.interruptStates i = .irqInactive) :
    ∃ y ∈ (fpuStep σ).1, ¬ ValidIrqMasks y.2 := by
  refine ⟨_, fpuStep_any σ { σ.machineState with irqMasks := fun _ => false }, fun h => ?_⟩
  have := h i hi
  cases this

/-- **`ValidIrqMasks` at boot** (`initIrqMasks`: every line masked). -/
theorem boot_vim : ValidIrqMasks (initASt (Z := Unit)) := fun _ _ => rfl

end

end Fl4Proofs.P3.SInv
