/-
P3 (line irqfix, gen 3): **l4v's own `valid_irq_handlers`** (`ValidIrqHandlersL`: a handler cap's line is in
`IRQSignal`) and its step relation (spec side only; outside the `JAtZ` cone: SpecInvValidIrqHandlersD).

l4v (Isabelle `proof/invariant-abstract/Invariants_AI.thy`, `valid_irq_handlers_def`) asks
`cap_irqs cap ⊆ {irq. interrupt_states s irq = IRQSignal}` (`irq_issued`) for every cap of `caps_of_state`.
The port's `SInvV.ValidIrqHandlers` (SpecInvValidIrqHandlers) weakened it to `≠ IRQInactive`, which allows a
handler cap on a timer or reserved line. This module is vih1 (SpecInvValidIrqHandlers) and vih2's ack
(SpecInvValidIrqHandlersD) restated with l4v's `= IRQSignal` (`L` suffix):

* `ValidIrqHandlersL σ`; `ValidIrqHandlersL.vih`: it implies the port's `ValidIrqHandlers`.
* `HKL σ σ'`: every line named by a handler cap of `σ'` is in `IRQSignal` in `σ'`, or was named in `σ` and stays
  in `IRQSignal` if it was; reflexive, transitive, and `ValidIrqHandlersL` is kept along it.
* Leaves: `hkl_setCap` (a non-handler cap, a cap read from a slot, or a handler cap whose line is in
  `IRQSignal`), `hkl_setIrqState_signal` (`set_irq_state IRQSignal`: every spec writer of a non-inactive state
  writes `IRQSignal`, `Fl4Spec` Interrupt / X64.Arch / Ext.IrqControl), `hkl_setIrqState_inactive` (a line no
  slot names, the deletion's `deleted_irq_handler`, as vih1).
* `WLH` instances (`ValidIrqHandlersL` and `HKL σ0 ·` read only vih2's `hV`), so vih2's generated frames
  (SpecInvValidIrqHandlersF1..F4) keep them.
* The ack: `vimhl_ack` / `vimhl_invokeIrqHandler_ack` (`ValidIrqMasks ∧ ValidIrqHandlersL` kept, the invoked
  handler cap in a slot).
* `boot_vihl`: `initASt` holds no handler cap.

No premise; no sorry.
-/
import Fl4Proofs.P3.SpecInvValidIrqHandlersD

open Classical

namespace Fl4Proofs.P3.SInvVL
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 1000000

/-- **l4v `valid_irq_handlers`** (module docstring): every handler cap's line is in `IRQSignal`. -/
def ValidIrqHandlersL (σ : State Unit) : Prop :=
  ∀ p cref irq, capOpt (σ.kheap p) cref = some (.irqHandlerCap irq) → σ.interruptStates irq = .irqSignal

/-- l4v's form implies the port's (`IRQSignal ≠ IRQInactive`). -/
theorem ValidIrqHandlersL.vih {σ : State Unit} (h : ValidIrqHandlersL σ) : ValidIrqHandlers σ :=
  fun p cref irq hc e => by have := h p cref irq hc; rw [e] at this; cases this

theorem ValidIrqHandlersL.active {σ : State Unit} (h : ValidIrqHandlersL σ) {irq : Irq} (hn : HIrq σ irq) :
    σ.interruptStates irq = .irqSignal := by
  obtain ⟨p, cref, hc⟩ := hn; exact h p cref irq hc

/-- **The step relation of `ValidIrqHandlersL`** (module docstring). -/
def HKL (σ σ' : State Unit) : Prop :=
  ∀ irq, HIrq σ' irq → σ'.interruptStates irq = .irqSignal ∨
    (HIrq σ irq ∧ (σ.interruptStates irq = .irqSignal → σ'.interruptStates irq = .irqSignal))

theorem HKL.refl (σ : State Unit) : HKL σ σ := fun _ h => Or.inr ⟨h, id⟩

theorem HKL.trans {σ1 σ2 σ3 : State Unit} (h1 : HKL σ1 σ2) (h2 : HKL σ2 σ3) : HKL σ1 σ3 := by
  intro irq h3
  rcases h2 irq h3 with e | ⟨hn2, m23⟩
  · exact Or.inl e
  · rcases h1 irq hn2 with e | ⟨hn1, m12⟩
    · exact Or.inl (m23 e)
    · exact Or.inr ⟨hn1, fun e => m23 (m12 e)⟩

theorem ValidIrqHandlersL.hk {σ σ' : State Unit} (h : ValidIrqHandlersL σ) (hk : HKL σ σ') :
    ValidIrqHandlersL σ' := by
  intro p cref irq hc
  rcases hk irq ⟨p, cref, hc⟩ with e | ⟨hn, m⟩
  · exact e
  · exact m (h.active hn)

/-- `HKL` of every outcome. -/
def HKML {α : Type} (m : NonDet (State Unit) α) : Prop := ∀ σ x, x ∈ (m σ).1 → HKL σ x.2

theorem hkml_bind {α β : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) β} (hm : HKML m)
    (hf : ∀ a, HKML (f a)) : HKML (m >>= f) := by
  intro σ x ⟨y, hy, hx⟩
  exact (hm σ y hy).trans (hf y.1 y.2 x hx)

theorem hkl_of_kheap_is {σ σ' : State Unit} (hk : σ'.kheap = σ.kheap)
    (hi : σ'.interruptStates = σ.interruptStates) : HKL σ σ' := by
  intro irq h
  refine Or.inr ⟨?_, fun e => by rw [hi]; exact e⟩
  obtain ⟨p, cref, hc⟩ := h
  exact ⟨p, cref, by rw [← hk]; exact hc⟩

/-! ## Leaves -/

/-- **`set_cap` as an `HKL` step**. -/
theorem hkl_setCap {c : Cap} (sl : CslotPtr) {σ : State Unit}
    (hc : ∀ irq, c = .irqHandlerCap irq → HIrq σ irq ∨ σ.interruptStates irq = .irqSignal) :
    ∀ x ∈ (setCap (Z := Unit) c sl σ).1, HKL σ x.2 := by
  obtain ⟨o, r⟩ := sl
  intro x hx irq ⟨p, cref, h⟩
  obtain ⟨hi, hcaps⟩ := vih_setCap_out hx
  rw [hi]
  rcases hcaps p cref _ h with ⟨-, -, e⟩ | h0
  · rcases hc irq e.symm with hn | ha
    · exact Or.inr ⟨hn, id⟩
    · exact Or.inl ha
  · exact Or.inr ⟨⟨p, cref, h0.2⟩, id⟩

theorem hkl_setCap_named {c : Cap} (sl : CslotPtr) {σ : State Unit} {p0 : ObjRef} {r0 : CnodeIndex}
    (h0 : capOpt (σ.kheap p0) r0 = some c) : ∀ x ∈ (setCap (Z := Unit) c sl σ).1, HKL σ x.2 :=
  hkl_setCap sl fun irq e => Or.inl ⟨p0, r0, e ▸ h0⟩

theorem hkl_setIrqState_signal {st : IrqState} (hst : st = .irqSignal) (i : Irq) :
    HKML (setIrqState (Z := Unit) st i) := by
  intro σ x hx irq hn
  obtain ⟨hk, hi⟩ := setIrqState_out hx
  rw [hi]
  by_cases e : irq = i
  · subst e; left; rw [Function.update_self]; exact hst
  · right
    obtain ⟨p, cref, hc⟩ := hn
    exact ⟨⟨p, cref, by rw [← hk]; exact hc⟩, fun h => by rw [Function.update_of_ne e]; exact h⟩

/-- `set_irq_state IRQInactive` of a line no slot names. -/
theorem hkl_setIrqState_inactive {i : Irq} {σ : State Unit} (hn : ¬ HIrq σ i) :
    ∀ x ∈ (setIrqState (Z := Unit) .irqInactive i σ).1, HKL σ x.2 := by
  intro x hx irq hn'
  obtain ⟨hk, hi⟩ := setIrqState_out hx
  have hn0 : HIrq σ irq := by obtain ⟨p, cref, hc⟩ := hn'; exact ⟨p, cref, by rw [← hk]; exact hc⟩
  have e : irq ≠ i := fun e => hn (e ▸ hn0)
  right
  rw [hi]
  exact ⟨hn0, fun h => by rw [Function.update_of_ne e]; exact h⟩

/-! ## `WLH` instances -/

theorem hkl_of_hV {σ σ' : State Unit} (e : hV σ' = hV σ) : HKL σ σ' := by
  intro irq ⟨p, cref, h⟩
  refine Or.inr ⟨⟨p, cref, by rw [← hV_cap e]; exact h⟩, fun h' => by rw [hV_is e]; exact h'⟩

instance : WLH ValidIrqHandlersL := wlh_of_hV fun σ σ' e h p cref irq hc => by
  rw [hV_is e]; exact h p cref irq (by rw [← hV_cap e]; exact hc)

instance (σ0 : State Unit) : WLH (fun σ => HKL σ0 σ) := wlh_of_hV fun _ _ e h => h.trans (hkl_of_hV e)

theorem vihl_of_hV {σ σ' : State Unit} (e : hV σ' = hV σ) (h : ValidIrqHandlersL σ) : ValidIrqHandlersL σ' :=
  fun p cref irq hc => by rw [hV_is e]; exact h p cref irq (by rw [← hV_cap e]; exact hc)

/-! ## The IRQ ack -/

theorem hkml_ack (irq : Irq) : HKML (doMachineOp (Z := Unit) (maskInterrupt false irq)) := by
  intro σ x hx
  have e : maskInterrupt false irq σ.machineState =
      ({((), { σ.machineState with irqMasks := Function.update σ.machineState.irqMasks irq false })}, False) := rfl
  rw [SInvV.dmo_single e] at hx
  rw [Set.mem_singleton_iff.1 hx]
  exact hkl_of_kheap_is rfl rfl

/-- **The ack with the invoked handler cap in a slot** keeps `ValidIrqMasks ∧ ValidIrqHandlersL`. -/
theorem vimhl_ack {irq : Irq} {σ : State Unit} (hm : SInvV.ValidIrqMasks σ) (hh : ValidIrqHandlersL σ)
    (hn : HIrq σ irq) :
    ∀ x ∈ (doMachineOp (Z := Unit) (maskInterrupt false irq) σ).1,
      SInvV.ValidIrqMasks x.2 ∧ ValidIrqHandlersL x.2 :=
  fun x hx => ⟨vim_ack hm (hh.vih.active hn) x hx, hh.hk (hkml_ack irq σ x hx)⟩

theorem vimhl_invokeIrqHandler_ack {irq : Irq} {σ : State Unit} (hm : ValidIrqMasks σ) (hh : ValidIrqHandlersL σ)
    (hn : HIrq σ irq) : ∀ x ∈ (invokeIrqHandler (Z := Unit) (.aCKIrq irq) σ).1,
      ValidIrqMasks x.2 ∧ ValidIrqHandlersL x.2 := by
  intro x hx
  simp only [invokeIrqHandler, archInvokeIrqHandler] at hx
  exact vimhl_ack hm hh hn x hx

/-! ## Boot -/

/-- **`ValidIrqHandlersL` at boot**: `initKheap` holds no handler cap. -/
theorem boot_vihl : ValidIrqHandlersL (initASt (Z := Unit)) := by
  intro p cref irq hc
  exact (boot_vih p cref irq hc rfl).elim

end

end Fl4Proofs.P3.SInvVL
