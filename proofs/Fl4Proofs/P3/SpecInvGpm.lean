/-
P3 (DESIGN.md §9), invariant line G1 (KENTRY-PLAN g7a-4 (3), s27): **no cap
covers the global PML4** (`GpmOutV`, l4v `valid_global_refs`:
`x64_global_pml4 ∈ global_refs`, outside the `cap_range` of every cap, untyped
ones included), carried across the whole kernel entry. Spec side only; it is
C27's spec half (`DevGpm` asks it for the device untyped caps only).

* `GpmOutV σ := IrqOutV (fun _ => σ.archState.x64GlobalPml4) (uV σ)`: sg1's
  `IdleOutV` with the global PML4 for the idle thread. It is carried by the
  SpecGlob family `S N M` (SpecInvSgA..SgE) at `M := fun _ => g`: the family's
  cap-domination argument (SpecInvUtN8 `CD` / `DMV`: every cap after a step
  covers only what a cap before covered) is stated for an arbitrary `M`, so
  nothing new is proved per writer.
* `g` itself is constant: SpecInvGpK1..K6's `GpK g` (no spec step writes
  `x64GlobalPml4`).
* `kentry_gpmOut`, `kcall_gpmOut`, `fip_gpmOut` (the FaultIP write then an
  event), `fip_view` / `fip_gpm`, `budget_view` / `budget_gpm` (the dispatch
  state after the time stamp and a passing budget check).
-/
import Fl4Proofs.P3.SpecInvGpK6
import Fl4Proofs.P3.SpecInvSgE
open Classical

namespace Fl4Proofs.P3.SInvGp
open Fl4Spec Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvU Fl4Proofs.P3.SInvG

noncomputable section

/-- **No cap covers the global PML4 [J]** (module docstring; l4v `valid_global_refs`). -/
def GpmOutV (σ : State Unit) : Prop := IrqOutV (fun _ => σ.archState.x64GlobalPml4) (uV σ)

theorem boot_gpmOut : GpmOutV (initASt (Z := Unit)) := boot_irqOut _

/-- The family at the state's node and global PML4. -/
theorem S_of_gpm {σ : State Unit} (hG : SpecGlobS σ) (hI : GpmOutV σ) (hU : UtInv3 σ) :
    S σ.interruptIrqNode (fun _ => σ.archState.x64GlobalPml4) σ :=
  ⟨hU, hI, fun irq a ha => hG.irq irq a ha⟩

/-- **`GpmOutV` across the syscall entry.** -/
theorem kentry_gpmOut (c : Syscall) {σ : State Unit} (hG : SpecGlobS σ) (hU : UtInv3 σ) (hI : GpmOutV σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, GpmOutV y.2 := by
  intro y hy
  have hT : GpmIs σ.archState.x64GlobalPml4 y.2 := gpk_fl4KernelEntrySyscall true c σ rfl y hy
  have hS := sgN_kentry c σ.interruptIrqNode (fun _ => σ.archState.x64GlobalPml4) σ (S_of_gpm hG hI hU) rfl y hy
  have e : y.2.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := hT
  unfold GpmOutV; rw [e]; exact hS.2.1

/-- **`GpmOutV` across every kernel event.** -/
theorem kcall_gpmOut (rep : Bool) (ev : Event) {σ : State Unit} (hG : SpecGlobS σ) (hU : UtInv3 σ)
    (hI : GpmOutV σ) : ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, GpmOutV y.2 := by
  intro y hy
  have hT : GpmIs σ.archState.x64GlobalPml4 y.2 := gpk_fl4CallKernel rep ev σ rfl y hy
  have hS := sgN_fl4CallKernel rep ev σ.interruptIrqNode (fun _ => σ.archState.x64GlobalPml4) σ
    (S_of_gpm hG hI hU) rfl y hy
  have e : y.2.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := hT
  unfold GpmOutV; rw [e]; exact hS.2.1

/-- The FaultIP write keeps the view. -/
theorem fip_view {σ : State Unit} {t : ObjRef} {w : Unit × State Unit}
    (hw : w ∈ (fl4SyscallFaultIP (Z := Unit) t σ).1) : uV w.2 = uV σ :=
  uk_mem (fun _ => uk_fl4SyscallFaultIP t) hw

/-- The FaultIP write keeps the global PML4. -/
theorem fip_gpm {σ : State Unit} {t : ObjRef} {w : Unit × State Unit}
    (hw : w ∈ (fl4SyscallFaultIP (Z := Unit) t σ).1) :
    w.2.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 :=
  gpk_fl4SyscallFaultIP t σ rfl w hw

/-- `GpmOutV` across the FaultIP write. -/
theorem fip_gpmOut {σ : State Unit} {t : ObjRef} {w : Unit × State Unit}
    (hw : w ∈ (fl4SyscallFaultIP (Z := Unit) t σ).1) (hI : GpmOutV σ) : GpmOutV w.2 := by
  unfold GpmOutV; rw [fip_view hw, fip_gpm hw]; exact hI

/-- **`GpmOutV` across the FaultIP write then an event** (the trap / unknown-syscall exits). -/
theorem fipEv_gpmOut (rep : Bool) (ev : Event) {σ : State Unit} (hG : SpecGlobS σ) (hU : UtInv3 σ)
    (hI : GpmOutV σ) {t : ObjRef} {w : Unit × State Unit} (hw : w ∈ (fl4SyscallFaultIP (Z := Unit) t σ).1) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) w.2).1, GpmOutV y.2 := by
  intro y hy
  have hv := fip_view hw
  have hN : NodeIs σ.interruptIrqNode w.2 := nk_fl4SyscallFaultIP t σ rfl w hw
  have hS0 : S σ.interruptIrqNode (fun _ => w.2.archState.x64GlobalPml4) w.2 := by
    rw [fip_gpm hw]; exact s_of_view hv (S_of_gpm hG hI hU)
  have hT : GpmIs w.2.archState.x64GlobalPml4 y.2 := gpk_fl4CallKernel rep ev w.2 rfl y hy
  have hS := sgN_fl4CallKernel rep ev σ.interruptIrqNode _ w.2 hS0 hN y hy
  have e : y.2.archState.x64GlobalPml4 = w.2.archState.x64GlobalPml4 := hT
  unfold GpmOutV; rw [e]; exact hS.2.1

/-- The time stamp then a passing budget check keep the view. -/
theorem budget_view {σ : State Unit} {σb : State Unit}
    (h : (true, σb) ∈ ((updateTimeStamp (Z := Unit) >>= fun _ => checkBudgetRestart (Z := Unit)) σ).1) :
    uV σb = uV σ := by
  obtain ⟨x, hx, hb⟩ := h
  exact (checkBudgetRestart_true hb rfl).trans (uk_mem (fun _ => uk_updateTimeStamp) hx)

/-- The time stamp then the budget check keep the global PML4. -/
theorem budget_gpm {σ : State Unit} {y : Bool × State Unit}
    (h : y ∈ ((updateTimeStamp (Z := Unit) >>= fun _ => checkBudgetRestart (Z := Unit)) σ).1) :
    y.2.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 :=
  ik_bind gpk_updateTimeStamp (fun _ => gpk_checkBudgetRestart) σ rfl y h

end

end Fl4Proofs.P3.SInvGp
