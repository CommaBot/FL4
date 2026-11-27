/-
# P2 (line p3mc, gen 39): the cheap spec start facts at the second boot start `σR`

`JReachU3.start` / `JReachU17` ask of the start's spec state, beside `SInvX`: `SInvIP`, `UtPgR` (with `JAtZ`
and `MR`), and `JReachU17` adds `GpmOutV`, `IdleVtS`, `DevRangeS`. At `σR` (P2/BootRSpec) every cap is the null
cap but `threadCap tRp` in the root thread's CSpace-root slot and `schedContextCap scRp 0` in its timeout-handler
slot (`capAt_R` / `capOpt_R`), so each fact about untyped / I/O-port / vtable caps or cap ranges holds as at `σB`
(gen 34 / 35), the two caps checked once:

* **`sInvIP_R`** (`SInvIP σR`: no I/O-port cap, `SpecUtZ` vacuous), **`utPgR_R`**, **`devRangeS_R`** (no
  untyped cap);
* **`gpmOut_R`** (`GpmOutV σR`: the caps' ranges `{tRp}`, `{scRp}` miss the global PML4), **`idleVtS_R`**
  (`IdleVtS σR`: the idle thread's vtable slot is null), **`idleOut_R`** (`IdleOutV σR`), `irqOut_R` (`IrqOutV`
  for every map missing `tRp` and `scRp`: P3's `UtInv3` part at `σR`'s IRQ node).

No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootRMem
import Fl4Proofs.P2.BootWordF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical

noncomputable section

/-- `capOpt` at `σR`. -/
theorem capOpt_σR {p : Fl4Spec.ObjRef} {c : Fl4Spec.CnodeIndex} {cap : Fl4Spec.Cap}
    (h : capOpt ((σR (Z := Unit)).kheap p) c = some cap) :
    cap = .nullCap ∨ (p = tRp ∧ c = Fl4Spec.tcbCnodeIndex 0 ∧ cap = .threadCap tRp) ∨
      (p = tRp ∧ c = Fl4Spec.tcbCnodeIndex 4 ∧ cap = .schedContextCap scRp 0) := capOpt_R h

/-- No I/O-port cap at `σR`. -/
theorem noIo_R (f l : Fl4Spec.IoPort) : ¬ SInvIo.Has (σR (Z := Unit)) f l := by
  rintro ⟨p, cref, hc⟩
  rcases capOpt_σR hc with e | ⟨-, -, e⟩ | ⟨-, -, e⟩ <;> cases e

theorem ioi_R : SInvR.G5.SpecIoP (σR (Z := Unit)) ∧ SInvIo.IoNoOverlap (σR (Z := Unit)) :=
  SInvIo.ioi_iff.1 ⟨fun f l hh => absurd hh (noIo_R f l), fun f l _ _ hh => absurd hh (noIo_R f l)⟩

/-- **`SInvIP` at `σR`.** -/
theorem sInvIP_R : SInvR.G5.SInvIP (σR (Z := Unit)) :=
  ⟨ioi_R.1, ioi_R.2, fun _ _ _ _ h => by
    rcases capAt_R h with e | ⟨-, e⟩ | ⟨-, e⟩ <;> cases e⟩

/-- **`UtPgR` at `σR`** (no untyped cap). -/
theorem utPgR_R : SInvUZ.UtPgR (σR (Z := Unit)) := fun _ _ _ _ _ h => by
  rcases capOpt_σR h with e | ⟨-, -, e⟩ | ⟨-, -, e⟩ <;> cases e

/-- **`DevRangeS` at `σR`** (no untyped cap). -/
theorem devRangeS_R : SInvDV.DevRangeS (σR (Z := Unit)) := fun _ _ _ _ _ h => by
  rcases capOpt_σR h with e | ⟨-, -, e⟩ | ⟨-, -, e⟩ <;> cases e

/-- **`IrqOutV` at `σR`** for every map missing the root thread: the null cap covers nothing, the thread cap only
`tRp`. -/
theorem irqOut_R (N : Fl4Spec.Irq → Fl4Spec.ObjRef) (hN : ∀ irq, N irq ≠ tRp) (hS : ∀ irq, N irq ≠ scRp) :
    SInvU.IrqOutV N (SInvU.uV (σR (Z := Unit))) := by
  intro irq s c hs hc
  rcases capAt_R hs with e | ⟨-, e⟩ | ⟨-, e⟩
  · subst e; simp [SInvU.covR, SInvU.capRng, Fl4Spec.objRefs] at hc
  · subst e
    simp only [SInvU.covR, SInvU.capRng, Fl4Spec.objRefs, Set.mem_singleton_iff] at hc
    exact hN irq hc
  · subst e
    simp only [SInvU.covR, SInvU.capRng, Fl4Spec.objRefs, Set.mem_singleton_iff] at hc
    exact hS irq hc

/-- **`GpmOutV` at `σR`.** -/
theorem gpmOut_R : SInvGp.GpmOutV (σR (Z := Unit)) := irqOut_R _ (fun _ => by decide) (fun _ => by decide)

/-- **`IdleOutV` at `σR`.** -/
theorem idleOut_R : SInvG.IdleOutV (σR (Z := Unit)) := irqOut_R _ (fun _ => by decide) (fun _ => by decide)

/-- **`IdleVtS` at `σR`**: the idle thread's vtable slot holds the null cap. -/
theorem idleVtS_R : SInvIV.IdleVtS (σR (Z := Unit)) := fun a ha => by
  rcases capAt_R (sl := ((σR (Z := Unit)).idleThread, Fl4Spec.tcbCnodeIndex 1)) ha with e | ⟨e, -⟩ | ⟨e, -⟩
  · exact e
  · exact absurd (congrArg Prod.fst e) (by decide)
  · exact absurd (congrArg Prod.fst e) (by decide)

end

end Fl4Proofs.P2.BootSt
