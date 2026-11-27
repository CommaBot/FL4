/-
# P2 (line p3mc, gen 39): **`NonIdle` from the node words**, and `NonIdle` at the second boot start

`NonIdle st arI AR MR s` (P2/E2EVFl4W9, a [P] field of the vmF / vmR / sl entry records `VmFEntV13` /
`VmREntV13` / `SlEntV13`) quantifies over every P3 reachable state `JReachU17 s a τ` at the store state `s`. It is
decided by two of `s`'s words alone:

* **`jAt_of_reachU3`**: every `JReachU3` state is a `JAt` state (`start` carries a `JAtZ`; every other
  constructor ends in `RJM`, whose `RJ` carries `JAt`);
* **`nonIdle_of_words`**: if core `L.cpu s`'s `CUR_THREAD` and `IDLE_THREAD` words differ (`L.curW s ≠ L.idleW s`),
  `NonIdle` holds for every `arI`, `AR`, `MR`: at a `JAtZ` state P3's `SchedRel` (`xtop.fin`) at the core `Z.c =
  L.cpu s` (`SchedCore.cur`) reads `τ.curThread` / `τ.idleThread` off those words (`SchedSpec.curThread`,
  `SchedSpec.idleTh`);
* **`nonIdle_R`**: `NonIdle` at the second boot start's store state `sR` (P2/BootRMem: `CUR_THREAD = tRw`,
  `IDLE_THREAD = tiB`), for every `arI`, `AR`, `MR` (in particular the tops' `archT`, `ART`, `modelMR`).
  Gen 37's `nonIdle_false_B` is the converse at `sB` (equal words there).

No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootRMem
import Fl4Proofs.P2.E2EVFl4W9
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical
open Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2EV Fl4Proofs.P2.OwnMapP Fl4Proofs.P2.OwnMapV

noncomputable section

section gen
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- **Every `JReachU3` state is a `JAt` state.** -/
theorem jAt_of_reachU3 : ∀ {s : S} {a : A} {σ : Fl4Spec.State Unit},
    SInvR.G5.JReachU3 (L := L) arI AR MR s a σ → JAt (L := L) arI AR s a σ
  | _, _, _, .start J hV _ _ _ _ => ⟨_, _, _, _, _, _, J, hV⟩
  | _, _, _, .step _ _ _ _ _ _ _ hR => hR.1.2
  | _, _, _, .irq _ _ _ _ _ hR => hR.1.2
  | _, _, _, .user _ _ _ _ _ _ _ hR => hR.1.2
  | _, _, _, .vmf _ _ _ _ _ _ _ _ hR => hR.1.2
  | _, _, _, .trap _ _ _ _ _ _ _ _ hR => hR.1.2
  | _, _, _, .sysU _ _ _ _ _ _ _ _ _ hR => hR.1.2

theorem U64.eq_of_bv {x y : U64} (h : x.bv = y.bv) : x = y := by
  cases x; cases y; cases h; rfl

/-- **`NonIdle` from the node words** (module docstring). -/
theorem nonIdle_of_words {s : S} (h : L.curW s ≠ L.idleW s) : E2EV.NonIdle st arI AR MR s := by
  intro a τ hJ
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, -⟩ := jAt_of_reachU3 hJ.1
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  rw [hs.curThread, hs.idleTh]
  intro e
  apply h
  unfold LawfulStore.curW LawfulStore.idleW
  rw [hc.cur]
  exact U64.eq_of_bv e

end gen

/-- **`NonIdle` at the second boot start** (every `arI`, `AR`, `MR`). -/
theorem nonIdle_R {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop}
    {MR : A → Fl4Spec.MachineState → Prop} : E2EV.NonIdle bst arI AR MR sR :=
  nonIdle_of_words sR_cur_ne_idle

/-- In particular at the tops' instance. -/
theorem nonIdle_R_top : E2EV.NonIdle bst LocPlatM.archT LocPlatM.ART modelMR sR := nonIdle_R

end

end Fl4Proofs.P2.BootSt
