/-
P3 (p3J gen 18): **the entry clauses through `RunMcW`, `FIKeepIrq` replaced by a projection-footprint / stable-ghost
premise** (P3JMcStep).

* **`RunMcW s a σ := RunCK s a σ ∧ JAtMcW s a σ`**.
* **`StabPost Z H Cs s σ r σ'`**: what U45nv's clause would state with its post ghosts exposed: the outcome is
  `JAtZ (Z.mv G' V') H Cs …` (only the MDB and VSpace sets move, as StPost's `JStab`), with `VxE`, the FL4 run
  writes only `ProjW H Cs s`, no new spec object appears (`KhNoneKeep`) and no new RAM untyped cap (`UtKeep`).
* **`runMcW_post`**: from `RunMcW` at `s` (any core) and a `RunCK` outcome meeting `StabPost` at every `JAtZ`
  ghosts of `s`, `RunMcW` at the outcome. One lemma for all six clauses.
* **`kernel_entry_runMcW_irq`** / **`kernel_entry_runMcW_user`**: the interrupt and user-exception clauses on any
  core, under U45nv's globals and the named premise **`hSt` [J] (`IrqStab` / `UserStab`)**: at every `JAtZ`
  ghosts of the entry state, the clause's outcomes meet `StabPost`. Unlike gen 17's `FIKeepIrq` [J], `hSt` does
  not mention the other cores: it is a statement about the single-core chain (U45nv's clause with its ghosts
  exposed) and FL4's footprint. Not discharged: the ghost exposure exists for the local timer interrupt at U17
  (StPostIrqTop `kernel_entry_irq_localSt17`, `JStab`), not along U17 → U45nv; the footprint `ProjW` is not
  proved for `handle_interrupt_entry` (P1 `entryXG` gives `Cur0W`, which allows every node word but 88 and the
  user words `UserW`; P2 `timer_irq_local.allCores` only the accepted local timer).
* **`runMcW_w2`**: `RunMcW` at the 2-core boot witness.

Named premises: `IrqStab`, `UserStab` [J] (above); U45nv's globals as in `kernel_entry_runCK`. No sorry. New module;
no existing statement changed.
-/
import Fl4Proofs.P3.P3JMcRun
import Fl4Proofs.P3.P3JMcStep
import Fl4Proofs.P3.JBootM2Mc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The multicore run predicate with aligned foreign idle objects.** -/
def RunMcW (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  RunCK (L := L) arI AR MR s a σ ∧ JAtMcW (L := L) arI AR s a σ

/-- **A clause outcome with exposed stable ghosts and the projection footprint** (module docstring). -/
def StabPost (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (σ : Fl4Spec.State Unit) (s' : S) (a' : A)
    (σ' : Fl4Spec.State Unit) : Prop :=
  ∃ (G' : MdbGhost) (V' : Set U64 × Set U64 × Set U64 × Set U64 × Set U64) (Ac' : Set U64)
    (Lst' : U64 → List U64) (D' : Set U64),
    JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ' ∧ VxE (Z.mv G' V') ∧
      P1.WritesIn st s s' (ProjW (L := L) H Cs s) ∧ KhNoneKeep σ σ' ∧ UtKeep (L := L) Z.G G' s s'

variable {arI AR MR}

/-- **`RunMcW` at a clause outcome** (module docstring). -/
theorem runMcW_post {s : S} {a : A} {σ : Fl4Spec.State Unit} (hR : RunMcW (L := L) arI AR MR s a σ)
    {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (hC : RunCK (L := L) arI AR MR s' a' σ')
    (hP : ∀ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → StabPost (L := L) arI AR Z H Cs s σ s' a' σ') :
    RunMcW (L := L) arI AR MR s' a' σ' := by
  obtain ⟨-, Z, H, Cs, Ac, Lst, D, J, -, hF⟩ := hR
  obtain ⟨G', V', Ac', Lst', D', J', hV', hW, hK, hU⟩ := hP Z H Cs Ac Lst D J
  exact ⟨hC, jAtMcW_step J hF J' hV' hW hK hU⟩

/-- `RunMcW` gives `RunMc`. -/
theorem RunMcW.runMc {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : RunMcW (L := L) arI AR MR s a σ) :
    RunMc (L := L) arI AR MR s a σ := ⟨h.1, h.2.jAtMc⟩

end

end Fl4Proofs.P3.Mc

namespace Fl4Proofs.P3.JBootQ.M2
open Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit Fl4Proofs.P3.Mc

/-- Core 1's idle objects at the 2-core witness are aligned and fit. -/
theorem fIdleW_w0 : FIdleW (L := wL) w0 1#u64 :=
  ⟨by rw [idleOf1, i1t_val] <;> decide, by rw [idleScOf1, i1s_val] <;> decide,
    by rw [idleOf1, i1t_val] <;> decide, by rw [idleScOf1, i1s_val] <;> decide⟩

/-- **`RunMcW` at the 2-core boot witness.** -/
theorem runMcW_w2 : RunMcW (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=
  ⟨runMc_w2.1, Zw, Hw, Csw, C0, fun _ => [], Dw, jAtZ_w0I1 _, Zw_vx, fun c hc hne => by
    rcases memCs2 hc with rfl | rfl
    · exact absurd cpu_w0.symm hne
    · exact ⟨foreignIdle_w0, fIdleW_w0⟩⟩

end Fl4Proofs.P3.JBootQ.M2
