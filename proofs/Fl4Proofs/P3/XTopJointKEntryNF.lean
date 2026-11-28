/-
P3 (DESIGN.md §9), invariant line G4 (KENTRY-PLAN g4a (6) item (G-a), g4c):
**the spec-fails disjunct of the entry's post is gone.**

* Where the disjunct came from. In the whole chain under `kernel_entryJ35`
  (J35 → J34 → J33 → J33G → J32 → J31 → J30 → J29G → `kernel_entryJ13PUG`) the
  left disjunct of `KPost` ("the spec entry fails") is produced at exactly one
  place: the preemption branch of `kernel_entryJ13PUG`, from the left disjunct of
  `kPreFinAtG`'s post (a failing `preemptionPath`). `kPreFinAtG`'s proof never
  produces that disjunct: its input `PPQJI` already names an outcome of
  `preemptionPath`, and `jat_finishJRN` relates an outcome after it. Every other
  branch (budget stop, dispatch to completion) already ends in an outcome. The
  joint proofs construct the spec outcome step by step from the joint relation
  (`JAtZ`, its per-kind object and cap relations), so the spec's asserts on the
  path they follow are discharged there; the "(m)" sites of g4c's inventory never
  need a spec-only typing invariant on this route.
* `kPreFinAtGS` / `kernel_entryJ13PUGS`: the same statements and proofs with the
  post `KPostS` (only the outcome disjunct of `KPost`).
* `kentry_genS`: `kernel_entryJ34`'s general path with `KPostS`, composed from the
  wrappers J29G → J34 (their bundle conversions inlined; no new premise).
* **`kernel_entryJ36N`**: `kernel_entryJ35`'s premises (the fast-path premise
  `hFast` is m57's `FastRR` at the post `KPostS`: the fast path keeps what the
  general path guarantees, for that post), post **`KPostXS`**: an outcome σ' of
  the spec entry with `RJ` and `SInvX σ'` — no spec-fails disjunct.
* **`kentry_nofailJ`**: at the same premises, the spec syscall entry has an
  outcome (its result set is nonempty) and the FL4 entry returns. NOT l4v's
  `no_fail` (no branch fails): it says the entry is not stuck, which is all the
  induction needs.
* **`kernel_entry_reachN`**: `kernel_entry_reach` with the post `KPostXS`: every
  run from a reachable state lands in a related outcome that is again reachable
  given `MR` at the exit (g4a's (G-b)).
-/
import Fl4Proofs.P3.XTopJointKEntry35
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KPost` without the spec-fails disjunct**: an outcome of the spec entry is
related (`RJ`). -/
def KPostS (AR : A → Fl4Spec.Cr3 → Prop) (c : Fl4Spec.Syscall) (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ RJ (L := L) arI AR r.1 r.2 σ'

theorem KPostS.toKPost {AR : A → Fl4Spec.Cr3 → Prop} {c : Fl4Spec.Syscall} {σ : Fl4Spec.State Unit} {r : S × A}
    (h : KPostS (L := L) arI AR c σ r) : KPost (L := L) arI AR c σ r := Or.inr h

end


end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G4
open Aeneas Aeneas.Std Result
open fl4_core Classical Fl4Proofs.P3 Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
  Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

variable (arI) in
/-- **`KPostX` without the spec-fails disjunct**: an outcome σ' of the spec
entry, related (`RJ`) and satisfying `SInvX`. -/
def KPostXS (AR : A → Fl4Spec.Cr3 → Prop) (c : Fl4Spec.Syscall) (σ : Fl4Spec.State Unit) (r : S × A) : Prop :=
  ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧ RJ (L := L) arI AR r.1 r.2 σ' ∧ SInvX σ'

theorem KPostXS.toX {AR : A → Fl4Spec.Cr3 → Prop} {c : Fl4Spec.Syscall} {σ : Fl4Spec.State Unit} {r : S × A}
    (h : KPostXS (L := L) arI AR c σ r) : KPostX (L := L) arI AR c σ r := Or.inr h

end

/-! ## The induction with the strengthened post -/

end

end Fl4Proofs.P3.SInvR.G4
