/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr5): **`kernel_entryJ14P`**,
XTopJointKEntry13P's `kernel_entryJ13P` with the Untyped invocation taken out
of `JPreDecHyp` [W] (mr4 NEXT (1)).

* `JPreDecHypK K`: `JPreDecHyp` asked only for the caps `K c argsU` names
  (`JPreDecHyp` is `JPreDecHypK (fun c _ => NoPreKind c → False)` by
  definition); `KDispHypsK K` = `KDispHyps13P` with `JPreDecHypK K`;
  `KDispHypsK.to` (a stronger family premise from a weaker one at each
  dispatch state), `KDispHypsK.to13P`.
* `PreKind14`: CNode and Thread caps, and an Untyped cap whose first argument
  is a VT-x object type (14..18; those are `JUtPath.vtx` [scope] anyway, stated
  at `JAtPre`, so they stay here).
* `jPreDecHyp_of14`: `JPreDecHyp` from `JPreDecHypK PreKind14` at a `JAtZ`
  dispatch state: the Untyped cap by UtRetResetJM's `decode_invocation_untypedJM`
  with `JAtZ.jUtRetHypM` (RAM: the reset under `MachPlat`, `reset_loopJM`) or
  `JAtZ.jUtRetHypDevM` (device: never preempted), from the cap's `JPath`.
* `kernel_entryJ14P`: `kernel_entryJ13P` with `KDispHypsK PreKind14`;
  `j14P_platform` (non-vacuity of the platform premises, as `j13P_platform`).
-/
import Fl4Proofs.P3.XTopJointKEntry13P
import Fl4Proofs.P3.UtRetResetJM
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The caps `JPreDecHyp` is still asked for after mr5 step 1** (module
docstring): CNode, Thread, and an Untyped cap at a VT-x object type. -/
def PreKind14 : capability.Cap → List U64 → Prop
  | .CNode .., _ => True
  | .Thread _, _ => True
  | .Untyped .., argsU => ∃ x, argsU.head? = some x ∧ 14 ≤ x.val ∧ x.val < 19
  | _, _ => False

variable {arI}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {MR : A → Fl4Spec.MachineState → Prop}

end

end

end Fl4Proofs.P3
