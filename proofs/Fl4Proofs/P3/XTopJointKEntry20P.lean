/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr8): **`kernel_entryJ20P`**,
XTopJointKEntry19P's `kernel_entryJ19P` with no [W] invocation premise left:
the last case `JPreDecHypK PreKind18` [W] asked for (an Untyped cap retyping
a VT-x object, types 14..18) is out of the semantic scope, as XTopJointEntry's
`JVtxScope` [scope] already says for every other VT-x decode (lead decision,
mr7's open question). It is now asked as that scope premise, stated at
`MachPlat`'s preempted post:

* `JVtxScopeM` [scope]: `JVtxScope` with `JAtPreMV MR` as the preempted post.
* `JVtxHypM` [scope]: `JVtxScopeM` for an Untyped cap whose first argument is a
  VT-x object type (14..18), at the dispatch state, with exactly the decode
  facts `JPreDecHypK PreKind18` had (it replaces it field for field).
* `jPreDecHyp_of20`: `JPreDecHypK PreKind18` from `JVtxHypM` (an unfold:
  `PreKind18` names only those caps).
* `KDispHypsKV20` (`KDispHypsKV12 PreKind18` with `JVtxHypM`), `.to12`, NEW TOP
  `kernel_entryJ20P` (wrapper over J19P), `j20P_platform` (non-vacuity of the
  platform premises, unchanged: `j19P_platform`).
-/
import Fl4Proofs.P3.XTopJointKEntry18P
import Fl4Proofs.P3.XTopJointKEntry21M
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **A VT-x cap's decode at `MachPlat`** [scope]: `JVtxScope` (XTopJointEntry)
with `JAtPreMV MR` as the preempted post. Same scope justification: outside
the semantic scope (DESIGN §9: the VCPU/EPT object families have no functional
refinement yet; P0 covers their extracted core), the cap's statement named.
The `MachPlat` form is needed because the one decode stated with it, an
Untyped retype to a VT-x type (`JVtxHypM`), may run the untyped reset, whose
preemption point can preempt: the preempted post must then carry the machine
facts (`MR`, `ValidMachineTime`, `ValidIrqMasks`) the `MachPlat` top needs,
and `XCapP.reXP` (which turns a `JAtPre` statement into a `JAtPreMV` one) only
applies to decodes that never preempt. -/
abbrev JVtxScopeM (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (lbl length : U64)
    (c : capability.Cap) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (argsU : List U64) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef) (ct : U64) : Prop :=
  XCapP (L := L) arI (JAt (L := L) arI AR) (JAtPreMV (L := L) arI AR MR) s ar σ lbl length (cslotAddr sl) c blk
    call don fp buf extra slbl (argsU.map UScalar.bv) ci sl excaps buffer ct

variable {arI} {MR : A → Fl4Spec.MachineState → Prop}

end

end

end Fl4Proofs.P3
