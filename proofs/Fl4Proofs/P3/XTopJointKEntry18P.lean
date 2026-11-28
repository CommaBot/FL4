/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr7): **`kernel_entryJ18P`**,
XTopJointKEntry17P's `kernel_entryJ17P` with the Thread invocation taken out
of `JPreDecHypK` [W]: the five installing labels run the deletion loop at
`MachPlat` (XTopJointMRTcb, XTopJointMRTcbL), so the Thread cap's decode is
proved at `JAtPreMV`.

* `PreKind18`: an Untyped cap whose first argument is a VT-x object type
  (14..18, `JUtPath.vtx` [scope]); nothing else.
* `jPreDecHyp_of18`: `JPreDecHypK PreKind17` from `JPreDecHypK PreKind18` at a
  `JAtZ` dispatch state: the Thread cap as XTopJointEntry's `decOK_J` does
  (generated: scratch/mr7/gen18.py + t18.lean), by XTopJointMRTcbL's
  `decode_invocation_threadJ_stepM` (`MRV` at the dispatch state from
  `JPreDecHypK`'s own premises, `MachPlat`, `MRKeepD`, `JEntryGlobM.ppA`);
  SetEPTRoot ([scope] `JVtxScope`, stated at `JAtPre`) by `XCapP.reXP`: its
  spec decode is no installing label, so it never preempts.
* `kernel_entryJ18P`: J17P with `KDispHypsKV7 PreKind18`.
-/
import Fl4Proofs.P3.XTopJointKEntry17P
import Fl4Proofs.P3.XTopJointMRTcbL
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **The caps `JPreDecHypK` is still asked for after mr7's Thread step**
(module docstring): an Untyped cap at a VT-x object type. -/
def PreKind18 : capability.Cap → List U64 → Prop
  | .Untyped .., argsU => ∃ x, argsU.head? = some x ∧ 14 ≤ x.val ∧ x.val < 19
  | _, _ => False

end

end Fl4Proofs.P3
