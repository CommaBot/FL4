/-
P3 (DESIGN.md §9), kernel entry (KENTRY-PLAN mr6): **`kernel_entryJ17P`**,
XTopJointKEntry16P's `kernel_entryJ16P` with the CNode invocation taken out of
`JPreDecHypK` [W]: CNode Revoke/Delete run the deletion loop at `MachPlat`
(XTopJointMRDel, XTopJointMRCnode), so the CNode cap's decode is proved at
`JAtPreMV`.

* `PreKind17`: Thread caps, and an Untyped cap whose first argument is a
  VT-x object type (14..18, `JUtPath.vtx` [scope]).
* `KDispHypsKV7.toK`: a dispatch premise from a narrower family premise.
* `jPreDecHyp_of17`: `JPreDecHypK PreKind14` from `JPreDecHypK PreKind17` at a
  `JAtZ` dispatch state: the CNode cap as XTopJointEntry's `decOK_J` does, by
  XTopJointMRCnode's `decode_invocation_cnodeJ_stepsLM` (`JEntryGlobM`'s
  platform/scope facts, `JEntryAt.live`, `MRV` at the dispatch state from
  `JPreDecHypK`'s own premises, `MachPlat`, `MRKeepD`, `PPPlatA`).
* `kernel_entryJ17P`: J16P with `KDispHypsKV7 PreKind17`, and `MRKeepD` [P]
  (MachKeepD: MRKeep plus the finalisation's TLB/EPT/vspace/DMA/irq_free
  operations, arch-only; `modelArch_mrKeepD`) in place of `MRKeep`.
-/
import Fl4Proofs.P3.XTopJointKEntry15P
import Fl4Proofs.P3.XTopJointKEntry16M
import Fl4Proofs.P3.XTopJointMRCnode
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **The caps `JPreDecHypK` is still asked for after mr6's CNode step**
(module docstring): Thread, and an Untyped cap at a VT-x object type. -/
def PreKind17 : capability.Cap → List U64 → Prop
  | .Thread _, _ => True
  | .Untyped .., argsU => ∃ x, argsU.head? = some x ∧ 14 ≤ x.val ∧ x.val < 19
  | _, _ => False

end

end Fl4Proofs.P3
