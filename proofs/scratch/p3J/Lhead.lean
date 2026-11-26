/-
P3 (line p3J, gen 2): **the path premises narrowed to the invoked slot** (inventory K1 / K4:
`JPathAtMU30`'s ∀-slot form is false on every SMP boot).

* **`LookAt ct cptr σ sl c`**: the spec's `lookupCapAndSlot ct (toBl cptr)` at `σ` has the single
  outcome `ok (absCap c, sl)` (l4v `lookup_cap_and_slot`, Syscall_A `handle_invocation`). With
  `capAt (L.mem s) (cslotAddr sl) = ok c` (already a hypothesis of every path premise) it pins the slot
  and the cap FL4's `cspace.lookup_slot` reads (`lookup_slot_refines`: the two lookups agree).
* `JPathAtM … JPathAtMU30` ↦ `JPathAtML … JPathAtMU29L`, **`JPathAtMU35`**: each the original with
  `LookAt ct cptr σ sl c →` after its last hypothesis (text copies, `scratch/p3J/genL.py`).
* The 16 conversions `JPathAtX.toY` re-proved on them (`…L`): the originals' proofs with the extra
  hypothesis passed through.
* **`handle_invocation_refinesMXPL`**: `handle_invocation_refinesMXP` with `hDec` asked only at the
  slot / cap the lookup returned (`LookAt`; the original proof has that outcome as `hl` where it applies
  `hDec`).
* `handle_invocation_entryJMUL`, `handle_invocation_entryJMUML`: the two consumers that apply the path
  premise (copies of `Fl4ProofsI.P3.handle_invocation_entryJMU` / `Fl4ProofsQI.P3.handle_invocation_entryJMUM`).
No new premise; no sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU35
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3

/-- **The invoked slot**: the spec's `lookupCapAndSlot` for `cptr` at `σ` returns `(absCap c, sl)`
(l4v Syscall_A `handle_invocation`: `lookup_cap_and_slot thread cptr`). -/
def LookAt (ct cptr : Aeneas.Std.U64) (σ : Fl4Spec.State Unit) (sl : Fl4Spec.CslotPtr) (c : fl4_core.capability.Cap) :
    Prop :=
  (Fl4Spec.lookupCapAndSlot (Z := Unit) ct.bv (Fl4Spec.toBl cptr.bv)).run σ = ({(.ok (absCap c, sl), σ)}, False)

end Fl4Proofs.P3
