/-
Range specs for small helpers whose callers' P0 proofs need more than
"does not fail", e.g. that a shift amount masked with `& 63` is below 64.
xtask/scripts/gen_p0.py derives each one's P0 theorem from its spec.
-/
import Fl4Core.Funs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P0
open fl4_core

@[step] theorem debug.type_shift.spec (bp : U64) :
    debug.type_shift bp ⦃ r => r.val < 64 ⦄ := by
  unfold debug.type_shift; step*

@[step] theorem debug.size_shift.spec (bp : U64) :
    debug.size_shift bp ⦃ r => r.val < 64 ⦄ := by
  unfold debug.size_shift; step*

end Fl4Proofs.P0
