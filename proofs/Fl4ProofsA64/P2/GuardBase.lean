/-
# P2 (AArch64): the two helpers `GuardGE` takes from modules not ported yet

x86_64's `P2/GuardGE.lean` imports `P2/AccessSched.lean`, which brings `PathObl.bind_guard_congr` (its own)
and `P1.ok_inj_ff` (from `P1/FastFin.lean`), both below the x86-only roots of P1 on AArch64. They are copied
here verbatim (same names, same proofs), so the AArch64 `GuardGE` and the program-tree base can be built
now. When `AccessSched` / `FastFin` are ported, those ports drop their copies and import this module.

No premises.
-/
import Fl4ProofsA64.P1.FastDecline
import Fl4ProofsA64.P2.AccessLeaf
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1

theorem ok_inj_ff {α : Type _} {x y : α} (h : (ok x : Result α) = ok y) : x = y := by
  have h2 := spec_of_eq_fd h; rw [WP.spec_ok] at h2; exact h2

end Fl4ProofsA64.P1

namespace Fl4ProofsA64.P2.PathObl

/-- Composing along a bind: equal first steps, and equal continuations at the
values the (real) first step produces. -/
theorem bind_guard_congr {α β : Type} {m m' : Result α} {k k' : α → Result β} (h : m' = m)
    (hk : ∀ x, m = ok x → k' x = k x) : Std.bind m' k' = Std.bind m k := by
  rw [h]
  cases m with
  | ret x => rw [bind_ok, bind_ok]; exact hk x rfl
  | vis i k0 =>
    rw [bind_vis, bind_vis]; congr 1; funext y; cases i; exact PEmpty.elim y
  | div => rw [bind_div, bind_div]

end Fl4ProofsA64.P2.PathObl
