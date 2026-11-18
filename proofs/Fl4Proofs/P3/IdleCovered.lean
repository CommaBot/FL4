/-
P3: **regression check: the joint cover does not force a cap over the idle
thread**.

Before the fix, `JCovD.h` asked every TCB of `H` to be covered by a cap or
dead, and `DeadP` excludes the idle thread, so `JAtZ` forced a physical,
non-untyped cap over the current core's idle TCB (the scheduler relation
puts it in `Z.T`, `zH` in `H`). FL4's boot (`create_idle_threads`) gives
the idle thread and the idle SC no cap, so no state reachable from boot
satisfied `JAtZ`. `JCovD` now exempts the idle objects (`IdleAt`), keeping
them outside the RAM untyped regions (`idleOut`).

`JCovD.idle_uncovered`: a heap holding only the idle TCB, with no cap at
all (so the idle TCB not covered) and no dead object, satisfies `JCovD`.
-/
import Fl4Proofs.P3.ScPlaceDead
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The idle TCB uncovered, `JCovD` holds** (module docstring). -/
theorem JCovD.idle_uncovered (s : S) (Cs : Set U64) :
    JCovD (L := L) (fun _ => none) (fun q => if q = L.idleW s then some .tcb else none)
        ⟨[], fun _ => none⟩ ∅ Cs s ∧
      ¬ Covered (L.mem s) ⟨[], fun _ => none⟩ (L.idleW s).val ((L.idleW s).val + 2 ^ P1.HKind.bits .tcb) := by
  refine ⟨⟨fun q k hq => by simp at hq, fun q k hq => ?_, fun _ h => h.elim,
    fun x hx => by simp at hx, fun x hx => by simp at hx⟩, ?_⟩
  · by_cases e : q = L.idleW s
    · exact Or.inr (Or.inr (Or.inl e))
    · simp only [e, if_false] at hq; cases hq
  · rintro ⟨y, hy, -⟩
    simp at hy

end

end Fl4Proofs.P3.Sched
