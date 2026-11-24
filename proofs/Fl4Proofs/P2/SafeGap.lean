/-
P2: **`BodyOK` does not follow from the per-path obligations** (a
counterexample to step 4 of the handoff plan in `SerialSafe.lean`).

`SerialSafe.Safe` checks a body in the **start-memory world**: at a
speculative read (`rds`) it asks every continuation `k v` to be safe from the
*unchanged* memory `μ`, so a later write is checked (`MoveV`) against owners
computed with the racy word still at its start value. `PathObl.dec_alt`
certifies the declined run in the **read-value world**: from an alternative
state where the racy word *holds* `v`, every write passes `StepOK` there.
`Deciders` does not bridge the two when the racy value moves the racy word
itself to the gate (or to a held owner), which no other core can do beside the
gate, but which `Safe`'s `∀ v` still explores.

The toy (words `z = false`, `a = true`; cores `c = false`, `d = true`; one
lock `()`, held by `d`, so `c` holds only `core c`):

* `own z` = gate if `z = 1`, else `lock ()`; `own a` = `core c`, except when
  `a = 1 ∧ z ≠ 1`, where it is `lock ()`. `Deciders` holds (`town_deciders`).
* Body on core `c` (`tprog`): read `z` speculatively (it is `lock ()`'s, held
  by `d`, not in `ReadSet`); if it read 1, write `a := 1`.
* Its `PathObl` v3 holds with `Acc` false, `ReadSet = ∅`, `DecSet = {a}`,
  `Pre m := m a ≠ 1 ∨ m z = 1`, no locks, `ko` free: `write_own` (`a` is
  `core c`'s at every `Pre` state), `dec_alt`'s per-write check (the write
  happens only where `z = 1`, and there it moves no owner: `town_move_racy`),
  `move` likewise; `DecOnce` (one racy read), alignment, no user words.
* `Safe` from the start memory `z = a = 0` fails (`body_not_safe`): in the
  branch `v = 1`, writing `a := 1` with `z` still 0 moves `a` to `lock ()`,
  not held by `c`. So `BodyOK` is false at a reachable state (`c` arms and
  enters with `d` holding the lock), while every real execution is `Allowed`:
  `d` cannot make `z = 1` beside the gate (that would move `z` to the gate).

Consequence: `BodyOK` with the present `Safe` cannot be discharged from
`PathObl` v3 + `DecOnce` + `Deciders`. A fix must check the continuation in the
worlds the interleaving can actually reach, e.g. a `Safe` whose premises are
required at every memory reachable from `μ` by `Foreign` writes (then
`Safe.foreign` is immediate and the read value is the reached memory's,
matching `dec_alt`'s alternative states), or strengthen `PathObl` so the
per-write check is made against the start-memory world.
-/
import Fl4Proofs.P2.SerialSafe

namespace Fl4Proofs.P2.SafeGap
open Fl4Proofs.P2.Serial

/-- The toy ownership map (`false` = `z`, `true` = `a`; core `false` runs the
path; the one lock is held by core `true`). -/
def town (m : Bool → ℕ) : Bool → Owner Bool Unit
  | false => if m false = 1 then .gate else .lock ()
  | true => if m true = 1 then (if m false = 1 then .core false else .lock ()) else .core false

theorem town_deciders : Deciders town := by
  intro m b v x hx
  cases b <;> cases x
  · exact Or.inl rfl
  · by_cases hz : m false = 1
    · right; simp [town, hz]
    · left
      by_cases ha : m true = 1
      · simp [town, hz, ha]
      · exfalso; apply hx
        have h1 : Function.update m false v true = m true := Function.update_of_ne (by decide) _ _
        simp [town, h1, ha]
  · exfalso; apply hx
    have h1 : Function.update m true v false = m false := Function.update_of_ne (by decide) _ _
    simp [town, h1]
  · exact Or.inl rfl

/-- At every entry with `a ≠ 1 ∨ z = 1` (`Pre`), `a` is `core c`'s. -/
theorem town_entry (m : Bool → ℕ) (h : m true ≠ 1 ∨ m false = 1) : town m true = .core false := by
  rcases h with h | h
  · simp [town, h]
  · by_cases ha : m true = 1 <;> simp [town, h, ha]

/-- In the read-value world (`z = 1`), the write `a := 1` moves no owner. -/
theorem town_move_racy (m : Bool → ℕ) (hz : m false = 1) :
    MoveV town false (fun _ : Unit => False) m (Function.update m true 1) := by
  intro x hx
  exfalso; apply hx
  have h1 : Function.update m true 1 false = m false := Function.update_of_ne (by decide) _ _
  cases x
  · simp [town, h1]
  · by_cases ha : m true = 1 <;> simp [town, h1, hz, ha]

/-- The body: read `z` speculatively; if 1, write `a := 1`. -/
def tprog : Prog Bool ℕ Unit :=
  .rds false (fun v => if v = 1 then .wr true 1 .done else .done)

/-- **`Safe` fails at the start memory** (any classes). -/
theorem body_not_safe (cls : Bool → ℕ → ℕ) (ko : Bool → ClsOwner Bool) :
    ¬ Safe town cls ko false (fun _ : Unit => False) (fun _ => 0) tprog := by
  intro h
  cases h with
  | rds hk =>
    have h1 : Safe town cls ko false (fun _ : Unit => False) (fun _ => 0)
        (Prog.wr true 1 Prog.done) := by
      have h0 := hk 1
      dsimp only at h0
      rw [if_pos rfl] at h0
      exact h0
    cases h1 with
    | wr _ hm _ _ =>
      have hne : town (Function.update (fun _ => 0) true 1) true ≠ town (fun _ => 0) true := by
        simp [town]
      have h2 := (hm true hne).2
      simp [town, HeldV] at h2

end Fl4Proofs.P2.SafeGap
