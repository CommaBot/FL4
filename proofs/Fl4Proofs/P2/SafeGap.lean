/-
P2: **why `SerialSafe.Safe` is stated over `Foreign`-reachable memories**: with
its first version (v1, kept here as `Safe1`, its speculative-read and write
rules) `BodyOK` does not follow from the per-path obligations; with v2 the same
body is `Safe` (`body_safe_v2`).

`Safe1` checks a body in the **start-memory world**: at a
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

Consequence: `BodyOK` with `Safe1` cannot be discharged from
`PathObl` v3 + `DecOnce` + `Deciders`. A fix must check the continuation in the
worlds the interleaving can actually reach, e.g. a `Safe` whose premises are
required at every memory reachable from `μ` by `Foreign` writes (then
`Safe.foreign` is immediate and the read value is the reached memory's,
matching `dec_alt`'s alternative states), or strengthen `PathObl` so the
per-write check is made against the start-memory world. The first is
`SerialSafe.Safe` v2; there `z = 1` is unreachable by `Foreign` writes (it
would move `z` to the gate), so the bad branch is never explored
(`freach_inv`, `body_safe_v2`).
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

/-- `Safe` v1's rules for speculative reads and writes (its class condition
on writes left out, which only weakens it): continuations of a speculative read
are checked from the unchanged memory. -/
inductive Safe1 (own : (Bool → ℕ) → Bool → Owner Bool Unit) (c : Bool) (hs : Unit → Prop) :
    (Bool → ℕ) → Prog Bool ℕ Unit → Prop
  | done {μ : Bool → ℕ} : Safe1 own c hs μ .done
  | rds {μ : Bool → ℕ} {a : Bool} {k : ℕ → Prog Bool ℕ Unit} :
      (∀ v, Safe1 own c hs μ (k v)) → Safe1 own c hs μ (.rds a k)
  | wr {μ : Bool → ℕ} {a : Bool} {v : ℕ} {k : Prog Bool ℕ Unit} :
      HeldV c hs (own μ a) → MoveV own c hs μ (Function.update μ a v) →
      Safe1 own c hs (Function.update μ a v) k → Safe1 own c hs μ (.wr a v k)

/-- **`Safe1` fails at the start memory.** -/
theorem body_not_safe : ¬ Safe1 town false (fun _ : Unit => False) (fun _ => 0) tprog := by
  intro h
  cases h with
  | rds hk =>
    have h1 : Safe1 town false (fun _ : Unit => False) (fun _ => 0)
        (Prog.wr true 1 Prog.done) := by
      have h0 := hk 1
      dsimp only at h0
      rw [if_pos rfl] at h0
      exact h0
    cases h1 with
    | wr _ hm _ =>
      have hne : town (Function.update (fun _ => 0) true 1) true ≠ town (fun _ => 0) true := by
        simp [town]
      have h2 := (hm true hne).2
      simp [town, HeldV] at h2

/-- From `a = 0, z ≠ 1`, `Foreign` writes (another core's, beside the gate)
keep `a = 0` (it is `c`'s) and `z ≠ 1` (`z = 1` would move `z` to the gate). -/
theorem freach_inv {cls : Bool → ℕ → ℕ} {ko : Bool → ClsOwner Bool} {μ μ' : Bool → ℕ}
    (hR : FReach town cls ko false (fun _ : Unit => False) μ μ') :
    μ true = 0 → μ false ≠ 1 → μ' true = 0 ∧ μ' false ≠ 1 := by
  induction hR with
  | refl => exact fun h1 h2 => ⟨h1, h2⟩
  | @step μ μ' b v hF _ ih =>
    intro h1 h2
    cases b
    · have hv : v ≠ 1 := by
        rintro rfl
        have hne : town (Function.update μ false 1) false ≠ town μ false := by
          simp [town, h2]
        exact (hF.2.1 false hne).2 (Or.inr (by simp [town]))
      exact ih (by simp [Function.update, h1]) (by simp [hv])
    · exact (hF.1 (Or.inl (by simp [town, h1, HeldV]))).elim

/-- **Regression: with `Safe` v2 the body is safe** (any classes). -/
theorem body_safe_v2 (cls : Bool → ℕ → ℕ) (ko : Bool → ClsOwner Bool) :
    Safe town cls ko false (fun _ : Unit => False) (fun _ => 0) tprog := by
  refine .rds fun μ' hR => ?_
  have h := freach_inv hR rfl (by simp)
  show Safe town cls ko false (fun _ : Unit => False) μ'
    (if μ' false = 1 then Prog.wr true 1 Prog.done else Prog.done)
  rw [if_neg h.2]
  exact .done

end Fl4Proofs.P2.SafeGap
