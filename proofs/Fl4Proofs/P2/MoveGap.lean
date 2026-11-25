/-
P2: **why the `SafeStep.start` bridge needs `MoveLocal` beside `Deciders`** (the open
point of `SerialSafe`'s plan, step 4).

`PathObl.dec_alt` certifies a declined run's writes (`StepOK`, i.e. `MoveV`)
in an alternative state `s*` that holds, at once, every value the path read
racily. In the real interleaving those reads happened at different times: when
the path writes, the memory `μ` differs from the alternative `μ*` on words
other cores wrote (non-`PO` for this core in `μ`). With `Deciders` alone the
owners of the core's words need not agree across `μ` and `μ*`: two racy words
can together, in `μ*`, decide an owner (here: make themselves gate-owned and
pin the written word to this core), although no real memory ever holds both
values (they are another core's words, and the combination would move them to
the gate, which `Foreign` forbids).

The toy (words `a`, `b1`, `b2`; cores `c = false`, `d = true`; no locks):

* `own b1 = own b2` = gate if `b1 = b2 = 1`, else `core d`; `own a` =
  `core c` if `b1 = b2 = 1`, else `core d` if `a = 1`, else `core c`.
  `Deciders` holds (`mown_deciders`).
* Body on core `c` (`mprog`): read `b1`, then `b2`, speculatively (they are
  `d`'s, not in `ReadSet`); if both read 1, write `a := 1`; decline.
* Its `PathObl` v3 holds with `Acc` false, `ReadSet = ∅`, `DecSet = {a}`,
  `ko` free: `write_own` (`a` is `core c`'s at the entry `a = b1 = b2 = 0`,
  `mown_entry`), `dec_alt`'s per-write check (in every alternative the write
  happens only where `b1 = b2 = 1`, and there it moves no owner:
  `mown_move_alt`), `DecOnce` (each racy word read once), alignment.
* `Safe` (v2) fails from the entry (`body_not_safe`): `d` writes `b1 := 1`
  (`Foreign`), `c` reads 1, `d` writes `b1 := 0` and `b2 := 1`, `c` reads 1,
  and `c`'s write `a := 1` in the memory `b1 = 0, b2 = 1` moves `a` to
  `core d`. This is a real execution (each of `d`'s writes moves no owner, so
  it is `Allowed` for `d`) whose step of `c` is not `Allowed`, not only not `Safe`.
* `MoveLocal` fails for `mown` (`mown_not_moveLocal`): where `a` moves after
  the write is decided by `b1`, `b2`, which are neither `a`'s owner's nor the
  gate's.

Consequence: `SafeStep.start` cannot be discharged from `PathObl` v3 + `DecOnce` +
`Deciders`. With `SerialSafe.MoveHeld` (proved for `OwnMap.own`:
`OwnMap.moveHeld`; `Deciders` and `MoveLocal` imply it) the per-write check transfers from `μ*` to `μ`
(`SerialSafe.moveV_transfer`), since `μ` and `μ*` differ only on words the core
may not read in `μ`.
-/
import Fl4Proofs.P2.SerialSafe

namespace Fl4Proofs.P2.MoveGap
open Fl4Proofs.P2.Serial

/-- The toy's words. -/
inductive W where
  | a
  | b1
  | b2
  deriving DecidableEq

/-- The toy ownership map (core `false` runs the path, core `true` owns `b1`, `b2`). -/
def mown (m : W → ℕ) : W → Owner Bool Unit
  | .a => if m .b1 = 1 ∧ m .b2 = 1 then .core false
      else if m .a = 1 then .core true else .core false
  | _ => if m .b1 = 1 ∧ m .b2 = 1 then .gate else .core true

theorem mown_deciders : Deciders mown := by
  intro m b v x hx
  cases b with
  | a =>
    cases x with
    | a => exact Or.inl rfl
    | b1 => exfalso; apply hx; simp [mown, Function.update]
    | b2 => exfalso; apply hx; simp [mown, Function.update]
  | b1 =>
    by_cases h11 : m .b1 = 1 ∧ m .b2 = 1
    · right; simp only [mown, if_pos h11]
    · cases x with
      | a =>
        by_cases ha : m .a = 1
        · left; simp only [mown, if_neg h11, if_pos ha]
        · exfalso; apply hx; simp [mown, Function.update, ha, h11]
      | b1 => exact Or.inl rfl
      | b2 => left; rfl
  | b2 =>
    by_cases h11 : m .b1 = 1 ∧ m .b2 = 1
    · right; simp only [mown, if_pos h11]
    · cases x with
      | a =>
        by_cases ha : m .a = 1
        · left; simp only [mown, if_neg h11, if_pos ha]
        · exfalso; apply hx; simp [mown, Function.update, ha, h11]
      | b1 => left; rfl
      | b2 => exact Or.inl rfl

/-- The body: read `b1`, `b2` speculatively; if both are 1, write `a := 1`. -/
def mprog : Prog W ℕ Unit :=
  .rds .b1 (fun u => .rds .b2 (fun w => if u = 1 ∧ w = 1 then .wr .a 1 .done else .done))

/-- At the entry `a = b1 = b2 = 0`, `a` is `core c`'s. -/
theorem mown_entry : mown (fun _ => 0) .a = .core false := by simp [mown]

/-- In every alternative memory where the write happens (`b1 = b2 = 1`), it moves no owner. -/
theorem mown_move_alt (m : W → ℕ) (h1 : m .b1 = 1) (h2 : m .b2 = 1) :
    MoveV mown false (fun _ : Unit => False) m (Function.update m .a 1) := by
  intro x hx
  exfalso; apply hx
  cases x <;> simp [mown, Function.update, h1, h2]

/-- The memories of the run: entry, `b1 = 1`, `b2 = 1`. -/
def m0 : W → ℕ := fun _ => 0
def m1 : W → ℕ
  | .b1 => 1
  | _ => 0
def m2 : W → ℕ
  | .b2 => 1
  | _ => 0

/-- A write of `d` (to `b1` or `b2`) between memories where neither has both
racy words 1 and `a = 0` moves no owner, so it is `Foreign` for `c`. -/
theorem foreign_d (cls : W → ℕ → ℕ) {μ : W → ℕ} {b : W} {v : ℕ} (hb : b ≠ .a)
    (ha : μ .a = 0) (h11 : ¬ (μ .b1 = 1 ∧ μ .b2 = 1))
    (h11' : ¬ (Function.update μ b v .b1 = 1 ∧ Function.update μ b v .b2 = 1)) :
    Foreign mown cls (fun _ => .free) false (fun _ : Unit => False) μ b v := by
  have ha' : Function.update μ b v .a = 0 := by rw [Function.update_of_ne (Ne.symm hb)]; exact ha
  have hown : ∀ x, mown (Function.update μ b v) x = mown μ x := by
    intro x
    cases x <;> simp only [mown, if_neg h11, if_neg h11', ha, ha']
  refine ⟨?_, fun x hx => absurd (hown x) hx, Or.inr ⟨by simp, by simp⟩⟩
  cases b with
  | a => exact absurd rfl hb
  | b1 => simp [mown, h11, PO, HeldV]
  | b2 => simp [mown, h11, PO, HeldV]

/-- **The body is not `Safe` (v2) from the entry** (any classes, `ko` free). -/
theorem body_not_safe (cls : W → ℕ → ℕ) :
    ¬ Safe mown cls (fun _ => .free) false (fun _ : Unit => False) m0 mprog := by
  intro h
  have e01 : Function.update m0 .b1 1 = m1 := by funext y; cases y <;> rfl
  have e10 : Function.update m1 .b1 0 = m0 := by funext y; cases y <;> rfl
  have e02 : Function.update m0 .b2 1 = m2 := by funext y; cases y <;> rfl
  have hR1 : FReach mown cls (fun _ => .free) false (fun _ : Unit => False) m0 m1 := by
    refine .step (foreign_d cls (b := .b1) (v := 1) (by decide) rfl (by decide) ?_) ?_
    · rw [e01]; decide
    · rw [e01]; exact .refl _
  have hR2 : FReach mown cls (fun _ => .free) false (fun _ : Unit => False) m1 m2 := by
    refine .step (foreign_d cls (b := .b1) (v := 0) (by decide) rfl (by decide) ?_) ?_
    · rw [e10]; decide
    rw [e10]
    refine .step (foreign_d cls (b := .b2) (v := 1) (by decide) rfl (by decide) ?_) ?_
    · rw [e02]; decide
    · rw [e02]; exact .refl _
  cases h with
  | rds hk =>
    have h1 : Safe mown cls (fun _ => .free) false (fun _ : Unit => False) m1
        (.rds .b2 (fun w => if m1 .b1 = 1 ∧ w = 1 then .wr .a 1 .done else .done)) := hk m1 hR1
    cases h1 with
    | rds hk2 =>
      have h2 : Safe mown cls (fun _ => .free) false (fun _ : Unit => False) m2
          (if m1 .b1 = 1 ∧ m2 .b2 = 1 then .wr .a 1 .done else .done) := hk2 m2 hR2
      have e : (m1 .b1 = 1 ∧ m2 .b2 = 1) := ⟨rfl, rfl⟩
      rw [if_pos e] at h2
      cases h2 with
      | wr _ hm _ _ =>
        have hne : mown (Function.update m2 .a 1) .a ≠ mown m2 .a := by
          simp [mown, m2, Function.update]
        have := (hm m2 (.refl _) .a hne).2
        simp [mown, m2, Function.update, HeldV] at this

/-- **`MoveLocal` fails for the toy**: whether `a` moves is decided by `b1`, `b2`. -/
theorem mown_not_moveLocal : ¬ MoveLocal mown := by
  intro h
  have e := h m2 (Function.update m2 .b1 1) .a 1 .a (by simp [mown, m2]) rfl (by
    intro y hy
    cases y with
    | a => rfl
    | b1 => simp [mown, m2] at hy
    | b2 => rfl)
  simp [mown, m2, Function.update] at e

end Fl4Proofs.P2.MoveGap
