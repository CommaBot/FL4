/-
# P2: guarded = real, with a postcondition (`GE`), and its composition rules

For the per-path obligation's `acc` (`P2/PathObl.lean`): `GE m' m Q` says the computation `m'` (run on a
guarded store) is `m` (the same code on the real store), and every value `m` returns satisfies `Q`. The
rules follow the code's shape, so a body whose reads and writes are covered by leaf lemmas is discharged by
unfolding it and applying them in program order:

* `GE.ret`, `GE.refl` (a store-free step, syntactically equal on both sides: its value is what it returns),
  `GE.bind` (the continuation at the values the first step's `Q` admits), `GE.ite`, `GE.mono`;
* normalisers for a bind whose first step is itself a bind, an `ok` or an `if`, and for a tuple-let
  (`Aeneas.Std.uncurry`): `GE.bind_assoc`, `GE.bind_ok`, `GE.bind_ite`, `GE.uncurry`;
* `GE.loop`: along a loop, an invariant of the real loop states and a decreasing measure.

`ge_step` applies one rule (store-free binds by `GE.refl` at reducible transparency, so a guarded step is
never unfolded against a real one); callers extend it with their leaf lemmas (`P2/FootTimerGE.lean`).

No named premises.
-/
import Fl4Proofs.P2.AccessSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P1

/-- The guarded computation `m'` is the real one `m`, and `m`'s values satisfy `Q`. -/
def GE {α : Type} (m' m : Result α) (Q : α → Prop) : Prop := m' = m ∧ ∀ x, m = ok x → Q x

namespace GE

theorem ret {α : Type} {x : α} {Q : α → Prop} (h : Q x) : GE (ok x) (ok x) Q :=
  ⟨rfl, fun y e => (ok_inj_ff e) ▸ h⟩

theorem refl {α : Type} (m : Result α) : GE m m (fun x => m = ok x) := ⟨rfl, fun _ e => e⟩

theorem mono {α : Type} {m m' : Result α} {P Q : α → Prop} (h : GE m' m P) (hq : ∀ x, P x → Q x) :
    GE m' m Q := ⟨h.1, fun x e => hq x (h.2 x e)⟩

theorem bind {α β : Type} {m m' : Result α} {k k' : α → Result β} {P : α → Prop} {Q : β → Prop}
    (h : GE m' m P) (hk : ∀ x, P x → GE (k' x) (k x) Q) : GE (Std.bind m' k') (Std.bind m k) Q := by
  obtain ⟨e, hp⟩ := h
  refine ⟨PathObl.bind_guard_congr e fun x hx => (hk x (hp x hx)).1, fun y hy => ?_⟩
  cases m with
  | ret x => rw [bind_ok] at hy; exact (hk x (hp x rfl)).2 y hy
  | vis i k0 =>
    have h2 := spec_of_eq_fd hy
    rw [bind_vis] at h2
    simp [WP.spec_vis] at h2
  | div =>
    have h2 := spec_of_eq_fd hy
    rw [bind_div] at h2
    simp [WP.spec_div] at h2

theorem ite {α : Type} {c : Prop} [Decidable c] {a a' b b' : Result α} {Q : α → Prop}
    (h1 : c → GE a' a Q) (h2 : ¬ c → GE b' b Q) : GE (if c then a' else b') (if c then a else b) Q := by
  by_cases hc : c
  · simp only [if_pos hc]; exact h1 hc
  · simp only [if_neg hc]; exact h2 hc

theorem bind_assoc {α β γ : Type} {m m' : Result α} {f f' : α → Result β} {k k' : β → Result γ}
    {Q : γ → Prop} (h : GE (Std.bind m' fun x => Std.bind (f' x) k') (Std.bind m fun x => Std.bind (f x) k) Q) :
    GE (Std.bind (Std.bind m' f') k') (Std.bind (Std.bind m f) k) Q := by
  rw [Std.bind_assoc, Std.bind_assoc]; exact h

theorem bind_ok {α β : Type} {x : α} {k k' : α → Result β} {Q : β → Prop} (h : GE (k' x) (k x) Q) :
    GE (Std.bind (ok x) k') (Std.bind (ok x) k) Q := by
  rw [Std.bind_ok, Std.bind_ok]; exact h

theorem bind_ite {α β : Type} {c : Prop} [Decidable c] {a a' b b' : Result α} {k k' : α → Result β}
    {Q : β → Prop} (h : GE (if c then Std.bind a' k' else Std.bind b' k') (if c then Std.bind a k else Std.bind b k) Q) :
    GE (Std.bind (if c then a' else b') k') (Std.bind (if c then a else b) k) Q := by
  by_cases hc : c
  · simp only [if_pos hc] at h ⊢; exact h
  · simp only [if_neg hc] at h ⊢; exact h

theorem uncurry {α β γ : Type} {f f' : α → β → Result γ} {a : α} {b : β} {Q : γ → Prop}
    (h : GE (f' a b) (f a b) Q) : GE (Aeneas.Std.uncurry f' (a, b)) (Aeneas.Std.uncurry f (a, b)) Q := by
  rw [uncurry_apply_pair, uncurry_apply_pair]; exact h

end GE

/-- A loop body's postcondition: a `cont` state keeps `I` with a smaller measure, a `done` value
satisfies `Q`. -/
def LoopPost {α β : Type} (I : α → Prop) (μ : α → Nat) (Q : β → Prop) (x : α) : ControlFlow α β → Prop
  | .cont y => I y ∧ μ y < μ x
  | .done z => Q z

namespace GE

/-- Along a loop: an invariant `I` of the real loop states, kept by the real body's `cont` steps with a
decreasing measure `μ`; its `done` values satisfy `Q`. -/
theorem loop {α β : Type} {body body' : α → Result (ControlFlow α β)} (I : α → Prop) (μ : α → Nat)
    {Q : β → Prop}
    (h : ∀ x, I x → GE (body' x) (body x) (LoopPost I μ Q x)) :
    ∀ x, I x → GE (Aeneas.Std.loop body' x) (Aeneas.Std.loop body x) Q := by
  suffices H : ∀ n x, μ x = n → I x → GE (Aeneas.Std.loop body' x) (Aeneas.Std.loop body x) Q from
    fun x hx => H _ x rfl hx
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hn hx
    unfold Aeneas.Std.loop
    refine GE.bind (h x hx) fun r hr => ?_
    cases r with
    | cont y => exact ih (μ y) (hn ▸ hr.2) y rfl hr.1
    | done z => exact GE.ret hr

end GE

/-- `fuel - 1` below a non-zero `fuel`. -/
theorem ge_sub1_lt' {fuel fuel1 : U64} (h : ¬ fuel = 0#u64) (e : fuel - 1#u64 = ok fuel1) :
    fuel1.val < fuel.val := by
  have h0 : fuel.val ≠ 0 := fun e0 => h (UScalar.eq_of_val_eq (by simp [e0]))
  obtain ⟨z, ez, hz⟩ := spec_ex_fd (U64.sub_spec (x := fuel) (y := 1#u64) (by scalar_tac))
  rw [ez] at e
  have := ok_inj_ff e
  subst this
  scalar_tac

/-- `fuel - 1` below a positive `fuel`. -/
theorem ge_sub1_lt {fuel fuel1 : U64} (h : fuel > 0#u64) (e : fuel - 1#u64 = ok fuel1) :
    fuel1.val < fuel.val := by
  obtain ⟨z, ez, hz⟩ := spec_ex_fd (U64.sub_spec (x := fuel) (y := 1#u64) (by scalar_tac))
  rw [ez] at e
  have := ok_inj_ff e
  subst this
  scalar_tac

/-- One composition rule (no leaf lemmas). -/
macro "ge_step" : tactic => `(tactic| with_reducible first
  | with_reducible apply GE.bind_assoc
  | with_reducible apply GE.bind_ok
  | with_reducible apply GE.bind_ite
  | with_reducible apply GE.uncurry
  | (with_reducible refine GE.ite (fun _ => ?_) (fun _ => ?_))
  | (with_reducible refine GE.ret ?_)
  | (with_reducible refine GE.bind (GE.refl _) (fun _ _ => ?_)))

end Fl4Proofs.P2
