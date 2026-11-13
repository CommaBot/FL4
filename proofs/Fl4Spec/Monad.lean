/-
The nondeterministic state monad of the seL4 abstract specification
(l4v lib/Monads/nondet/Nondet_Monad.thy), the base of the Lean port of
the spec (DESIGN.md §9, "The abstract spec").

A computation maps a state to the set of its possible (result, new state)
pairs and whether it can fail. Failure is a `Prop`: the spec only needs
to state it, and nondeterministic parts are not executed. The exception
monad of l4v (`('s, 'e + 'a) nondet_monad`, `bindE`, `throwError`,
`liftE`) is `ExceptT ε (NonDet σ)`.
-/
import Mathlib.Data.Set.Basic

namespace Fl4Spec

/-- l4v `nondet_monad`. -/
def NonDet (σ α : Type) : Type := σ → Set (α × σ) × Prop

namespace NonDet
variable {σ α β : Type}

/-- l4v `return`. -/
def pure (a : α) : NonDet σ α := fun s => ({(a, s)}, False)

/-- l4v `bind`: every result of `m` continues with `f`; the whole fails if
`m` fails or `f` fails from any result of `m`. -/
def bind (m : NonDet σ α) (f : α → NonDet σ β) : NonDet σ β := fun s =>
  ({r | ∃ x ∈ (m s).1, r ∈ (f x.1 x.2).1}, (m s).2 ∨ ∃ x ∈ (m s).1, (f x.1 x.2).2)

instance : Monad (NonDet σ) where
  pure := NonDet.pure
  bind := NonDet.bind

/-- l4v `get`. -/
def get : NonDet σ σ := fun s => ({(s, s)}, False)
/-- l4v `put`. -/
def put (s : σ) : NonDet σ Unit := fun _ => ({((), s)}, False)
/-- l4v `gets`. -/
def gets (f : σ → α) : NonDet σ α := fun s => ({(f s, s)}, False)
/-- l4v `modify`. -/
def modify (f : σ → σ) : NonDet σ Unit := fun s => ({((), f s)}, False)
/-- l4v `select`: any element of `A`. -/
def select (A : Set α) : NonDet σ α := fun s => ({x | x.1 ∈ A ∧ x.2 = s}, False)
/-- l4v `alternative` (`⊓`): either computation. -/
def alternative (f g : NonDet σ α) : NonDet σ α := fun s => ((f s).1 ∪ (g s).1, (f s).2 ∨ (g s).2)
/-- l4v `fail`. -/
def fail : NonDet σ α := fun _ => (∅, True)
/-- l4v `assert`. -/
def assert (P : Prop) : NonDet σ Unit := fun s => ({x | P ∧ x = ((), s)}, ¬P)
/-- l4v `assert_opt`. -/
def assertOpt : Option α → NonDet σ α
  | some a => NonDet.pure a
  | none => fail
/-- l4v `state_assert`. -/
def stateAssert (P : σ → Prop) : NonDet σ Unit := fun s => assert (P s) s
/-- l4v `gets_the`. -/
def getsThe (f : σ → Option α) : NonDet σ α := fun s => assertOpt (f s) s
/-- l4v `when`. -/
def when (P : Prop) [Decidable P] (m : NonDet σ Unit) : NonDet σ Unit := if P then m else NonDet.pure ()
/-- l4v `unless`. -/
def «unless» (P : Prop) [Decidable P] (m : NonDet σ Unit) : NonDet σ Unit := if P then NonDet.pure () else m

/-- l4v `mapM_x`. -/
def mapMx (f : α → NonDet σ β) : List α → NonDet σ Unit
  | [] => NonDet.pure ()
  | a :: as => NonDet.bind (f a) fun _ => mapMx f as

/-- Results of l4v `whileLoop C B` from `r, s`: the states where the
condition first fails, after any number of rounds of the body. -/
inductive WhileResults (C : α → σ → Prop) (B : α → NonDet σ α) : α → σ → α × σ → Prop
  | done {r s} : ¬C r s → WhileResults C B r s (r, s)
  | step {r s r' s' x} : C r s → (r', s') ∈ (B r s).1 → WhileResults C B r' s' x → WhileResults C B r s x

/-- States reachable at the start of a round. -/
inductive WhileReach (C : α → σ → Prop) (B : α → NonDet σ α) (r₀ : α) (s₀ : σ) : α → σ → Prop
  | start : WhileReach C B r₀ s₀ r₀ s₀
  | step {r s r' s'} : WhileReach C B r₀ s₀ r s → C r s → (r', s') ∈ (B r s).1 → WhileReach C B r₀ s₀ r' s'

/-- l4v `whileLoop`: fails if the body fails in a reachable round or the
loop can run forever. -/
def whileLoop (C : α → σ → Prop) (B : α → NonDet σ α) (r : α) : NonDet σ α := fun s =>
  ({x | WhileResults C B r s x},
   (∃ r' s', WhileReach C B r s r' s' ∧ C r' s' ∧ (B r' s').2) ∨
   (∃ f : ℕ → α × σ, f 0 = (r, s) ∧ ∀ n, C (f n).1 (f n).2 ∧ f (n + 1) ∈ (B (f n).1 (f n).2).1))

/-- The computation never fails from `s` (l4v `no_fail` at one state). -/
def NoFail (m : NonDet σ α) (s : σ) : Prop := ¬(m s).2

/-- Hoare triple (l4v `valid`): from any state satisfying `P`, every
result satisfies `Q`. -/
def Valid (P : σ → Prop) (m : NonDet σ α) (Q : α → σ → Prop) : Prop :=
  ∀ s, P s → ∀ x ∈ (m s).1, Q x.1 x.2

end NonDet

/-- l4v's exception monad `('s, 'e + 'a) nondet_monad`. -/
abbrev NonDetE (σ ε α : Type) := ExceptT ε (NonDet σ) α

namespace NonDetE
variable {σ ε α : Type}
/-- l4v `liftE`. -/
def liftE (m : NonDet σ α) : NonDetE σ ε α := ExceptT.lift m
/-- l4v `throwError`. -/
def «throwError» (e : ε) : NonDetE σ ε α := throw e
/-- l4v `returnOk`. -/
def returnOk (a : α) : NonDetE σ ε α := pure a
/-- l4v `whenE`. -/
def whenE (P : Prop) [Decidable P] (m : NonDetE σ ε Unit) : NonDetE σ ε Unit := if P then m else pure ()
/-- l4v `unlessE`. -/
def unlessE (P : Prop) [Decidable P] (m : NonDetE σ ε Unit) : NonDetE σ ε Unit := if P then pure () else m
/-- l4v `throw_opt`. -/
def throwOpt (e : ε) : Option α → NonDetE σ ε α
  | some a => pure a
  | none => throw e
/-- l4v `assertE`. -/
def assertE (P : Prop) : NonDetE σ ε Unit := liftE (NonDet.assert P)
/-- l4v `catch`: handle an exception with `h`. -/
def «catch» (m : NonDetE σ ε α) (h : ε → NonDet σ α) : NonDet σ α :=
  NonDet.bind (ExceptT.run m) fun
    | .ok a => NonDet.pure a
    | .error e => h e
/-- l4v `handleE'`. -/
def handleE {ε' : Type} (m : NonDetE σ ε α) (h : ε → NonDetE σ ε' α) : NonDetE σ ε' α :=
  ExceptT.mk (NonDet.bind (ExceptT.run m) fun
    | .ok a => NonDet.pure (.ok a)
    | .error e => ExceptT.run (h e))
/-- l4v `mapME_x`. -/
def mapMEx {β : Type} (f : α → NonDetE σ ε β) : List α → NonDetE σ ε Unit
  | [] => pure ()
  | a :: as => do let _ ← f a; mapMEx f as
end NonDetE

end Fl4Spec
