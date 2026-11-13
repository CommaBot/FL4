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
import Mathlib.Order.CompleteLattice.Basic

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

/-- l4v `forM_x` (`mapM_x` with the arguments swapped). -/
def forMx (xs : List α) (f : α → NonDet σ β) : NonDet σ Unit := mapMx f xs

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

instance : Inhabited (NonDet σ α) := ⟨fail⟩

/-- l4v `select_f`: run a precomputed result set (with failure flag) of
some other computation, leaving the state unchanged. -/
def selectF (S : Set α × Prop) : NonDet σ α := fun s => ({x | x.1 ∈ S.1 ∧ x.2 = s}, S.2)

/-- l4v `Nondet_Empty_Fail.mk_ef`: an empty result set counts as failure. -/
def mkEf (S : Set α × Prop) : Set α × Prop := (S.1, S.1 = ∅ ∨ S.2)

/-- l4v `liftM`. -/
def liftM (f : α → β) (m : NonDet σ α) : NonDet σ β := NonDet.bind m fun x => NonDet.pure (f x)

/-- l4v `gets_map`. -/
def getsMap {γ : Type} (f : σ → γ → Option α) (p : γ) : NonDet σ α :=
  NonDet.bind (gets f) fun m => assertOpt (m p)

/-- l4v `maybeM`. -/
def maybeM (f : α → NonDet σ Unit) : Option α → NonDet σ Unit
  | some x => f x
  | none => NonDet.pure ()

/-- l4v `mapM`. -/
def mapM (f : α → NonDet σ β) : List α → NonDet σ (List β)
  | [] => NonDet.pure []
  | a :: as => NonDet.bind (f a) fun b => NonDet.bind (mapM f as) fun bs => NonDet.pure (b :: bs)

/-- l4v `zipWithM_x`. -/
def zipWithMx {γ : Type} (f : α → β → NonDet σ γ) : List α → List β → NonDet σ Unit
  | a :: as, b :: bs => NonDet.bind (f a b) fun _ => zipWithMx f as bs
  | _, _ => NonDet.pure ()

/-- l4v `zipWithM`. -/
def zipWithM {γ : Type} (f : α → β → NonDet σ γ) : List α → List β → NonDet σ (List γ)
  | a :: as, b :: bs => NonDet.bind (f a b) fun c =>
      NonDet.bind (zipWithM f as bs) fun cs => NonDet.pure (c :: cs)
  | _, _ => NonDet.pure []

/-- The meaning of a recursive monadic definition made with Isabelle's
`function` package without a termination proof (`rec_del`, `cap_revoke`):
the least fixed point of its defining functional `F` (results ordered by
inclusion, failure by implication). `F` is built from `bind`, `if` and
`case`, which are monotone, so this is a fixed point. On the domain of the
Isabelle function (the arguments from which every recursion terminates) it
is the unique solution of the defining equations, so it agrees with
Isabelle's definition there; outside the domain Isabelle's value is
unspecified. -/
def lfp {ι : Type} (F : (ι → NonDet σ α) → ι → NonDet σ α) : ι → NonDet σ α :=
  (sInf {f : ι → σ → Set (α × σ) × Prop | ∀ i s, F f i s ≤ f i s} : ι → σ → Set (α × σ) × Prop)

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
/-- l4v `liftME`. -/
def liftME {β : Type} (f : α → β) (m : NonDetE σ ε α) : NonDetE σ ε β := do
  let x ← m
  pure (f x)
/-- l4v `mapME`. -/
def mapME {β : Type} (f : α → NonDetE σ ε β) : List α → NonDetE σ ε (List β)
  | [] => pure []
  | a :: as => do
    let b ← f a
    let bs ← mapME f as
    pure (b :: bs)
/-- For `Fl4Spec.undefined` at monadic types (Isabelle `undefined` in a
nonexhaustive `case` whose arms are computations): the witness is irrelevant,
`undefined` is `Classical.choice`. -/
instance : Nonempty (NonDetE σ ε α) := ⟨liftE NonDet.fail⟩
end NonDetE

/-- l4v `Reader_Option_Monad.lookup`: the reader option monad
`'s ⇒ 'a option`. Its bind is l4v `obind`; `do` notation works. -/
abbrev Lookup (σ α : Type) := ReaderT σ Option α

namespace Lookup
variable {σ α β : Type}
/-- l4v `ofail`. -/
def ofail : Lookup σ α := fun _ => none
/-- l4v `oreturn`. -/
def oreturn (a : α) : Lookup σ α := fun _ => some a
/-- l4v `oassert`. -/
def oassert (P : Prop) [Decidable P] : Lookup σ Unit := if P then oreturn () else ofail
/-- l4v `oassert_opt`. -/
def oassertOpt : Option α → Lookup σ α
  | none => ofail
  | some x => oreturn x
/-- l4v `oliftM`. -/
def oliftM (f : α → β) (m : Lookup σ α) : Lookup σ β := do let x ← m; oreturn (f x)
/-- l4v `owhen`. -/
def owhen (P : Prop) [Decidable P] (f : Lookup σ Unit) : Lookup σ Unit := if P then f else oreturn ()
/-- l4v `ounless`. -/
def ounless (P : Prop) [Decidable P] (f : Lookup σ Unit) : Lookup σ Unit := if P then oreturn () else f
/-- l4v `asks`. -/
def asks (f : σ → α) : Lookup σ α := fun s => some (f s)
end Lookup

/-- l4v `opt_map` (infix `|>`): compose a partial map with a partial
projection. -/
def optMap {σ α β : Type} (f : σ → Option α) (g : α → Option β) : σ → Option β :=
  fun s => match f s with
    | none => none
    | some x => g x

/-- l4v `opt_map_Some` (infix `||>`). -/
abbrev optMapSome {σ α β : Type} (f : σ → Option α) (g : α → β) : σ → Option β :=
  optMap f fun s => some (g s)

/-- l4v `opt_pred` (infix `|<`): a predicate through a partial projection,
false where the projection is undefined. -/
def optPred {α β : Type} (P : α → Prop) (proj : β → Option α) : β → Prop :=
  fun x => match proj x with
    | none => False
    | some y => P y

end Fl4Spec
